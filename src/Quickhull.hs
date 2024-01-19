{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RebindableSyntax  #-}
{-# LANGUAGE TypeOperators     #-}

module Quickhull
    ( Point
    , Line
    , SegmentedPoints
    , quickhull

    -- Exported for display
    , initialPartition
    , partition

    -- Exported just for testing
    , propagateL
    , shiftHeadFlagsL
    , segmentedScanl1
    , propagateR
    , shiftHeadFlagsR
    , segmentedScanr1
    ) where

import           Data.Array.Accelerate
import           Data.Array.Accelerate.Debug.Trace
import qualified Prelude                       as P


-- Points and lines in two-dimensional space
--
type Point = (Int, Int)
type Line = (Point, Point)

-- This algorithm will use a head-flags array to distinguish the different
-- sections of the hull (the two arrays are always the same length).
--
-- A flag value of 'True' indicates that the corresponding point is
-- definitely on the convex hull. The points after the 'True' flag until
-- the next 'True' flag correspond to the points in the same segment, and
-- where the algorithm has not yet decided whether or not those points are
-- on the convex hull.
--
type SegmentedPoints = (Vector Bool, Vector Point)


-- Core implementation
-- -------------------

-- Initialise the algorithm by first partitioning the array into two
-- segments. Locate the left-most (p₁) and right-most (p₂) points. The
-- segment descriptor then consists of the point p₁, followed by all the
-- points above the line (p₁,p₂), followed by the point p₂, and finally all
-- of the points below the line (p₁,p₂).
--
-- To make the rest of the algorithm a bit easier, the point p₁ is again
-- placed at the end of the array.
--
-- We indicate some intermediate values that you might find beneficial to
-- compute.
--

initialPartition :: Acc (Vector Point) -> Acc SegmentedPoints
initialPartition points =
    let
        p1, p2 :: Exp Point
        p1 = the $ fold1 min points
        p2 = the $ fold1 max points

        isUpper :: Acc (Vector Bool)
        isUpper = map (pointIsLeftOfLine (T2 p1 p2)) points

        isLower :: Acc (Vector Bool)
        isLower = map (pointIsLeftOfLine (T2 p2 p1)) points

        offsetUpper :: Acc (Vector Int)
        countUpper :: Acc (Scalar Int)
        T2 offsetUpper countUpper = scanl' (+) (isUpper ! I1 0 ? (1,0)) (map boolToInt (shiftHeadFlagsL isUpper))

        offsetLower :: Acc (Vector Int)
        countLower :: Acc (Scalar Int)
        T2 offsetLower countLower = scanl' (+) (isLower ! I1 0 ? (1,0)) (map boolToInt (shiftHeadFlagsL isLower))

        zipFunction ::Exp Bool -> Exp Bool -> Exp Int -> Exp Int -> Exp (Maybe DIM1)
        zipFunction isUppervalue isLowervalue offUpper offLower = isUppervalue ? (Just_ (index1 offUpper), isLowervalue ? (Just_ (index1 (offLower + the countUpper)), Nothing_))

        destination :: Acc (Vector (Maybe DIM1))
        destination = zipWith4 zipFunction isUpper isLower offsetUpper offsetLower

        base :: Acc (Vector Point)
        base = generate
                    (I1 (the countLower + the countUpper + 1))
                    (\(I1 ix) -> ix == 0 ||
                        ix == the countLower + the countUpper
                        ? (p1, p2))

        newPoints :: Acc (Vector Point)
        newPoints = permute const base (destination !) points

        headFlags :: Acc (Vector Bool)
        headFlags = zipWith (==) newPoints base
    in
        T2 headFlags newPoints


-- The core of the algorithm processes all line segments at once in
-- data-parallel. This is similar to the previous partitioning step, except
-- now we are processing many segments at once.
--
-- For each line segment (p₁,p₂) locate the point furthest from that line
-- p₃. This point is on the convex hull. Then determine whether each point
-- p in that segment lies to the left of (p₁,p₃) or the right of (p₂,p₃).
-- These points are undecided.
--
partition :: Acc SegmentedPoints -> Acc SegmentedPoints
partition (T2 headFlags points) =
    let
        propL :: Acc (Vector Point)
        propL = propagateL (atraceId "HeadFlags" headFlags) (atraceId "Points: " points)

        propR :: Acc (Vector Point)
        propR = propagateR headFlags points

        distances :: Acc (Vector Int)
        distances = atraceId "distances" (zipWith3 (\p1 p2 p -> nonNormalizedDistance (T2 p1 p2) p) propL propR points)

        moreDistantPoint :: Exp (Point, Int) -> Exp (Point, Int) -> Exp (Point, Int)
        moreDistantPoint t1@(T2 _ d1) t2@(T2 _ d2) = d1 >= d2 ? (t1,t2)

        partial_furthest_point :: Acc (Vector Point)
        partial_furthest_point = atraceId "partial furthest point" $ map fst $ segmentedScanl1 moreDistantPoint headFlags (zip points distances)

        furthest_point :: Acc (Vector Point)
        furthest_point =         atraceId "Furthest point: " $ map fst $ segmentedScanr1 moreDistantPoint headFlags (zip partial_furthest_point distances)

        isFurthestPoint :: Acc (Vector Bool)
        isFurthestPoint =         atraceId "isFuthestPoint" $ zipWith (==) furthest_point points

        isLeftFirst:: Acc (Vector Bool)
        isLeftFirst =             atraceId "is Left First " $ zipWith3 (\p p1 m -> pointIsLeftOfLine (T2 p1 m) p ) points propL furthest_point

        isLeftSecond:: Acc (Vector Bool)
        isLeftSecond =            atraceId "is Left Second" $ zipWith3 (\p p2 m -> pointIsLeftOfLine (T2 m p2) p ) points propR furthest_point

        offsetLeftFirst :: Acc (Vector Int)
        offsetLeftFirst = atraceId "offsetLeftFirst" $ segmentedScanl1 (+) headFlags (map boolToInt isLeftFirst)

        offsetLeftSecond :: Acc (Vector Int)
        offsetLeftSecond = atraceId "offsetLeftSecnd" $ segmentedScanl1 (+) headFlags (map boolToInt isLeftSecond)

        countOffsetLeftFirst :: Acc (Vector Int)
        countOffsetLeftFirst = atraceId "cntoffLeftFirst" $ segmentedScanr1 max headFlags offsetLeftFirst

        countOffsetLeftSecond :: Acc (Vector Int)
        countOffsetLeftSecond = atraceId "cntoffLeftSecnd" $ segmentedScanr1 max headFlags offsetLeftSecond

        stenFunc :: Stencil3 (Int, Int) -> Exp Int
        stenFunc (T2 prev1 prev2 , T2 current1 current2,  _) = (current1 == 0 && current2 == 0) ? ((prev1 == current1 && prev2 == current2) ? (0, prev1 + prev2 + 2), 0)

        stencilRes :: Acc (Vector Int)
        stencilRes = stencil stenFunc clamp (zip countOffsetLeftFirst countOffsetLeftSecond)

        generalOffset :: Acc (Vector Int)
        generalOffset = atraceId "genOff" $ scanl1 (+) stencilRes

        zipFunction4 :: Exp Bool -> Exp Bool -> Exp Int -> Exp Int -> Exp Int
        zipFunction4 headFlag isFurthest genOff colf = isFurthest ? (headFlag ? (genOff,genOff + colf + 1), 0)

        truePointsDestinations :: Acc (Vector Int)
        truePointsDestinations = atraceId "True points destination" $ zipWith4 zipFunction4 headFlags isFurthestPoint generalOffset countOffsetLeftFirst

        zipFunction6 ::Exp Bool -> Exp Bool -> Exp Int -> Exp Int -> Exp Int -> Exp Int -> Exp (Maybe DIM1)
        zipFunction6 islf isls olf ols colf genoff= islf ? (Just_ (index1 (genoff + olf)), isls ? (Just_ (index1 (genoff + ols + colf + 1)), Nothing_))

        basePointDestination :: Acc (Vector (Maybe DIM1))
        basePointDestination =   atraceId "Base points destination" $   zipWith (\isTruePoint truePointsDestination -> isTruePoint ? (Just_ (index1 truePointsDestination), Nothing_)) isFurthestPoint truePointsDestinations

        destination :: Acc (Vector (Maybe DIM1))
        destination = zipWith6 zipFunction6 isLeftFirst isLeftSecond offsetLeftFirst offsetLeftSecond countOffsetLeftFirst generalOffset

        final_dimension :: Exp Int
        final_dimension =   generalOffset !! (length generalOffset - 1)

        finalbase :: Acc (Vector Point)
        finalbase = permute const (fill (I1 (final_dimension + 1)) (points ! I1 0)) (basePointDestination!) points

        newPoints :: Acc (Vector Point)
        newPoints = atraceId "newPoint" $ permute const finalbase (destination !) points

        newHeadFlags :: Acc (Vector Bool)
        newHeadFlags = atraceId "newHeadFlags" $ zipWith (==) newPoints finalbase
    in
        -- initialPartition points
        T2 newHeadFlags newPoints


-- The completed algorithm repeatedly partitions the points until there are
-- no undecided points remaining. What remains is the convex hull.
--
quickhull :: Acc (Vector Point) -> Acc (Vector Point)
quickhull points = asnd $ awhile (unit . not . the . and . afst) partition (initialPartition points)


-- Helper functions
-- ----------------

propagateL :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
propagateL = segmentedScanl1 const

propagateR :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
propagateR = segmentedScanr1 const

shiftHeadFlagsL :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsL flags = scatter inices (fill (shape flags) True_) (drop 1 flags)
    where inices = generate (I1 (length flags - 1)) (\(I1 i) -> i)

shiftHeadFlagsR :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsR flags = scatter inices (fill (shape flags) True_) flags
    where inices = generate (I1 (length flags - 1)) (\(I1 i) -> i + 1)

segmentedScanl1
    :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedScanl1 f flags array = map snd $ scanl1 (segmented f) (zip flags array)

segmentedScanr1
    :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedScanr1 f flags array = map snd $ scanr1 (flip (segmented f)) (zip flags array)


-- Given utility functions
-- -----------------------

pointIsLeftOfLine :: Exp Line -> Exp Point -> Exp Bool
pointIsLeftOfLine (T2 (T2 x1 y1) (T2 x2 y2)) (T2 x y) = nx * x + ny * y > c
  where
    nx = y1 - y2
    ny = x2 - x1
    c  = nx * x1 + ny * y1

nonNormalizedDistance :: Exp Line -> Exp Point -> Exp Int
nonNormalizedDistance (T2 (T2 x1 y1) (T2 x2 y2)) (T2 x y) = nx * x + ny * y - c
  where
    nx = y1 - y2
    ny = x2 - x1
    c  = nx * x1 + ny * y1

segmented :: Elt a => (Exp a -> Exp a -> Exp a) -> Exp (Bool, a) -> Exp (Bool, a) -> Exp (Bool, a)
segmented f (T2 aF aV) (T2 bF bV) = T2 (aF || bF) (bF ? (bV, f aV bV))

