{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RebindableSyntax  #-}
{-# LANGUAGE TypeOperators     #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use guards" #-}

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
    let p1, p2 :: Exp Point
        p1 = the $ fold1 min points
        p2 = the $ fold1 max points

        isUpper :: Acc (Vector Bool)
        isUpper = map (pointIsLeftOfLine (T2 p1 p2)) points

        isLower :: Acc (Vector Bool)
        isLower = map (pointIsLeftOfLine (T2 p2 p1)) points

        offsetUpper :: Acc (Vector Int)
        countUpper :: Acc (Scalar Int)
        T2 offsetUpper countUpper =
            scanl' (+) (isUpper ! I1 0 ? (1, 0)) (map boolToInt (shiftHeadFlagsL isUpper))

        offsetLower :: Acc (Vector Int)
        countLower :: Acc (Scalar Int)
        T2 offsetLower countLower =
            scanl' (+) (isLower ! I1 0 ? (1, 0)) (map boolToInt (shiftHeadFlagsL isLower))

        zipFunction :: Exp Bool -> Exp Bool -> Exp Int -> Exp Int -> Exp (Maybe DIM1)
        zipFunction isUppervalue isLowervalue offUpper offLower =
            isUppervalue
                ? ( Just_ (index1 offUpper)
                  , isLowervalue ? (Just_ (index1 (offLower + the countUpper)), Nothing_)
                  )

        destination :: Acc (Vector (Maybe DIM1))
        destination = zipWith4 zipFunction isUpper isLower offsetUpper offsetLower

        base :: Acc (Vector Point)
        base = generate
            (I1 (the countLower + the countUpper + 1))
            (\(I1 ix) -> ix == 0 || ix == the countLower + the countUpper ? (p1, p2))

        newPoints :: Acc (Vector Point)
        newPoints = permute const base (destination !) points

        headFlags :: Acc (Vector Bool)
        headFlags = zipWith (==) newPoints base
    in  T2 headFlags newPoints


-- The core of the algorithm processes all line segments at once in
-- data-parallel. This is similar to the previous partitioning step, except
-- now we are processing many segments at once.
--
-- For each line segment (p₁,p₂) locate the point furthest from that line
-- p₃. This point is on the convex hull. Then determine whether each point
-- p in that segment lies to the left of (p₁,p₃) or the right of (p₂,p₃).
-- These points are undecided.
partition :: Acc SegmentedPoints -> Acc SegmentedPoints
partition (T2 headFlags points) =
    let
        -- provides p1 point of the line for each point
        propL :: Acc (Vector Point)
        propL = propagateL headFlags points

        -- provides p2 point of the line for each point
        propR :: Acc (Vector Point)
        propR = propagateR headFlags points

        -- compute distances for each point with their line p1 p2
        distances :: Acc (Vector Int)
        distances = zipWith3 (\p1 p2 p -> nonNormalizedDistance (T2 p1 p2) p) propL propR points

        -- function that propagates the tuple (point, distance) with the highest distance
        -- In the case that there are multiple points that have the maximum distance, the testing
        -- framework expects the top-most, right-most point.
        moreDistantPoint :: Exp (Point, Int) -> Exp (Point, Int) -> Exp (Point, Int)
        moreDistantPoint t1@(T2 p1 d1) t2@(T2 p2 d2) =
            (if (d1 > d2) || (d1 == d2 && p1 > p2) then t1 else t2)

        partial_furthest_point :: Acc (Vector Point)
        partial_furthest_point =
            map fst $ segmentedScanl1 moreDistantPoint headFlags (zip points distances)

        -- double scan (left and right) to have the furthest point from the line of a segment for
        -- each point of a segment
        certainly_on_hull :: Acc (Vector Point)
        certainly_on_hull = map fst
            $ segmentedScanr1 moreDistantPoint headFlags (zip partial_furthest_point distances)

        -- True flag for every true HeadFlag and at every index in which the point is the furthest
        -- point
        isFurthestPoint :: Acc (Vector Bool)
        isFurthestPoint = zipWith (==) certainly_on_hull points

        -- Check if the point is at the left of the line that is formed with p1 and the furthest
        -- point
        isLeftFirst :: Acc (Vector Bool)
        isLeftFirst =
            zipWith3 (\p p1 m -> pointIsLeftOfLine (T2 p1 m) p) points propL certainly_on_hull

        -- Check if the point is at the left of the line that is formed with the furthest point and
        -- p2
        isLeftSecond :: Acc (Vector Bool)
        isLeftSecond =
            zipWith3 (\p p2 m -> pointIsLeftOfLine (T2 m p2) p) points propR certainly_on_hull

        -- scans and count True flags in isLeftFirst
        offsetLeftFirst :: Acc (Vector Int)
        offsetLeftFirst = segmentedScanl1 (+) headFlags (map boolToInt isLeftFirst)

        -- scans and count True flags in isLeftSecond
        offsetLeftSecond :: Acc (Vector Int)
        offsetLeftSecond = segmentedScanl1 (+) headFlags (map boolToInt isLeftSecond)

        -- at every index, gets the total amount of elements that will be added in the first line
        countOffsetLeftFirst :: Acc (Vector Int)
        countOffsetLeftFirst = segmentedScanr1 max headFlags offsetLeftFirst

        -- at every index, gets the total amount of elements that will be added in the second line
        countOffsetLeftSecond :: Acc (Vector Int)
        countOffsetLeftSecond = segmentedScanr1 max headFlags offsetLeftSecond

        stenFunc :: Stencil3 (Int, Int, Bool) -> Exp Int
        stenFunc (T3 preColf preCols preHF, T3 _ _ currHF, _) =
            if not currHF || (preColf == (-1) && preCols == (-1))
                -- if it's not a headflag or it is the first element of the array then we don't need
                -- to increment and put 0
                then 0
                -- the value will be incremented by the amount of elements that will be inserted
                -- since last True HeadFlags up to now
                else preColf + preCols + (preHF ? (1, 2))

        -- out of bound elements must be recognizable, it returns a negative tuple
        boundary :: Boundary (Vector (Int, Int, Bool))
        -- False is not necessary, could also be True
        boundary = function $ \_ -> T3 (-1) (-1) False_

        -- apply the stencil
        stencilRes :: Acc (Vector Int)
        stencilRes = stencil stenFunc
                             boundary
                             (zip3 countOffsetLeftFirst countOffsetLeftSecond headFlags)

        -- provides an offset for all future points, since countOffSetLeftFirst and Second only
        -- consider the actual segment
        generalOffset :: Acc (Vector Int)
        generalOffset = scanl1 (+) stencilRes

        -- function that explains how to use the general offset to compute the destination index of
        -- either a headFlags point or a furthest point
        zipFunction4 :: Exp Bool -> Exp Bool -> Exp Int -> Exp Int -> Exp Int
        zipFunction4 headFlag isFurthest genOff colf = if isFurthest
            then if headFlag then genOff else genOff + colf + 1 -- colf = countOffsetLineFirst
            else 0

        -- compute destination index for headFlags points and furthest points
        furthestOrHF_PointsDestinations :: Acc (Vector Int)
        furthestOrHF_PointsDestinations =
            zipWith4 zipFunction4 headFlags isFurthestPoint generalOffset countOffsetLeftFirst

        basePointDestination :: Acc (Vector (Maybe DIM1))
        basePointDestination = zipWith
            (\isHF_orFurthest truePointsDestination -> if isHF_orFurthest
                then -- if headFlag or is a furthest point
                     Just_ (index1 truePointsDestination) -- get the computed value at that index
                else Nothing_
            )
            isFurthestPoint
            furthestOrHF_PointsDestinations

        -- compute the destination of all the other points that might still be on the convex hull
        -- (but we don't know yet)
        zipFunction6
            :: Exp Bool -> Exp Bool -> Exp Int -> Exp Int -> Exp Int -> Exp Int -> Exp (Maybe DIM1)
        zipFunction6 is_lf is_ls olf ols colf genoff = if is_lf -- is left first
            -- general offset + offset left first
            then Just_ (index1 (genoff + olf))
            -- is left second 
            else if is_ls
                -- general offset + count offset left first + offset left second
                then Just_ (index1 (genoff + colf + 1 + ols))
                -- if none of those than the point surely isn't part of the convex hull
                else Nothing_

        destination :: Acc (Vector (Maybe DIM1))
        destination = zipWith6 zipFunction6
                               isLeftFirst
                               isLeftSecond
                               offsetLeftFirst
                               offsetLeftSecond
                               countOffsetLeftFirst
                               generalOffset

        -- the amount of needed points(+1) is stored at the end of the generalOffset vector at the
        -- last index
        final_dimension :: Exp Int
        final_dimension = generalOffset !! (length generalOffset - 1) + 1

        -- write on an empty base all the HF points and the furthest points
        finalbase :: Acc (Vector Point)
        finalbase = permute const
                            (fill (I1 final_dimension) (points ! I1 0))
                            (basePointDestination !)
                            points

        -- write on the final base all the other points (not HF and not Furthest that might still
        -- be part of the convex hull)
        newPoints :: Acc (Vector Point)
        newPoints = permute const finalbase (destination !) points

        -- all points on the final base that have not been overwritten are the HF for the next step
        newHeadFlags :: Acc (Vector Bool)
        newHeadFlags = zipWith (==) newPoints finalbase
    in
        -- initialPartition points
        T2 newHeadFlags newPoints


-- The completed algorithm repeatedly partitions the points until there are
-- no undecided points remaining. What remains is the convex hull.
--
quickhull :: Acc (Vector Point) -> Acc (Vector Point)
quickhull points = tail $ asnd $ awhile (map not . and . afst) partition (initialPartition points)


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

