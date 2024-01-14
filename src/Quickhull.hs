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
        p1 = the $ fold1
            (\pt1@(T2 x1 y1) pt2@(T2 x2 y2) ->
                if x1 < x2 then pt1 else if x1 > x2 then pt2 else if y1 > y2 then pt1 else pt2
            )
            points
        p2 = the $ fold1
            (\pt1@(T2 x1 y1) pt2@(T2 x2 y2) ->
                if x1 > x2 then pt1 else if x1 < x2 then pt2 else if y1 < y2 then pt1 else pt2
            )
            points

        baseline :: Exp Line
        baseline = T2 p1 p2

        opposite_baseline :: Exp Line
        opposite_baseline = T2 p2 p1

        isUpper :: Acc (Vector Bool)
        isUpper = map (pointIsLeftOfLine baseline) points

        isLower :: Acc (Vector Bool)
        isLower = map (pointIsLeftOfLine opposite_baseline) points

        offsetUpper :: Acc (Vector Int)
        countUpper :: Acc (Scalar Int)
        T2 offsetUpper countUpper = filter (isUpper !!) (generate (shape points) (\(I1 ix) -> ix))
            -- error "TODO: number of points above the line and their relative index"

        offsetLower :: Acc (Vector Int)
        countLower :: Acc (Scalar Int)
        T2 offsetLower countLower = filter (isLower !!) (generate (shape points) (\(I1 ix) -> ix))
            -- error "TODO: number of points below the line and their relative index"

        zeros :: Acc (Vector Int)
        zeros = fill  (I1 (the countLower + the countUpper + constant 2)) 0

        generateUpper :: Acc (Vector Int)
        generateUpper = generate (I1 (the countUpper)) (\(I1 ix) -> ix+1 )

        generateLower :: Acc (Vector Int)
        generateLower = generate (I1 (the countLower)) (\(I1 ix) -> ix+2 + the countUpper )

        concatVector:: Acc(Vector Int)
        concatVector = scatter generateLower (scatter generateUpper zeros offsetUpper) offsetLower

        justIndexes :: Acc (Vector (Maybe DIM1))
        justIndexes = generate (I1 (the countLower + the countUpper + constant 2)) (\(I1 ix) -> Just_ (index1 ix))

        nothingBase :: Acc (Vector (Maybe DIM1))
        nothingBase = fill (shape points) Nothing_

        destination :: Acc (Vector (Maybe DIM1))
        destination = scatter concatVector nothingBase justIndexes

        p12base :: Acc (Vector Point)
        p12base = generate 
                    (I1 (the countLower + the countUpper + constant 3)) 
                    (\(I1 ix) -> ix == 0 || ix == the countLower + the countUpper + constant 2 ? (p1, p2))

        newPoints :: Acc (Vector Point)
        newPoints = permute max p12base (destination !) points

        headFlags :: Acc (Vector Bool)
        headFlags = 
            generate (shape newPoints)
                (\(I1 ix) -> (
                 ix == 0 ||
                 ix == the countUpper + 1 ||
                 ix == the countLower + the countUpper + constant 2)
                 ? (True_, False_))
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
partition (T2 headFlags points) = error "TODO: partition"


-- The completed algorithm repeatedly partitions the points until there are
-- no undecided points remaining. What remains is the convex hull.
--
quickhull :: Acc (Vector Point) -> Acc (Vector Point)
quickhull = error "TODO: quickhull"


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

