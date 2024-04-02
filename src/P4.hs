{-@ LIQUID "--higherorder" @-} 
{-@ LIQUID "--exact-data-cons" @-}

{-
CMSC 433 Fall 2023
Project 4 - Binary / Balanced / Binary-Search Trees
Perfect Score:  100 points

This project asks you to implement 10 functions associated with manipulating binary trees, balanced binary trees, and binary search trees.

Each function includes a textual description of what the functions should do.  In addition, many functions also contain Liquid Haskell refinement types that precisely describe the functions' intended behavior.

Three of the operations (memberBST, insertBST and deleteBST) require you to implement the associated operations "in time proportional to the height of the tree."  This means you must use one of the tree-based recursive implementations of these operations; examples (but not the only approach) may be found here: 

    https://en.wikipedia.org/wiki/Binary_search_tree.

You are *not* allowed to convert the trees to lists, perform the associated list operations, then convert the lists back to trees, even though the Liquid Haskell specifications use this approach to define correctness!

YOU ARE NOT REQUIRED TO USE LIQUID HASKELL FOR THIS PROJECT!  If you do, however, and are able to prove your specifications correct, then your code will be guaranteed to pass all tests we will use in autograding.

This project file also contains a companion file, P4Lists.hs, which implements various list utility functions that you may use.  This file has been verified using Liquid Haskell, it should be noted.
-}

module P4Solutions where

import P4Lists
import Data.Void (vacuous)
import Distribution.Compat.CharParsing (lower)
import Data.Graph (Tree(Node))
import Distribution.SPDX (LicenseId(NCGL_UK_2_0))

-- PROBLEM 1 (5 points)
--
-- Implement function upperBound, which should return True iff all elements in
-- the list are <= the given element.

{-@ reflect upperBound @-}
upperBound :: Ord a => [a] -> a -> Bool
--
-- TODO
--
upperBound (a:[]) v = a <= v
upperBound [] _ = False
upperBound (h:t) v
    | h <= v = upperBound t v
    | otherwise = False

-- PROBLEM 2 (5 points)
--
-- Implement function lowerBound, which should return True iff the given value
-- is <= all elements in the list.

{-@ reflect lowerBound @-}
lowerBound :: Ord a => a -> [a] -> Bool
--
-- TODO
--
lowerBound v (a:[]) = a >= v
lowerBound _ [] = False
lowerBound v (h : t)
    | h >= v = lowerBound v t
    | otherwise = False

-- Binary-tree data type

data BinaryTree a =
    NullBT
    | NodeBT a (BinaryTree a) (BinaryTree a)
    deriving (Eq, Show)

-- Liquid Haskell version of binary trees  
{-@
data BinaryTree a =
      NullBT
    | NodeBT (val :: a) (left :: BinaryTree a) (right :: BinaryTree a)
@-}

-- Version of max suitable for Liquid Haskell

{-@ inline max' @-}
max' :: Ord a => a -> a -> a
max' x y = if x > y then x else y

-- Height of a binary tree

{-@ measure height @-}
height :: BinaryTree a -> Int
height NullBT = 0
height (NodeBT a t1 t2) = 1 + max' (height t1) (height t2)

-- In-order listing of nodes in binary tree

{-@ reflect inOrder @-}
inOrder :: BinaryTree a -> [a]
inOrder NullBT = []
inOrder (NodeBT v t1 t2) = concatenate (inOrder t1) (v:(inOrder t2))

-- Test if given binary tree is null

{-@ measure nullBT @-}
nullBT :: BinaryTree a -> Bool
nullBT NullBT = True
nullBT _ = False

-- PROBLEM 3 (10 points)
--
-- Implement function balancedBT, which should return True if and only if
-- the given tree is *balanced*.  This property holds of a tree if, for
-- every node in the tree, the heights of the subtrees rooted at the node
-- differ by at most 1.

{-@ measure balancedBT @-}
balancedBT :: BinaryTree a -> Bool
--
-- TODO
--
balancedBT NullBT = True
balancedBT (NodeBT a l r) = (abs((height l) - (height r)) <= 1) && balancedBT l && balancedBT r

-- Liquid Haskell type of balanced binary trees

{-@ type BalancedBT a = {t : BinaryTree a | balancedBT t} @-}

-- PROBLEM 4 (10 points)
--
-- Implement function makeBalancedBT, which, given a list, builds a
-- balanced binary tree whose in-order traversal is the same as the
-- input list.

{-@ makeBalancedBT :: l:[a] -> {t : BalancedBT a | inOrder t == l} @-}
makeBalancedBT :: [a] -> BinaryTree a
--
-- TODO
--
makeBalancedBT [] = NullBT
makeBalancedBT x = let (l, h : r) = splitAt (length x `div` 2) x in NodeBT h (makeBalancedBT l) (makeBalancedBT r)

-- PROBLEM 5 (10 points)
--
-- Implement function balanceBT, which, given a binary tree, returns
-- a balanced binary tree whose in-order traveral is the same as that
-- of the input tree.

{-@ balanceBT :: t1:(BinaryTree a) -> {t2 : BalancedBT a | inOrder t1 == inOrder t2} @-}
balanceBT :: BinaryTree a -> BinaryTree a
--
-- TODO
--
balanceBT NullBT = NullBT
balanceBT x = makeBalancedBT (inOrder x)

-- PROBLEM 6 (10 points)
--
-- Implement function bst, which returns True iff the input binary tree
-- is a binary search tree (BST).  A BST has the property that, at each node,
-- all the node values in the left subtree are <= the node's value and all node
-- values in the right subtree are >= the node's value.

{-@ reflect bst @-}
bst :: (Ord a) => BinaryTree a -> Bool
--
-- TODO
--
bst NullBT = True
bst (NodeBT x l r) = bstLeft x l && bstRight x r && bst l && bst r


bstLeft :: (Ord a) => a -> BinaryTree a -> Bool
bstLeft _ NullBT = True
bstLeft x (NodeBT v _ _ ) = x >= v 

bstRight :: (Ord a) => a -> BinaryTree a -> Bool
bstRight _ NullBT = True
bstRight x (NodeBT v _ _ ) = x <= v

-- PROBLEM 7 (10 points)
--
-- Implement function minBST, which for non-empty BSTs returns
-- the smallest value stored in the tree.

{-@ minBT :: t : {t1 : BST a | not (nullBT t)} -> {v : a | lowerBound v (inOrder t)} @-}
minBT :: BinaryTree a -> a
--
-- TODO
--
minBT (NodeBT v NullBT _ ) = v
minBT (NodeBT v l r ) = minBT l

-- PROBLEM 8 (10 points)
--
-- Implement function memberBST, which returns True iff the given element
-- is in the given BST.  Your function must work in time proportional to
-- the height of the tree; no generating a list from the tree!

{-@ memberBST :: k:a -> t:(BST a) -> {v : Bool | v == member k (inOrder t)} @-}
memberBST :: Ord a => a -> BinaryTree a -> Bool
--
-- TODO
--
memberBST _ NullBT = False
memberBST k (NodeBT v l r )
    | k == v = True
    | k < v = memberBST k l
    | otherwise = memberBST k r



-- PROBLEM 9 (10 points)
--
-- Implement functon insertBST, which inserts the given value into the
-- given BST in such a way that the result tree is also a BST.  Your
-- function must work in time proportional to the height of the tree;
-- no generating a list from the tree!

{-@ insertBST :: k:a -> t:(BST a) -> {t':BST a | inOrder t1 == insert k (inOrder t)} @-}
insertBST :: (Ord a) => a -> BinaryTree a -> BinaryTree a
--
-- TODO
--
insertBST v NullBT = (NodeBT v NullBT NullBT)
insertBST k (NodeBT v l r) 
    | k < v = NodeBT v (insertBST k l) r
    | otherwise = NodeBT v l (insertBST k r)


-- PROBLEM 10 (20 points)
--
-- Implement function deleteBST, which removes the given value from the
-- BST if it is there, returning a BST.  Your function must work in
-- time proportional to the height of the tree; no generating a list from
-- the tree!

deleteBST :: (Ord a) => a -> BinaryTree a -> BinaryTree a

deleteBST _ NullBT = NullBT
deleteBST v (NodeBT v2 NullBT r)
    | v > v2 = r
    | v < v2 = NodeBT v2 NullBT r
    | otherwise = NullBT
deleteBST v (NodeBT v2 l NullBT)
    | v < v2 = l
    | v > v2 = NodeBT v2 l NullBT
    | otherwise = NullBT
deleteBST v (NodeBT v2 l r)
    | v < v2 = NodeBT v2 (deleteBST v l) r
    | v > v2 = NodeBT v2 l (deleteBST v r)
    | otherwise = NodeBT (successor r) l (deleteBST (successor r) r)

successor :: BinaryTree a -> a
successor (NodeBT v NullBT _ )= v
successor (NodeBT v l _ ) = successor l

main :: IO ()
main = do

    let bst1 = NodeBT 8 (NodeBT 2 NullBT NullBT) (NodeBT 5 NullBT NullBT)
    putStrLn $ show $ bst1

    let bst2 = deleteBST 5 bst1
    putStrLn $ show $ bst2



    


