
{-@ LIQUID "--higherorder" @-} 
{-@ LIQUID "--exact-data-cons" @-}

{-
CMSC 433 Fall 2023
Project 4 - Auxiliary list operations

You may use these in your solutions if you wish. Please do not modify, however; we will use our own version of this file for grading your submission.
-}

module P4Lists where

-- List concatenation suitable for Liquid Haskell

{-@ reflect concatenate @-}
concatenate :: [a] -> [a] -> [a]
concatenate [] l = l
concatenate (h:t) l = h:(concatenate t l)

-- Liquid Haskell type of ordered lists

{-@ type OrderedList a = [a]<{\x y -> x <= y}> @-} 

-- Check if given element is in sorted list

{-@ member :: a -> OrderedList a -> Bool @-}

member :: Ord a => a -> [a] -> Bool
member v [] = False
member v (h:t)
    | v > h     = member v t
    | v == h    = True
    | otherwise = False

-- Insert element into sorted list; note Liquid Haskell specification

{-@ insert :: a -> OrderedList a -> OrderedList a @-}
insert :: Ord t => t -> [t] -> [t]
insert v [] = [v]
insert v (h:t) =
    if v <= h
    then v:h:t
    else h:(insert v t)

-- Remove first instance of element from sorted list, if element is there

{-@ delete :: a -> OrderedList a -> OrderedList a @-}
delete :: Ord a => a -> [a] -> [a]
delete v [] = []
delete v (h:t)
    | v >  h    = h : (delete v t)
    | v == h    = t
    | otherwise = h:t

-- Insertion sort; note Liquid Haskell specification

{-@ insertionSort :: [a] -> OrderedList a @-}

insertionSort :: Ord a => [a] -> [a]
insertionSort [] = []
insertionSort (h:t) = insert h (insertionSort t)
