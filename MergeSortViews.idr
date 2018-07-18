import Data.List.Views

import Data.Vect
import Data.Vect.Views

import Data.Nat.Views

total
mergeSort : Ord a => List a -> List a
mergeSort input with (splitRec input)
  mergeSort [] | SplitRecNil = []
  mergeSort [x] | SplitRecOne = [x]
  mergeSort (lefts ++ rights) | (SplitRecPair lrec rrec) = merge (mergeSort lefts | lrec) (mergeSort rights | rrec)

total
equalSuffix : Eq a => List a -> List a -> List a
equalSuffix input1 input2 with (snocList input1)
  equalSuffix [] input2 | Empty = []
  equalSuffix (xs ++ [x]) input2 | (Snoc rec1) with (snocList input2)
    equalSuffix (xs ++ [x]) [] | (Snoc rec1) | Empty = []
    equalSuffix (xs ++ [x]) (ys ++ [y]) | (Snoc rec1) | (Snoc rec2) = let suffixRec = equalSuffix xs ys | rec1 | rec2
                                                                      in if x == y
                                                                         then suffixRec ++ [x]
                                                                         else suffixRec


total
mergeSortV : Ord a => Vect n a -> Vect n a
mergeSortV input with (splitRec input)
  mergeSortV [] | SplitRecNil = []
  mergeSortV [x] | SplitRecOne = [x]
  mergeSortV (xs ++ ys) | (SplitRecPair lrec rrec) = merge (mergeSortV xs | lrec) (mergeSortV ys | rrec)

total
toBinary : Nat -> String
toBinary k with (halfRec k)
  toBinary Z | HalfRecZ = ""
  toBinary (n + n) | (HalfRecEven rec) = (toBinary n | rec) ++ "0"
  toBinary (S (n + n)) | (HalfRecOdd rec) = (toBinary n | rec) ++ "1"

total
palindrome: Eq a => List a -> Bool
palindrome xs with (vList xs)
  palindrome [] | VNil = True
  palindrome [x] | VOne = True
  palindrome (x :: (ys ++ [y])) | (VCons rec) = x == y && (palindrome ys | rec)

