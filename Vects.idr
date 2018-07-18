module Vects

import Data.Vect

tryIndex: Integer -> Vect n a -> Maybe a
tryIndex {n} i xs = case integerToFin i n of
                         Nothing => Nothing
                         (Just x) => Just (index x xs)

vectTake: (k : Fin n) -> Vect n a -> Vect (finToNat k) a
vectTake FZ (x :: xs) = []
vectTake (FS x) (y :: xs) = y :: vectTake x xs

sumEntries : Num a => (pos : Integer) -> Vect n a -> Vect n a -> Maybe a
sumEntries {n} pos xs ys = case integerToFin pos n of
                                Nothing => Nothing
                                (Just i) => Just ((index i xs) + (index i ys))


