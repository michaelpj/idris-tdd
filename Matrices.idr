module Matrices 

import Data.Vect

transposeMat : Vect m (Vect n elem) -> Vect n (Vect m elem)
transposeMat [] = replicate _ []
transposeMat (x :: xs) = zipWith (::) x (transpose xs)

addMatrix: Num a => Vect m (Vect n a) -> Vect m (Vect n a) -> Vect m (Vect n a)
addMatrix [] [] = []
addMatrix (x :: xs) (y :: ys) = (zipWith (+) x y) :: (addMatrix xs ys)

dotp: Num a => Vect n a -> Vect n a -> a
dotp [] [] = 0
dotp (x :: xs) (y :: ys) = x * y + dotp xs ys
 
mulTrans : Num a => (xs : Vect n (Vect m a)) -> (ys : Vect p (Vect m a)) -> Vect n (Vect p a)
mulTrans [] ys = []
mulTrans (x :: xs) ys = (map (dotp x) ys) :: mulTrans xs ys

mulMatrix: Num a => Vect n (Vect m a) -> Vect m (Vect p a) -> Vect n (Vect p a)
mulMatrix xs ys = mulTrans xs (transposeMat ys)
