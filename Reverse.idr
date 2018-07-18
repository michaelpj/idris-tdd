module Main

import Data.Vect

reverse' : Vect n elem -> Vect n elem
reverse' [] = []
reverse' (x :: xs) = reverseProof (reverse' xs ++ [x])
         where
            reverseProof : Vect (k + 1) elem -> Vect (S k) elem
            reverseProof {k} result = rewrite plusCommutative 1 k in result

myPlusCommutes : (n : Nat) -> (m : Nat) -> n + m = m + n
myPlusCommutes Z Z = Refl
myPlusCommutes Z (S k) = rewrite sym (plusZeroRightNeutral k) in Refl
myPlusCommutes (S k) Z = rewrite plusZeroRightNeutral k in Refl
myPlusCommutes (S k) (S j) =    rewrite sym(plusSuccRightSucc k j)
                             in rewrite sym(plusSuccRightSucc j k)
                             in rewrite myPlusCommutes k j
                             in Refl

reverseProof_xs : Vect ((S n) + k) a -> Vect (n + (S k)) a
reverseProof_xs {n} {k} xs = rewrite sym(plusSuccRightSucc n k) in xs

myReverse : Vect n a -> Vect n a
myReverse xs = reverse' [] xs
          where
                reverse' : Vect n a -> Vect m a -> Vect (n+m) a
                reverse' {n} acc [] = rewrite plusZeroRightNeutral n in acc
                reverse' acc (x :: xs) = reverseProof_xs (reverse' (x::acc) xs)
