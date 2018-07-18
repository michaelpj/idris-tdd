module Elem

import Data.Vect

removeElem : (value : a) -> (xs : Vect (S n) a) -> (prf : Elem value xs) -> Vect n a
removeElem value (value :: ys) Here = ys
removeElem {n = Z} value (y :: []) (There later) = absurd later
removeElem {n = (S k)} value (y :: ys) (There later) = y :: (removeElem value ys later)

notInNil : Elem value [] -> Void
notInNil Here impossible
notInNil (There _) impossible

notInTail : (contraHead : (value = x) -> Void) -> (contraTail : Elem value xs -> Void) -> Elem value (x :: xs) -> Void
notInTail contraHead contraTail Here = contraHead Refl
notInTail contraHead contraTail (There later) = contraTail later

isElem' : DecEq ty => (value : ty) -> (xs : Vect n ty) -> Dec (Elem value xs)
isElem' value [] = No notInNil
isElem' value (x :: xs) = case decEq value x of
                              Yes Refl => Yes Here
                              No contraHead => case isElem' value xs of
                                                 Yes prf => Yes (There prf)
                                                 No contraTail => No (notInTail contraHead contraTail)

data Last : List a -> a -> Type where
     LastOne : Last [value] value
     LastCons : (prf : Last xs value) -> Last (x :: xs) value

Uninhabited (Last [] a) where
    uninhabited LastOne impossible
    uninhabited (LastCons _) impossible

notNilTail : (contra : (x = value) -> Void) -> Last [x] value -> Void
notNilTail contra LastOne = contra Refl
notNilTail contra (LastCons prf) = absurd prf

notTail : (contra : Last (z :: zs) value -> Void) -> Last (y :: (z :: zs)) value -> Void
notTail contra (LastCons prf) = contra prf

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] value = No (\prf => absurd prf)
isLast (y :: ys) value = case isLast ys value of
                              Yes prf => Yes (LastCons prf)
                              No contra => case ys of
                                 [] => case decEq y value of
                                            Yes Refl => Yes LastOne
                                            No contra => No (notNilTail contra)
                                 (z :: zs) => No (notTail contra)
