{-# LANGUAGE ScopedTypeVariables, DataKinds, TypeFamilies, RankNTypes, ConstraintKinds, TypeOperators, UndecidableInstances, TemplateHaskell #-}
module Types.Nat( 
  -- * Representation data types
  Digit(..),
  Nat(..),
  nat,
  -- * Converting between values and types
  -- ** Digits
  TypeDigit(..),
  reifyDigit,
  -- ** Naturals
  TypeNat(..),
  reifyNat,
  -- * Arithmetic
  (:+),
  (:-),
  (:*),
  -- * Comparison
  Compare,
  (:<),
  (:==),
  (:>),
  (:>=),
  (:<=),
 )  
  where

import Prelude hiding(Int)
import Types.Common
import Types.Bool
import Types.Ord

import Language.Haskell.TH(Q, Type)

infixl :.

data Digit = D0 | D1 | D2 | D3 | D4 | D5 | D6 | D7 | D8 | D9

-- | A 'Nat' is a snoc-list of 'Digit's.
--
-- @D1 :. D4 :. D0@ represents 140.
data Nat 
  = Dec Digit 
  | Nat :. Digit

dig :: Integer -> Q Type
dig 0 = [t| D0 |]
dig 1 = [t| D1 |]
dig 2 = [t| D2 |]
dig 3 = [t| D3 |]
dig 4 = [t| D4 |]
dig 5 = [t| D5 |]
dig 6 = [t| D6 |]
dig 7 = [t| D7 |]
dig 8 = [t| D8 |]
dig 9 = [t| D9 |]

-- | Type quoter: for instance:
--
-- @v :: Vector $(nat 127) Double@
nat :: Integer -> Q Type
nat n = case quotRem n 10 of
  (0, d) -> [t| Dec $(dig d) |]
  (m, d) -> [t| $(nat m) :. $(dig d) |]

--- reflecting digits
class TypeDigit (d :: Digit) where reflectDigit :: Num a => Tagged d a
instance TypeDigit D0 where reflectDigit = Tagged 0
instance TypeDigit D1 where reflectDigit = Tagged 1
instance TypeDigit D2 where reflectDigit = Tagged 2
instance TypeDigit D3 where reflectDigit = Tagged 3
instance TypeDigit D4 where reflectDigit = Tagged 4
instance TypeDigit D5 where reflectDigit = Tagged 5
instance TypeDigit D6 where reflectDigit = Tagged 6
instance TypeDigit D7 where reflectDigit = Tagged 7
instance TypeDigit D8 where reflectDigit = Tagged 8
instance TypeDigit D9 where reflectDigit = Tagged 9

-- reflect nats
class TypeNat (n :: Nat) where reflectNat :: Num a => Tagged n a

instance TypeDigit d => TypeNat (Dec d) where
  reflectNat = conv reflectDigit 
    where
      conv :: Tagged dig a -> Tagged (Dec dig) a 
      conv = Tagged . unTagged

instance (TypeNat n, TypeDigit d) => TypeNat (n :. d) where
  reflectNat = mk reflectNat reflectDigit
    where
      mk :: Num a => Tagged n a -> Tagged d a -> Tagged (n :. d) a
      mk (Tagged n) (Tagged d) = Tagged (10*n + d)

-- reify nats
reifyDigit :: forall a r. (Eq a, Num a) => a -> (forall d. TypeDigit d => Tagged d r) -> r
reifyDigit 0 k = unTagged (k :: Tagged D0 r)
reifyDigit 1 k = unTagged (k :: Tagged D1 r)
reifyDigit 2 k = unTagged (k :: Tagged D2 r)
reifyDigit 3 k = unTagged (k :: Tagged D3 r)
reifyDigit 4 k = unTagged (k :: Tagged D4 r)
reifyDigit 5 k = unTagged (k :: Tagged D5 r)
reifyDigit 6 k = unTagged (k :: Tagged D6 r)
reifyDigit 7 k = unTagged (k :: Tagged D7 r)
reifyDigit 8 k = unTagged (k :: Tagged D8 r)
reifyDigit 9 k = unTagged (k :: Tagged D9 r)
      
reifyNat :: forall a r. Integral a => a -> (forall n. TypeNat n => Tagged n r) -> r
reifyNat n k = 
  case quotRem n 10 of
    (0, d) ->
      reifyDigit d cont
        where
          cont :: forall d. TypeDigit d => Tagged d r
          cont = reTag (k :: Tagged (Dec d) r)
    (m, d) -> 
      reifyNat m cont
        where
          cont :: forall n. TypeNat n => Tagged n r
          cont = Tagged (reifyDigit d cont2)
            where
              cont2 :: forall d. TypeDigit d => Tagged d r
              cont2 = reTag (k :: Tagged (n :. d) r)
        

-- addition
type family Div10 (n :: Nat) :: Nat
type instance Div10 (Dec d) = Dec D0 
type instance Div10 (n :. d) = n

type family Mod10 (n :: Nat) :: Digit
type instance Mod10 (Dec d) = d
type instance Mod10 (n :. d) = d

type family Succ (n :: Nat) :: Nat
type instance Succ (Dec D0) = Dec D1
type instance Succ (Dec D1) = Dec D2
type instance Succ (Dec D2) = Dec D3
type instance Succ (Dec D3) = Dec D4
type instance Succ (Dec D4) = Dec D5
type instance Succ (Dec D5) = Dec D6
type instance Succ (Dec D6) = Dec D7
type instance Succ (Dec D7) = Dec D8
type instance Succ (Dec D8) = Dec D9
type instance Succ (Dec D9) = Dec D1 :. D0
type instance Succ (n :. D0) = n :. D1
type instance Succ (n :. D1) = n :. D2
type instance Succ (n :. D2) = n :. D3
type instance Succ (n :. D3) = n :. D4
type instance Succ (n :. D4) = n :. D5
type instance Succ (n :. D5) = n :. D6
type instance Succ (n :. D6) = n :. D7
type instance Succ (n :. D7) = n :. D8
type instance Succ (n :. D8) = n :. D9
type instance Succ (n :. D9) = (Succ n) :. D0

infixr :+
-- | Type-level '+'
type family (:+) (m :: Nat) (n :: Nat) :: Nat
type instance (Dec D0) :+ n = n
type instance (Dec D1) :+ n = Succ n
type instance (Dec D2) :+ n = Succ (Succ n)
type instance (Dec D3) :+ n = Succ (Succ (Succ n))
type instance (Dec D4) :+ n = Succ (Succ (Succ (Succ n)))
type instance (Dec D5) :+ n = Succ (Succ (Succ (Succ (Succ n))))
type instance (Dec D6) :+ n = Succ (Succ (Succ (Succ (Succ (Succ n)))))
type instance (Dec D7) :+ n = Succ (Succ (Succ (Succ (Succ (Succ (Succ n))))))
type instance (Dec D8) :+ n = Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ n)))))))
type instance (Dec D9) :+ n = Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ n))))))))
type instance (m :. d) :+ n = (Dec d) :+ ((m :+ Div10 n) :. Mod10 n)

-- comparison
-- | Type-level 'compare'
type family Compare (m :: Nat) (n :: Nat) :: Ordering
-- D0
type instance Compare (Dec D0) (Dec D0) = EQ
type instance Compare (Dec D0) (Dec D1) = LT
type instance Compare (Dec D0) (Dec D2) = LT
type instance Compare (Dec D0) (Dec D3) = LT
type instance Compare (Dec D0) (Dec D4) = LT
type instance Compare (Dec D0) (Dec D5) = LT
type instance Compare (Dec D0) (Dec D6) = LT
type instance Compare (Dec D0) (Dec D7) = LT
type instance Compare (Dec D0) (Dec D8) = LT
type instance Compare (Dec D0) (Dec D9) = LT
type instance Compare (Dec D0) (yi :. yl) = LT
type instance Compare (yi :. yl) (Dec D0) = GT
-- D1
type instance Compare (Dec D1) (Dec D0) = GT
type instance Compare (Dec D1) (Dec D1) = EQ
type instance Compare (Dec D1) (Dec D2) = LT
type instance Compare (Dec D1) (Dec D3) = LT 
type instance Compare (Dec D1) (Dec D4) = LT
type instance Compare (Dec D1) (Dec D5) = LT 
type instance Compare (Dec D1) (Dec D6) = LT
type instance Compare (Dec D1) (Dec D7) = LT 
type instance Compare (Dec D1) (Dec D8) = LT
type instance Compare (Dec D1) (Dec D9) = LT
type instance Compare (Dec D1) (yi :. yl) = LT
type instance Compare (yi :. yl) (Dec D1) = GT
-- D2
type instance Compare (Dec D2) (Dec D0) = GT
type instance Compare (Dec D2) (Dec D1) = GT
type instance Compare (Dec D2) (Dec D2) = EQ
type instance Compare (Dec D2) (Dec D3) = LT
type instance Compare (Dec D2) (Dec D4) = LT
type instance Compare (Dec D2) (Dec D5) = LT
type instance Compare (Dec D2) (Dec D6) = LT
type instance Compare (Dec D2) (Dec D7) = LT
type instance Compare (Dec D2) (Dec D8) = LT
type instance Compare (Dec D2) (Dec D9) = LT
type instance Compare (Dec D2) (yi :. yl) = LT
type instance Compare (yi :. yl) (Dec D2) = GT
-- D3
type instance Compare (Dec D3) (Dec D0) = GT
type instance Compare (Dec D3) (Dec D1) = GT
type instance Compare (Dec D3) (Dec D2) = GT
type instance Compare (Dec D3) (Dec D3) = EQ
type instance Compare (Dec D3) (Dec D4) = LT
type instance Compare (Dec D3) (Dec D5) = LT
type instance Compare (Dec D3) (Dec D6) = LT
type instance Compare (Dec D3) (Dec D7) = LT
type instance Compare (Dec D3) (Dec D8) = LT
type instance Compare (Dec D3) (Dec D9) = LT
type instance Compare (Dec D3) (yi :. yl) = LT
type instance Compare (yi :. yl) (Dec D3) = GT
-- D4
type instance Compare (Dec D4) (Dec D0) = GT
type instance Compare (Dec D4) (Dec D1) = GT
type instance Compare (Dec D4) (Dec D2) = GT
type instance Compare (Dec D4) (Dec D3) = GT
type instance Compare (Dec D4) (Dec D4) = EQ
type instance Compare (Dec D4) (Dec D5) = LT
type instance Compare (Dec D4) (Dec D6) = LT
type instance Compare (Dec D4) (Dec D7) = LT
type instance Compare (Dec D4) (Dec D8) = LT
type instance Compare (Dec D4) (Dec D9) = LT
type instance Compare (Dec D4) (yi :. yl) = LT
type instance Compare (yi :. yl) (Dec D4) = GT
-- D5
type instance Compare (Dec D5) (Dec D0) = GT
type instance Compare (Dec D5) (Dec D1) = GT
type instance Compare (Dec D5) (Dec D2) = GT
type instance Compare (Dec D5) (Dec D3) = GT
type instance Compare (Dec D5) (Dec D4) = GT
type instance Compare (Dec D5) (Dec D5) = EQ
type instance Compare (Dec D5) (Dec D6) = LT
type instance Compare (Dec D5) (Dec D7) = LT
type instance Compare (Dec D5) (Dec D8) = LT
type instance Compare (Dec D5) (Dec D9) = LT
type instance Compare (Dec D5) (yi :. yl) = LT
type instance Compare (yi :. yl) (Dec D5) = GT
-- D6
type instance Compare (Dec D6) (Dec D0) = GT
type instance Compare (Dec D6) (Dec D1) = GT
type instance Compare (Dec D6) (Dec D2) = GT
type instance Compare (Dec D6) (Dec D3) = GT
type instance Compare (Dec D6) (Dec D4) = GT
type instance Compare (Dec D6) (Dec D5) = GT
type instance Compare (Dec D6) (Dec D6) = EQ
type instance Compare (Dec D6) (Dec D7) = LT
type instance Compare (Dec D6) (Dec D8) = LT
type instance Compare (Dec D6) (Dec D9) = LT
type instance Compare (Dec D6) (yi :. yl) = LT
type instance Compare (yi :. yl) (Dec D6) = GT
-- D7
type instance Compare (Dec D7) (Dec D0) = GT
type instance Compare (Dec D7) (Dec D1) = GT
type instance Compare (Dec D7) (Dec D2) = GT
type instance Compare (Dec D7) (Dec D3) = GT
type instance Compare (Dec D7) (Dec D4) = GT
type instance Compare (Dec D7) (Dec D5) = GT
type instance Compare (Dec D7) (Dec D6) = GT
type instance Compare (Dec D7) (Dec D7) = EQ
type instance Compare (Dec D7) (Dec D8) = LT
type instance Compare (Dec D7) (Dec D9) = LT
type instance Compare (Dec D7) (yi :. yl) = LT
type instance Compare (yi :. yl) (Dec D7) = GT
-- D8
type instance Compare (Dec D8) (Dec D0) = GT
type instance Compare (Dec D8) (Dec D1) = GT
type instance Compare (Dec D8) (Dec D2) = GT
type instance Compare (Dec D8) (Dec D3) = GT
type instance Compare (Dec D8) (Dec D4) = GT
type instance Compare (Dec D8) (Dec D5) = GT
type instance Compare (Dec D8) (Dec D6) = GT
type instance Compare (Dec D8) (Dec D7) = GT
type instance Compare (Dec D8) (Dec D8) = EQ
type instance Compare (Dec D8) (Dec D9) = LT
type instance Compare (Dec D8) (yi :. yl) = LT
type instance Compare (yi :. yl) (Dec D8) = GT
-- D9
type instance Compare (Dec D9) (Dec D0) = GT
type instance Compare (Dec D9) (Dec D1) = GT
type instance Compare (Dec D9) (Dec D2) = GT
type instance Compare (Dec D9) (Dec D3) = GT
type instance Compare (Dec D9) (Dec D4) = GT
type instance Compare (Dec D9) (Dec D5) = GT
type instance Compare (Dec D9) (Dec D6) = GT
type instance Compare (Dec D9) (Dec D7) = GT
type instance Compare (Dec D9) (Dec D8) = GT
type instance Compare (Dec D9) (Dec D9) = EQ
type instance Compare (Dec D9) (yi :. yl) = LT
type instance Compare (yi :. yl) (Dec D9) = GT
-- multidigit
type instance Compare (xn :. xd) (yn :. yd) = (Compare xn yn) `ThenCompareBy` (Compare (Dec xd) (Dec yd))

type a :< b = OrdEq (Compare a b) LT
type a :== b = OrdEq (Compare a b) EQ
type a :> b = OrdEq (Compare a b) GT
type a :>= b = Not (a :< b)
type a :<= b = Not (a :> b)

-- * Subtraction
-- | Precondition: @m ':>=' n@.
type family Pred (n :: Nat) :: Nat
type instance Pred (Dec D1) = (Dec D0)
type instance Pred (Dec D2) = (Dec D1)
type instance Pred (Dec D3) = (Dec D2)
type instance Pred (Dec D4) = (Dec D3)
type instance Pred (Dec D5) = (Dec D4)
type instance Pred (Dec D6) = (Dec D5)
type instance Pred (Dec D7) = (Dec D6)
type instance Pred (Dec D8) = (Dec D7)
type instance Pred (Dec D9) = (Dec D8)
type instance Pred (Dec D1 :. D0) = (Dec D9)
type instance Pred (Dec D2 :. D0) = (Dec D1 :. D9)
type instance Pred (Dec D3 :. D0) = (Dec D2 :. D9)
type instance Pred (Dec D4 :. D0) = (Dec D3 :. D9)
type instance Pred (Dec D5 :. D0) = (Dec D4 :. D9)
type instance Pred (Dec D6 :. D0) = (Dec D5 :. D9)
type instance Pred (Dec D7 :. D0) = (Dec D6 :. D9)
type instance Pred (Dec D8 :. D0) = (Dec D7 :. D9)
type instance Pred (Dec D9 :. D0) = (Dec D8 :. D9)
type instance Pred (xd :. xm :. D0) = Pred (xd :. xm) :. D9
type instance Pred (xd :. D1) = (xd :. D0)
type instance Pred (xd :. D2) = (xd :. D1)
type instance Pred (xd :. D3) = (xd :. D2)
type instance Pred (xd :. D4) = (xd :. D3)
type instance Pred (xd :. D5) = (xd :. D4)
type instance Pred (xd :. D6) = (xd :. D5)
type instance Pred (xd :. D7) = (xd :. D6)
type instance Pred (xd :. D8) = (xd :. D7)
type instance Pred (xd :. D9) = (xd :. D8)

-- | Type-level '-'
infixl :-
type family (:-) (m :: Nat) (n :: Nat) :: Nat
type instance x :- (Dec D0) = x
type instance x :- (Dec D1) = (Pred x) 
type instance x :- (Dec D2) = (Pred x) :- (Dec D1)
type instance x :- (Dec D3) = (Pred x) :- (Dec D2)
type instance x :- (Dec D4) = (Pred x) :- (Dec D3)
type instance x :- (Dec D5) = (Pred x) :- (Dec D4)
type instance x :- (Dec D6) = (Pred x) :- (Dec D5)
type instance x :- (Dec D7) = (Pred x) :- (Dec D6)
type instance x :- (Dec D8) = (Pred x) :- (Dec D7)
type instance x :- (Dec D9) = (Pred x) :- (Dec D8)
type instance (xn :. xd) :- (yn :. yd) = ((xn :- yn) :. xd) :- (Dec yd)
-- no instance (invalid)
-- type instance (Dec xd) :- (yn :. yd)

-- * Multiplication
infixr :*
-- | Type-level '*'
type family (:*) (m :: Nat) (n :: Nat) :: Nat
type instance x :* (Dec D0) = Dec D0
type instance x :* (Dec D1) = x :+ (x :* Dec D0)
type instance x :* (Dec D2) = x :+ (x :* Dec D1)
type instance x :* (Dec D3) = x :+ (x :* Dec D2)
type instance x :* (Dec D4) = x :+ (x :* Dec D3)
type instance x :* (Dec D5) = x :+ (x :* Dec D4)
type instance x :* (Dec D6) = x :+ (x :* Dec D5)
type instance x :* (Dec D7) = x :+ (x :* Dec D6)
type instance x :* (Dec D8) = x :+ (x :* Dec D7)
type instance x :* (Dec D9) = x :+ (x :* Dec D8)
type instance x :* (yn :. yd) = ((x :* yn) :. D0) :+ (x :* Dec yd)

