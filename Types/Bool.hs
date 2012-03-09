{-# LANGUAGE ScopedTypeVariables, DataKinds, TypeFamilies, RankNTypes #-}
-- | Convenience type families on the 'Bool' datatype
module Types.Bool where

import Types.Common

-- | Class whose instances are type-level 'Bool's
class TypeBool (b :: Bool) where reflectBool :: Tagged b Bool
instance TypeBool True     where reflectBool = Tagged True
instance TypeBool False    where reflectBool = Tagged False

-- | Reification on 'Bool's
reifyBool :: forall r. Bool -> (forall b. TypeBool b => Tagged b r) -> r
reifyBool True k  = unTagged (k :: Tagged True r)
reifyBool False k = unTagged (k :: Tagged False r)

-- | Type-level '&&'
type family And (b1 :: Bool) (b2 :: Bool) :: Bool
type instance And True True = True
type instance And b False = False
type instance And False b = False

-- | Type-level '||'
type family Or (b1 :: Bool) (b2 :: Bool) :: Bool
type instance Or False False = False
type instance Or True b = True
type instance Or b True = True

-- | Type-level 'not'
type family Not (b :: Bool) :: Bool
type instance Not True = False
type instance Not False = True