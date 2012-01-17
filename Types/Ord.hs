{-# LANGUAGE PolyKinds, TypeFamilies #-}
module Types.Ord where

import Types.Common

type family (p :: Ordering) `ThenCompareBy` (q :: Ordering) :: Ordering
type instance LT `ThenCompareBy` r = LT
type instance EQ `ThenCompareBy` r = r
type instance GT `ThenCompareBy` r = GT

type family OrdEq (p :: Ordering) (q :: Ordering) :: Bool
--
type instance OrdEq LT LT = True
type instance OrdEq LT EQ = False
type instance OrdEq LT GT = False
--
type instance OrdEq EQ LT = False
type instance OrdEq EQ EQ = True
type instance OrdEq EQ GT = False
--
type instance OrdEq GT LT = False
type instance OrdEq GT EQ = False
type instance OrdEq GT GT = True
