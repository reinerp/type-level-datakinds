{- |
Redefinitions of 'Tagged' and 'Proxy' with polymorphic kinds.
-}

{-# LANGUAGE DataKinds, PolyKinds, ConstraintKinds, EmptyDataDecls #-}
module Types.Common where

-- | Tagging values by type
newtype Tagged a b = Tagged { unTagged :: b }

-- | Change the tag
reTag :: Tagged a c -> Tagged b c
reTag = Tagged . unTagged

-- | We satisfy a predicate if and only if @pred t ~ True@
type Sat pred t = pred t ~ True

-- | Empty datatype
data Proxy a
