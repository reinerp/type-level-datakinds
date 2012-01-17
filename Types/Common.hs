{-# LANGUAGE PolyKinds, ConstraintKinds #-}
module Types.Common where

newtype Tagged a b = Tagged { unTagged :: b }

type Sat pred t = pred t ~ True