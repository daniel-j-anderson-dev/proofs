module Equality

public export
data Equality : a -> a -> Type where
  Reflexive : {0 x : a} -> Equality x x
  