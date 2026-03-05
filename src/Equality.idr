module Equality

public export
data Equality : a -> a -> Type where    -- declare that equality exists
  Reflexive : {0 x : a} -> Equality x x -- the main property of equality is that everything is equal to itself

-- if x ≡ y then f(x) ≡ f(y)
public export
congruence : (f: a -> b) -> Equality x y -> Equality (f x) (f y)
congruence f Reflexive = Reflexive


public export
map : (f: a -> b) -> (witness: Equality x y) -> Equality (f x) (f y)
map = congruence
