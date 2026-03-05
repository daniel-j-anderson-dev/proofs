module Equality

-- declare that equality exists
-- the main property of equality is that everything is equal to itself
public export
data Equality : a -> a -> Type where
  Reflexive : {0 x : a} -> Equality x x

-- proof `Equality` is congruent under function application
-- x ≡ y → f(x) ≡ f(y)
public export
congruence : (f: a -> b) -> Equality x y -> Equality (f x) (f y)
congruence f Reflexive = Reflexive
