module MyNat

import Equality

-- (x, y ∈ a, f ∈ a → b) → (x ≡ y → f(x) ≡ f(y))
congruence : (f: a -> b) -> Equality x y -> Equality (f x) (f y)
congruence f Reflexive = Reflexive

public export
data Natural = Zero | Successor Natural

public export
(+) : Natural -> Natural -> Natural
Zero + n = n 
(Successor m) + n = Successor (m + n)

-- Monoid (ℕ, +, 0)
-- - Associativity:
--   ∀ a, b, c ∈ ℕ, (a + b) + c = a + (b + c)
-- - Neutral element:
--   ∃ 0 ∈ ℕ | ∀ m ∈ ℕ, 0 + m = m + 0 = m
-- from: https://en.wikipedia.org/wiki/Abelian_group

-- wts zero is identity --
-- wts 0 + m = m
-- by definition is true
public export
zeroLeftNeutral : (m: Natural) -> Equality (Zero + m) m
zeroLeftNeutral m = Reflexive

-- wts a + 0 = a
-- proof by induction:
-- base case a + 0 = a
public export
zeroRightNeutral : (m : Natural) -> Equality (m + Zero) m
zeroRightNeutral Zero = Reflexive
zeroRightNeutral (Successor m) = 
  let inductiveHypothesis = zeroRightNeutral m in
  congruence Successor inductiveHypothesis