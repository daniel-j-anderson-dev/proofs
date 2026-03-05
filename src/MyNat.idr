module MyNat

import Equality

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

-- wts m + 0 = m
-- proof by induction:
-- base case m + 0 = m
public export
zeroRightNeutral : (m : Natural) -> Equality (m + Zero) m
zeroRightNeutral Zero = Reflexive
zeroRightNeutral (Successor m) = 
  let inductiveHypothesis = zeroRightNeutral m in
  congruence Successor inductiveHypothesis

-- wts m + 0 = m AND 0 + m = m
-- m + 0 = m AND 0 + m = m
-- from `zeroLeftNeutral`: m + 0 = m is true
-- true AND 0 + m = m
-- from `zeroRNeutral`: 0 + m = m is true
-- true AND true
-- true
zeroNeutral : ((m: Natural) -> Equality (Zero + m) m, (m : Natural) -> Equality (m + Zero) m)
zeroNeutral = (zeroLeftNeutral, zeroRightNeutral)
