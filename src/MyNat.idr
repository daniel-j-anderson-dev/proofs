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

-- wts a + 0 = a
-- proof by induction:
-- base case a + 0 = a
public export
zeroRightNeutral : (m: Natural) -> Equal (m + Zero) m
zeroRightNeutral Zero = Reflexive
zeroRightNeutral (Successor a) =
  let inductiveHypothesis = zeroRightNeutral a in


