module MyNat

import Equality

public export
data Natural = Zero | Succesor Natural

public export
(+) : Natural -> Natural -> Natural
Zero + n = n 
(Succesor m) + n = Succesor (m + n)

-- Abelian group (ℕ, +, 0)
-- - Associativitvy:
--   ∀ a, b, c ∈ ℕ, (a + b) + c = a + (b + c)
-- - Neutral element:
--   ∃ 0 ∈ ℕ | ∀ a ∈ ℕ, 0 + a = a + 0 = a
-- - Inverse element:
--   ∀ a, ∈ ℕ ∃ a_inv ∈ ℕ | a + a_inv = a_inv + a = 0 where 0 is the neutral element
-- from: https://en.wikipedia.org/wiki/Abelian_group

-- wts zero is identity --
-- wts e+a = a
-- by definition is true
public export
zeroLeftNeutral : (m: Natural) -> Equality (Zero + m) m
zeroLeftNeutral m = Reflexive

-- wts a + e = a
-- proof by induction:
-- base case a+0 = a
public export
zeroRightNeutral : (m: Natural) -> Equal (m + Zero) m
zeroRightNeutral Zero = Reflexive
zeroRightNeutral m = Reflexive

