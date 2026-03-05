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
--   For all a, b, and c in ℕ, the equation (a + b) + c = a + (b + c) holds.
-- - Neutral element:
--   There exists an element e in ℕ, such that for all elements a in ℕ, the equation e+a = a+e = a holds.
-- - Inverse element:
--   For each a in ℕ there exists an element b in ℕ such that a + b = b + a = e , where e is the identity element.
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

