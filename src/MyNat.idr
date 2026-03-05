module MyNat

import Equality

public export
data Natural = Zero | Succesor Natural

public export
(+) : Natural -> Natural -> Natural
Zero + n = n 
(Succesor m) + n = Succesor (m + n)

-- Abelian group (ℝ, +, 0)
-- - Associativitvy:
--   For all a, b, and c in A, the equation (a · b) · c = a · (b · c) holds.
-- - Neutral element:
--   There exists an element e in A, such that for all elements a in A, the equation e·a = a·e = a holds.
-- - Inverse element:
--   For each a in A there exists an element b in A such that a · b = b · a = e , where e is the identity element.
-- from: https://en.wikipedia.org/wiki/Abelian_group

-- Inverse element
public export
zeroLeftNeutral : (m: Natural) -> Equality (Zero + m) m
zeroLeftNeutral m = Reflexive
