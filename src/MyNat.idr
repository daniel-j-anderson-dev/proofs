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
-- base case
-- 0 + m = 0
-- by definition
public export
zeroLeftNeutral : (m: Natural) -> Equality (Zero + m) m
zeroLeftNeutral m = Reflexive

-- inductive step. Assume the inductive hypothesis for some m
-- inductive hypothesis is m + 0 = m
--                           want to show : Successor(m) + 0 = Successor(m)
-- substitute for the inductive hypothesis: Successor(m + 0) = Successor(m)
--                                    QED : Successor(m)     = Successor(m)
public export
zeroRightNeutral : (m : Natural) -> Equality (m + Zero) m
zeroRightNeutral Zero = Reflexive
zeroRightNeutral (Successor m) = 
  let inductiveHypothesis = zeroRightNeutral m in
  congruence Successor inductiveHypothesis

public export
zeroNeutral : ((m: Natural) -> Equality (Zero + m) m, (m : Natural) -> Equality (m + Zero) m)
zeroNeutral = (zeroLeftNeutral, zeroRightNeutral)
