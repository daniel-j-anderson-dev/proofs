module Addition

import Natural
import Equality


public export
(+) : Natural -> Natural -> Natural
Zero + n = n 
(Successor m) + n = Successor (m + n)

-- Monoid (ℕ, +, 0)
-- - Neutral element:
--   ∃ 0 ∈ ℕ | ∀ n ∈ ℕ, 0 + n = n + 0 = n
-- - Associativity:
--   ∀ a, b, c ∈ ℕ, (a + b) + c = a + (b + c)

public export
zeroLeftNeutral : (n: Natural) -> Equality (Zero + n) n
zeroLeftNeutral n = Reflexive

public export
zeroRightNeutral : (n: Natural) -> Equality (n + Zero) n
zeroRightNeutral Zero = Reflexive
zeroRightNeutral (Successor k) =
  let inductiveHypothesis = zeroRightNeutral k
  in Equality.map Successor inductiveHypothesis

public export
zeroNeutral : ((m: Natural) -> Equality (Zero + m) m, (n : Natural) -> Equality (n + Zero) n)
zeroNeutral = (zeroLeftNeutral, zeroRightNeutral)

-- ∀ a, b, c, if a, b, c ∈ ℕ then (a + b) + c = a + (b + c)
public export
associativity : (a: Natural) -> (b: Natural) -> (c: Natural) -> Equality ((a + b) + c) (a + (b + c))

-- base case a = 0
-- (0 + b) + c = 0 + (b + c)
-- because of zero is neutral simplifies to
-- b + c = b + c
-- true due to reflexive property of equality
associativity Zero b c = Reflexive

-- inductive case a = Successor(k)
-- Need to show: Successor((k + b) + c) = Successor(k + (b + c))
associativity (Successor k) b c = 
  let inductiveHypothesis = associativity k b c
  in Equality.map Successor inductiveHypothesis 

-- associativity =
--   Natural.induction
--     (\a => (b: Natural) -> (c: Natural) -> Equality ((a + b) + c) (a + (b + c)))
--     (\b, c => Reflexive)
--     (\k, inductiveHypothesis => \b, c => Equality.map Successor (inductiveHypothesis b c))
