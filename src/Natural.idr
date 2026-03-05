module Natural


public export
data Natural = Zero | Successor Natural

-- visibility
public export
-- fn name
induction
-- params
  -- a proposition that depends on a natural number
   : (proposition: Natural -> Type) 
  -- proof that P(0)
  -> (baseCase: proposition Zero)
  -- proof that for all k if k is Natural then if P(k) then P(k + 1)
  -> (inductiveCase: (k: Natural) -> proposition k -> proposition (Successor k))
  -> (n: Natural)
-- return type
  -> proposition n

-- base case n = 0
induction _ baseCase _ Zero = baseCase

-- recursively loop from k all the way to zero checking the prop every step of the way
-- params: prop, b, inductiveCase all pass through to the next recursive layer without changing
induction proposition baseCase inductiveCase (Successor k) =
  inductiveCase k (induction proposition baseCase inductiveCase k)
