module MyNat

import Equality

public export
data Natural = Zero | Succesor Natural

public export
(+) : Natural -> Natural -> Natural
Zero + n = n 
(Succesor m) + n = Succesor (m + n)
