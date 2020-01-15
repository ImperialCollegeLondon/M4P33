/-
The lattice structure on affine algebraic subsets of kⁿ

Kevin Buzzard
-/

import affine_algebraic_set.basic -- the basic theory of affine algebraic sets.
import affine_algebraic_set.union

/-
# The lattice structure on `affine_algebraic_set k n`. 

Lean level: hard. 

Let k be a field and let n be a natural number. We put the
structure of a semilattice_sup on the type of affine algebraic subsets
of kⁿ.

## References

Martin Orr's lecture notes at https://homepages.warwick.ac.uk/staff/Martin.Orr/2017-8/alg-geom/

## Tags

algebraic geometry, algebraic variety
-/

-- end of docstring; code starts here. 

-- affine algebraic sets are a semilattice_sup

-- instance : semilattice_sup (affine_algebraic_set k n) := sorry