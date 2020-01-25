/-
The intersection of algebraic sets is an algebraic set.

Kevin Buzzard
-/

import affine_algebraic_set.basic -- the basic theory of affine algebraic sets.

/-
# The intersection of (any number of) affine algebraic sets is affine.

Let k be a field and let n be a natural number. We prove the following
theorem in this file:

Theorem. If I is an index set, and for each i ∈ I we have an
affine algebraic subset Vᵢ of kⁿ, then the intersection ⋂_{i ∈ I} Vᵢ
is also an affine algebraic subset of kⁿ.

Lean version: 

** TODO

Maths proof: if Vᵢ is cut out by the set Sᵢ ⊆ k[X_1,X_2,…,X_n]
and we consider the set S = ⋃_{i ∈ I} Sᵢ then it is straightforward
to check that this works.

## References

Martin Orr's lecture notes at
https://homepages.warwick.ac.uk/staff/Martin.Orr/2017-8/alg-geom/

## Tags

algebraic geometry, algebraic variety
-/

-- end of docstring; code starts here. 

-- We're proving theorems about affine algebraic sets so the names of the theorems
-- should start with "affine_algebraic_set".
namespace affine_algebraic_set

-- let k be a field
variables {k : Type*} [discrete_field k]

-- and let σ be a set of indexes for our polynomial variables e.g. σ = {1,2,...,n}
variable {σ : Type*}

-- We're working with multivariable polynomials, so let's get access to their notation
open mv_polynomial

-- this should be proved by general nonsense really. 

/-- An arbitrary intersection of affine algebraic subsets of kⁿ
  is an affine algebraic subset of kⁿ -/
def Inter (I : Type*) (V : I → affine_algebraic_set k σ) :
  affine_algebraic_set k σ :=
{ carrier := ⋂ (i : I), (V i : set (σ → k)), -- the underlying set is the union of the two sets defining V and W
  is_algebraic' :=
  -- We now need to prove that the union is cut out by some set of polynomials.
  begin
    use ⋃ (i : I), (classical.some (V i).is_algebraic),
    ext x,
    rw 𝕍_Union,
    congr',
    funext i,
    exact classical.some_spec (V i).is_algebraic,
  end
}

end affine_algebraic_set