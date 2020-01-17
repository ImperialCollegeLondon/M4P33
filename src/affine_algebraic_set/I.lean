/-
Copyright (c) 2020 Kevin Buzzard and 
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, and whoever else wants to join in.
-/

-- imports the theory of multivariable polynomials over rings
import data.mv_polynomial
import for_mathlib.mv_polynomial

/-!
# The 𝕀 construction

Let k be a commutative ring and let n be a natural number.

This file defines the map 𝕍 from subsets of k[X₁,X₂,…,Xₙ]
to affine algebraic sets in kⁿ, and the map 𝕀 from affine algebraic
sets in kⁿ to ideals of k[X₁,X₂,…, Xₙ]. It proves basic properties
about them which can be shown without the Nullstellensatz.

To get 𝕍 in VS Code, type `\bbV`.

Note: we never assume that the number of variables is finite,
so actually instead of using a natural number n, we use an
arbitrary set N for our variables.

All the definitions work for k a commutative ring, but not all
of the the theorems do. But computer scientists want us to set
up the theory for commutative rings and mathematicians should
learn to think more like computer scientists. 
So k starts off being a commutative ring.

## Important definitions

* `𝕍 : set (mv_polynomial n k) → set (n → k)` 
  sending a subset S of k[X₁,X₂,…Xₙ] to the subset of kⁿ cut out by the zeros of all
  the elements of S.

## 

## References

Martin Orr's lecture notes at
https://homepages.warwick.ac.uk/staff/Martin.Orr/2017-8/alg-geom/

## Tags

algebraic geometry, algebraic variety, 𝕍
-/

-- start of file 
-- We're dealing with multivariable polynomials so let's open
-- the namespace to get easy access to all the functions
open mv_polynomial

-- let k be a commutative ring
variables {k : Type*} [comm_ring k]

-- and let n be any set, but pretend it's {1,2,...,n}.
-- We'll work with polynomials in variables X_i for i ∈ n.
variable {n : Type*}

/- Interlude: Lean 3 notation hell.

* the multivariable polynomial ring k[X₁, X₂, ..., Xₙ] is denoted
  `mv_polynomial n k`.

* The set kⁿ is denoted
  `n → k`
  (which means maps from n to k, and if you're thinking
   about n as {1,2,3,...,n} then you can see that this makes sense).

* subsets of a set X are denoted
  `set X`

* To evaluate a polynomial f on a vector x, we seem to have to write
  `eval x f`
  Note the order! "Maps on the right".

-/

namespace affine_algebraic_set

/-- 𝕀 : the function sending a subset of kⁿ to
  a subset of k[X₁,X₂,…Xₙ], defined in Martin Orr's notes. -/
def 𝕀 (X : set (n → k)) : set (mv_polynomial n k) :=
{f | ∀ x ∈ X, eval x f = 0 }

open set

/-- f ∈ 𝕀 X ↔ for all x ∈ X, f(x) = 0. This is true by definition. -/
lemma mem_𝕀_iff {X : set (n → k)} {f : mv_polynomial n k} :
  f ∈ 𝕀 X ↔ ∀ x ∈ X, eval x f = 0 := iff.rfl

-- proofs which a mathematician might get something from start here

/-- 𝕀 ∅ = all of k[X₁,X₂,…,Xₙ] -/
lemma empty : 𝕀 (∅ : set (n → k)) = univ :=
begin
  -- we have to prove that every f ∈ k[X₁,X₂,…,Xₙ] is in 𝕀 ∅ 
  rw eq_univ_iff_forall,
  -- so say f ∈ k[X₁,X₂,…,Xₙ] is arbitrary
  intro f,
  -- and we need to prove f ∈ 𝕀 ∅. 
  -- Equivalently, we need to prove that for all x ∈ ∅, f(x) = 0
  rw mem_𝕀_iff,
  -- so say x is in the empty set
  intros x hx,
  -- and now we have a contradiction, so we can prove anything
  cases hx
end

lemma univ {k : Type*} [integral_domain k] [infinite k] {n : Type*} :
  𝕀 (univ : set (n → k)) = {0} :=
begin
  -- we prove inclusions in both directions
  apply set.subset.antisymm,
  { -- this way is the slightly tricky way;
    -- we need to prove that 𝕀 (kⁿ) ⊆ 0
    -- so say f ∈ 𝕀 (kⁿ) is arbitrary
    intros f hf,
    -- and we need to prove it's zero
    rw mem_singleton_iff,
    -- -> only poly that's zero everywhere is zero poly
    rw mem_𝕀_iff at hf,
    rw ←mv_polynomial.eval_eq_zero,
    intro x, apply hf x, apply mem_univ,
  },
  { 
    -- unpack set
     rw singleton_subset_iff,
     -- apply definition of 𝕀 
     rw mem_𝕀_iff,
     simp,
  },
end

lemma 𝕀_antimono (V W : set (n → k)) :
  V ⊆ W → 𝕀 W ⊆ 𝕀 V :=
begin
  -- Assume V ⊆ W and f a polynomial
  intros H f,
  -- Apply Definition of 𝕀 twice
  rw [mem_𝕀_iff,mem_𝕀_iff],
  -- More Assumptions
  intro P,
  intros x HX,
  -- Use that f(x)=0 ∀ x∈W
  apply P,
  -- Use V ⊆ W
  from H HX,
end

-- The image of 𝕀 is an ideal

-- We do this by defining a function 𝕀' from subsets of kⁿ to ideals of R,
-- and showing that 𝕀' agrees with 𝕀 when you take the ideal and consider
-- it as a set 
noncomputable def 𝕀' (X : set (n → k)) : ideal (mv_polynomial n k) :=
{ carrier := 𝕀 X, -- underlying set is just 𝕀(X)
  zero := by simp [𝕀], -- zero is obviously in.
  add := begin
    -- Goal: if f and g are in 𝕀(X), then so is f + g.
    -- say f and g are elements of 𝕀(X).
    rintros f g hf hg,
    -- We know f(x) = 0 for all x ∈ X and g(x) = 0 for all x ∈ X
    change ∀ (x : n → k), x ∈ X → eval x f = 0 at hf,
    change ∀ (x : n → k), x ∈ X → eval x g = 0 at hg,
    -- so now say x ∈ X.
    intros x hx,
    -- We want to prove (f + g)(x)=0. But (f + g)(x)=f(x) + g(x)
    rw eval_add,
    -- so (f + g)(x) = 0 + 0
    rw [hf _ hx, hg _ hx],
    -- which is 0
    apply zero_add
  end,
  smul := begin
    -- goal: if f ∈ 𝕀(X) and c ∈ k[X₁,X₂,…,X_ₙ], then cf ∈ 𝕀(X).
    rintros c f hf,
    -- We know f(x) = 0 for all x ∈ X.
    change ∀ (x : n → k), x ∈ X → eval x f = 0 at hf,
    -- Let's choose x ∈ X
    intros x hx,
    -- We need to prove cf(x)=0. 
    -- But cf(x)=c(x)f(x)
    rw [smul_eq_mul, eval_mul],
    -- and f(x)=0
    rw hf _ hx,
    -- so we're done
    rw mul_zero
    -- refl omitted because Lean rw is clever
  end }

  lemma 𝕀_eq_𝕀' (X : set (n → k)) : (𝕀' X : set (mv_polynomial n k)) = 𝕀 X := rfl

end affine_algebraic_set