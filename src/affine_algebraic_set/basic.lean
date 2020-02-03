/-
Copyright (c) 2020 Kevin Buzzard
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, and whoever else wants to join in.
-/

import data.mv_polynomial

-- We want to be able to talk about V ⊆ W if V and W are affine algebraic sets
-- We will need import order.lattice at some point I guess

import affine_algebraic_set.V_and_I

/-!
# Affine algebraic sets

This file defines affine algebraic subsets of affine n-space and proves basic properties
about them.

## Important definitions

* `affine_algebraic_set k n` -- the type of affine algebraic subsets of kⁿ.

## Notation

None as yet -- do we need 𝔸ⁿ for affine n-space?

## Implementation notes

None yet. 

## References

Martin Orr's lecture notes https://homepages.warwick.ac.uk/staff/Martin.Orr/2017-8/alg-geom/

## Tags

algebraic geometry, algebraic variety
-/

-- let k be a commutative ring
variables {k : Type*} [comm_ring k]

-- and let σ be any set -- but think of it as {1,2,3,...,n}. It's the set
-- which indexes the variables of the polynomial ring we're thinking about.
variable {σ : Type*}

-- In Lean, the multivariable polynomial ring k[X₁, X₂, ..., Xₙ] is
-- denoted `mv_polynomial σ k`. We could use better notation.
-- The set 𝔸ⁿ or kⁿ is denoted `σ → k` (which means maps from {1,2,...,n} to k).
-- We use local notation for this.

local notation `𝔸ⁿ` := σ → k

-- We now make some definitions which we'll need in the course.

namespace mv_polynomial -- means "multivariable polynomial"

/-- The set of zeros in kⁿ of a function f ∈ k[X₁, X₂, ..., Xₙ] -/
def zeros (f : mv_polynomial σ k) : set (σ → k) :=
{x | f.eval x = 0} -- I just want to write f(x) = 0 really

/-- x is in the zeros of f iff f(x) = 0 -/
@[simp] lemma mem_zeros (f : mv_polynomial σ k) (x : σ → k) :
  x ∈ f.zeros ↔ f.eval x = 0 := iff.rfl

-- note that the next result needs that k is a field. 

/-- The zeros of f * g are the union of the zeros of f and of g -/
lemma zeros_mul {k : Type*} [discrete_field k] (f g : mv_polynomial σ k) :
  zeros (f * g) = zeros f ∪ zeros g :=
begin
  -- two sets are equal if they have the same elements
  ext,
  -- and now it's not hard to prove using `mem_zeros` and other
  -- equalities known to Lean's simplifier.
  simp, -- TODO -- should I give the full proof here?
end

end mv_polynomial

open mv_polynomial

/-- An affine algebraic subset of kⁿ is the common zeros of a set of polynomials -/
structure affine_algebraic_set (k : Type*) [comm_semiring k] (σ : Type*) := 
-- imagine σ = {1,2,3,...,n}, the general case is no different.
-- Maps σ → k are another way of thinking about kⁿ.

-- To give an affine algebraic set is to give two things: the set itself
-- (called `carrier` in Lean) and the proof that it's in the image of 𝕍.

-- carrier ⊆ kⁿ
(carrier : set (σ → k))

-- proof that there's a set S of polynomials such that the carrier is equal to the 
-- intersection of the zeros of the polynomials in the set.
(is_algebraic' : ∃ S : set (mv_polynomial σ k), carrier = 𝕍 S)

namespace affine_algebraic_set

-- this is invisible notation so mathematicians don't need to understand the definition
/-- An affine algebraic set can be regarded as a subset of 𝔸ⁿ -/
instance : has_coe_to_fun (affine_algebraic_set k σ) :=
{ F := λ _, _,
  coe := carrier
}

-- use `is_algebraic'` not `is_alegbraic` because the notation's right -- no "carrier".
def is_algebraic (V : affine_algebraic_set k σ) :
  ∃ S : set (mv_polynomial σ k), (V : set _) = 𝕍 S :=
affine_algebraic_set.is_algebraic' V

-- Now some basic facts about affine algebraic subsets. 

/-- Two affine algebraic subsets with the same carrier are equal! -/
lemma ext {V W : affine_algebraic_set k σ} : (V : set _) = W → V = W :=
begin
  intro h,
  cases V,
  cases W,
  simpa, -- TODO -- why no debugging output?
end

-- Do I want this instance? Seems to be useful for regular functions
/-- We can talk about elements of affine algebraic subsets of kⁿ  -/
instance : has_mem 𝔸ⁿ (affine_algebraic_set k σ) :=
⟨λ x V, x ∈ V.carrier⟩

-- Computer scientists insist on using ≤ for any order relation such as ⊆ .
-- It is some sort of problem with notation I think. 
instance : has_le (affine_algebraic_set k σ) :=
⟨λ V W, (V : set 𝔸ⁿ) ⊆ W⟩

instance : partial_order (affine_algebraic_set k σ) :=
{ le := (≤),
  le_refl := λ _ _, id,
  le_trans := λ _ _ _, set.subset.trans,
  le_antisymm := λ U V hUV hVU, ext (set.subset.antisymm hUV hVU)
}

/-- Mathematicians want to talk about affine algebraic subsets of kⁿ
    being subsets of one another -/
instance : has_subset (affine_algebraic_set k σ) :=
⟨affine_algebraic_set.has_le.le⟩

end affine_algebraic_set
