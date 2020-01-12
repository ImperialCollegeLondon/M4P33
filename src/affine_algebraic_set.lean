/-
Copyright (c) 2020 Kevin Buzzard
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, and whoever else wants to join in.
-/

import for_mathlib.algebraically_closed
import data.mv_polynomial
/-!
# Affine algebraic sets

This file defines affine algebraic subsets of affine n-space and proves basic properties
about them.

## Important definitions

* `affine_algebraic_set k` -- the type of affine algebraic sets over the field `k`.

## Notation

None as yet -- do we need 𝔸ⁿ for affine n-space?

## Implementation notes

Much, but not all, of this file assumes that `k` is algebraically closed.
Remark: analysis/complex/polynomial.lean contains proof that ℂ is alg closed.

## References

Martin Orr's lecture notes!

## Tags

algebraic geometry, algebraic variety
-/

-- let k be a field
variables {k : Type*} [discrete_field k]

-- and let n be a natural number
variable {n : ℕ}

-- In Lean, the multivariable polynomial ring k[X₁, X₂, ..., Xₙ] is
-- denoted `mv_polynomial (fin n) k`. We could use better notation.
-- The set kⁿ is denoted `fin n → k` (which means maps from {0,1,2,...,(n-1)} to k).

-- We now make some definitions which we'll need in the course.

namespace mv_polynomial -- means "multivariable polynomial"

/-- The set of zeros in kⁿ of a function f ∈ k[X₁, X₂, ..., Xₙ] -/
def zeros (f : mv_polynomial (fin n) k) : set (fin n → k) :=
{x | f.eval x = 0}

/-- x is in the zeros of f iff f(x) = 0 -/
@[simp] lemma mem_zeros (f : mv_polynomial (fin n) k) (x : fin n → k) :
  x ∈ f.zeros ↔ f.eval x = 0 := iff.rfl

/-- The zeros of f * g are the union of the zeros of f and of g -/
lemma zeros_mul (f g : mv_polynomial (fin n) k) :
  zeros (f * g) = zeros f ∪ zeros g :=
begin
  -- two sets are equal if they have the same elements
  ext,
  -- and now it's not hard to prove using `mem_zeros` and other
  -- equalities known to Lean's simplifier.
  simp,
end

open mv_polynomial

/-- An affine algebraic subset of kⁿ is the common zeros of a set of polynomials -/
structure affine_algebraic_set (k : Type*) [discrete_field k] (n : ℕ) := 
-- a subset of the set of maps {0,1,2,...,n-1} → k (called "carrier")
(carrier : set (fin n → k)) 
-- ...such that there's a set of polynomials such that the carrier is equal to the 
-- intersection of the zeros of the polynomials in the set.
(is_algebraic : ∃ S : set (mv_polynomial (fin n) k), carrier = ⋂ f ∈ S, zeros f) -- ...such that

namespace affine_algebraic_set

-- Now some basic facts about affine algebrai subsets. 


set_option trace.simplify.rewrite false
set_option trace.simplify.rewrite true

/-- Two affine algebraic subsets with the same carrier are equal! -/
lemma ext (V W : affine_algebraic_set k n) : V.carrier = W.carrier → V = W :=
begin
  intro h,
  cases V,
  cases W,
  simpa,
end

/-- We can talk about elements of affine algebraic subsets of kⁿ  -/
instance : has_mem (fin n → k) (affine_algebraic_set k n) :=
⟨λ x V, x ∈ V.carrier⟩

/-- The union of two algebraic subsets of kⁿ is an algebraic subset-/
def union (V W : affine_algebraic_set k n) : affine_algebraic_set k n :=
{ carrier := V.carrier ∪ W.carrier,
  is_algebraic :=
  begin
    -- say S is the set that defines V
    cases V.is_algebraic with S hS,
    -- and T is the set that defines W
    cases W.is_algebraic with T hT,
    use {u | ∃ (s ∈ S) (t ∈ T), u = s * t},
    -- To prove that V ∪ W is defined by this set, we prove both inclusions
    apply set.subset.antisymm,
    { -- say x ∈ V ∪ W,
      intros x hx,
      -- it's either in V or W.
      cases hx with hxV hxW,
      { -- Say it's in V
        rw set.mem_Inter,
        -- we have to show it's a zero of all the s * t
        intro u,
        suffices : ∀ s ∈ S, ∀ t ∈ T, u = s * t → x ∈ zeros u,
          simpa using this,
        rintro s hs t ht rfl,
        sorry,
      },
      {
        sorry
      }
    },
    {
      sorry
    }
  end
}
end affine_algebraic_set