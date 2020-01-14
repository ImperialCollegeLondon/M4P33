/-
Copyright (c) 2020 Kevin Buzzard
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, and whoever else wants to join in.
-/

import affine_algebraic_set.basic

/-!
# The 𝕍 construction and the 𝕀 construction.

Let k be a commutative ring and let n be a natural number. 

This file defines the map 𝕍 from subsets of k[X₁,X₂,…,Xₙ]
to affine algebraic sets in kⁿ, and the map 𝕀 from affine algebraic
sets in kⁿ to ideals of k[X₁,X₂,…, Xₙ]. It proves basic properties
about them which can be shown without the Nullstellensatz.

To get 𝕍 in VS Code, type `\bbV`. To get `𝕀` type `\bbI`.

All the definitions work for k a commutative ring, but hardly any
of the the theorems do. But computer scientists
want us to think like them because it makes their lives easier.
So k starts off being a commutative ring, and only becomes a field
when it has to be, and only becomes an algebraically closed field
when it has to be.

Remark: `analysis/complex/polynomial.lean` contains the proof that ℂ is algebrically
closed.

Exercise: how do you think you type ℂ in VS Code?

## Important definitions

* `𝕍 : _ 
  sending a subset of k[X₁,X₂,…Xₙ] to an affine algebraic subset of kⁿ

* 𝕀 : _
  sending an affine algebraic subset of kⁿ to an ideal of k[X₁,X₂,…Xₙ]

## Notation

Any comments about canonical forms for `simp` need to go here

## 

## References

Martin Orr's lecture notes.

## Tags

algebraic geometry, algebraic variety, 𝕍, 𝕀
-/

-- start of file 

-- We're going to develop 𝕍 and 𝕀 in a theory called the theory of affine algebraic sets.
-- We imported the basic theory of affine algebraic sets above, so to get started we
-- just do this:

namespace affine_algebraic_set

-- let k be a commutative ring
variables {k : Type*} [comm_ring k]

-- and let n be a natural number
variable {n : ℕ}

-- In Lean 3, the multivariable polynomial ring k[X₁, X₂, ..., Xₙ] is
-- denoted `mv_polynomial (fin n) k`.
-- The set kⁿ is denoted `fin n → k` (which means maps from {0,1,2,...,(n-1)} to k).

/-- 𝕍 : the function sending a subset of k[X₁,X₂,…Xₙ] to an
  affine algebraic subset of kⁿ, define in Martin Orr's notes -/
def 𝕍 : set (mv_polynomial (fin n) k) → affine_algebraic_set k n :=
λ (S : set (mv_polynomial (fin n) k)),
{ carrier := _,
  is_algebraic := ⟨by assumption, rfl⟩
}

namespace 𝕍

-- facts about 𝕍
lemma mem_iff (S : set (mv_polynomial (fin n) k)) (x : fin n → k) :
  x ∈ ⇑(𝕍 S) ↔ ∀ s ∈ S, s.eval x = 0 := sorry

/-- If S ⊆ T then 𝕍(T) ⊆ 𝕍(S) -/
theorem sub_of_sub (S T : set (mv_polynomial (fin n) k)) :
  S ⊆ T → 𝕍 T ⊆ 𝕍 S :=
-- Say S ⊆ T and x ∈ 𝕍 T. 
begin
  intro hST,
  intros x hx,
  sorry
end

end 𝕍

/-- 𝕀 : the function sending an affine algebraic subset of kⁿ to
  an ideal of k[X₁,X₂,…Xₙ], defined in Martin Orr's notes. -/
def 𝕀 : affine_algebraic_set k n → ideal (mv_polynomial (fin n) k) := sorry

end affine_algebraic_set
