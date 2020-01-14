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

open mv_polynomial

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
  is_algebraic' := ⟨by assumption, rfl⟩
}

namespace 𝕍

-- this is infrastructure -- ignore the proof.
lemma carrier_def (S : set (mv_polynomial (fin n) k)) : (𝕍 S : set _) = {x | ∀ s ∈ S, eval x s = 0} :=
begin
  show (⋂ (f ∈ S), zeros f) = _,
  ext x,
  -- TODO(kmb): how come simp doesn't finish the job now even though set.mem_Inter is a simp lemma?
  rw set.mem_Inter,
  simp,
end

-- This is infrastructure -- ignore the proof.
lemma mem_iff (S : set (mv_polynomial (fin n) k)) (x : fin n → k) :
  x ∈ ⇑(𝕍 S) ↔ ∀ s ∈ S, eval x s = 0 :=
begin
  rw carrier_def,
  exact iff.rfl,
end

/-- If S ⊆ T then 𝕍(T) ⊆ 𝕍(S) -/
theorem antimono (S T : set (mv_polynomial (fin n) k)) :
  S ⊆ T → 𝕍 T ⊆ 𝕍 S :=
begin
-- Say S ⊆ T and x ∈ 𝕍 T. 
  intro hST,
  intros x hx,
  -- We want to prove x ∈ 𝕍 S.
  -- We know that ∀ t ∈ T, t(x) = 0, and we want to prove that ∀ s ∈ S, s(x) = 0. 
  rw mem_iff at hx ⊢,
  -- So say s ∈ S.
  intros s hs,
  -- then s ∈ T so we're done
  exact hx _ (hST hs),
end

end 𝕍

/-- 𝕀 : the function sending a subset of kⁿ to
  an ideal of k[X₁,X₂,…Xₙ], defined in Martin Orr's notes. -/
noncomputable def 𝕀 : set (fin n → k) → ideal (mv_polynomial (fin n) k) :=
λ X, 
{ carrier := {f | ∀ x ∈ X, eval x f = 0 },
  -- Now need to prove that it's an ideal.
  zero := by simp, -- zero is obviously in.
  add := begin
    -- Goal: if f and g are in 𝕀(X), then so is f + g.
    -- say f and g are elements of 𝕀(X).
    rintros f g hf hg,
    -- We know f(x) = 0 for all x ∈ X and g(x) = 0 for all x ∈ X
    change ∀ (x : fin n → k), x ∈ X → eval x f = 0 at hf,
    change ∀ (x : fin n → k), x ∈ X → eval x g = 0 at hg,
    -- so now say x ∈ X.
    intros x hx,
    -- We want to prove (f + g)(x)=0. But (f + g)(x)=f(x) + g(x)
    rw eval_add,
    -- so (f + g)(x) = 0 + 0
    rw [hf _ hx, hg _ hx],
    -- which is 0
    rw zero_add
    -- refl omitted because Lean rw is clever
  end,
  smul := begin
    -- goal: if f ∈ 𝕀(X) and c ∈ k[X₁,X₂,…,X_ₙ], then cf ∈ 𝕀(X).
    rintros c f hf,
    -- We know f(x) = 0 for all x ∈ X.
    change ∀ (x : fin n → k), x ∈ X → eval x f = 0 at hf,
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

end affine_algebraic_set
