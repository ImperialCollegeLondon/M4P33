/-
Copyright (c) 2020 Kevin Buzzard
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, and whoever else wants to join in.
-/

-- imports the theory of multivariable polynomials over rings
import data.mv_polynomial

/-!
# The 𝕍 construction

Let k be a commutative ring and let n be a natural number.

This file defines the map 𝕍 from subsets of k[X₁,X₂,…,Xₙ]
to affine algebraic sets in kⁿ, and the map 𝕀 from affine algebraic
sets in kⁿ to ideals of k[X₁,X₂,…, Xₙ]. It proves basic properties
about them which can be shown without the Nullstellensatz.

To get 𝕍 in VS Code, type `\bbV`.

Note: we never assume that the number of variables is finite,
so actually instead of using a natural number n, we use an
arbitrary set N for our variables.

All the definitions work for k a commutative ring, but hardly any
of the the theorems do. But computer scientists want us to set
up the theory for commutative rings and mathematicians should
learn to think more like computer scientists. 
So k starts off being a commutative ring, and only becomes a field
when it has to be, and only becomes an algebraically closed field
when it has to be.

Remark: `analysis/complex/polynomial.lean` contains the proof that ℂ is algebrically
closed.

Exercise: how do you think you type ℂ in VS Code?

## Important definitions

* `𝕍 : set (mv_polynomial n k) → set (n → k)` 
  sending a subset S of k[X₁,X₂,…Xₙ] to the subset of kⁿ cut out by the zeros of all
  the elements of S.

## 

## References

Martin Orr's lecture notes at https://homepages.warwick.ac.uk/staff/Martin.Orr/2017-8/alg-geom/

## Tags

algebraic geometry, algebraic variety, 𝕍
-/

-- start of file 
-- We're dealing with multivariable polynomials so let's open the namespace to get
-- easy access to all the functions
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

/-- 𝕍 : the function sending a subset of k[X₁,X₂,…Xₙ] to an
  affine algebraic subset of kⁿ, define in Martin Orr's notes -/
def 𝕍 (S : set (mv_polynomial n k)) : set (n → k) :=
{x : n → k | ∀ f ∈ S, eval x f = 0}

-- Now let's prove a bunch of theorems about 𝕍, in a namespace

namespace affine_algebraic_set.𝕍

-- the theorems will be about sets, so let's open the set namespace
-- giving us easier access to theorems about sets 

open set

/-- x ∈ 𝕍 S ↔ for all f ∈ S, f(x) = 0. This is true by definition. -/
lemma mem_iff {S : set (mv_polynomial n k)} {x : n → k} :
  x ∈ 𝕍 S ↔ ∀ f ∈ S, eval x f = 0 := iff.rfl

/-- 𝕍(∅) = kⁿ -/
lemma empty : 𝕍 (∅ : set (mv_polynomial n k)) = univ :=
begin
  -- We need to show that for all x in kⁿ, x ∈ 𝕍 ∅
  rw eq_univ_iff_forall,
  -- so say x ∈ kⁿ,
  intro x,
  -- By definition of 𝕍, we need to check that f(x) = 0 for all f in ∅
  rw mem_iff,
  -- so say f is a polynomial
  intro f,
  -- and f is in the empty set
  intro hf,
  -- well, our assumptions give a contradiction, and we can deduce anything from a contradiction
  cases hf,
end

/-- Over a non-zero commutative ring, 𝕍 (k[X₁,X₂,…,Xₙ]) = ∅ -/
lemma univ {k : Type*} [nonzero_comm_ring k] {n : Type*} :
  𝕍 (univ : set (mv_polynomial n k)) = ∅ :=
begin
  -- It suffices to show that for all x ∈ kⁿ, x isn't in 𝕍 (all polynomials)
  rw eq_empty_iff_forall_not_mem,
  -- so say x ∈ kⁿ
  intro x,
  -- we need to check that it's not true that for every polynomial f, f(x) = 0
  rw mem_iff,
  -- so let's assume that f(x) = 0 for every polynomial f, and get a contradiction
  intro h,
  -- let's consider the constant polynomial 1
  replace h := h (C 1) (mem_univ _),
  -- evaluating 1 at x gives the value 1
  rw eval_C at h,
  -- so 1 = 0 in k, which contradicts k being non-zero
  exact zero_ne_one h.symm 
end

/-- If S ⊆ T then 𝕍(T) ⊆ 𝕍(S) -/
theorem antimono (S T : set (mv_polynomial n k)) :
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

theorem union (S T : set (mv_polynomial n k)) :
𝕍 (S ∪ T) = 𝕍 S ∩ 𝕍 T :=
begin
  -- let's prove this by proving ⊆ and ⊇
  apply set.subset.antisymm,
  { -- goal : 𝕍 (S ∪ T) ⊆ 𝕍 S ∩ 𝕍 T
    -- so let x be an element of the LHS
    intros x hx,
    -- then x ∈ 𝕍 (S ∪ T) so ∀ f ∈ S ∪ T, f(x) = 0. Call this hypothesis `hx`.
    rw mem_iff at hx,
    -- To prove x ∈ 𝕍 S ∩ 𝕍 T, it suffices to prove x ∈ 𝕍 S and x ∈ 𝕍 T
    split,
    { -- To prove x ∈ 𝕍 S, we need to show that for all f ∈ S, f(x) = 0
      rw mem_iff,
      -- so say f ∈ S
      intros f hf,
      -- By hypothesis `hx`, it suffices to prove that f ∈ S ∪ T
      apply hx,
      -- but this is obvious
      left, assumption
    },
    { -- To prove x ∈ 𝕍 T, the argument is the same,
      -- so we write it the way a computer scientist would.
      -- (they prefer one line to four)
      exact mem_iff.2 (λ f hf, hx _ (set.subset_union_right _ _ hf)),
    },
  },
  { -- ⊢ 𝕍 S ∩ 𝕍 T ⊆ 𝕍 (S ∪ T) (NB `⊢` means "the goal is")
    -- say x is in 𝕍 S and 𝕍 T
    rintro x ⟨hxS, hxT⟩,
    -- We need to show that for all f ∈ S ∪ T, f(x) = 0
    rw mem_iff,
    -- so choose f in S ∪ T
    intros f hf,
    -- Well, f is either in S or in T, so there are two cases.
    cases hf,
    { -- Say f ∈ S
      -- Recall that x ∈ 𝕍 S, so ∀ f ∈ S, f(x) = 0
      rw mem_iff at hxS,
      -- so we're done.
      exact hxS f hf
    },
    { -- Say f ∈ T
      -- The argument is the same so we do it in one step
      exact hxT f hf,
    }
  }
end

-- Infinite (or rather, arbitrary) unions work just the same
-- We consider a collection Sᵢ of subsets indexed by i ∈ I.
theorem Union {I : Type*} (S : I → set (mv_polynomial n k)) :
𝕍 (⋃ i, S i) = ⋂ i, 𝕍 (S i) :=
begin
  -- To prove equality of two subsets of kⁿ it suffices to prove ⊆ and ⊇.
  apply set.subset.antisymm,
  { -- Goal: 𝕍 (⋃ i, S i) ⊆ ⋂ i, 𝕍 (S i)
    -- Let x be in the left hand side
    intros x hx,
    -- it suffices to prove that for all i, x ∈ 𝕍 (S i) 
    rw set.mem_Inter,
    -- so choose j
    intro j,
    -- and say f ∈ S j
    intros f hf,
    -- We now want to prove f(x) = 0.
    -- Now we know x ∈ 𝕍 (⋃ i, S i), so g(x) = 0 for all g in ⋃ i, S i
    -- Hence it suffices to prove that f ∈ ⋃ i, S i
    apply hx,
    -- By definition of the infinite union, it suffices to find i such that f ∈ S i
    rw set.mem_Union,
    -- and we can use j for this i
    use j,
    -- and what we need to show is true now by assumption, because f ∈ S j
    assumption
  },
  { -- Now the other way.
    -- ⊢ (⋂ (i : I), 𝕍 (S i)) ⊆ 𝕍 (⋃ (i : I), S i)
    -- Say x is in the left hand side
    intros x hx,
    -- It suffices to show that for all f ∈ ⋃ i, S i, f(x) = 0
    rw mem_iff,
    -- so say f is a polynomial in this union
    intros f hf,
    -- If f is in the union, then it's in one of the S i, so say f ∈ S j
    rw set.mem_Union at hf,
    cases hf with j hj,
    -- Now we know x is in the intersection of the 𝕍 (S i) for all i,
    -- so x ∈ 𝕍 (S j)
    rw set.mem_Inter at hx,
    have hxj := hx j,
    -- and because f(x) = 0 for every element of S j, and f ∈ S j, we know f(x) = 0
    exact hxj _ hj
  }
end

-- temp end because I need to fix proof below
end affine_algebraic_set.𝕍 #exit

instance : has_mul (set (mv_polynomial n k)) := ⟨λ S T, {u | ∃ (s ∈ S) (t ∈ T), u = s * t}⟩

theorem mul (S T : set (mv_polynomial n k)) :
𝕍 (S * T) = 𝕍 S ∪ 𝕍 T :=
begin
  -- to prove that the two sets are equal we will prove ⊆ and ⊇ 
  apply set.subset.antisymm,
  { -- This is the "harder" of the two inclusions;
    -- we need to check that if x vanishes on every element of S*T, 
    -- then x ∈ 𝕍 S or x ∈ 𝕍 T. So let x be in 𝕍 (S * T)
    intros x hx,
    -- We then know that for every f ∈ S * T, f(x) = 0
    rw mem_iff at hx,
    classical, -- We now proudly assume the law of the excluded middle.
    -- If x ∈ 𝕍 S then the result is easy...
    by_cases hx2 : x ∈ 𝕍 S,
      -- because 𝕍 S ⊆ 𝕍 S ∪ 𝕍 T
      exact subset_union_left _ _ hx2,
    -- ...so we can assume assume x ∉ 𝕍 S,
    -- and hence that there's s ∈ S such that s(x) ≠ 0
    rw [hS, set.mem_Inter, not_forall] at hx2,
    cases hx2 with s hs,
    have hs2 : s ∈ S ∧ ¬eval x s = 0,
      simpa using hs,
    cases hs2 with hsS hns,
    -- we now show x ∈ W
    right,
    rw set.mem_Inter,
    -- Say t ∈ T
    intro t,
    -- We want to prove that t(x) = 0.
    suffices : t ∈ T → eval x t = 0,
      simpa,
    intro ht,
    -- Now by assumption, x vanishes on s * t. 
    replace hx' := hx' (s * t) s hsS t ht rfl,
    -- so s(x) * t(x) = 0
    rw eval_mul at hx',
    -- so either s(x) or t(x) = 0, but we chose s such that s(x) ≠ 0.
    cases mul_eq_zero.1 hx' with hxs hxt,
      -- So the case s(x) = 0 is a contradiction
      contradiction,
    -- and t(x) = 0 is what we wanted to prove
    assumption
  },
  { -- Here's the easier of the two inclusions.
    -- say x ∈ V ∪ W,
    intros x hx,
    -- it's either in V or W.
    cases hx with hxV hxW,
    { -- Say x ∈ V
      -- We know that x vanishes at every element of S.
      rw set.mem_Inter at hxV,
      -- We want to prove x vanishes at every polynomial of the form s * t
      -- with s ∈ S and t ∈ T.
      rw set.mem_Inter,
      -- so let's take an element u of the form s * t
      rintro u,
      -- Let's now notice that the goal has got completely out of hand, and
      -- simplify it back to ∀ s ∈ S and ∀ t ∈ T, (s * t)(x) = 0.
      suffices : ∀ s ∈ S, ∀ t ∈ T, u = s * t → u.eval x = 0,
      {rw [set.mem_Inter], rintros ⟨s, hsS, t, htT, rfl⟩, exact this s hsS t htT rfl},
      rintro s hs t ht rfl,
      -- we need to show st(x)=0.
      -- Because x ∈ V, we have s(x)=0. 
      have hx := set.mem_Inter.1 (hxV s) hs,
      change s.eval x = 0 at hx,
      -- It suffices to show s(x)*t(x)=0
      rw eval_mul,
      -- but s(x) = 0,
      rw hx,
      -- and now it's obvious
      apply zero_mul,
    },
    { -- This is the case x ∈ W and it's essentially completely the same as the x ∈ V argument so I won't
      -- comment it. Some sort of argument with the `wlog` tactic might be able to do this.
      rw set.mem_Inter at hxW ⊢,
      rintro u,
        suffices : ∀ s ∈ S, ∀ t ∈ T, u = s * t → u.eval x = 0,
        {rw [set.mem_Inter], rintros ⟨s, hsS, t, htT, rfl⟩, exact this s hsS t htT rfl},
      rintro s hs t ht rfl,
      have hx := hxW t,
      rw set.mem_Inter at hx,
      replace hx : eval x t = 0 := hx ht,
      rw eval_mul,
      rw hx, simp,
    }
  }
end

end affine_algebraic_set.𝕍
