/-
Algebraic geometry M4P33, Jan-Mar 2020, formalised in Lean.

Copyright (c) 2020 Kevin Buzzard
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, and whoever else in the class wants to join in.

Note: if you are viewing this file in a browser via the following
link: 

https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FImperialCollegeLondon%2FM4P33%2Fmaster%2Fsrc%2Faffine_algebraic_set%2FV.lean

then you can click around on the code and see the state of Lean's "brain"
at any point within any begin/end proof block.
-/

-- imports the theory of multivariable polynomials over rings
import data.mv_polynomial

/-!
# Lecture 2 : The 𝕍 construction

Let k be a commutative ring and let n be a natural number.

This file defines the map 𝕍 from subsets of k[X₁,X₂,…,Xₙ]
to subsets of kⁿ, and proves basic properties about this map.

To get 𝕍 in VS Code, type `\bbV`.

Note: we never assume that the number of variables is finite,
so actually instead of using a natural number n, we use an
arbitrary set n for our variables.

All the definitions work for k a commutative ring, but not all
of the the theorems do. However, computer scientists want us to set
up the theory in as much generality as possible, and I believe that
mathematicians should learn to think more like computer scientists. 
So k starts off being a commutative ring, and occasionally changes later.

## Lean 3 notation: important comments.

Because we're not using Lean 4, we will have to deal with some
awkward notational issues.

* the multivariable polynomial ring k[X₁,X₂,…,Xₙ] is denoted
  `mv_polynomial n k`.

* The set kⁿ is denoted
  `n → k`.

  (note: this means maps from n to k, and if you're thinking
   about n as {1,2,3,...,n} then you can see that this makes sense).

* subsets of a set X are denoted
  `set X`

* The subset of X which is all of X is not called X :-) It's called
  `univ`

* To evaluate a polynomial f on a vector x, we write
  `eval x f`

  Note the order! "Maps on the right".

## Important definitions

* `𝕍 : set (mv_polynomial n k) → set (n → k)` 
  sending a subset S of k[X₁,X₂,…Xₙ] to the subset of kⁿ cut out
  by the zeros of all the elements of S.

## References

Martin Orr's lecture notes at
  https://homepages.warwick.ac.uk/staff/Martin.Orr/2017-8/alg-geom/

## Tags

algebraic geometry, algebraic variety, 𝕍
-/

-- code starts here

-- We're dealing with multivariable polynomials so let's open the
-- namespace to get easy access to all the functions
open mv_polynomial

-- let k be a commutative ring
variables {k : Type*} [comm_ring k]

-- and let n be any set, but pretend it's {1,2,...,n} with n a natural number.
-- We'll work with polynomials in variables X_i for i ∈ n.
variable {n : Type*}

/- recall:

     Maths                 Lean 3
     ---------------------------------------
     k[X₁, X₂, ..., Xₙ]    mv_polynomial n k
     kⁿ                    n → k
     subsets of X          set X
     the subset X of X     univ
     f(x)                  eval x f
-/

/-- 𝕍 : the function sending a subset S of k[X₁,X₂,…Xₙ] to
  the subset of kⁿ defined as the intersection of the zeros of all
  the elements of S. For more details, see Martin Orr's notes -/
def 𝕍 (S : set (mv_polynomial n k)) : set (n → k) :=
{x : n → k | ∀ f ∈ S, eval x f = 0}

-- Now let's prove a bunch of theorems about 𝕍, in a namespace

namespace affine_algebraic_set

-- the theorems will be about sets, so let's open the set namespace
-- giving us easier access to theorems about sets 

open set

-- The following lemma has a trivial proof so don't worry about it.
/-- x ∈ 𝕍 S ↔ for all f ∈ S, f(x) = 0. This is true by definition. -/
lemma mem_𝕍_iff {S : set (mv_polynomial n k)} {x : n → k} :
  x ∈ 𝕍 S ↔ ∀ f ∈ S, eval x f = 0 := iff.rfl

-- The rest of the proofs in this file are supposed to be comprehensible
-- to mathematicians 

/-- 𝕍(∅) = kⁿ -/
lemma 𝕍_empty : 𝕍 (∅ : set (mv_polynomial n k)) = univ :=
begin
  -- We need to show that for all x in kⁿ, x ∈ 𝕍 ∅
  rw eq_univ_iff_forall,
  -- so say x ∈ kⁿ.
  intro x,
  -- By definition of 𝕍, we need to check that f(x) = 0 for all f in ∅
  rw mem_𝕍_iff,
  -- so say f is a polynomial
  intro f,
  -- and f is in the empty set
  intro hf,
  -- well, our assumptions give a contradiction,
  -- and we can deduce anything from a contradiction
  cases hf,
end

/-- Over a non-zero commutative ring, 𝕍 (k[X₁,X₂,…,Xₙ]) = ∅ -/
lemma 𝕍_univ {k : Type*} [nonzero_comm_ring k] {n : Type*} :
  𝕍 (univ : set (mv_polynomial n k)) = ∅ :=
begin
  -- It suffices to show that for all x ∈ kⁿ, x isn't in 𝕍 (all polynomials)
  rw eq_empty_iff_forall_not_mem,
  -- so say x ∈ kⁿ
  intro x,
  -- we need to check that it's not true that for every polynomial f, f(x) = 0
  rw mem_𝕍_iff,
  -- so let's assume that f(x) = 0 for every polynomial f,
  intro h,
  -- and get a contradiction (note that the goal is now `false`).
  -- Let's consider the constant polynomial 1; we deduce 1(x) = 0.
  replace h := h (C 1) (mem_univ _),
  -- evaluating 1 at x gives the value 1
  rw eval_C at h,
  -- so 1 = 0 in k, which contradicts k being non-zero
  exact zero_ne_one h.symm 
end

/-- 𝕍({0}) = kⁿ -/
lemma 𝕍_zero : 𝕍 ({0} : set (mv_polynomial n k)) = univ :=
begin
  -- It suffices to prove every element of kⁿ is in 𝕍(0)
  rw eq_univ_iff_forall,
  -- so say x ∈ kⁿ
  intro x,
  -- To prove it's in V(0), we need to show f(x)=0 for all f in {0} 
  rw mem_𝕍_iff,
  -- so take f in {0}
  intros f hf,
  -- Then it's zero!
  rw mem_singleton_iff at hf, 
  -- so we have to prove 0(x) = 0
  rw hf,
  -- which is obvious
  refl,
end

/-- If k ≠ 0 then 𝕍({1}) = ∅ -/
lemma 𝕍_one {k : Type*} [nonzero_comm_ring k] {n : Type*} :
  𝕍 ({1} : set (mv_polynomial n k)) = ∅ :=
begin
  -- this is basically the same proof as 𝕍_univ
  -- It suffices to show that for all x ∈ kⁿ, x isn't in 𝕍 ({1})
  rw eq_empty_iff_forall_not_mem,
  -- so say x ∈ kⁿ
  intro x,
  -- we need to check that it's not true that for all f ∈ {1}, f(x) = 0
  rw mem_𝕍_iff,
  -- so let's assume that f(x) = 0 for every polynomial f in {1},
  intro h,
  -- and get a contradiction (note that the goal is now `false`).
  -- Setting f = 1, we deduce 1(x) = 0.
  replace h := h (C 1) (mem_singleton _),
  -- evaluating the polynomial 1 at x gives the value 1
  rw eval_C at h,
  -- so 1 = 0 in k, which contradicts k being non-zero
  exact zero_ne_one h.symm 
end

/-- If S ⊆ T then 𝕍(T) ⊆ 𝕍(S) -/
theorem 𝕍_antimono (S T : set (mv_polynomial n k)) :
  S ⊆ T → 𝕍 T ⊆ 𝕍 S :=
begin
  -- We are assuming S ⊆ T
  intro hST,
  -- Let x ∈ 𝕍 T be arbitrary 
  intros x hx,
  -- We want to prove x ∈ 𝕍 S.
  -- We know that ∀ t ∈ T, t(x) = 0, and we want to
  -- prove that ∀ s ∈ S, s(x) = 0. 
  rw mem_𝕍_iff at hx ⊢,
  -- So say s ∈ S.
  intros s hs,
  -- we want to prove s(x) = 0.
  -- But t(x) = 0 for all t in T, so it suffices to prove s ∈ T
  apply hx,
  -- and this is clear because S ⊆ T
  exact hST hs
end

theorem 𝕍_union (S T : set (mv_polynomial n k)) :
𝕍 (S ∪ T) = 𝕍 S ∩ 𝕍 T :=
begin
  -- let's prove this equality of sets by proving ⊆ and ⊇
  apply set.subset.antisymm,
  { -- Step 1: we prove the inclusion 𝕍 (S ∪ T) ⊆ 𝕍 S ∩ 𝕍 T.
    -- So let x be an element of the LHS
    intros x hx,
    -- then x ∈ 𝕍 (S ∪ T) so ∀ f ∈ S ∪ T, f(x) = 0. Call this hypothesis `hx`.
    rw mem_𝕍_iff at hx,
    -- To prove x ∈ 𝕍 S ∩ 𝕍 T, it suffices to prove x ∈ 𝕍 S and x ∈ 𝕍 T
    split,
    { -- We deal with the two cases separately.
      -- To prove x ∈ 𝕍 S, we need to show that for all f ∈ S, f(x) = 0
      rw mem_𝕍_iff,
      -- so say f ∈ S
      intros f hf,
      -- By hypothesis `hx`, it suffices to prove that f ∈ S ∪ T
      apply hx,
      -- but this is obvious
      left, assumption
    },
    { -- To prove x ∈ 𝕍 T, the argument is the same,
      -- so we write it the way a computer scientist would.
      -- (they prefer one incomprehensible line to four simple ones)
      exact mem_𝕍_iff.2 (λ f hf, hx _ (set.subset_union_right _ _ hf)),
    },
  },
  { -- Step 2: we prove the other inclusion.
    -- ⊢ 𝕍 S ∩ 𝕍 T ⊆ 𝕍 (S ∪ T) (NB `⊢` means "the goal is")
    -- say x is in 𝕍 S and 𝕍 T
    rintro x ⟨hxS, hxT⟩,
    -- We need to show that for all f ∈ S ∪ T, f(x) = 0
    rw mem_𝕍_iff,
    -- so choose f in S ∪ T
    intros f hf,
    -- Well, f is either in S or in T, so there are two cases.
    cases hf,
    { -- Say f ∈ S
      -- Recall that x ∈ 𝕍 S, so ∀ f ∈ S, f(x) = 0
      rw mem_𝕍_iff at hxS,
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
theorem 𝕍_Union {I : Type*} (S : I → set (mv_polynomial n k)) :
𝕍 (⋃ i, S i) = ⋂ i, 𝕍 (S i) :=
begin
  -- To prove equality of two subsets of kⁿ it suffices to prove ⊆ and ⊇.
  apply set.subset.antisymm,
  { -- Goal: 𝕍 (⋃ i, S i) ⊆ ⋂ i, 𝕍 (S i)
    -- Let x be in the left hand side
    intros x hx,
    -- it suffices to prove that for all j, x ∈ 𝕍 (S j) 
    rw set.mem_Inter,
    -- so choose some j ∈ I
    intro j,
    -- and say f ∈ S j.
    intros f hf,
    -- We now want to prove f(x) = 0.
    -- Now we know x ∈ 𝕍 (⋃ i, S i), so g(x) = 0 for all g in ⋃ i, S i
    -- Hence it suffices to prove that f ∈ ⋃ i, S i
    apply hx,
    -- By definition of the infinite union, it suffices to find
    -- some i ∈ I such that f ∈ S i
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
    rw mem_𝕍_iff,
    -- so say f is a polynomial in this union
    intros f hf,
    -- If f is in the union, then it's in one of the S i, so say f ∈ S j
    rw set.mem_Union at hf,
    cases hf with j hj,
    -- Now we know x is in the intersection of the 𝕍 (S i) for all i,
    -- so x ∈ 𝕍 (S j)
    rw set.mem_Inter at hx,
    have hxj := hx j,
    -- and because h(x) = 0 for every element h ∈ S j, 
    -- and we know f ∈ S j, we deduce f(x) = 0 as required.
    exact hxj _ hj
  }
end

-- For convenience, let's define multiplication on subsets of k[X₁,X₂,…,Xₙ]
-- in the obvious way: S * T := {s * t | s ∈ S, t ∈ T}.
instance : has_mul (set (mv_polynomial n k)) :=
⟨λ S T, {u | ∃ (s ∈ S) (t ∈ T), u = s * t}⟩

-- For this theorem, we need that k satisfies a * b = 0 => a = 0 or b = 0
theorem 𝕍_mul {k : Type*} [integral_domain k] {n : Type*}
  (S T : set (mv_polynomial n k)) :
𝕍 (S * T) = 𝕍 S ∪ 𝕍 T :=
begin
  -- to prove that the two sets are equal we will prove ⊆ and ⊇ 
  apply set.subset.antisymm,
  { -- This is the "harder" of the two inclusions;
    -- we need to check that if x vanishes on every element of S*T, 
    -- then x ∈ 𝕍 S or x ∈ 𝕍 T. So let x be in 𝕍 (S * T)
    intros x hx,
    -- We then know that for every f ∈ S * T, f(x) = 0
    rw mem_𝕍_iff at hx,
    -- Note for logicians: in this proof, we will assume
    -- the law of the excluded middle.
    classical, 
    -- If x ∈ 𝕍 S then the result is easy...
    by_cases hx2 : x ∈ 𝕍 S,
      -- because 𝕍 S ⊆ 𝕍 S ∪ 𝕍 T
      exact subset_union_left _ _ hx2,
    -- ...so we can assume assume x ∉ 𝕍 S,
    -- and hence that there's s ∈ S such that s(x) ≠ 0
    rw mem_𝕍_iff at hx2, push_neg at hx2, rcases hx2 with ⟨s, hs, hsx⟩,
    -- we now show x ∈ 𝕍 T,
      right,
    -- i.e., that for all t ∈ T we have t(x) = 0
    rw mem_𝕍_iff,
    -- So say t ∈ T
    intros t ht,
    -- We want to prove that t(x) = 0.
    -- Now by assumption, x vanishes on s * t. 
    replace hx := hx (s * t) ⟨s, hs, t, ht, rfl⟩,
    -- so s(x) * t(x) = 0
    rw eval_mul at hx,
    -- so either s(x) or t(x) = 0,
    cases mul_eq_zero.1 hx with hxs hxt,
      -- So the case s(x) = 0 is a contradiction
      contradiction,
    -- and t(x) = 0 is what we wanted to prove
    assumption
  },
  { -- Here's the easier of the two inclusions.
    -- say x ∈ 𝕍 S ∪ 𝕍 T,
    intros x hx,
    -- it's either in 𝕍 S or 𝕍 T.
    cases hx with hxS hxT,
    { -- Say x ∈ 𝕍 S.
      -- We know that x vanishes at every element of S.
      rw mem_𝕍_iff at hxS,
      -- We want to prove x vanishes at every polynomial of the form s * t
      -- with s ∈ S and t ∈ T.
      rw mem_𝕍_iff,
      -- so let's take a polynomial of the form s * t
      rintro _ ⟨s, hs, t, ht, rfl⟩,
      -- we need to show st(x)=0. So it suffices to show s(x)*t(x)=0
      rw eval_mul,
      -- Because x ∈ 𝕍 S, we have s(x)=0.
      replace hxS := hxS s hs,
      -- so it suffices to show 0 * t(x) = 0
      rw hxS,
      -- but this is obvious
      apply zero_mul, 
    },
    { -- This is the case x ∈ 𝕍 T and it's of course completely analogous.
      -- If I knew more about Lean's `WLOG` tactic I might not have to do
      -- this case. I'll just do it the computer science way (i.e., a proof
      -- which is quick and incomprehensible)
      rintro _ ⟨s, hs, t, ht, rfl⟩,
      rw [eval_mul, hxT t ht, mul_zero],
    }
  }
end

-- Pedantic exercise: we assumed a * b = 0 => a = 0 or b = 0. Give an
-- example of a commutative ring with that property which is not an
-- integral domain. Is the theorem still true for this ring?

-- Questions or comments? You can often find me on the Lean chat
-- at https://leanprover.zulipchat.com (login required,
-- real names preferred, be nice)

-- Prove a theorem. Write a function. xenaproject.wordpress.com
end affine_algebraic_set
