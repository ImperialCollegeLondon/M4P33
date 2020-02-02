/-

Zariski's Lemma: if k is a field and K is a field finitely generated
as a k-algebra, then K is also finitely-generated as a k-module

-/

import ring_theory.integral_closure field_theory.subfield

example : 2 + 2 = 4 := rfl

open_locale classical

lemma subalgebra.mem_coe_submodule (R : Type*) [comm_ring R] (A : Type*) [comm_ring A] [algebra R A]
  (M : subalgebra R A) (x : A) : x ∈ (M : submodule R A) ↔ x ∈ M := iff.rfl

lemma subalgebra.coe_submodule_top (R : Type*) [comm_ring R] (A : Type*) [comm_ring A] [algebra R A] :
  ((⊤ : subalgebra R A) : submodule R A) = ⊤ :=
begin
  ext,
  convert iff.refl true,
  rw [eq_true, subalgebra.mem_coe_submodule],
  exact algebra.mem_top,
end

universes u v

theorem Zariski's_lemma
  -- let k be a field
  (k : Type u) [discrete_field k]
  -- and let k ⊆ K be another field
  (K : Type v) [discrete_field K] [algebra k K] 
  -- Assume that there's a finite subset S of K
  (S : set K) (hfs : S.finite)
  -- which generates K as a k-algebra
  -- (note: `⊤` is "the largest k-subalgebra of K", i.e., K)
  (hsgen : algebra.adjoin k S = ⊤)
  -- Then
  :
  -- K is finite-dimensional as a k-vector space
(⊤ : submodule k K).fg
:=
begin
  -- It suffices to prove that for a fixed K, for all subfields k of K and for
  -- all subsets S of K of size n, if k[S]=K then K/k is module-finite.
  unfreezeI,
  revert k,
  obtain ⟨n, hn⟩ : {n : ℕ // @fintype.card S (set.finite.fintype hfs) = n} :=
    ⟨_, rfl⟩,
  -- We prove this by induction on n.
  induction n with d hd,
  { -- The base case has the size of S being zero
    intros,
    -- so S is empty
    have hS : S = ∅,
      rw fintype.card_eq_zero_iff at hn,
      rw set.eq_empty_iff_forall_not_mem,
      intros x hx, exact hn ⟨x, hx⟩,
    -- which means K = k (as subalgebras of K)
    rw [hS, algebra.adjoin_empty] at hsgen,
    -- (and hence as submodules of K)
    have hbottop : ((⊥ : subalgebra k K) : submodule k K) =
                   ((⊤ : subalgebra k K) : submodule k K),
      rw hsgen,
    -- and now this case is easy (rofl)
    rw [←subalgebra.coe_submodule_top, ←hbottop],
    rw submodule.fg_def,
    use {1},
    split, simp,
    ext x,
    rw subalgebra.mem_coe_submodule,
    rw algebra.mem_bot,
    rw submodule.mem_span_singleton,
    rw set.mem_range,
    split,
      rintro ⟨y, hy⟩, use y, rwa [algebra.smul_def'', mul_one] at hy,
      rintro ⟨y, hy⟩, use y, rw [algebra.smul_def'', hy, mul_one],
  },
  { -- In the inductive step we assume |S|=d+1 and we assume the result
    -- is true for all subfields k of K and all |S| of size d.
    intros k _ _ hSgen,
    -- In this step we break into two cases. 
    by_cases h : ∀ s ∈ S, is_integral k s,
    { -- In the first case,
      -- all elements of S are algebraic (a.k.a. integral) over k.
      -- In this case, it is a standard fact that K is also finite over k
      -- (just apply the tower law and induction).
      convert fg_adjoin_of_finite hfs h, rw hSgen,
      exact (subalgebra.coe_submodule_top k K).symm
    },
    -- The main part of the argument is here.
    -- We know there exists s ∈ S which is transcendental over k.
    -- We will use the inductive hypothesis to get a contradiction.
    exfalso,
    -- Firstly let's take s ∈ S transcendental over k.
    push_neg at h,
    rcases h with ⟨s, hs, hsnonint⟩,
    -- Let L:=k(s) be the subfield of K generated by k and s.
    let L := field.closure ((set.range (algebra_map K : k → K)) ∪ {s}),
    -- Let S' be S minus {s}
    set S' := S \ {s} with hS',
    -- then S' is finite(!)
    haveI : fintype S := sorry,
    haveI : fintype S' := fintype.of_injective (λ s, _ : S' → S) _,
    -- then S' has size d.
    have hs' : fintype.card S' = d,
    -- by the inductive hypo, K is algebraic over L, so it's
    -- algebraic over k[s][1/D] for some denominator D; this
    -- means k[s][1/D] is a field, which can't happen (it implies
    -- that D is in every maximal ideal of k[s] and hence 1+D is in
    -- none of them, thus 1+D is in k, so D is too, contradiction)
    repeat {sorry}
  }
end

