/-

Zariski's Lemma: if k is a field and K is a field finitely generated
as a k-algebra, then K is also finitely-generated as a k-module

-/

import ring_theory.integral_closure

example : 2 + 2 = 4 := rfl

open_locale classical

#check iff_true

lemma subalgebra.mem_coe_submodule (R : Type*) [comm_ring R] (A : Type*) [comm_ring A] [algebra R A]
  (M : subalgebra R A) (x : A) : x ∈ (M : submodule R A) ↔ x ∈ M := iff.rfl

--set_option pp.all true
lemma subalgebra.coe_submodule_top (R : Type*) [comm_ring R] (A : Type*) [comm_ring A] [algebra R A] :
  ((⊤ : subalgebra R A) : submodule R A) = ⊤ :=
begin
  ext,
  convert iff.refl true,
  rw [eq_true, subalgebra.mem_coe_submodule],
  exact algebra.mem_top,
end

theorem Zariskis_lemma
  -- let k be a field
  (k : Type*) [discrete_field k]
  -- and let k ⊆ K be another field
  (K : Type*) [discrete_field K] [algebra k K] 
  -- Assume that there's a finite subset S of K
  (S : set K) (hfs : S.finite)
  -- which generates K as a k-algebra
  -- (note: `⊤` is "the largest k-subalgebra of K", i.e., K)
  (hsgen : algebra.adjoin k S = ⊤)
  -- Then
  :
  -- K is finitely-generated as a k-vector space
(⊤ : submodule k K).fg
:=
begin
  unfreezeI,
  revert k,
  -- need to do induction on size of S
  intros,
  by_cases h : ∀ s ∈ S, is_integral k s,
  { convert fg_adjoin_of_finite hfs h, rw hsgen,
    exact (subalgebra.coe_submodule_top k K).symm},
  push_neg at h,
  sorry
end

