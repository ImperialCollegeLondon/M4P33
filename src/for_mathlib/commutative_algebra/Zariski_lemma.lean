/-

Zariski's Lemma: if k is a field and K is a field finitely generated
as a k-algebra, then K is also finitely-generated as a k-module

-/

import ring_theory.integral_closure field_theory.subfield

import linear_algebra.finite_dimensional

import for_mathlib.finset -- Chris' lemma about S - {s}

import field_theory.minimal_polynomial -- I need a poly for an algebraic element
-- and this will do

example : 2 + 2 = 4 := rfl

open_locale classical

lemma subalgebra.mem_coe_submodule (R : Type*) [comm_ring R] (A : Type*)
  [comm_ring A] [algebra R A]
  (M : subalgebra R A) (x : A) : x ∈ (M : submodule R A) ↔ x ∈ M := iff.rfl

lemma subalgebra.coe_submodule_top (R : Type*) [comm_ring R]
  (A : Type*) [comm_ring A] [algebra R A] :
  ((⊤ : subalgebra R A) : submodule R A) = ⊤ :=
begin
  ext,
  convert iff.refl true,
  rw [eq_true, subalgebra.mem_coe_submodule],
  exact algebra.mem_top,
end

lemma clear_denominators (R : Type*) [comm_ring R] {K : Type*}
  [discrete_field K] [algebra R K] {S : finset K} {T : set K}
  (hST : ↑S ⊆ field.closure T) :
  ∃ D : K, D ≠ 0 ∧ D ∈ ring.closure T ∧ ∀ s ∈ S, D * s ∈ ring.closure T :=
begin
  revert hST,
  apply finset.induction_on S, -- no good because I lose hST
  { intro, use 1,
    split, symmetry, exact zero_ne_one,
    split, exact is_submonoid.one_mem _,
    intros s hs, cases hs,
  },
  rintros a s has H hasT,
  replace H := H (set.subset.trans (finset.subset_insert a s) hasT),
  rcases H with ⟨D0, hD00, hD0T, hD0⟩,
  rcases hasT (finset.mem_insert_self a s) with ⟨n, hn, d, hd, hd0, hnd⟩,
  use D0 * d,
  split, exact mul_ne_zero hD00 hd0,
  split, exact is_submonoid.mul_mem hD0T hd,
  intros k hk,
  rw finset.mem_insert at hk,
  cases hk,
  { rw hk,
    rw mul_assoc,
    apply is_submonoid.mul_mem hD0T,
    convert hn,
    rw ←hnd, 
    exact mul_div_cancel' n hd0,
  },
  rw [mul_assoc, mul_left_comm],
  exact is_submonoid.mul_mem hd (hD0 k hk),
end

universes u

open set algebra

/-
We formalise the proof in "A note on Zariski's Lemma" by John McCabe,
AMM Vol 83 No 7.
-/

-- We start with the following lemma.
lemma not_fin_dim_of_fin_gen_alg_of_nonintegral
  -- Let k be a field
  (k : Type*) [discrete_field k] (K : Type*) [discrete_field K]
  -- and let K be a field which is generated as a k-algebra
  -- by the finite set S ⊆ K
  [algebra k K] (S : finset K) (hSgen : adjoin k (↑S : set K) = ⊤)
  -- Say s ∈ S is transcendental over k
  (s : K) (hs : s ∈ S) (hsnonint : ¬ is_integral k s)
  -- Then
  :
  --  K/k(s) can't be finite-dimensional
  ¬ (finite_dimensional (field.closure (range (algebra_map K : k → K) ∪ {s})) K)
  :=
begin
  -- The argument to prove this in Atiyah--Macdonald uses the Artin-Tate lemma. 
  -- I won't formalise this but I'll leave it here for reference.
  -- Assume K is finite-dimensional over L := k(s).
  -- Choose a basis y₁, y₂, … yₘ.
  -- We can write each sᵢ∈S as sᵢ=∑ⱼ aᵢⱼyⱼ 
  -- and we can write each yᵢyⱼ as Σₖ bᵢⱼₖ yₖ with the a's and b's in L.
  -- If R is the k-algebra generated by the aᵢⱼ and the bᵢⱼₖ then
  -- any polynomial in the sᵢ with coefficients in k is easily checked to
  -- be an R-linear combination of the yₖ, and in particular K is a finite R-module.
  -- Because R is Noetherian we have that K is a Noetherian R-module, and hence
  -- its submodule L is a Noetherian R-module. Because R is a finitely-generated
  -- k-algebra this means that L is also a finitely-generated k-algebra.
  -- But L=k(s) is not finitely-generated, because consider 1/(d₁d₂…dₙ+1)
  -- where the dᵢ are the denominators of a finite set of generators

  -- A shorter to formalise argument is found in "A note on Zariski's Lemma"
  -- by John McCabe, AMM Vol 83 No 7. I'll formalise this instead.
  
  -- Assume K/L is finite-dimensional
  set L := (field.closure (range (algebra_map K : k → K) ∪ {s})) with hL,
  intro hKL,
  -- Each sᵢ ∈ S is thus algebraic over L, 
  have hLKi : ∀ (t : K), is_integral ↥L t,
    intro t,
    exact is_integral_of_noetherian' hKL t,
  -- so if we let X be the (finite) set of the coefficients
  -- of all the min polys of the sᵢ over L=k(s)
  set X := finset.image subtype.val (finset.bind S
    (λ t, let p := minimal_polynomial (hLKi t) in
    finset.image p.coeff (@finsupp.support ℕ _ _ p))) with hX,
  -- and if we choose D∈ k[s] non-zero such that D*X ⊆ k[s]
  have hX : ↑X ⊆ field.closure (range (algebra_map K) ∪ {s}),
  { rintro x hx,
    rw finset.mem_coe at hx,
    rw [hX, finset.mem_image] at hx,
    rcases hx with ⟨⟨yv, yp⟩, hy, hyx⟩,
    rw [←hL, ←hyx],
    exact yp },
  rcases clear_denominators k hX with ⟨D, hD0, hDL, hDden⟩, 
  -- then each sᵢ is integral over R := k[s][1/D].
  set R := adjoin k ({s, 1/D} : set K) with hR,
  have hSint : ∀ s ∈ S, is_integral R s,
  -- Hence K=k[S] is integral over k[s][1/D]. 
  -- This means k[s][1/D] is a field (a standard trick; a non-zero element of k[s][1/D]
  -- has an inverse in K, which is integral over k[s][1/D] and now multiply up
  -- and expand out), which can't happen (it implies
  -- that D is in every maximal ideal of k[s] and hence 1+D is in
  -- none of them, thus 1+D is in k, so D is too, contradiction)

  sorry
end
  
  /-

1 goal
L : set K := field.closure (range (algebra_map K) ∪ {s}),
hL : L = field.closure (range (algebra_map K) ∪ {s}),
hKL : finite_dimensional ↥L K
⊢ false
-/

instance Zariski's_lemma
  -- let k be a field
  (k : Type u) [discrete_field k]
  -- and let k ⊆ K be another field (note: I seem to need that it's in the same universe)
  (K : Type u) [discrete_field K] [algebra k K] 
  -- Assume that there's a finite subset S of K
  (S : finset K)
  -- which generates K as a k-algebra
  -- (note: `⊤` is "the largest k-subalgebra of K", i.e., K)
  (hsgen : adjoin k (↑S : set K) = ⊤)
  -- Then
  :
  -- K is finite-dimensional as a k-vector space
  finite_dimensional k K
:=
begin
  -- I will show that if K is a field and S is a finite subset, 
  -- then for all subfields k of K, if K=k(S) then K is finite-dimensional
  -- as a k-vector space.
  unfreezeI, revert S k,
  -- We'll do it by induction on the size of S,
  intro S, apply finset.strong_induction_on S, clear S, intros S IH,
  intros k hk hka, letI := hk, letI := hka,
  intro hSgen,
  -- Let's deal first with the case where all the elements of S are algebraic
  -- over k
  by_cases h_int : ∀ s ∈ S, is_integral k s,
  -- In this case, the result is standard, because K is finitely-generated
  -- and algebraic over k, so it's module-finite (use the
  -- tower law and induction)
  { convert fg_adjoin_of_finite (finset.finite_to_set S) h_int,
    rw hSgen,
    rw finite_dimensional.iff_fg,
    apply congr_arg,
    convert (subalgebra.coe_submodule_top k K).symm,
  },
  -- The remaining case is where S contains an element transcendental over k.
  push_neg at h_int,
  rcases h_int with ⟨s, hs, hsnonint⟩,
  -- We prove that this cannot happen.
  exfalso,
  -- Let L:=k(s) be the subfield of K generated by k and s.
  set L := field.closure ((set.range (algebra_map K : k → K)) ∪ {s}) with hL,
  -- then K = L(S - {s})
  -- and |S - {s}| < |S|, so by induction, K is finite-dimensional over L,
  have hKL : finite_dimensional L K,
  { refine IH (S.erase s) (finset.erase_ssubset hs) ↥L _,
    -- NB this is a proof that k(S)=L(S - {s})
    rw algebra.eq_top_iff at ⊢ hSgen,
    intro x, replace hSgen := hSgen x,
    rw ←subalgebra.mem_coe at ⊢ hSgen,
    revert hSgen x,
    show ring.closure (range (algebra_map K) ∪ ↑S) ≤
    ring.closure (range (algebra_map K) ∪ ↑(S.erase s)),
    apply ring.closure_subset,
    apply union_subset,
    { refine subset.trans _ ring.subset_closure, 
      refine subset.trans _ (subset_union_left _ _),
      rintro x ⟨x0, hx0⟩,
      suffices hx : x ∈ L,
      { use ⟨x, hx⟩,
        refl,
      },
      rw hL,
      apply field.subset_closure,
      apply subset_union_left _ _,
      use x0,
      exact hx0
    }, 
    { refine subset.trans _ ring.subset_closure,
      intros t ht,
      by_cases hst : t = s,
      { apply subset_union_left,
        cases hst, clear hst,
        suffices hsL : s ∈ L,
          use ⟨s, hsL⟩,
          refl,
        rw hL,
        apply field.subset_closure,
        apply subset_union_right _ _,
        apply mem_singleton
      },
      { apply subset_union_right _ _,
        exact finset.mem_erase_of_ne_of_mem hst ht,
      }
    }
  },
  
  convert not_fin_dim_of_fin_gen_alg_of_nonintegral k K S hSgen s hs hsnonint hKL, refl,

end

#check finset.image