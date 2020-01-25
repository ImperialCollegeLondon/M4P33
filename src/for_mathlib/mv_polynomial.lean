import data.mv_polynomial
import data.polynomial

-- workaround for the "open_locale at top of file" issue in Lean 3
example : ℕ := 37

open_locale classical

lemma sum.rec_comp_left (X : Type*) (Y : Type*) (β : Type*) (γ : Type*)
  (i : β → X) (j : γ → X) (f : X → Y) (x : β ⊕ γ) :
  f (sum.rec i j x) = sum.rec (f ∘ i) (f ∘ j) x := by cases x; refl

namespace mv_polynomial

/-- Evaluating the constant polynomial 1 anywhere gives 1 -/
theorem eval_one {X : Type*} {R : Type*} [comm_semiring R]
  (x : X → R) : eval x 1 = 1 := eval_C _
  
-- this must be done somewhere else because the analogue is
-- in the polynomial namespace
theorem eval_pow {X : Type*} {R : Type*} [comm_semiring R]
  (f : mv_polynomial X R) (m : ℕ) (x : X → R) :
eval x (f ^ m) = (eval x f)^m :=
begin
  induction m with d hd,
    rw pow_zero,
    rw pow_zero,
    rw eval_one,
  rw pow_succ,
  rw pow_succ,
  rw eval_mul,
  rw hd,
end

end mv_polynomial

namespace polynomial

/-- Over an infinite integral domain a polynomial f is zero if it
    evaluates to zero everywhere -/
lemma eval_eq_zero
  {k : Type*} [integral_domain k] [infinite k] {f : polynomial k}
  (H : ∀ x, polynomial.eval x f = 0) : f = 0 :=
begin
  rcases infinite.exists_not_mem_finset (roots f) with ⟨x, hx⟩,
  contrapose! hx with hf,
  rw mem_roots hf,
  apply H,
end

/-- Over an infinite integral domain a polynomial f is zero iff it
    evaluates to zero everywhere -/
lemma eval_eq_zero_iff
  {k : Type*} [integral_domain k] [infinite k] {f : polynomial k} :
  (∀ x, polynomial.eval x f = 0) ↔ f = 0 :=
⟨polynomial.eval_eq_zero, by { rintro rfl x, exact rfl }⟩

end polynomial

def fin.equiv_empty : fin 0 ≃ empty :=
{ to_fun := λ i, false.elim $ nat.not_lt_zero _ i.2,
  inv_fun := empty.elim,
  left_inv := λ i, false.elim $ nat.not_lt_zero _ i.2,
  right_inv := λ x, x.elim }

def fin.equiv_pempty : fin 0 ≃ pempty :=
{ to_fun := λ i, false.elim $ nat.not_lt_zero _ i.2,
  inv_fun := pempty.elim,
  left_inv := λ i, false.elim $ nat.not_lt_zero _ i.2,
  right_inv := λ x, x.elim }

namespace mv_polynomial

@[simp] lemma eval_rename
  {k : Type*} [comm_semiring k]
  {m : Type*} {n : Type*} (e : m → n) (f : mv_polynomial m k) (x) :
  eval x (rename e f) = eval (x ∘ e) f :=
by apply f.induction_on; { intros, simp * }

lemma equiv_eval_eq_zero
  {k : Type*} [comm_semiring k]
  {m : Type*} {n : Type*} (e : m ≃ n)
  (H : (∀ f : mv_polynomial m k, (∀ x, eval x f = 0) → f = 0))
  (f : mv_polynomial n k) (hf : ∀ x, eval x f = 0) : f = 0 :=
begin
  let φ := ring_equiv_of_equiv k e,
  suffices h : φ.symm f = 0, { simpa using congr_arg φ h },
  apply H,
  intro x,
  show eval x (rename e.symm f) = 0,
  simp [hf],
end

end mv_polynomial

universe variables u v

def equiv.option {X : Type u} {Y : Type v} (e : X ≃ Y) : option X ≃ option Y :=
{ to_fun := option.map e,
  inv_fun := option.map e.symm,
  left_inv := λ x, by { cases x, refl, simp },
  right_inv :=  λ x, by { cases x, refl, simp } }

/-- n ↦ none -/
def fin_succ_equiv_option' (n : ℕ) : fin (n+1) ≃ option (fin n) :=
{ to_fun := λ x, if h : x.1 < n then some ⟨_, h⟩ else none,
  inv_fun := λ x, option.rec_on x ⟨n, nat.lt_succ_self _⟩ $
    λ x, ⟨x.1, lt_trans x.2 $ nat.lt_succ_self _⟩,
  left_inv := λ x,
  begin
    cases x with x hx,
    rw [nat.lt_succ_iff, le_iff_lt_or_eq] at hx,
    cases hx with hx hx,
    { dsimp, rw dif_pos hx},
    { dsimp, rw dif_neg _, cases hx, refl, apply not_lt_of_le, cases hx, refl}
  end,
  right_inv := begin
    intro x,
    cases x with x,
    { dsimp, rw dif_neg, apply lt_irrefl},
    dsimp,
    cases x with x hx,
    rw dif_pos hx,
  end }

/-- 0 ↦ none-/
def fin_succ_equiv_option (n : ℕ) : fin (n+1) ≃ option (fin n) :=
{ to_fun := λ x, if h : x.1 = 0 then none else some ⟨x.1 - 1, begin
    rw nat.sub_lt_left_iff_lt_add,
      convert x.2 using 1, apply add_comm,
    exact nat.pos_of_ne_zero h,
  end⟩,
  inv_fun := λ x, option.rec ⟨0, nat.zero_lt_succ _⟩
    (λ y, ⟨y.1 + 1, add_lt_add_right y.2 1⟩) x, 
  left_inv := 
  begin
    rintro ⟨⟨x⟩, hx⟩,
      refl,
    dsimp,
    rw dif_neg,
      simp,
    apply nat.succ_ne_zero
  end,
  right_inv := begin
    rintro (_ | ⟨x, h⟩),
      refl,
    dsimp,
    rw dif_neg,
      simp,
    apply nat.succ_ne_zero
  end }


lemma fintype.induction {P : Π (X : Type*) [fintype X], Prop}
  (h0 : P pempty) (hs : ∀ (X : Type*) [fintype X], P X → P (option X))
  (he : ∀ {X Y : Type*} [fintype X] [fintype Y] (e : X ≃ Y), P X → P Y)
  (X : Type*) [fintype X] : P X :=
begin
  rcases fintype.exists_equiv_fin X with ⟨n, ⟨e⟩⟩,
  apply he (equiv.ulift.trans e.symm), clear e,
  induction n with n ih,
  { exact he (equiv.ulift.trans fin.equiv_pempty).symm h0 },
  { specialize hs _ ih,
    apply he _ hs,
    refine (equiv.ulift.trans _).symm,
    refine (fin_succ_equiv_option n).trans _,
    refine equiv.ulift.option.symm }
end

/- 
mv_polynomial.option_equiv_right :
-- mv_polynomial (option β) α ≃+* mv_polynomial β (polynomial α)

it's built from

. mv_polynomial.ring_equiv_of_equiv
. mv_polynomial.sum_ring_equiv
. mv_polynomial.ring_equiv_congr

glued together with 

. ring_equiv.trans
-/

namespace mv_polynomial

attribute [simp] sum_to_iter_Xr sum_to_iter_Xl sum_to_iter_C

@[simp] theorem option_equiv_right_X_none {α β} [comm_semiring α] :
  option_equiv_right α β (X none) = C polynomial.X :=
show map (eval₂ polynomial.C (λu:punit, polynomial.X))
  (sum_to_iter α β unit
    (rename (equiv.option_equiv_sum_punit._match_1 β)
      (X none))) = C polynomial.X,
by simp

@[simp] theorem option_equiv_right_X_some {α β} [comm_semiring α] (b : β) :
  option_equiv_right α β (X (some b)) = X b :=
show map (eval₂ polynomial.C (λu:punit, polynomial.X))
  (sum_to_iter α β unit
    (rename (equiv.option_equiv_sum_punit._match_1 β)
      (X (some b)))) = X b,
by simp

@[simp] theorem option_equiv_right_C {α β} [comm_semiring α] (a : α) :
  option_equiv_right α β (C a) = C (polynomial.C a) :=
show map (eval₂ polynomial.C (λu:punit, polynomial.X))
  (sum_to_iter α β unit
    (rename (equiv.option_equiv_sum_punit._match_1 β)
      (C a))) = C (polynomial.C a),
by simp

/-
Mario Carneiro: I also brute forced my way through several other definitions
here, that should have definitional lemmas: ring_equiv_of_equiv,
option_equiv_sum_punit (the definition should not be simp), sum_comm (ditto),
sum_ring_equiv, punit_ring_equiv

Mario Carneiro: Ideally this proof should be dunfold option_equiv_right; simp
-/

theorem eval₂_eval₂ (R : Type*) [comm_semiring R] (β : Type*) (γ : Type*)
(S : Type*) [comm_semiring S] (f : R → S) [is_semiring_hom f]
(i : β → S) (j : γ → S) (p : mv_polynomial β (mv_polynomial γ R)) :
eval₂ (eval₂ f j) i p = eval i (map (eval₂ f j) p) :=
hom_eq_hom _ _ (by apply_instance) (by apply_instance)
  (λ _, by rw [eval₂_C, map_C, eval_C]) (λ _, by rw [eval₂_X, map_X, eval_X]) p

set_option class.instance_max_depth 100
theorem map_eval₂' {R : Type*} [comm_semiring R] {β : Type*} {γ : Type*}
  {S : Type*} [comm_semiring S] {f : R → S} [is_semiring_hom f]
  {j : γ → S} {p : mv_polynomial β (mv_polynomial γ R)} :
  map (eval₂ f j) p = eval₂ (C ∘ f) (λ n, sum.rec X (C ∘ j) n) (iter_to_sum _ _ _ p) :=
begin
  rw iter_to_sum,
  rw eval₂_eval₂,
  rw ←eval₂_eq_eval_map,
  apply hom_eq_hom, apply_instance, apply_instance,
  { intro b,
    suffices : (C (eval₂ f j b) : mv_polynomial β S) =
      eval₂ (C ∘ f) (λ n, sum.rec X (C ∘ j) n) (eval₂ C (X ∘ sum.inr) b),
    simpa using this,
    rw ←rename,
    rw eval₂_rename,
    rw [show ((λ (n : β ⊕ γ), sum.rec X (C ∘ j) n) ∘ sum.inr : γ → mv_polynomial β S) = C ∘ j,
      by funext b; refl],
    apply eval₂_comp_left},
  { intro b,
    simp},
end

theorem eval₂_eval₂' (R : Type*) [comm_semiring R] (β : Type*) (γ : Type*)
(S : Type*) [comm_semiring S] (f : R → S) [is_semiring_hom f]
(i : β → S) (j : γ → S) (p : mv_polynomial β (mv_polynomial γ R)) :
eval₂ (eval₂ f j) i p = eval₂ f (λ n, sum.rec i j n) (iter_to_sum _ _ _ p) :=
begin
  rw eval₂_eval₂,
  rw map_eval₂',
  generalize : iter_to_sum _ _ _ p = p',
  apply hom_eq_hom _ _ _ _ _ _ p',
    apply_instance, apply_instance, apply_instance,
  { intro r,
    rw [eval₂_C, eval₂_C, eval_C]},
  { rintro (b | c),
    { simp},
    { simp},
  }
end

/-- Over an infinite integral domain a polynomial f in finitely many
    variables is zero if it evaluates to zero everywhere -/
lemma fin_eval_eq_zero
  {k : Type*} [int : integral_domain k] [inf : infinite k]
  {n : Type*} [fin : fintype n] :
  ∀ {f : mv_polynomial n k}, (∀ x, eval x f = 0) → f = 0 :=
begin
  unfreezeI,
  revert inf int k,
  revert fin n,
  refine fintype.induction _ _ _,
  { intros k int inf f H,
    have h : (pempty_ring_equiv k) f = 0 := H _,
    replace h := congr_arg (pempty_ring_equiv k).symm h,
    rw [ring_equiv.symm_apply_apply] at h,
    convert h, symmetry, exact ring_equiv.map_zero _ },
  { intros n _ ih k int inf f hf,
    set φ := option_equiv_right k n with hφ,
    suffices h : φ f = 0, { simpa using congr_arg φ.symm h },
    apply ih,
    { intro x,
      apply polynomial.eval_eq_zero,
      intro xoo,
      let xo : option n → k :=
        λ j, option.rec xoo (λ i, polynomial.eval xoo (x i)) j,
        convert hf xo,
        rw hφ,
        apply hom_eq_hom _ _ _ _ _ _ f,
          apply_instance, apply_instance, apply_instance, 
        { intro a,
          rw eval_C,
          simp},
        { intro xn,
          cases xn with xn hxn,
          { simp },
          { simp },
        }
      },
    { resetI,
      apply infinite.of_injective polynomial.C,
      swap, assumption,
      intros x y h, exact polynomial.C_inj.1 h, 
    } },
  { intros m n _ _ e H k int inf f,
    apply mv_polynomial.equiv_eval_eq_zero e,
    apply @H }
end
.

lemma mem_vars_iff_mem_degrees {R : Type*} [comm_semiring R] {σ : Type*}
  {p : mv_polynomial σ R} {n : σ} : n ∈ vars p ↔ n ∈ degrees p := 
multiset.mem_to_finset


variables {R : Type*} [comm_semiring R] {σ : Type*} {p : mv_polynomial σ R} 
#check finset.bind (p.support : finset (σ →₀ ℕ)) finsupp.support

#check finset.sup -- a fold
#check finset.bind -- via multiset.bind 
#check multiset.bind -- join map
#check multiset.sum -- a foldr

lemma puzzle (α : Type*) (s : finset α) (β : Type*) [decidable_eq β]
  (f : α → finset β) :
finset.bind s f = finset.sup s f  :=
begin
  ext x,
  rw finset.mem_bind,
  split,
  { rintro ⟨a, has, hxa⟩,
    have h : f a ≤ _ := finset.le_sup has,
    exact h hxa
  },
  { intro hx,
    sorry

  }
end

example {R : Type*} [comm_semiring R] {σ : Type*} {p : mv_polynomial σ R} :
vars p = p.support.bind finsupp.support :=
begin
  ext x,
  rw mem_vars_iff_mem_degrees,
  unfold degrees,
  congr',
  rw puzzle,
  simp,
  sorry
  -- unfold finsupp.to_multiset,
  -- rw finset.sup_eq_supr,
  -- unfold finset.sup,
  -- unfold finset.bind,
  -- simp,
  -- split,
  -- rw mem_sup,
end

-- I will need to learn the interface for finsupp to do this one
-- Remark: only need φ 0 = 0, not semiring hom.
lemma vars_map_sub {R : Type*} [comm_semiring R] {S : Type*} [comm_semiring S]
  {σ : Type*} {φ : R → S} [is_semiring_hom φ] {p : mv_polynomial σ R} :
vars (map φ p) ⊆ vars p :=
begin
  intro i,
  sorry,
end

-- I think I'll also need to learn about finsupp to do this one.
-- lemma eval_eq_of_eq_on_vars {R : Type*} [comm_semiring R] {σ : Type*}
--   (f g : σ → R) (p : mv_polynomial σ R)
--   (h : ∀ i ∈ (p.support.bind finsupp.support), f i = g i) :
-- eval f p = eval g p :=
-- begin
--   unfold eval,
--   sorry
-- end

lemma eval₂_eq_of_eq_on_vars {R : Type*} [comm_semiring R]
  {S : Type*} [comm_semiring S] {σ : Type*}
  (f g : σ → S) (φ : R → S) (p : mv_polynomial σ R)
  [is_semiring_hom φ] -- do we need this??
  (h : ∀ i ∈ (p.support.bind finsupp.support), f i = g i) :
  -- *TODO* why does the pretty printer change that to the less
  -- mathematician-friendly 
  -- h : ∀ (i : σ), i ∈ finset.bind (p.support) finsupp.support → f i = g i
  -- ?
eval₂ φ f p = eval₂ φ g p :=
begin
  unfold eval₂,
  --*TODO*: goal now starts
  -- ⊢ finsupp.sum p (λ (s : σ →₀ ℕ)
  -- Why is this not displayed as ⊢ p.sum ...?
  -- Of course what I really want is $\Sigma_p$
  -- or one of its myriad variants.
  -- This would be less confusing for mathematicians.
  unfold finsupp.sum finsupp.prod,
  refine finset.sum_congr rfl _,
  intros x hx,
  congr' 1,
  refine finset.prod_congr rfl _,
  intros i hi,
  /-
  simp only [finset.mem_bind, exists_imp_distrib] at h,
  have := h i x hx hi,
  rw this,
  -/
  replace h := h i,
  rw finset.mem_bind at h,
  rw exists_imp_distrib at h,
  replace h := h x,
  rw exists_imp_distrib at h,
  rw h, assumption, assumption
end

lemma mem_rename_range {R : Type*} [comm_semiring R]
  {σ τ : Type*} {g : σ → τ} (p : mv_polynomial τ R)
  (h : (vars p).to_set ⊆ set.range g) :
  ∃ q : mv_polynomial σ R, rename g q = p := sorry

open function

/-- Over an infinite integral domain a polynomial f is zero iff it
    evaluates to zero everywhere -/
lemma eval_eq_zero  {k : Type*} [integral_domain k] [infinite k]
  {n : Type*} {f : mv_polynomial n k} :
(∀ x, eval x f = 0) ↔ f = 0 :=
begin
  split, swap, intros hf x, rw [hf, eval_zero], -- easy direction
  intro hev,
  let n0 := ((vars f).to_set : Type _),
  let g : n0 → n := λ i, i.1,
  have g_inj : injective g,
    intros i1 i2 h, exact subtype.ext.2 h,
  let R0 := mv_polynomial (vars f).to_set k,
  sorry
end

end mv_polynomial

