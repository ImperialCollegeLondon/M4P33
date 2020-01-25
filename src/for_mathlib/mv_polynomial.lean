import data.mv_polynomial

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

-- Thanks to Johan Commelin for doing a bunch of the eval stuff below.

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

-- no longer sure if I even care about `vars`.
lemma mem_vars_iff_mem_degrees {R : Type*} [comm_semiring R] {σ : Type*}
  {p : mv_polynomial σ R} {n : σ} : n ∈ vars p ↔ n ∈ degrees p := 
multiset.mem_to_finset

-- Chris Hughes' alternative definition of `mv_polynomial.vars` using `bind`.
-- I have no idea whether this should be noncomputable.
/-- `vars' p` is the set of variables appearing in the polynomial `p`.
    It's probably the same as `vars p`. -/
noncomputable def vars' {R : Type*} {σ : Type*} [comm_semiring R]
  (p : mv_polynomial σ R) :
finset σ :=
p.support.bind finsupp.support

-- things which might need proving?

-- I will need to learn the interface for finsupp to do this one
-- Remark: I think only need φ 0 = 0, not semiring hom, but coeff_map wanted it.
lemma vars_map_sub {R : Type*} [comm_semiring R] {S : Type*} [comm_semiring S]
  {σ : Type*} {φ : R → S} [is_semiring_hom φ] {p : mv_polynomial σ R} :
vars' (map φ p) ⊆ vars' p :=
begin
  intros i hi,
  unfold vars' at hi ⊢,
  rw finset.mem_bind at hi ⊢,
  rcases hi with ⟨s, hs, his⟩,
  use s,
  existsi _, exact his, clear his i,
  simp,
  intro hps,
  dunfold mv_polynomial at p,
  have hps' : φ (p.to_fun s) = 0,
    convert is_semiring_hom.map_zero _, assumption,
  revert hs,
  simp,
  intro h1,
  apply h1,
  convert hps',
  change mv_polynomial σ R at p,
  change (map φ p).coeff s = φ (p.coeff s),
  apply coeff_map,
end

-- Thanks to Chris for this one

lemma eval₂_eq_of_eq_on_vars {R : Type*} [comm_semiring R]
  {S : Type*} [comm_semiring S] {σ : Type*}
  (f g : σ → S) (φ : R → S) (p : mv_polynomial σ R)
  [is_semiring_hom φ] -- do we need this??
  (h : ∀ i ∈ vars' p, f i = g i) :
eval₂ φ f p = eval₂ φ g p :=
begin
  unfold eval₂,
  unfold finsupp.sum finsupp.prod,
  refine finset.sum_congr rfl _,
  intros x hx,
  congr' 1,
  refine finset.prod_congr rfl _,
  intros i hi,
  simp only [vars', finset.mem_bind, exists_imp_distrib] at h,
  have := h i x hx hi,
  rw this,
end

-- KB practicing.
example {R : Type*} [comm_semiring R]
  {S : Type*} [comm_semiring S] {σ : Type*}
  (f g : σ → S) (φ : R → S) (p : mv_polynomial σ R)
  [is_semiring_hom φ] -- do we need this??
  (h : ∀ i ∈ vars' p, f i = g i) :
eval₂ φ f p = eval₂ φ g p :=
begin
  unfold eval₂,
  unfold finsupp.prod finsupp.sum,
  rw finset.sum_congr rfl,
  intros x hx,
  congr' 1,
  rw finset.prod_congr rfl,
  intros i hi,
  rw h,
  unfold vars',
  rw finset.mem_bind,
  use x,
  use hx,
  assumption,
end

def eq_sum_monomial_coeff {R : Type*} [comm_semiring R] {σ : Type*}
{p : mv_polynomial σ R} :
finset.sum p.support (λ s, monomial s (p.coeff s)) = p :=
begin
  apply mv_polynomial.ext,
  intro s,
  rw coeff_sum,
  simp only [coeff_monomial],
  by_cases hs : s ∈ p.support,
  { rw ←finset.sum_subset (show {s} ⊆ p.support, begin
      intros i hi,
      convert hs,
      cases hi, assumption, cases hi
    end),
    swap,
    { intros t ht hts,
      rw if_neg,
      intro hts2,
      apply hts,
      rw hts2,
      apply set.mem_singleton,
    },
    convert finset.sum_singleton,
    rw if_pos,
    refl
  },
  { rw ←finset.sum_subset (finset.empty_subset p.support),
    swap,
    { intros t ht1 ht2,
      rw if_neg,
      intro hts,
      apply hs,
      rwa hts at ht1,
    },
    rw finset.sum_empty,
    rw finsupp.not_mem_support_iff at hs,
    exact hs.symm
  }
end

/- Is this a sensible thing to prove?

lemma mem_rename_range {R : Type*} [comm_semiring R]
  {σ τ : Type*} {g : σ → τ} (p : mv_polynomial τ R)
  (h : (vars' p).to_set ⊆ set.range g) :
  ∃ q : mv_polynomial σ R, rename g q = p := sorry

-/

lemma preimage_subtype_range {R : Type*} [comm_semiring R]
  {σ : Type*} (p : mv_polynomial σ R) :
  ∃ q : mv_polynomial {i : σ // i ∈ p.vars'} R, rename subtype.val q = p :=
begin
  use finset.sum p.support
    (λ s, 
      monomial (finsupp.comap_domain subtype.val s (λ _ _ _ _, subtype.eq))
        (p.coeff s)),
  apply mv_polynomial.ext,
  intro s,
  rw ←finset.sum_hom p.support (rename subtype.val),
    all_goals {try {apply_instance}},
  rw coeff_sum,
  conv begin to_rhs,
  rw ←@eq_sum_monomial_coeff _ _ _ p,
  end,
  rw coeff_sum,
  apply finset.sum_congr rfl,
  intros t ht,
  rw coeff_monomial,
  rw rename_monomial,
  rw coeff_monomial,
  congr',
  rw finsupp.map_domain_comap_domain, intros i j, exact subtype.eq,
  suffices : t.support ⊆ vars' p, by simpa,
  unfold vars',
  intros i hi,
  rw finset.mem_bind,
  use t,
  use ht,
  assumption,
end

-- We know `fin_eval_eq_zero` from above, which is the below
-- theorem in the special case where `n` is finite.
-- We now use it to prove the general case. 

/-- Over an infinite integral domain a polynomial f is zero iff it
    evaluates to zero everywhere -/
lemma eval_eq_zero  {k : Type*} [integral_domain k] [infinite k]
  {σ : Type*} {p : mv_polynomial σ k} :
(∀ x, eval x p = 0) ↔ p = 0 :=
begin
  split, swap, intros hf x, rw [hf, eval_zero], -- easy direction
  intro hev,
  cases preimage_subtype_range p with q hq,
  suffices : q = 0,
    rw this at hq, rw ←hq, apply is_semiring_hom.map_zero,
  apply fin_eval_eq_zero,
  intro s₀,
  set s : σ → k := λ i, if hi : i ∈ p.vars' then s₀ ⟨i, hi⟩ else 0 with hs,
  have hs₀ : s₀ = s ∘ subtype.val,
    ext i,
    rw hs,
    dsimp, split_ifs, simp, cases i, contradiction,
  rw hs₀,
  rw ←eval_rename,
  rw hq,
  apply hev,
end

-- finset.sum p.support (λ s, monomial s (p.coeff s)) = p :=

end mv_polynomial