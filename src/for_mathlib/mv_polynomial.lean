import data.mv_polynomial
import data.polynomial

example : true := trivial -- workaround for the "open_locale at top of file"
  -- issue

open_locale classical

lemma sum.rec_comp_left (X : Type*) (Y : Type*) (β : Type*) (γ : Type*) (i : β → X)
  (j : γ → X) (f : X → Y) (x : β ⊕ γ) :
  f (sum.rec i j x) = sum.rec (f ∘ i) (f ∘ j) x := by cases x; refl

namespace mv_polynomial

/-- Evaluating the constant polynomial 1 anywhere gives 1 -/
theorem eval_one {X : Type*} {R : Type*} [comm_semiring R]
  (x : X → R) : eval x 1 = 1 := eval_C _
  
-- this must be done somewhere else because it's in polynomial namespace
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
  {m : Type*} {n : Type*} (e : m ≃ n) (f : mv_polynomial m k) (x) :
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

/-- n ↦ none-/
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

#check mv_polynomial.option_equiv_right

namespace mv_polynomial

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
  { intro b, simp,
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

/-- Over an infinite integral domain a polynomial f is zero if it
    evaluates to zero everywhere -/
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
        apply hom_eq_hom _ _ _ _ _ _ f,
        sorry, sorry, sorry,
--          apply_instance, apply_instance, apply_instance, 
        { sorry},
        -- { intro a,
        --   rw eval_C,
        --   unfold_coes,
        --   suffices : ((φ.to_fun (C a : mv_polynomial (option n) k)) : mv_polynomial n (polynomial k)) =
        --     (C (polynomial.C a : polynomial k) : mv_polynomial n (polynomial k)),
        --     rw [this,eval_C, polynomial.eval_C],
        --   rw hφ,
        --   show (ring_equiv.trans (sum_ring_equiv k n unit) (ring_equiv_congr (mv_polynomial unit k) (punit_ring_equiv k))).to_fun
        --     (rename (equiv.option_equiv_sum_punit._match_1 n) (C a)) =
        --     C (polynomial.C a),
        --   rw rename_C,
        --   show (mul_equiv.to_equiv
        --     (ring_equiv.to_mul_equiv
        --       (ring_equiv_congr (mv_polynomial unit k) (punit_ring_equiv k)))).to_fun
        --     ((sum_to_iter k n unit) (C a)) =
        --     C (polynomial.C a),
        --   rw sum_to_iter_C,
        --   unfold ring_equiv_congr,
        --   show map ⇑(punit_ring_equiv k) _ = _,
        --   rw map_C,
        --   congr,
        --   dunfold punit_ring_equiv,
        --   unfold_coes, dsimp,
        --   simp},
        { intro x,
          cases x with x hx,
          { rw eval_X,
            show _ = xoo,
            rw hφ, 
            dunfold option_equiv_right,
            unfold_coes,
            rw ring_equiv.trans, dsimp,
            rw mul_equiv.trans, dsimp,
            rw equiv.trans, dsimp,
            dunfold ring_equiv_of_equiv,
            dsimp,
            simp,
            show polynomial.eval xoo
              (eval x
              ((mul_equiv.to_equiv
              (ring_equiv.to_mul_equiv
              (ring_equiv.trans (sum_ring_equiv k n unit)
              (ring_equiv_congr (mv_polynomial unit k) (punit_ring_equiv k))))).to_fun
              ((rename (equiv.option_equiv_sum_punit._match_1 n))
              (X none)))) =
              xoo,
            rw ring_equiv.trans, 
            show polynomial.eval xoo
              (eval x
              (((mul_equiv.trans (ring_equiv.to_mul_equiv (sum_ring_equiv k n unit))
              (ring_equiv.to_mul_equiv
              (ring_equiv_congr (mv_polynomial unit k) (punit_ring_equiv k)))).to_fun)
              (rename (equiv.option_equiv_sum_punit._match_1 n) (X none)))) =
              xoo,
            rw rename_X,
            rw mul_equiv.trans, dsimp,
            rw equiv.trans, dsimp,
            dunfold ring_equiv_congr,
            show polynomial.eval xoo
              (eval x
              ((map ⇑(punit_ring_equiv k))
              ((mul_equiv.to_equiv (ring_equiv.to_mul_equiv (sum_ring_equiv k n unit))).to_fun
              (X (sum.inr punit.star))))) = xoo,
            dunfold sum_ring_equiv,
            show polynomial.eval xoo
              (eval x
              (map ⇑(punit_ring_equiv k)
              ((mul_equiv.to_equiv
              (ring_equiv.to_mul_equiv
              (mv_polynomial_equiv_mv_polynomial k (n ⊕ unit) n (mv_polynomial unit k) (sum_to_iter k n unit) _
              (iter_to_sum k n unit)
                      _
                      _
                      _
                      _
                      _))).to_fun
              (X (sum.inr punit.star))))) = xoo,
            dunfold mv_polynomial_equiv_mv_polynomial,
            show polynomial.eval xoo
              (eval x
              (map ⇑(punit_ring_equiv k)
              ((sum_to_iter k n unit)
              (X (sum.inr punit.star))))) = xoo,
            rw sum_to_iter_Xr,
            simp,
            unfold_coes,
            dunfold punit_ring_equiv,
            dsimp,
            rw eval₂_X,
            rw polynomial.eval_X},
          { sorry}
        }
      },
    { resetI, sorry } },
  { intros m n _ _ e H k int inf f,
    apply mv_polynomial.equiv_eval_eq_zero e,
    apply @H }
end

/-- Over an infinite integral domain a polynomial f is zero iff it
    evaluates to zero everywhere -/
lemma eval_eq_zero_iff
  {k : Type*} [integral_domain k] [infinite k]
  {n : Type*} {f : mv_polynomial n k} :
  (∀ x, eval x f = 0) ↔ f = 0 :=
begin
  sorry
end

/-- Over an infinite integral domain a polynomial f is zero iff it
    evaluates to zero everywhere -/
lemma eval_eq_zero  {k : Type*} [integral_domain k] [infinite k]
  {n : Type*} {f : mv_polynomial n k} :
(∀ x, eval x f = 0) ↔ f = 0 :=
begin
  split, swap, intros hf x, rw [hf, eval_zero], -- easy direction
  sorry 
end

end mv_polynomial

