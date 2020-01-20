import data.mv_polynomial
import data.polynomial

example : true := trivial -- workaround for the "open_locale at top of file"
  -- issue

open_locale classical

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

def fin_succ_equiv_option (n : ℕ) : fin (n+1) ≃ option (fin n) :=
sorry

set_option pp.universes true

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

namespace mv_polynomial

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
    let φ := option_equiv_right k n,
    suffices h : φ f = 0, { simpa using congr_arg φ.symm h },
    apply ih,
    { sorry },
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

