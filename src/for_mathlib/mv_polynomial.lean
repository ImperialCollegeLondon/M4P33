import data.mv_polynomial

namespace mv_polynomial

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

/-- Over an infinite integral domain a polynomial f is zero iff it
    evaluates to zero everywhere -/
lemma mv_polynomial.eval_eq_zero  {k : Type*} [integral_domain k] [infinite k]
  {n : Type*} {f : mv_polynomial n k} :
(∀ x, eval x f = 0) ↔ f = 0 :=
begin
  split, swap, intros hf x, rw [hf, eval_zero], -- easy direction
  sorry 
end

end mv_polynomial

