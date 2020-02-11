import ring_theory.algebra

namespace mv_polynomial

/-- evaluation of a polynomial over R in an R-algebra is an R-algebra morphism-/
noncomputable def alg_eval
  {R : Type*} [comm_ring R] {A : Type*} [comm_ring A] [algebra R A] {σ : Type*}
  (f : σ → A) : mv_polynomial σ R →ₐ[R] A :=
{ commutes' := λ _, eval₂_C _ _ _,
  ..ring_hom.of (eval₂ (algebra_map A : R → A) f)
}

/-- An R-algebra homomorphism f : R[X_1, X_2, ...] → A
is determined by the evaluations f(X_1), f(X_2), ... -/
@[simp] lemma alg_eval_hom_X 
  {R : Type*} [comm_ring R] {A : Type*} [comm_ring A] [algebra R A] {σ : Type*}
--{σ : Type*} (c : ℤ → β) [is_ring_hom c]
  (f : mv_polynomial σ R →ₐ[R] A) (x : mv_polynomial σ R) :
  eval₂ (algebra_map A) (f ∘ X) x = f x :=
mv_polynomial.induction_on x
(λ r, by rw eval₂_C; exact (f.commutes r).symm)
(λ p q hp hq, by { rw [eval₂_add, hp, hq], exact (is_ring_hom.map_add f).symm })
(λ p n hp, by { rw [eval₂_mul, eval₂_X, hp], exact (is_ring_hom.map_mul f).symm })

/-- If A is an R-algebra, then to give an R-algebra homomorphism
f : R[X_i : i ∈ σ] → A is to give a map σ → A -/
noncomputable def alg_hom_equiv
  {R : Type*} [comm_ring R] {A : Type*} [comm_ring A] [algebra R A] {σ : Type} :
  (mv_polynomial σ R →ₐ[R] A) ≃ (σ → A) :=
{ to_fun := λ f, ⇑f ∘ X,
  inv_fun := alg_eval,
  left_inv := λ _, alg_hom.ext $ alg_eval_hom_X _,
  right_inv := λ _, funext $ λ _, eval₂_X _ _ _,
}

end mv_polynomial

-- quotients

namespace alg_hom

open function

theorem ext_iff {R : Type*} [comm_ring R]
  {A : Type*} [comm_ring A] [algebra R A]
  {B : Type*} [comm_ring B] [algebra R B] (φ ψ : A →ₐ[R] B) :
  φ = ψ ↔ ∀ a : A, φ a = ψ a :=
⟨λ h a, by rw h, alg_hom.ext⟩

noncomputable def quot.lift 
  {R : Type*} [comm_ring R]
  {A : Type*} [comm_ring A] [algebra R A]
  {B : Type*} [comm_ring B] [algebra R B]
  {C : Type*} [comm_ring C] [algebra R C]
  (f : A →ₐ[R] B) (hf : surjective f)
  (g : A →ₐ[R] C) (hfg : ∀ a : A, f a = 0 → g a = 0) :
  B →ₐ[R] C :=
{ to_fun := λ b, g (classical.some (hf b)),
  map_one' := begin
    change _ = (1 : C),
    rw [←g.map_one, ←sub_eq_zero_iff_eq, ←g.map_sub],
    apply hfg,
    rw [f.map_sub, sub_eq_zero_iff_eq, f.map_one],
    exact classical.some_spec (hf 1),
  end,
  map_mul' := begin
    intros b₁ b₂,
    show _ = _ * _,
    rw [←g.map_mul, ←sub_eq_zero_iff_eq, ←g.map_sub],
    apply hfg,
    rw [f.map_sub, sub_eq_zero_iff_eq, f.map_mul],
    rw [classical.some_spec (hf b₁), classical.some_spec (hf b₂)],
    exact classical.some_spec (hf (b₁ * b₂))
  end,
  map_zero' := begin
    change _ = (0 : C),
    apply hfg,
    exact classical.some_spec (hf 0),
  end,
  map_add' := begin
    intros b₁ b₂,
    show _ = _ + _,
    rw [←g.map_add, ←sub_eq_zero_iff_eq, ←g.map_sub],
    apply hfg,
    rw [f.map_sub, sub_eq_zero_iff_eq, f.map_add],
    rw [classical.some_spec (hf b₁), classical.some_spec (hf b₂)],
    exact classical.some_spec (hf (b₁ + b₂))  
  end,
  commutes' := begin
    intros r,
    rw [←g.commutes, ←sub_eq_zero_iff_eq, ←g.map_sub],
    apply hfg,
    rw [f.map_sub, sub_eq_zero_iff_eq, f.commutes, classical.some_spec (hf (algebra_map B r))]
  end
}

theorem quot.thm 
  {R : Type*} [comm_ring R]
  {A : Type*} [comm_ring A] [algebra R A]
  {B : Type*} [comm_ring B] [algebra R B]
  {C : Type*} [comm_ring C] [algebra R C]
  (f : A →ₐ[R] B) (hf : surjective f)
  (g : A →ₐ[R] C) (hfg : ∀ a : A, f a = 0 → g a = 0) :
  alg_hom.comp (quot.lift f hf g hfg) f = g :=
begin
  ext a,
  show g _ = g a,
  rw [←sub_eq_zero_iff_eq, ←g.map_sub],
  apply hfg,
  rw [f.map_sub, sub_eq_zero_iff_eq],
  exact classical.some_spec (hf _),
end

theorem quot.thm'
  {R : Type*} [comm_ring R]
  {A : Type*} [comm_ring A] [algebra R A]
  {B : Type*} [comm_ring B] [algebra R B]
  {C : Type*} [comm_ring C] [algebra R C]
  (f : A →ₐ[R] B) (hf : surjective f)
  (g : A →ₐ[R] C) (hfg : ∀ a : A, f a = 0 → g a = 0) (a : A) :
  (quot.lift f hf g hfg) (f a) = g a :=
begin
  have xxx := quot.thm f hf g hfg,
  rw alg_hom.ext_iff at xxx,
  exact xxx a,
end

end alg_hom
