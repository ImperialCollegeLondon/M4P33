/-
Copyright (c) 2020 Kevin Buzzard
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, and whoever else wants to join in.
-/

import affine_algebraic_set.regular_function

-- we want k-algebra homomorphisms
import ring_theory.algebra
/-!

# Regular maps

Definition and basic properties of regular maps 

-/

/-
  KB mathematician-friendly notation attempt
-/
local notation `subset_of` := set

variables {k : Type*} [integral_domain k] {m : Type*} {n : Type*} {p : Type*}

local notation `k[m]` := mv_polynomial m k
local notation `k[n]` := mv_polynomial n k
local notation `k[p]` := mv_polynomial p k
local notation `𝔸ᵐ` := m → k
local notation `𝔸ⁿ` := n → k
local notation `𝔸ᵖ` := p → k

-- For me(kmb), "function" and "map" are strongly synonymous and I find it difficult
-- to remember which is which when it comes "regular functions" and "regular maps".
-- However I do know that I'm trying to construct the category of affine algebraic sets
-- over an algebraically closed field k so this should inform what we should be proving.

-- We use polynomials
open mv_polynomial

-- We're proving theorems about affine algebraic sets so their names
-- should go in the affine algebraic set namespace
namespace affine_algebraic_set

variables {V : affine_algebraic_set k m} {W : affine_algebraic_set k n}
local notation `k[V]` := regular_fun V
local notation `k[W]` := regular_fun W


-- There are several equivalent definitions of a regular map. We begin
-- by defining them and showing their equivalence.

def is_morphism1 (φ : (V : subset_of 𝔸ᵐ) → (W : subset_of 𝔸ⁿ)) : Prop :=
∃ F : n → k[V], ∀ (v : (V : subset_of 𝔸ᵐ)) (i : n), (φ v : 𝔸ⁿ) i = F i v

def is_morphism2 (φ : (V : subset_of 𝔸ᵐ) → (W : subset_of 𝔸ⁿ)) : Prop :=
∃ Φ : k[n] →ₐ[k] k[V], ∀ (v : (V : subset_of 𝔸ᵐ)) (i : n), (φ v : 𝔸ⁿ) i = Φ (X i) v

def is_morphism3 (φ : (V : subset_of 𝔸ᵐ) → (W : subset_of 𝔸ⁿ)) : Prop :=
∃ Φ : k[n] →ₐ[k] k[V], ∀ (v : (V : subset_of 𝔸ᵐ)) (G : k[n]), G.eval (φ v) = (Φ G) v

def is_morphism4 (φ : (V : subset_of 𝔸ᵐ) → (W : subset_of 𝔸ⁿ)) : Prop :=
∃ φstar : k[W] →ₐ[k] k[V], ∀ (v : (V : subset_of 𝔸ᵐ)) (g : k[W]), g (φ v) = (φstar g) v

variable (φ : (V : subset_of 𝔸ᵐ) → (W : subset_of 𝔸ⁿ))

lemma four_implies_three : is_morphism4 φ → is_morphism3 φ :=
begin
  rintro ⟨φstar, hstar⟩,
  use alg_hom.comp φstar mv_polynomial.to_regular_fun.algebra_map,
  intros v G,
  exact hstar v (to_regular_fun.to_fun G),
end

lemma three_implies_two : is_morphism3 φ → is_morphism2 φ :=
begin
  rintro ⟨Φ, hΦ⟩,
  use Φ,
  intros v i,
  rw [←hΦ v (X i), eval_X],
end

lemma two_implies_one : is_morphism2 φ → is_morphism1 φ :=
begin
  rintro ⟨Φ, hΦ⟩,
  use (λ i, Φ (X i)),
  intros v i,
  exact hΦ v i,
end

lemma one_implies_two : is_morphism1 φ → is_morphism2 φ :=
begin
  rintro ⟨F, hF⟩,
  unfold is_morphism2,
  -- eval₂ gives the map
  let Φ.to_fun : mv_polynomial n k → regular_fun V := eval₂ (mv_polynomial.to_regular_fun.to_fun ∘ C) F,
  -- now need that it's a k-algebra hom.
  letI Φ.is_ring_hom : is_ring_hom Φ.to_fun := eval₂.is_ring_hom _ _,
  letI Φ.is_semiring_hom : is_semiring_hom Φ.to_fun := is_ring_hom.is_semiring_hom _,
  letI foo : is_semiring_hom (to_regular_fun.to_fun ∘ C : k → k[V]) := is_semiring_hom.comp _ _,
  let Φ.ring_hom := @ring_hom.of _ _ _ _ Φ.to_fun Φ.is_semiring_hom,
  let Φ : mv_polynomial n k →ₐ[k] regular_fun V :=
    { to_fun := Φ.to_fun,
      commutes' := begin
        intro t,
        show eval₂ (to_regular_fun.to_fun ∘ C : k → k[V]) F (C t) = _,
        convert eval₂_C _ _ _,
        exact foo,
      end,
      ..Φ.ring_hom},
  use Φ,
  intros v i,
  rw hF,
  apply congr_fun,
  apply congr_arg,
  show _ = eval₂ (to_regular_fun.to_fun ∘ C) F (X i),
  convert (eval₂_X _ _ _).symm,
  exact foo,
end

lemma two_implies_three : is_morphism2 φ → is_morphism3 φ :=
begin
  rintro ⟨Φ, hΦ⟩,
  use Φ,
  intros v G,
  replace hΦ := hΦ v,
  apply mv_polynomial.induction_on G,
  { intro a,
    rw eval_C,
    show a = (Φ (algebra_map (mv_polynomial n k) a)) v,
    rw alg_hom.commutes Φ a,
    show a = (C a : k[m]).eval v,
    rw eval_C,
  },
  { intros p q hp hq,
    rw [eval_add, hp, hq, alg_hom.map_add],
    refl
  },
  { intros p i h,
    rw [eval_mul, h, eval_X, hΦ, alg_hom.map_mul],
    refl
  }
end

lemma three_implies_four : is_morphism3 φ → is_morphism4 φ :=
begin
  rintro ⟨Φ,hΦ⟩,
  have hI : ∀ f : k[n], f ∈ 𝕀 W → Φ f = 0,
  { intros f hf,
    ext v,
    rw ←hΦ,
    rw mem_𝕀_iff at hf,
    rw hf,
    refl,
    exact (φ v).2
  },
  sorry
end

#exit
/-- A `morphism` between affine algebraic sets V ⊆ 𝔸ᵐ and W ⊆ 𝔸ⁿ, often called a regular map,
is a pair: a function φ : V → W, and a proof that there exists a k-algebra homomorphism
Φ : k[n] → k[V] such that for all t ≤ n and x ∈ V, φ(x)_t = (Φ X_t) x -/
structure morphism (V : affine_algebraic_set k m) (W : affine_algebraic_set k n) :=
(to_fun : (V : subset_of 𝔸ᵐ) → (W : subset_of 𝔸ⁿ))
(is_algebraic' : ∃ (Φ : k[n] →ₐ[k] regular_fun V),  ∀ (t : n) (x : (V : subset_of 𝔸ᵐ)),
  (to_fun x).1 t = Φ (X t) x)

-- notation
infixr ` →ᵣ `:25 := morphism


namespace morphism

variables {V : affine_algebraic_set k m}
  {W : affine_algebraic_set k n}
  {Y : affine_algebraic_set k p} -- X gets confused with mv_polynomial.X

local notation `k[V]` := regular_fun V
local notation `k[W]` := regular_fun W
local notation `k[Y]` := regular_fun Y

instance : has_coe_to_fun (V →ᵣ W) :=
{ F := _,
  coe := morphism.to_fun }

-- best attempt at prettiness so far
lemma is_algebraic (φ : V →ᵣ W) : ∃ (Φ : k[n] →ₐ[k] k[V]), ∀ (t : n) (x : (V : subset_of 𝔸ᵐ)),
  (φ x).1 t = Φ (X t) x := φ.is_algebraic'

def id (V : affine_algebraic_set k m) : V →ᵣ V :=
{ to_fun := id,
  is_algebraic' := begin
    use (to_regular_fun.algebra_map),
    intros t x,
    exact (eval_X t).symm,
  end }

-- lemma some_spec (φ : V →ᵣ W) (x : (V : subset_of 𝔸ᵐ)) (t : n) :
--   classical.some (φ.is_algebraic t) x = (φ x).1 t:=
-- begin
--   cases x,
--   exact (classical.some_spec (φ.is_algebraic t) _ _).symm,
-- end

-- lemma some_spec' (φ : V →ᵣ W) (x : (V : subset_of 𝔸ᵐ)) :
-- (λ (t : n), classical.some (φ.is_algebraic t) x) = (λ (t : n), (φ x).1 t) :=
-- by ext t; apply some_spec φ x t

/-- A regular map between varieties gives a ring map on regular functions. -/
def comap (φ : V →ᵣ W) : k[W] →+* k[V] :=
{ to_fun := λ f, 
  { to_fun := λ x, f (φ x),
    is_regular' := begin
    unfold is_regular,
      cases f.is_regular with F hF,
      cases φ.is_algebraic with Φ HΦ,
      cases to_regular_fun.surjective (Φ F) with G hG,
      use G,
      intro x,
      rw ←hF,
      unfold_coes at hG,
      have H : (to_regular_fun.to_fun : k[n] → k[V]) G x = 0,
      show ((to_regular_fun G : k[V]) ( x : (V : subset_of 𝔸ᵐ))) = _,
      use eval₂
        (C : k → k[m])
        (λ t, classical.some ((classical.some (φ.is_algebraic t)).is_regular) : n → k[m])
        F,
      intro x,
      rw ←hF,
      rw eval_eval₂
      -- now need to use mk'.some_spec
      -- suffices : eval (x : m → k) (eval₂ (C : k → k[m]) (λ t, (φ x).1 t) F) = eval (φ x) F,
      show eval (x : m → k) (eval₂ _ _ _) = _,
      rw some_spec' φ x,
      -- I think I need to rewrite
      -- conv begin
      --   to_lhs,
      --   congr, skip, congr, skip,
      --   simp [some_spec φ x],
      --   -- annoying
      -- end,
      -- unfold eval,
      -- rw eval₂_eq_eval_map,
      -- rw eval_eval,
      -- rw map_C,
      -- unfold_coes,
      -- unfold φ.to_fun,
      -- set y := φ (⟨x, hx⟩ : (V : subset_of 𝔸ᵐ)),
      -- unfold_coes at y,
      -- cases y with y hy,
      -- unfold_coes,
      -- rw eval_eval₂,
      -- let AAA := φ.to_regular_fun,
      -- We have a regular map φ : V → W 
      -- and a regular function f : W → k
      -- and we need to check the composite is a regular function
      -- f comes from a polynomial F ∈ k[X_τ]
--      let XXX := f.to_fun,

      -- φ gives us a regular function on V for each t ∈ n
      -- and hence a polynomial G_t ∈ k[X_σ] for each t ∈ T.
      -- we need a polynomial in k[X_σ]
      -- I think it's F(G_t) -- the evaluation of F when X_t ↦ G_t

      -- use eval₂ (C : k → mv_polynomial m k) 
      --   (λ t : n,
      --     begin
      --       let QQQ := 
      --         (classical.some (φ.to_regular_fun t).is_regular' : n → mv_polynomial m k),
      --       let YYY := f.to_fun,
      --       exact f.to_fun,
      --     end),

      -- intros x hx, 
      -- set YYY := λ t, (φ.to_regular_fun t).to_fun,
      -- set H := λ t, classical.some_spec (φ.to_regular_fun t).is_regular',
      -- set ZZZ := f.is_regular,
      -- simp only [(hF _ _).symm],
      sorry
    end
  },
  map_one' := sorry,
  map_mul' := sorry,
  map_zero' := sorry,
  map_add' := sorry }

--def comp (g : W →ᵣ Y) (f : V →ᵣ W) : V →ᵣ Y :=
--{ to_regular_fun := λ u, sorry,
--  in_codomain := sorry }



end morphism


