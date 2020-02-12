/-
Copyright (c) 2020 Kevin Buzzard
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, and whoever else wants to join in.
-/

import affine_algebraic_set.regular_function

-- we want k-algebra homomorphisms
import ring_theory.algebra

-- we want facts about k-algebra homs that aren't in mathlib
import for_mathlib.ring_theory.algebra

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
variables {Y : affine_algebraic_set k p} -- X gets confused with mv_polynomial.X
local notation `k[V]` := regular_fun V
local notation `k[W]` := regular_fun W
local notation `k[Y]` := regular_fun Y

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
  use alg_hom.comp φstar mv_polynomial.to_regular_fun_algebra_map,
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
  have hfΦ : ∀ (f : mv_polynomial n k),
    (to_regular_fun_algebra_map : mv_polynomial n k →ₐ[k] regular_fun W) f = 0 → Φ f = 0,
  { intros f hf,
    apply hI,
    intros x hx, 
    show (mv_polynomial.to_regular_fun_algebra_map :
      mv_polynomial n k →ₐ[k] regular_fun W) f ⟨x, hx⟩ = 0,
    rw hf,
    refl
  },
  existsi
    (alg_hom.quot.lift mv_polynomial.to_regular_fun_algebra_map to_regular_fun.surjective Φ hfΦ :
    regular_fun W →ₐ[k] regular_fun V),
  intros v g,
  cases to_regular_fun.surjective g with G hG,
  rw ←hG,
  convert hΦ v G,
  apply congr_fun _ v,
  dsimp,
  apply congr_arg,
  refine alg_hom.quot.thm' _ _ Φ _ G,
end

/-- A `morphism` between affine algebraic sets V ⊆ 𝔸ᵐ and W ⊆ 𝔸ⁿ, often called a regular map,
is a pair: a function φ : V → W, and a proof that there exists a k-algebra homomorphism
φstar : k[W] → k[V] such that g ∘ φ = φstar(g) for all g : k[W]  -/
structure morphism (V : affine_algebraic_set k m) (W : affine_algebraic_set k n) :=
(to_fun : (V : subset_of 𝔸ᵐ) → (W : subset_of 𝔸ⁿ))
(is_morphism' : 
  ∃ φstar : regular_fun W →ₐ[k] regular_fun V, ∀ (v : (V : subset_of 𝔸ᵐ)) (g : regular_fun W),
    g (to_fun v) = (φstar g) v)

-- notation
infixr ` →ᵣ `:25 := morphism

namespace morphism

instance : has_coe_to_fun (V →ᵣ W) :=
{ F := _,
  coe := morphism.to_fun }

-- best attempt at prettiness so far
lemma is_morphism (φ : V →ᵣ W) : ∃ (φstar : k[W] →ₐ[k] k[V]), ∀ (v : (V : subset_of 𝔸ᵐ))
  (g : k[W]), g (φ v) = φstar g v := φ.is_morphism'

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
noncomputable def comap (φ : V →ᵣ W) : k[W] →ₐ[k] k[V] :=
{ to_fun := λ f, 
  { to_fun := λ x, f (φ x),
    is_regular' := begin
    unfold is_regular,
      cases φ.is_morphism with Φ HΦ,
      cases to_regular_fun.surjective (Φ f) with G hG,
      use G,
      intro x,
      rw [HΦ x f, ←hG],
      refl,
    end
  },
  map_one' := rfl,
  map_mul' := λ f g, rfl,
  map_zero' := rfl,
  map_add' := λ f g, rfl,
  commutes' := λ r, begin
    ext x,
    convert (show r = r, from rfl),
    { refine eval_C r},
    { refine eval_C r},
  end
}

lemma comap_def (φ : V →ᵣ W) (f : k[W]) (v : (V : subset_of 𝔸ᵐ)) :
  φ.comap f v = f (φ v) := rfl

def id (V : affine_algebraic_set k m) : V →ᵣ V :=
{ to_fun := id,
  is_morphism' := ⟨alg_hom.id k _, λ _ _, rfl⟩}


def comp (φ : W →ᵣ Y) (ψ : V →ᵣ W) : V →ᵣ Y :=
{ to_fun := λ u, φ (ψ u),
  is_morphism' := ⟨alg_hom.comp ψ.comap φ.comap, begin
    intros v f,
    rw ←comap_def,
    rw ←comap_def,
    refl,
  end⟩
}



end morphism

end affine_algebraic_set

