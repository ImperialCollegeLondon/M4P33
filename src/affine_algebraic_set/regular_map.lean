/-
Copyright (c) 2020 Kevin Buzzard
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, and whoever else wants to join in.
-/

import affine_algebraic_set.regular_function

/-!

# Regular maps

Definition and basic properties of regular maps 

-/

variables {k : Type*} [integral_domain k] {σ : Type*} {τ : Type*} {υ : Type*}

/-- A "regular map" is a pair: a function V → W, and a proof that
all the induced "coordinate maps" V → W → 𝔸ᵐ → k are regular maps -/
structure regular_map (V : affine_algebraic_set k σ) (W : affine_algebraic_set k τ) :=
(to_regular_fun : ∀ t : τ, regular_fun V)
(in_codomain : ∀ x, (λ t, to_regular_fun t x) ∈ W)

-- notation
infixr ` →ᵣ `:25 := regular_map

open mv_polynomial

namespace regular_map

variables {V : affine_algebraic_set k σ}
  {W : affine_algebraic_set k τ}
  {Y : affine_algebraic_set k υ} -- X gets confused with mv_polynomial.X

def to_fun : (V →ᵣ W) → ((V : set (σ → k)) → (W : set (τ → k))) :=
λ φ v, ⟨λ t, (φ.to_regular_fun t) v, φ.in_codomain _⟩

instance : has_coe_to_fun (V →ᵣ W) :=
{ F := _,
  coe := regular_map.to_fun }

def id (V : affine_algebraic_set k σ) : V →ᵣ V :=
{ to_regular_fun := λ s, ⟨λ x, x.1 s, X s, λ x hx, by rw eval_X⟩,
  in_codomain := begin
    -- need to check our definition sends x to x
    intro x,
    cases x with x hx,
    exact hx
  end }

/-- A regular map between varieties gives a ring map on regular functions. -/
def comap (φ : V →ᵣ W) : regular_fun W →+* regular_fun V :=
{ to_fun := λ f, 
  { to_fun := λ x, f (φ x),
    is_regular' := begin
      -- We have a regular map φ : V → W 
      -- and a regular function f : W → k
      -- and we need to check the composite is a regular function
      -- f comes from a polynomial F ∈ k[X_τ]
      cases f.is_regular with F hF,
      -- φ gives us a regular function on V for each t ∈ τ
      -- and hence a polynomial G_t ∈ k[X_σ] for each t ∈ T.
      -- we need a polynomial in k[X_σ]
      -- I think it's F(G_t) -- the evaluation of F when X_t ↦ G_t
      use eval₂ (C : k → mv_polynomial σ k) 
        (λ t, classical.some (φ.to_regular_fun t).is_regular' : τ → mv_polynomial σ k) F,
      intros x hx,
      set H := λ t, classical.some_spec (φ.to_regular_fun t).is_regular',
      sorry
    end
  },
  map_one' := _,
  map_mul' := _,
  map_zero' := _,
  map_add' := _ }

def comp (g : W →ᵣ Y) (f : V →ᵣ W) : V →ᵣ Y :=
{ to_regular_fun := λ u, sorry,
  in_codomain := sorry }



end regular_map

