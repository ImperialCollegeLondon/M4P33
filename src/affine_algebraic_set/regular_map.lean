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

/-- A `morphism` between affine algebraic sets V ⊆ 𝔸ᵐ and W ⊆ 𝔸ⁿ, often called a regular map,
is a pair: a function V → W, and a proof that the induced n "coordinate maps" (the
composite maps V → W → 𝔸ⁿ → k with the final map being a projection) are regular maps -/
structure morphism (V : affine_algebraic_set k m) (W : affine_algebraic_set k n) :=
(to_fun : (V : subset_of 𝔸ᵐ) → (W : subset_of 𝔸ⁿ))
(is_algebraic' : ∀ (t : n), ∃ Ft : regular_fun V, ∀ (x : 𝔸ᵐ) (hx : x ∈ V), (to_fun ⟨x, hx⟩).1 t = Ft ⟨x, hx⟩)

-- notation
infixr ` →ᵣ `:25 := morphism

open mv_polynomial

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
lemma is_algebraic (φ : V →ᵣ W) (t : n) : ∃ Ft : k[V], ∀ (x : 𝔸ᵐ) (hx : x ∈ V),
  (φ ⟨x, hx⟩).1 t = Ft ⟨x, hx⟩ := φ.is_algebraic' t

def id (V : affine_algebraic_set k m) : V →ᵣ V :=
{ to_fun := id,
  is_algebraic' := begin
    intro t,
    use (regular_fun.mk' (X t)),
    intros x hx,
    show x t = eval x (X t),
    rw eval_X,
  end }

lemma some_spec (φ : V →ᵣ W) (x : (V : subset_of 𝔸ᵐ)) (t : n) :
  classical.some (φ.is_algebraic t) x = (φ x).1 t:=
begin
  cases x,
  exact (classical.some_spec (φ.is_algebraic t) _ _).symm,
end


/-- A regular map between varieties gives a ring map on regular functions. -/
def comap (φ : V →ᵣ W) : k[W] →+* k[V] :=
{ to_fun := λ f, 
  { to_fun := λ x, f (φ x),
    is_regular' := begin
    unfold is_regular,
      cases f.is_regular with F hF,
      let AAA := φ.is_algebraic',
      use eval₂
        (C : k → k[m])
        (λ t, classical.some ((classical.some (φ.is_algebraic t)).is_regular) : n → k[m])
        F,
      intro x,
      rw ←hF,
      -- now need to use AAA
      show _ = eval (_ : n → k) F,
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


