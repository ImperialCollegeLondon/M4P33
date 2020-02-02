import affine_algebraic_set.Zariski -- Zariski topology
import affine_algebraic_set.V_and_I -- 𝕍 and 𝕀 basics
import for_mathlib.topological_space -- silly fact about closed sets I couldn't find

open affine_algebraic_set

open_locale classical -- classical logic

variables (σ : Type*) (k : Type*) [integral_domain k]

local notation `𝔸ⁿ` := σ → k

-- Question: Let A be any subset of 𝔸ⁿ.
-- Prove that 𝕍(𝕀(A)) is the Zariski closure of A.

lemma sheet_1.question_1 (A : set 𝔸ⁿ) : 𝕍 (𝕀 A) = closure A :=
begin
  -- we prove both inclusions separately.
  apply set.subset.antisymm,
  { -- Here we prove 𝕍 (𝕀 A) ⊆ closure A
    -- say x ∈ 𝕍 (𝕀 A)
    intros x hx,
    change 𝔸ⁿ at x,
    -- it suffices to prove that x is in every closed set containing A,
    rw mem_closure_iff',
    -- so let C be a closed set containing A
    intros C hC hAC,
    -- Because C is closed, it's 𝕍(S) for some S
    rw is_closed_iff at hC,
    cases hC with S hS,
    rw hS at hAC ⊢, clear hS C,
    -- Our goal is to prove x ∈ 𝕍 S,
    -- or in other words that f(x) = 0 for all f ∈ S
    rw mem_𝕍_iff,
    -- so say g ∈ S
    intros g hg,
    -- now x ∈ 𝕍 (𝕀 A) by assumption, so f(x) = 0 forall f ∈ 𝕀 A,
    rw mem_𝕍_iff at hx,
    -- so it suffices to prove g ∈ 𝕀 A
    apply hx, clear hx,
    -- i.e. that f(y) = 0 for all y ∈ A
    rw mem_𝕀_iff,
    -- so say y ∈ A
    intros y hy,
    -- then y ∈ 𝕍 S,
    replace hy := hAC hy,
    -- so f(y) = 0 for all f ∈ S
    rw mem_𝕍_iff at hy,
    -- and this is what we needed
    apply hy,
    assumption},
  { -- to prove the closure of A is a subset of 𝕍 (𝕀 A), it suffices
    -- to prove that 𝕍 (𝕀 A) is closed and contains A
    rw closure_subset_iff_subset_of_is_closed,
    { -- The fact that A ⊆ 𝕍 (𝕀 A) is straightforward
      intros x hx, rw mem_𝕍_iff, intros f hf, rw mem_𝕀_iff at hf, 
      apply hf, assumption
    },
    { -- and the fact that 𝕍 (𝕀 A) is closed follows straight from
      -- the definition, because it's in the image of 𝕍.
      rw is_closed_iff, use 𝕀 A}
  }
end

-- computer science version:
lemma sheet_1.question_1' (A : set 𝔸ⁿ) : 𝕍 (𝕀 A) = closure A :=
set.subset.antisymm
  (λ x hx, mem_closure_iff'.2 $ λ C hC hAC, begin
    cases (is_closed_iff _).1 hC with S hS,
    rw hS at hAC ⊢,
    exact λ g hg, hx _ (λ y hy, hAC hy _ hg), 
  end)
  ((closure_subset_iff_subset_of_is_closed $ (is_closed_iff _).2 ⟨_, rfl⟩).2 
  (λ x hx f hf, hf _ hx))
