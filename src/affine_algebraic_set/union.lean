/-
Algebraic geometry lecture 1:

The union of two algebraic sets is an algebraic set.

Kevin Buzzard
-/

import affine_algebraic_set.basic -- the basic theory of affine algebraic sets.

/-
# The union of two affine algebraic sets is affine.

Latex statement of theorem:

Let $k$ be a field and let $n$ be a natural number.

Theorem. If $V$ and $w$ are two affine algebraic subsets of $k^n$
then their union $V\cup W$ is also an affine algebraic subset of $k^n$.


This file defines affine algebraic subsets of affine n-space and proves basic properties
about them.

## Important definitions

* `affine_algebraic_set k` -- the type of affine algebraic sets over the field `k`.

## Notation

None as yet -- do we need 𝔸ⁿ for affine n-space?

## Implementation notes

Much, but not all, of this file assumes that `k` is algebraically closed.
Remark: analysis/complex/polynomial.lean contains proof that ℂ is alg closed.

## References

Martin Orr's lecture notes!

## Tags

algebraic geometry, algebraic variety
-/

-- let k be a field
variables {k : Type*} [discrete_field k]

-- and let n be a natural number
variable {n : ℕ}

-- In Lean, the multivariable polynomial ring k[X₁, X₂, ..., Xₙ] is
-- denoted `mv_polynomial (fin n) k`. We could use better notation.
-- The set kⁿ is denoted `fin n → k` (which means maps from {0,1,2,...,(n-1)} to k).

-- We now make some definitions which we'll need in the course.

open mv_polynomial

namespace affine_algebraic_set

-- Now some basic facts about affine algebrai subsets.


set_option trace.simplify.rewrite false
set_option trace.simplify.rewrite true

/-- Two affine algebraic subsets with the same carrier are equal! -/
lemma ext (V W : affine_algebraic_set k n) : V.carrier = W.carrier → V = W :=
begin
  intro h,
  cases V,
  cases W,
  simpa, -- TODO -- why no debugging output?
end

/-- We can talk about elements of affine algebraic subsets of kⁿ  -/
instance : has_mem (fin n → k) (affine_algebraic_set k n) :=
⟨λ x V, x ∈ V.carrier⟩

/-- The union of two algebraic subsets of kⁿ is an algebraic subset-/
def union (V W : affine_algebraic_set k n) : affine_algebraic_set k n :=
{ carrier := V.carrier ∪ W.carrier,
  is_algebraic :=
  begin
    -- say S is the set that defines V
    cases V.is_algebraic with S hS,
    -- and T is the set that defines W
    -- (slightly fancier way)
    rcases W.is_algebraic with ⟨T, hT⟩,
    -- Now reduce it to a precise statement about zeros of polynomials
    rw [hS, hT],
    -- In Lean the question is this:

    -- Here's the answer to this question.
    use {u | ∃ (s ∈ S) (t ∈ T), u = s * t},
    -- To prove that V ∪ W is defined by this set, we prove both inclusions
    apply set.subset.antisymm,
    { -- say x ∈ V ∪ W,
      intros x hx,
      -- it's either in V or W.
      cases hx with hxV hxW,
      { -- Say it's in V
        rw set.mem_Inter,
        -- we have to show it's a zero of all the s * t
        intro u,
        suffices : ∀ s ∈ S, ∀ t ∈ T, u = s * t → x ∈ zeros u,
          sorry,
          --simpa using this, -- takes an age!
          -- TODO -- find rewrite?
          -- simpa only [...]?
        rintro s hs t ht rfl,
        rw zeros_mul,
        sorry

      },
      {
        sorry
      }
    },
    {
      sorry
    }
  end
}
end affine_algebraic_set