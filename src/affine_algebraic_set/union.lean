/-
Algebraic geometry lecture 1:

The union of two algebraic sets is an algebraic set.

Kevin Buzzard
-/

import affine_algebraic_set.basic -- the basic theory of affine algebraic sets.

/-!
# The union of two affine algebraic sets is affine.

Let k be a field and let n be a natural number. We prove the following
theorem in this file:

Theorem. If V and W are two affine algebraic subsets of kⁿ
then their union V ∪ W is also an affine algebraic subset of kⁿ.

Lean version:

`def union (V W : affine_algebraic_set k n) : affine_algebraic_set k n`

Maths proof: if V is cut out by the set S ⊆ k[X_1,X_2,…,X_n]
and W is cut out by T, then we claim V ∪ W is cut out by the set ST := { s*t | s ∈ S and t ∈ T}.
To prove that the set cut out by ST equals V ∪ W, we prove both inclusions separately.

One inclusion is very easy. If x ∈ V ∪ W then either every element of S vanishes at x or every
element of T vanishes on x, and either way every element of ST vanishes at x.

Conversely, if x vanishes at every element of ST, then we want to prove that x ∈ V ∪ W. If x is
in V then we're done. If not, then this means that there exists some s ∈ S with s(x) ≠ 0. 
Then for every t ∈ T, we have s(x)t(x)=st(x)=0, and hence t(x)=0, which implies that x is in W.

## Implementation notes

I defined an affine algebraic set to be the zeros of an arbitrary
set of functions, as opposed to just a finite set. We will see later
on that these definitions are equivalent.

If V is an affine algebraic set, then V is a pair. The first
element of the pair is a subset V.carrier ⊆ kⁿ, but we will call this set V as well (there is
a coercion from affine algebraic sets to subsets of kⁿ).
The second element of the pair is the proof that there exists a subset S of k[X_1,X_2,...,X_n]
such that V is cut out by S, by which I mean that V is the set of x ∈ k^n which vanish
at each element of S.

## References

Martin Orr's lecture notes at https://homepages.warwick.ac.uk/staff/Martin.Orr/2017-8/alg-geom/

## Tags

algebraic geometry, algebraic variety
-/

-- end of docstring; code starts here. 

-- We're proving theorems about affine algebraic sets so the names of the theorems
-- should start with "affine_algebraic_set".
namespace affine_algebraic_set

-- let k be a field
variables {k : Type*} [discrete_field k]

-- and let σ be any set e.g. {1,2,3,...,n}
variable {σ : Type*}

-- We're working with multivariable polynomials, so let's get access to their notation
open mv_polynomial

-- Now here's a basic fact about affine algebraic sets.

/-- The union of two algebraic subsets of kⁿ is an algebraic subset-/
def union (V W : affine_algebraic_set k σ) : affine_algebraic_set k σ :=
{ carrier := V ∪ W, -- the underlying set is the union of the two sets defining V and W
  is_algebraic' :=
  -- We now need to prove that the union of V and W is cut out by some set of polynomials.
  begin
    -- Now here's the bad news. 

    -- Lean notation for kⁿ is `σ → k`.
    -- Lean notation for k[X₁, X₂, ..., Xₙ] is `mv_polynomial σ k`.
    -- Lean notation for the subsets of X is `set X`

    -- Let's state what we're trying to prove, using Lean's notation.
    show 
    ∃ (U : set (mv_polynomial σ k)),
      -- such that
      (V : set _) ∪ W = 𝕍 U,
    -- say S is the set that defines V
    cases V.is_algebraic with S hS,
    -- and T is the set that defines W
    -- (slightly fancier way)
    rcases W.is_algebraic with ⟨T, hT⟩,
    -- Now reduce to an unwieldy precise statement about zeros of polynomials
    rw [hS, hT],
    -- Our goal is now to come up with a set U such that
    -- the zeros of U are exactly the union of the zeros of S and of T.
    -- Here's how to do it.
    use {u | ∃ (s ∈ S) (t ∈ T), u = s * t},
    -- The goal in maths is now
    -- ⋂ (s ∈ S) zeros(s) ∪ ⋂ (t ∈ T) zeros(t) = ⋂ (u ∈ ST) zeros(u).
    -- Lean manages to make quite a mess of its display of this. 
    
    -- To prove that the affine algebraic set cut out by this collection of polynomials
    -- is precisely the set V ∪ W, we check both inclusions.
    apply set.subset.antisymm,
    { -- Here's the easier of the two inclusions.
      -- say x ∈ V ∪ W,
      intros x hx, rw mem_𝕍_iff,
      -- it's either in V or W.
      cases hx with hxV hxW,
      { -- Say x ∈ V
        -- We know that x vanishes at every element of S.
        rw mem_𝕍_iff at hxV,
        -- We want to prove x vanishes at every polynomial of the form s * t
        -- with s ∈ S and t ∈ T.
        -- so let's take an element u of the form s * t
        rintro u,
        -- Let's now notice that the goal has got completely out of hand, and
        -- simplify it back to ∀ s ∈ S and ∀ t ∈ T, (s * t)(x) = 0.
        suffices : ∀ s ∈ S, ∀ t ∈ T, u = s * t → u.eval x = 0,
        {rintros ⟨s, hsS, t, htT, rfl⟩, exact this s hsS t htT rfl},
        rintro s hs t ht rfl,
        -- we need to show st(x)=0.
        -- Because x ∈ V, we have s(x)=0. 
        have hx := (hxV s) hs,
        change s.eval x = 0 at hx,
        -- It suffices to show s(x)*t(x)=0
        rw eval_mul,
        -- but s(x) = 0,
        rw hx,
        -- and now it's obvious
        apply zero_mul,
      },
      { -- This is the case x ∈ W and it's essentially completely the same as the x ∈ V argument so I won't
        -- comment it. Some sort of argument with the `wlog` tactic might be able to do this.
        rw mem_𝕍_iff at hxW,
        rintro u,
          suffices : ∀ s ∈ S, ∀ t ∈ T, u = s * t → u.eval x = 0,
          { rintros ⟨s, hsS, t, htT, rfl⟩, exact this s hsS t htT rfl},
        rintro s hs t ht rfl,
        have hx := hxW t,
        replace hx : eval x t = 0 := hx ht,
        rw eval_mul,
        rw hx, simp,
      }
    },
    { -- This is the harder way; we need to check that if x vanishes on every element of S*T, 
      -- then x ∈ V or x ∈ W.
      intros x hx, rw mem_𝕍_iff at hx,
      have hx' : ∀ u s : mv_polynomial σ k, s ∈ S → ∀ t ∈ T, u = s * t → u.eval x = 0,
        simpa using hx,
      classical, -- We now proudly assume the law of the excluded middle.
      -- If x ∈ V then the result is easy...
      by_cases hx2 : x ∈ (V : set _),
        left, rwa ←hS,
      -- ...so we can assume assume x ∉ V,
      -- and hence that there's s ∈ S such that s(x) ≠ 0
      rw [hS, mem_𝕍_iff, not_forall] at hx2,
      cases hx2 with s hs,
      have hs2 : s ∈ S ∧ ¬eval x s = 0,
        simpa using hs,
      cases hs2 with hsS hns,
      -- we now show x ∈ W
      right,
      rw mem_𝕍_iff,
      -- Say t ∈ T
      intro t,
      -- We want to prove that t(x) = 0.
      suffices : t ∈ T → eval x t = 0,
        simpa,
      intro ht,
      -- Now by assumption, x vanishes on s * t. 
      replace hx' := hx' (s * t) s hsS t ht rfl,
      -- so s(x) * t(x) = 0
      rw eval_mul at hx',
      -- so either s(x) or t(x) = 0, but we chose s such that s(x) ≠ 0.
      cases mul_eq_zero.1 hx' with hxs hxt,
        -- So the case s(x) = 0 is a contradiction
        contradiction,
      -- and t(x) = 0 is what we wanted to prove
      assumption
    }
  end
}
end affine_algebraic_set
