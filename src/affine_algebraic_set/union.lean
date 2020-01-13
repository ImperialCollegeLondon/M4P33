/-
Algebraic geometry lecture 1:

The union of two algebraic sets is an algebraic set.

Kevin Buzzard
-/

import affine_algebraic_set.basic -- the basic theory of affine algebraic sets.

/-
# The union of two affine algebraic sets is affine.

Pseudo-Latex statement of theorem:

Let $k$ be a field and let $n$ be a natural number.

Theorem. If $V$ and $W$ are two affine algebraic subsets of $k^n$
then their union $V\cup W$ is also an affine algebraic subset of $k^n$.

Maths proof: if $V$ is cut out by the set $S ⊆ k[X_1,X_2,…,X_n]$
and $W$ is cut out by $T$, then $V ∪ W$ is cut out by the set $ST := {st | s ∈ S and t ∈ T}.$
To prove that $ST$ cuts out $V ∪ W$, we prove both inclusion separately.

If $x ∈ V ∪ W$ then either every element of $S$ vanishes at $x$ or every element of $T$ vanishes on $x$,
and either way every element of $ST$ vanishes at $x$.

Conversely, if $x$ vanishes at every element of $ST$, then we want to prove that $x ∈ V ∪ W$. Suppose
for a contradiction that $x$ is in neither $V$ nor $W$. By definition, this means that there must
be some polynomials $s ∈ S$ and $t ∈ T$ such that $x$ it is not a zero of either $s$ or $t$. Hence
$x$ is not a zero of $st ∈ ST$, a contradiction.

## Implementation notes

I defined an affine algebraic set to be the zeros of an arbitrary
set of functions, as opposed to just a finite set. We will see later
on that these definitions are equivalent.

If V is an affine algebraic set, then V is a pair. The first
element of the pair is a subset V.carrier ⊆ k^n. The second
element of the pair is the proof that there exists a subset S of k[X_1,X_2,...,X_n]
such that V is cut out by S, by which I mean that V is the set of x ∈ k^n which vanish
at each element of S.

## References

Martin Orr's lecture notes!

## Tags

algebraic geometry, algebraic variety
-/

-- let k be a field
variables {k : Type*} [discrete_field k]

-- and let n be a natural number
variable {n : ℕ}

open mv_polynomial

namespace affine_algebraic_set

-- Unfortunately the notation here looks intimidating, but one can get used to it.

-- In Lean, the multivariable polynomial ring k[X₁, X₂, ..., Xₙ] is
-- denoted `mv_polynomial (fin n) k`. Here `fin n` is the type {0,1,2,...,(n-1)}.

-- Equally confusingly, 
-- The set kⁿ is denoted `fin n → k` (which means all maps from {0,1,2,...,(n-1)} to k).

-- Now some basic facts about affine algebraic sets.

/-- The union of two algebraic subsets of kⁿ is an algebraic subset-/
def union (V W : affine_algebraic_set k n) : affine_algebraic_set k n :=
{ carrier := V.carrier ∪ W.carrier, -- the underlying set is the union of the two sets defining V and W
  is_algebraic :=
  -- We now need to prove that this union is cut out by some set of polynomials.
  begin
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
    -- To prove that V ∪ W is defined by this set, we prove both inclusions
    apply set.subset.antisymm,
    { -- say x ∈ V ∪ W,
      intros x hx,
      -- it's either in V or W.
      cases hx with hxV hxW,
      { -- Say x ∈ V
        -- We know that x vanishes at every element of S.
        rw set.mem_Inter at hxV,
        -- We want to prove x vanishes at every polynomial of the form s * t
        -- with s ∈ S and t ∈ T.
        rw set.mem_Inter,
        -- so let's take an element u of the form s * t
        rintro u,
        -- Let's get the goal into the form we want
        suffices : ∀ s ∈ S, ∀ t ∈ T, u = s * t → u.eval x = 0,
        {rw [set.mem_Inter], rintros ⟨s, hsS, t, htT, rfl⟩, exact this s hsS t htT rfl},
        rintro s hs t ht rfl,
        -- we need to show st(x)=0. Let's use the fact that x ∈ V... 
        have hx := hxV s,
        rw set.mem_Inter at hx,
        -- ...and hence s(x) = 0
        replace hx : eval x s = 0 := hx hs,
        rw eval_mul,
        --But s ∈ S so x vanishes at s
        -- and hence st(x)=s(x)t(x)=0*t(x)=0.
        rw hx, simp,
      },
      { -- This is the case x ∈ W and it's essentially completely the same as the x ∈ V argument.
        rw set.mem_Inter at hxW ⊢,
        rintro u,
          suffices : ∀ s ∈ S, ∀ t ∈ T, u = s * t → u.eval x = 0,
          {rw [set.mem_Inter], rintros ⟨s, hsS, t, htT, rfl⟩, exact this s hsS t htT rfl},
        rintro s hs t ht rfl,
        have hx := hxW t,
        rw set.mem_Inter at hx,
        replace hx : eval x t = 0 := hx ht,
        rw eval_mul,
        rw hx, simp,
      }
    },
    { -- This is the harder way; we need to check that if x vanishes on every element of S*T, 
      -- then x ∈ V or x ∈ W.
      intros x hx,
      have hx' : ∀ u s : mv_polynomial (fin n) k, s ∈ S → ∀ t ∈ T, u = s * t → u.eval x = 0,
        simpa using hx,
      classical, -- in this next bit we assume the law of the excluded middle
      -- If x ∈ V then it's easy...
      by_cases hx2 : x ∈ V.carrier,
        left, rwa ←hS,
      -- so let's assume x ∉ V.
      -- We deduce that there's s ∈ S such that s(x) ≠ 0
      rw [hS, set.mem_Inter, not_forall] at hx2,
      cases hx2 with s hs,
      have hs2 : s ∈ S ∧ ¬eval x s = 0,
        simpa using hs,
      cases hs2 with hsS hns,
      -- we now show x ∈ W
      right,
      rw set.mem_Inter,
      -- so say t ∈ T
      intro t,
      suffices : t ∈ T → eval x t = 0,
        simpa,
      intro ht,
      -- We want to prove t(x)=0. Now by assumption, x vanishes on s*t. 
      replace hx' := hx' (s * t) s hsS t ht rfl,
      -- so s(x)*t(x)=0
      rw eval_mul at hx',
      -- so either s(x) or t(x) = 0, but we chose x such that s(x) ≠ 0.
      cases mul_eq_zero.1 hx' with hxs hxt,
        -- s(x)=0 is a contradiction
        contradiction,
      -- t(x) = 0 is what we wanted to prove
      assumption
    }
  end
}
end affine_algebraic_set