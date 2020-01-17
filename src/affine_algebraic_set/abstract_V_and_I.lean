/-

Thoughts about how much of the 𝕍 and 𝕀 theory
goes through abstractly

-/

import data.set.basic

variable {R : Type*} -- R = k[X₁,…,Xₙ]

variable {W : Type*} -- W = kⁿ

variable (P : R → W → Prop) -- P(f,x) is the statement f(x)=0

-- so P defines a subset of R × W : (f,x) is in the subset iff f(x) = 0

-- This is already enough to define 𝕍 and 𝕀

def 𝕍 (S : set R) : set W :=
{x : W | ∀ f ∈ S, P f x}

def 𝕀 (X : set W) : set R :=
{f : R | ∀ x ∈ X, P f x}

-- Note that 𝕍 and 𝕀 depend on P and so we'll have to mention P explicitly

-- restate definitions
lemma mem_𝕍_def (S : set R) (x : W) : x ∈ 𝕍 P S ↔ ∀ f ∈ S, P f x := iff.rfl
lemma mem_𝕀_def (V : set W) (f : R) : f ∈ 𝕀 P V ↔ ∀ x ∈ V, P f x := iff.rfl

-- 𝕍 is inclusion-reversing
lemma 𝕍_antimono (S T : set R) (h : S ⊆ T) : 𝕍 P T ⊆ 𝕍 P S :=
begin
  -- say x ∈ 𝕍(T)
  intros x hx,
  -- and s in S,
  intros s hs,
  -- We want to show P(s,x).
  -- Because x ∈ 𝕍(T), we know P(t,x) is true for all t ∈ T,
  -- so it suffices to prove s ∈ T
  apply hx,
  -- But S ⊆ T
  apply h,
  -- and s ∈ S so we're done
  exact hs
end

-- Here is how a computer scientist would write this proof:
lemma 𝕍_antimono' (S T : set R) (h : S ⊆ T) : 𝕍 P T ⊆ 𝕍 P S :=
λ x hx s hs, hx _ (h hs)

-- The advantage of writing it this way is that it also proves the converse!
lemma 𝕀_antimono (U V : set W) (h : U ⊆ V) : 𝕀 P V ⊆ 𝕀 P U :=
λ x hx s hs, hx _ (h hs)

-- Exercise: prove 𝕀_antimono the way a mathematician would, using only
-- intros, apply and exact. Need help? Try the natural number game.

lemma 𝕍𝕀_mono (U V : set W) (h : U ⊆ V) : 𝕍 P (𝕀 P U) ⊆ 𝕍 P (𝕀 P V) :=
begin
  -- 𝕍 is anti-monotonic
  apply 𝕍_antimono,
  -- and 𝕀 is too
  apply 𝕀_antimono,
  -- so we just have to prove U ⊆ V, which is an assumption
  exact h
end

-- computer science proof of the other direction
lemma 𝕀𝕍_mono (S T : set R) (h : S ⊆ T) : 𝕀 P (𝕍 P S) ⊆ 𝕀 P (𝕍 P T) :=
𝕀_antimono P _ _ (𝕍_antimono P _ _ h)

/-- U ⊆ 𝕍(𝕀(U)) -/
lemma sub_𝕍𝕀 (U : set W) : U ⊆ 𝕍 P (𝕀 P U) :=
begin
  intros x hx,
  rw mem_𝕍_def,
  intros f hf,
  rw mem_𝕀_def at hf,
  apply hf,
  exact hx,
end

/-- S ⊆ 𝕀(𝕍(S)) -/
lemma sub_𝕀𝕍 (S : set R) : S ⊆ 𝕀 P (𝕍 P S) :=
begin
  intros f hf,
  rw mem_𝕀_def,
  intros x hx,
  rw mem_𝕍_def at hx,
  apply hx,
  exact hf,
end

lemma 𝕍𝕀𝕍_eq_𝕍 (S : set R) : 𝕍 P (𝕀 P (𝕍 P S)) = 𝕍 P S :=
begin
  apply set.subset.antisymm,
  { intros x hx,
    rw mem_𝕍_def at hx ⊢,
    intros f hf,
    apply hx,
    apply sub_𝕀𝕍,
    assumption,
  },
  { apply sub_𝕍𝕀,
  }
end

lemma 𝕀𝕍𝕀_eq_𝕀 (V : set W) : (𝕀 P (𝕍 P (𝕀 P V))) = 𝕀 P V :=
begin
  apply set.subset.antisymm,
  { intros x hx,
    rw mem_𝕀_def at hx ⊢,
    intros f hf,
    apply hx,
    apply sub_𝕀𝕍, -- ??
    assumption,
  },
  { apply sub_𝕍𝕀, -- ??
  }
end

