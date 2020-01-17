-- *TODO* remove me
import tactic.linarith
/-

Thoughts about how much of the 𝕍 and 𝕀 theory
goes through abstractly.

-/

-- This is set theory. But we want to do some type theory as well.
-- Types are a convenient way of gathering mathematical objects
-- into well-defined collections, such as rings.
import data.type.basic

universes u v -- set theorists can set these both to be 0. Type 0 = sets.

-- Let $R$ be a set.
-- For example $R$ could be the ring `k[X₁,…,Xₙ]`
variable {R : Type u}

-- Let $\mathbb{A}^n$ be another set.
variable {W : Type v}

-- Let $P$ be a way of getting a true/false statement from a pair of
-- elements $f ∈ R$ and $x ∈ \mathbb{A}^n$. For example $P(f,x)$ can be
-- the statement that $f(x) = 0$. You can think of $P$ as being a subset
-- of $R\times \mathbb{A}^n$ if you like.
variable (P : R → W → Prop)

-- Let $\mathbb{V}$, a function from subsets of $R$ to subsets of $\mathbb{A}^n$
-- and $\mathbb{I}$, a function from subsets of $\mathbb{A}^n$ to subsets of $R$
-- be defined by following your nose using $P$. 

-- $\mathbf{theorem} For all $S\subseteq R$, $\V(\I(\V(S)))=\V(S)$, possibly
-- assuming some extra hypotheses, such as the fact that $k$ is algebraically
-- closed, or $S$ is an ideal.

def 𝕍 (S : set R) : set W :=
{x : W | ∀ f ∈ S, P f x}

--def T𝕍 := Π {R : Type*} {W : Type*}, (R → W → Prop) → set R → set W

--#check @𝕍
--#check T𝕍 -- T𝕍 : Type (max (u_3+1) (u_4+1) u_3 u_4)

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
    apply sub_𝕀𝕍, -- ?? -- TODO -- what just happened? Should say sub_𝕍𝕀
    assumption,
  },
  { apply sub_𝕍𝕀, -- ?? -- ??
  }
end

