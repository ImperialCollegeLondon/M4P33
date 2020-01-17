/-

Thoughts about how much of the 𝕍 and 𝕀 theory
goes through abstractly.

-/

-- This is set theory. But we want to do some type theory as well.
-- Types are a convenient way of gathering mathematical objects
-- into well-defined collections, such as rings.
import data.type.basic

-- We want to prove that the images of 𝕍 and 𝕀 are in natural
-- bijection with each other so we need the general theory
-- of bijections
import data.equiv.basic

universes u v -- set theorists can set these both to be 0.
              -- {R : Type 0} means "let R be a set".

-- Let $R$ be a set.
-- For example $R$ could be the ring `k[X₁,…,Xₙ]`
variables (R : Type u) {R}

-- Let $\mathbb{A}^n$ be another set.
variables (A : Type v) {A}

-- Let $P$ be a way of getting a true/false statement from a pair of
-- elements $f ∈ R$ and $x ∈ \mathbb{A}^n$. For example $P(f,x)$ can be
-- the statement that $f(x) = 0$. You can think of $P$ as being a subset
-- of $R\times \mathbb{A}^n$ if you like.
variable (P : R → A → Prop)
include P

-- Let $\mathbb{V}$, a function from subsets of $R$ to subsets of $\mathbb{A}^n$
-- and $\mathbb{I}$, a function from subsets of $\mathbb{A}^n$ to subsets of $R$
-- be defined by following your nose using $P$.

-- The main theorem we will prove today is

-- $\mathbf{theorem} For all $S\subseteq R$, $\V(\I(\V(S)))=\V(S)$, possibly
-- assuming some extra hypotheses, such as the fact that $k$ is algebraically
-- closed, or $S$ is an ideal.

def 𝕍_ (S : set R) : set A :=
{x : A | ∀ f ∈ S, P f x}
notation `𝕍`:max := 𝕍_ (by exact P)

-- Type of 𝕍_ is Π {R : Type*} {A : Type*}, (R → A → Prop) → set R → set A

def 𝕀_ (X : set A) : set R :=
{f : R | ∀ x ∈ X, P f x}
notation `𝕀`:max := 𝕀_ (by exact P)

-- restate definitions
lemma mem_𝕍_def (S : set R) (x : A) : x ∈ 𝕍 S ↔ ∀ f ∈ S, P f x := iff.rfl
lemma mem_𝕀_def (V : set A) (f : R) : f ∈ 𝕀 V ↔ ∀ x ∈ V, P f x := iff.rfl

-- 𝕍 is inclusion-reversing
lemma 𝕍_antimono (S T : set R) (h : S ⊆ T) : 𝕍 T ⊆ 𝕍 S :=
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
lemma 𝕍_antimono' (S T : set R) (h : S ⊆ T) : 𝕍 T ⊆ 𝕍 S :=
λ x hx s hs, hx _ (h hs)

-- The advantage of writing it this way is that it also proves the converse!
lemma 𝕀_antimono (U V : set A) (h : U ⊆ V) : 𝕀 V ⊆ 𝕀 U :=
λ x hx s hs, hx _ (h hs)

-- Exercise: prove 𝕀_antimono the way a mathematician would, using only
-- intros, apply and exact. Need help? Try the natural number game.

lemma 𝕍𝕀_mono (U V : set A) (h : U ⊆ V) : 𝕍 (𝕀 U) ⊆ 𝕍 (𝕀 V) :=
begin
  -- 𝕍 is anti-monotonic
  apply 𝕍_antimono,
  -- and 𝕀 is too
  apply 𝕀_antimono,
  -- so we just have to prove U ⊆ V, which is an assumption
  exact h
end

-- computer science proof of the other direction
lemma 𝕀𝕍_mono (S T : set R) (h : S ⊆ T) : 𝕀 (𝕍 S) ⊆ 𝕀 (𝕍 T) :=
𝕀_antimono P _ _ (𝕍_antimono P _ _ h)

-- During the lecture today, it was pointed out that 𝕍(S) was the largest
-- U such that S × U was a subset of P, and 𝕀(U) was the largest S
-- such that S × U was a subset of P. This geometric way of thinking
-- about things makes the next lemma trivial. Can you understand the Lean proof?

/-- U ⊆ 𝕍(𝕀(U)) -/
lemma sub_𝕍𝕀 (U : set A) : U ⊆ 𝕍 (𝕀 U) :=
begin
  intros x hx,
  rw mem_𝕍_def,
  intros f hf,
  rw mem_𝕀_def at hf,
  apply hf,
  exact hx,
end

/-- S ⊆ 𝕀(𝕍(S)) -/
lemma sub_𝕀𝕍 (S : set R) : S ⊆ 𝕀 (𝕍 S) :=
begin
  intros f hf,
  rw mem_𝕀_def,
  intros x hx,
  rw mem_𝕍_def at hx,
  apply hx,
  assumption,
end

-- Because the proofs of sub_𝕍𝕀 and sub_𝕀𝕍 are basically
-- the same, it might come as no surprise to see that you
-- can prove one of them using the other one! The trick is
-- to make sure you allow quantification over all R and A
-- so you can switch them around.
lemma sub_𝕀𝕍' (S : set R) : S ⊆ 𝕀 (𝕍 S) := sub_𝕍𝕀 _ _

lemma 𝕍𝕀𝕍_eq_𝕍 (S : set R) : 𝕍 (𝕀 (𝕍 S)) = 𝕍 S :=
begin
  apply set.subset.antisymm,
  { apply 𝕍_antimono,
    apply sub_𝕀𝕍
  },
  { apply sub_𝕍𝕀, -- amazingly, sub_𝕀𝕍 also works, because Lean 
                  -- realises that you want to swap R and A 
  }
end

lemma 𝕀𝕍𝕀_eq_𝕀 (V : set A) : (𝕀 (𝕍 (𝕀 V))) = 𝕀 V :=
𝕍𝕀𝕍_eq_𝕍 _ V -- same proof but with a different P

open set

/-- The images of 𝕍 and of 𝕀 are naturally in bijection -/
lemma not_the_nullstellensatz : {V // ∃ J, 𝕍 J = V} ≃ {I // ∃ V, 𝕀 V = I} :=
{ to_fun := λ V, ⟨𝕀 (V.1), V, rfl⟩,
  inv_fun := λ I, ⟨𝕍 I.1, I, rfl⟩,
  left_inv := begin
    rintro ⟨V, J, hJ⟩,
    rw subtype.ext,
    change 𝕍 (𝕀 V) = V,
    rw ←hJ,
    refine 𝕍𝕀𝕍_eq_𝕍 _ _,
  end,
  right_inv := begin
    rintro ⟨J, V, hV⟩,
    rw subtype.ext,
    change 𝕀 (𝕍 J) = J,
    rw ←hV,
    refine 𝕀𝕍𝕀_eq_𝕀 _ _,
  end
}
