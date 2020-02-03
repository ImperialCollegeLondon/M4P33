/-
Algebraic geometry M4P33, Jan-Mar 2020, formalised in Lean.

Copyright (c) 2020 Kevin Buzzard
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Alexander Uhlmann, and whoever else in the class
wants to join in.

Thoughts about how much of the 𝕍 and 𝕀 theory
goes through abstractly.

Note: I think that this file is now pretty much done.
-/

-- This is set theory. But we want to do some type theory as well.
-- Types are a convenient way of gathering mathematical objects
-- into well-defined collections, such as rings.
import data.type.basic

-- We want to prove that the images of 𝕍 and 𝕀 are in natural
-- bijection with each other so we need the general theory
-- of bijections
import data.equiv.basic

-- the lattice structure on subsets (infinite unions etc)
import data.set.lattice


universes u v -- set theorists can set these both to be 0.
              -- (R : Type 0) means "let R be a set".

-- Let R be a set.
-- For example R could be the ring `k[X₁,…,Xₙ]`
variables (R : Type u)
-- When we're talking about 𝕍 and 𝕀, we will not mention R as part
-- of the notation even though it is playing a role
{R}

-- Let 𝔸ⁿ be another set.
variables (A : Type v)
-- Similarly we will not explicitly mention A most of the time
{A}

-- Let `P` be a way of getting a true/false statement from a pair of
-- elements f ∈ R and x ∈ 𝔸ⁿ. For example P(f,x) can be
-- the statement that `f(x) = 0`. You can think of `P` as being a subset
-- of R × 𝔸ⁿ if you like.
variable (P : R → A → Prop)
include P

-- Let 𝕍, a function from subsets of R to subsets of
-- 𝔸ⁿ, and 𝕀, a function from subsets of 𝔸ⁿ
-- to subsets of R, be defined in the usual way.
-- One can think of 𝕍(S) as being the largest U such that S × U ⊆ P,
-- and 𝕀(U) as being the largest S such that S × U ⊆ P.

-- The main theorem we will prove today is

-- *Theorem* For all S ⊆ R, 𝕍(𝕀(𝕍(S)))=𝕍(S),
-- assuming some irrelevant extra hypotheses, such as the assumption
-- that k is algebraically closed, or S is an ideal.

def 𝕍_ (S : set R) : set A :=
{x : A | ∀ f ∈ S, P f x}
notation `𝕍`:max := 𝕍_ (by exact P)

-- Type of 𝕍_ is Π {R : Type*} {A : Type*}, (R → A → Prop) → set R → set A
-- i.e. (R → A → Prop) → (R → Prop) → (A → Prop)

def 𝕀_ (X : set A) : set R :=
{f : R | ∀ x ∈ X, P f x}
notation `𝕀`:max := 𝕀_ (by exact P)

-- restate definitions
lemma mem_𝕍_iff (S : set R) (x : A) : x ∈ 𝕍 S ↔ ∀ f ∈ S, P f x := iff.rfl
lemma mem_𝕀_iff (V : set A) (f : R) : f ∈ 𝕀 V ↔ ∀ x ∈ V, P f x := iff.rfl

-- we're going to be doing set theory
open set

/-- 𝕍(∅) is everything. -/
lemma 𝕍_empty : 𝕍 ∅ = univ :=
begin
  -- It suffices to show that every x of type A is in 𝕍 ∅
  rw eq_univ_iff_forall,
  -- so let x be in A
  intro x,
  -- we need to show that every f in the empty set satisfies (f,x) ∈ P
  rw mem_𝕍_iff,
  -- so say f is in the empty set
  intros f hf,
  -- but there are no elements in the empty set so we must be done
  cases hf,
end

/-- 𝕀(∅) is everything -/
lemma 𝕀_empty : 𝕀 ∅ = univ :=
-- computer science proof
eq_univ_iff_forall.2 $ λ x f, by rintro ⟨⟩

-- 𝕍 is inclusion-reversing
lemma 𝕍_antimono (S T : set R) (h : S ⊆ T) : 𝕍 T ⊆ 𝕍 S :=
begin
  -- say x ∈ 𝕍(T)
  intros x hx,
  -- and s in S,
  intros s hs,
  -- We want to show P(s,x) is true, or (s,x) ∈ P or s(x) = 0 or however
  -- you think about it.
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

-- Thanks to Alexander Uhlmann for spotting definition 3.1 here:
-- https://ncatlab.org/nlab/show/Galois+connection#GaloisTheory
lemma is_galois_connection {Y : set A} {J : set R} :
Y ⊆ 𝕍 J ↔ 𝕀 Y ⊇ J :=
begin
  split,
  { intros hY f hf,
    rw mem_𝕀_iff,
    intros x hx,
    exact hY hx f hf,
  },
  { intros hJ x hx f hf,
    exact hJ hf x hx,
  }
end

lemma 𝕍_union (S T : set R) : 𝕍 (S ∪ T) = 𝕍 S ∩ 𝕍 T :=
begin
  -- we prove both inclusions
  apply set.subset.antisymm,
  { -- say x ∈ 𝕍(S ∪ T)
    intros x hx,
    -- we need to prove x ∈ 𝕍 S and x ∈ 𝕍 T
    split,
    -- both of these follow easily from 𝕍_antimono
    -- exact 𝕍_antimono _ _ _ _ hx, -- TODO(kmb)
        -- why is the wrong underscore marked in red??
      exact 𝕍_antimono _ _ _ (subset_union_left _ _) hx,
      exact 𝕍_antimono _ _ _ (subset_union_right _ _) hx,
  },
  { -- say x ∈ 𝕍(S) ∩ 𝕍(T)
    rintros x ⟨hxS, hxT⟩,
    -- we need to prove that for all f ∈ S ∪ T, f(x) = 0
    intros f hf,
    -- well f is either in S or T (or both)
    cases hf,
    { -- and if f ∈ S then we're done because x ∈ 𝕍(S)
      exact hxS _ hf
    },
    { -- whereas if f ∈ T then we're done because x ∈ 𝕍(T)
      exact hxT _ hf
    }
  }
end 

-- We prove this one in a slightly different way.
lemma 𝕀_union (W X : set A) : 𝕀 (W ∪ X) = 𝕀 W ∩ 𝕀 X :=
begin
  -- By extensionality, two sets are equal iff they have the same elements
  ext x,
  -- To be in the intersection of two sets just means being in both of them
  show _ ↔ x ∈ 𝕀 W ∧ x ∈ 𝕀 X,
  -- By the definition of 𝕀,...
  rw [mem_𝕀_iff, mem_𝕀_iff, mem_𝕀_iff],
  --- we have to prove that 
  -- W ∪ X ⊆ {f : f(x) = 0} iff W ⊆ {f : f(x) = 0} and X ⊆ {f : f(x) = 0}
  show W ∪ X ⊆ _ ↔ W ⊆ _ ∧ X ⊆ _, -- the underscore just means "guess the set"
  -- We prove the iff by proving both directions separately
  split,
  { -- Here we prove W ∪ X ⊆ Z → W ⊆ Z ∧ X ⊆ Z
    intro hWX,
    split,
      refine set.subset.trans _ hWX, apply subset_union_left,
    refine set.subset.trans _ hWX, apply subset_union_right,
  },
  { -- and here we prove W ⊆ Z ∧ X ⊆ Z → W ∪ X ⊆ Z
    rintros ⟨hW, hX⟩, apply union_subset; assumption
  }
end

lemma 𝕍_Union (ι : Type*) (S : ι → set R) : 𝕍 (⋃ i, S i) = ⋂ i, 𝕍 (S i) :=
begin
  -- two sets are equal iff they have the same elements
  ext x,
  -- To be in the intersection of a bunch of sets just means
  -- being in all of them
  rw mem_Inter,
  -- By the definition of 𝕍,
  rw [mem_𝕍_iff],
  show (∀ (f : R), (f ∈ ⋃ (i : ι), S i) → P f x) ↔ ∀ (i : ι), ∀ f ∈ S i, P f x,
  -- Now prove both inclusions separately
  split,
    intros,
    apply a,
    rw mem_Union,
    use i,
    assumption,
  intros h f hf,
  rw mem_Union at hf,
  cases hf with i hi,
  apply h i,
  assumption,
end

-- an AI can find a proof of this too:
lemma 𝕀_Union (ι : Type*) (J : ι → set A) : 𝕀 (⋃ i, J i) = ⋂ i, 𝕀 (J i) :=
begin 
  ext,
  simp [𝕀_],
  tauto,
end


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

-- During the lecture today (17/01/20), it was pointed out that 𝕍(S) was the
-- largest U such that S × U was a subset of P, and 𝕀(U) was the largest S
-- such that S × U was a subset of P. This geometric way of thinking
-- about things makes the next lemma trivial. Can you understand the Lean proof?

/-- U ⊆ 𝕍(𝕀(U)) -/
lemma sub_𝕍𝕀 (U : set A) : U ⊆ 𝕍 (𝕀 U) :=
begin
  intros x hx,
  rw mem_𝕍_iff,
  intros f hf,
  rw mem_𝕀_iff at hf,
  apply hf,
  exact hx,
end

-- Because the proofs of sub_𝕍𝕀 and sub_𝕀𝕍 are basically
-- the same, it might come as no surprise to see that you
-- can prove one of them using the other one! The trick is
-- to make sure you allow quantification over all R and A
-- so you can switch them around.

/-- S ⊆ 𝕀(𝕍(S)) -/
lemma sub_𝕀𝕍 (S : set R) : S ⊆ 𝕀 (𝕍 S) :=
sub_𝕍𝕀 _ _

-- the big theorem
lemma 𝕍𝕀𝕍_eq_𝕍 (S : set R) : 𝕍 (𝕀 (𝕍 S)) = 𝕍 S :=
begin
  apply set.subset.antisymm,
  { apply 𝕍_antimono,
    apply sub_𝕀𝕍
  },
  { apply sub_𝕍𝕀,
  }
end

-- the same theorem again (permute R and A)
lemma 𝕀𝕍𝕀_eq_𝕀 (V : set A) : (𝕀 (𝕍 (𝕀 V))) = 𝕀 V :=
𝕍𝕀𝕍_eq_𝕍 _ V -- same proof but with a different P

open set

-- this final proof is written in a very computer-science way
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

-- The Nullstellensatz says that the image of 𝕀 is precisely the
-- radical ideals. One inclusion is clear (which?)