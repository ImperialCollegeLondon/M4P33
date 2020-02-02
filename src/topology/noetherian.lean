/- 

Noetherian topological spaces

-/

import topology.basic data.set.basic

namespace topology

open set

open_locale classical

/-- A subspace Y of a topological space X is *irreducible* if it is non-empty,
and for every cover by two closed sets C₁ and C₂, one of the Cᵢ has to be Y. -/
def is_irreducible {X : Type*} [topological_space X] (Y : set X) : Prop :=
(∃ x, x ∈ Y) ∧ ∀ C₁ C₂ : set X,
  is_closed C₁ → is_closed C₂ → Y ⊆ C₁ ∪ C₂ → Y ⊆ C₁ ∨ Y ⊆ C₂

/-- A non-empty Y is irreducible iff every non-empty open subset of Y is dense -/
lemma irred_iff_nonempty_open_dense {X : Type*} [topological_space X] (Y : set X):
is_irreducible Y ↔ (∃ x, x ∈ Y) ∧
  ∀ U₁ U₂ : set X, is_open U₁ → is_open U₂ →
  U₁ ∩ Y ≠ ∅ → U₂ ∩ Y ≠ ∅ → U₁ ∩ U₂ ∩ Y ≠ ∅ :=
have function.surjective (has_neg.neg : set X → set X) :=
  λ x, ⟨-x, compl_compl x⟩,
begin
  dsimp only [is_irreducible],
  rw [← forall_iff_forall_surj this, forall_swap,
      ← forall_iff_forall_surj this],
  finish [set.ext_iff, set.subset_def]
end

-- in the below, I bet "affine algebraic set" can be replaced by "Noetherian topological space".

/-
Corollary 5.3. Let S be a irreducible topological space and U ⊆ S a non-empty
open subset. Then U is irreducible (in the subspace topology).
-/

lemma open_irred {X : Type*} [topological_space X]
  (S : set X) (hiS : is_irreducible S) (V : set X) (hV : is_open V) :
  (∃ x, x ∈ V ∩ S) → is_irreducible (V ∩ S) :=
begin
  rintro ⟨x, hx⟩,
  rw irred_iff_nonempty_open_dense,
  split, use x, assumption,
  intros U₁ U₂ oU₁ oU₂ hne₁ hne₂,
  rw irred_iff_nonempty_open_dense at hiS,
  rcases hiS with ⟨h3, h4⟩,
  replace h4 := h4 (V ∩ U₁) (V ∩ U₂)
    (is_open_inter hV oU₁) (is_open_inter hV oU₂),
  convert h4 (by convert hne₁ using 1; ac_refl) (by convert hne₂ using 1; ac_refl) using 1,
  ext, split; finish,
end

/-
Definition. Let X be a topological space. An irreducible component of X is
a maximal irreducible subset of X.

-/

def irreducible_component {X : Type*} [topological_space X] (S : set X) : Prop :=
is_irreducible S ∧ ∀ T, S ⊆ T → is_irreducible T → S = T

/-

A topological space is Noetherian if it satisfies the descending chain
condition for open subsets

-/


/-

Hartshorne 1.5: in a Noetherian top space X, every nonempty closed subset Y
can be expressed as a finite union of irred closed subsets Y_i. If we
require that Y_i ¬⊆ Y_j for i ≠ j then the Y_i are uniquely determined.
They're called the irred cpts of Y.

-/

def 
/-
Proof: existence: the set of non-empty closed subsets which can't be written
as a finite union of irreds is empty because it can't have a minimal
member. 

Throwing away some Y_i we can assume i ≠ j → ¬ Y_i ⊆ Y_j. 

Now say we have 2 reps . Then Z_1 ⊆ ∪ Y_j so Z_1 = ∪ (Z_1 ∩ Y_j), but
Z_1 is irred so Z_1 ⊆ Y_j for some j. Similarly Y_j ⊆ Z_k so k=1
and now replacing Y by the closure of Y - Z_1 we're done by induction on
the number of Z_i


Proposition 5.4. Let V be an affine algebraic set. Then:
(1) The union of the irreducible components of V is all of V .
(2) V has only finitely many irreducible components.

Lemma 5.5. Every affine algebraic set can be written as a union of finitely many
irreducible closed subsets.

Proposition 5.6. Let V be an affine algebraic set. Write V = V 1 ∪ · · · ∪ V r , where
the V i are irreducible closed subsets and ¬ V i ⊆ V j for ¬ i = j.
Then V 1 , . . . , V r are precisely the irreducible components of V .


-/

end topology
