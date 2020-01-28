/- 

Noetherian topological spaces

-/

import topology.basic

namespace topology

open set

/-- A topological space X is irreducible if it is non-empty, and for every cover by two closed sets C₁ and C₂, 
one of the Cᵢ has to be X. -/
def irreducible (X : Type*) [topological_space X] : Prop :=
nonempty X ∧ ∀ C₁ C₂ : set X, is_closed C₁ → is_closed C₂ → C₁ ∪ C₂ = univ → C₁ = univ ∨ C₂ = univ

lemma irred_iff_nonempty_open_dense {X : Type*} [topological_space X] :
irreducible X ↔ nonempty X ∧ ∀ U₁ U₂ : set X, is_open U₁ → is_open U₂ → U₁ ≠ ∅ → U₂ ≠ ∅ → U₁ ∩ U₂ ≠ ∅ :=
begin
  split,
  { rintro ⟨hXne, hXC⟩,
    split, assumption,
    intros U₁ U₂ O₁ O₂ h₁ h₂,
    replace hXC := hXC (-U₁) (-U₂) (is_closed_compl_iff.2 O₁) (is_closed_compl_iff.2 O₂),
    finish [set.ext_iff]
  },
  { rintro ⟨hXne, hXU⟩,
    split, assumption,
    intros C₁ C₂ c₁ c₂ hc,
    replace hXU := hXU (-C₁) (-C₂) (is_open_compl_iff.2 c₁) (is_open_compl_iff.2 c₂),
    finish [set.ext_iff]
  }
end


-- in the below, I bet "affine algebraic set" can be replaced by "Noetherian topological space".

/-
Corollary 5.3. Let S be a irreducible topological space and U ⊆ S a non-empty
open subset. Then U is irreducible (in the subspace topology).
-/

/-
Definition. Let S be a topological space. An irreducible component of S is
a maximal irreducible subset of S.

Proposition 5.4. Let V be an affine algebraic set. Then:
(1) The union of the irreducible components of V is all of V .
(2) V has only finitely many irreducible components.

Lemma 5.5. Every affine algebraic set can be written as a union of finitely many
irreducible closed subsets.

Proposition 5.6. Let V be an affine algebraic set. Write V = V 1 ∪ · · · ∪ V r , where
the V i are irreducible closed subsets and V i 6⊆ V j for i 6 = j.
Then V 1 , . . . , V r are precisely the irreducible components of V .


-/

end topology
