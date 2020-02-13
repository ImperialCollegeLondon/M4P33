/- 

Noetherian topological spaces

-/

-- this import gives us irreducible topological spaces
import topology.subset_properties

open set

open_locale classical

lemma irred_iff_not_union_closed {X : Type*} [topological_space X] (Y : set X) :
is_irreducible Y ↔ Y.nonempty ∧ ∀ C₁ C₂ : set X,
  is_closed C₁ → is_closed C₂ → Y ⊆ C₁ ∪ C₂ → Y ⊆ C₁ ∨ Y ⊆ C₂ :=
begin
  split,
  { rintro ⟨h0, h⟩,
    split, exact h0,
    rwa ←is_preirreducible_iff_closed_union_closed,
  },
  { rintro ⟨h0, h⟩,
    split, assumption,
    rwa is_preirreducible_iff_closed_union_closed,
  }
end


/-- A non-empty Y is irreducible iff every non-empty open subset of Y is dense -/
lemma irred_iff_nonempty_open_dense {X : Type*} [topological_space X] (Y : set X):
is_irreducible Y ↔ Y.nonempty ∧
  ∀ U₁ U₂ : set X, is_open U₁ → is_open U₂ →
  (Y ∩ U₁).nonempty → (Y ∩ U₂).nonempty → (Y ∩ (U₁ ∩ U₂)).nonempty := iff.rfl


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

A topological space is Noetherian if it satisfies the descending chain
condition for open subsets

-/


/-

Hartshorne 1.5: in a Noetherian top space X, every nonempty closed subset Y
can be expressed as a finite union of irred closed subsets Y_i. If we
require that Y_i ¬⊆ Y_j for i ≠ j then the Y_i are uniquely determined.
They're called the irred cpts of Y.

-/

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

