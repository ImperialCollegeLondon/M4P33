/- 

Noetherian topological spaces

-/

-- this import gives us irreducible topological spaces
import topology.subset_properties

-- this gives us the type of open sets in a top space
import topology.opens

open set

open_locale classical

@[simp]
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
  (V ∩ S).nonempty → is_irreducible (V ∩ S) :=
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

Alternatively, we have upwards induction on closed sets. 
-/

namespace topological_space

open_locale classical

variables {X : Type*} [topological_space X]

instance for_ken : partial_order (closeds X) := subtype.partial_order _

def is_noetherian (X : Type*) [topological_space X] : Prop :=
well_founded ((<) : closeds X → closeds X → Prop)

-- factorises means expressable as finite union of closed irreducibles. 
def factorises {X : Type*} [topological_space X] (C : closeds X) :=
∃ ι : finset (set X), sUnion (↑ι : set _) = C.1 ∧ 
(∀ Ci ∈ ι, is_irreducible Ci) ∧ (∀ Ci ∈ ι, is_closed Ci)

lemma inter_ssubet_of_not_subset {X : Type*} {A B : set X}
(A_not_sub_B : ¬ A ⊆ B) : A ∩ B ⊂ A := ⟨inter_subset_left _ _,
  not_subset.2 $ let ⟨a,a_in_A,a_not_in_B⟩ := not_subset.1 A_not_sub_B in  
  ⟨a,a_in_A, λ a_in_A_inter_B, a_not_in_B a_in_A_inter_B.2⟩
⟩

lemma eq_union_inter_of_subset_union {X : Type*} {A B C : set X}
(A_subset_B_union_C : A ⊆ B ∪ C) : A = (A ∩ B) ∪ (A ∩ C) := 
inter_distrib_left A B C ▸ eq_of_subset_of_subset 
(subset_inter (subset.refl _) (A_subset_B_union_C))
(inter_subset_left _ _)

lemma induction_step {X : Type*} [topological_space X] 
{Y : set X} (Y_closed : is_closed Y)
(Y_not_irreducible : ¬ is_irreducible Y) :
Y = ∅ ∨ 
∃ C1 C2 : set X, is_closed C1 ∧ is_closed C2 ∧ Y = C1 ∪ C2 ∧ C1 < Y ∧ C2 < Y 
:= begin
  cases (classical.em (Y.nonempty)) with Y_nonempty Y_not_nonempty, 
  -- Case of Y nonempty, 
  apply or.inr, 
  simp at Y_not_irreducible, -- Tell lean to expand on Y not irreducible. 
  have not_forall, from Y_not_irreducible Y_nonempty, 
  push_neg at not_forall, -- Makes the not forall statement usable. 
  rcases not_forall with ⟨X1, X2, X1_closed, X2_closed, 
  Y_subset_X1_union_X2, not_Y_subset_X1, not_Y_subset_X2⟩,
  use Y ∩ X1, use Y ∩ X2, -- These are the desired two closed sets. 
  split, exact (is_closed_inter Y_closed X1_closed), -- Y ∩ X1 closed
  split, exact (is_closed_inter Y_closed X2_closed), -- Y ∩ X2 closed
  split, exact eq_union_inter_of_subset_union Y_subset_X1_union_X2, -- Y = Y ∩ X1 ∪ Y ∩ X2
  split, exact (inter_ssubet_of_not_subset not_Y_subset_X1), -- Y ∩ X1 ⊂ Y
  exact (inter_ssubet_of_not_subset not_Y_subset_X2), -- Y ∩ X2 ⊂ Y
  -- Case of Y empty
  apply or.inl, 
  apply eq_empty_iff_forall_not_mem.2,
  apply forall_not_of_not_exists Y_not_nonempty,  
end
/-- In a Noetherian top space X, 
every closed subset C can be "factorised", 
that is expressable as a finite union of irreducible closed subsets C_i. 
Note that emptyset has a factorisation, the empty union,
analogous to 1 being empty product of primes. --/
theorem finite_union_irreducibles {X : Type*} [topological_space X] 
(X_noetherian : is_noetherian X) : 
∀ C : closeds X, factorises C :=
  -- We prove factorisation of closed sets by induction.
  @well_founded.fix _ (λ C : closeds X, factorises C) _ X_noetherian $ 
  -- Let Y be a closed set of X, and assume the induction hypothesis, 
  -- all closed sets strictly smaller than Y factorises. 
  λ Y : closeds X, λ induction_hypothesis, 
  -- We do cases on whether Y is irreducible. 
  or.elim (classical.em (is_irreducible Y.1))
  (-- Case of Y being irreducible. 
    λ Y_irreducible, 
    -- Since Y is irreducible, Y gives a factorisation of Y. 
    ⟨{Y.1},  -- The finset containing only 
      sUnion_singleton Y.1, -- Proof that union of sets in {Y} is Y.  
      -- Proof that everything in {Y} is irreducible. 
      λ (Y1 : set X) Y1_in_finset, -- Take a set in {Y}
        have Y1_eq_Y : Y1 = Y.1, from eq_of_mem_singleton Y1_in_finset,
        Y1_eq_Y.symm ▸ Y_irreducible,  -- Y1 = Y is irreducible, so done. 
      -- Proof that everything in {Y} is irreducible. 
      λ (Y1 : set X) Y1_in_finset, -- Take a set in {Y}
        have Y1_eq_Y : Y1 = Y.1, from eq_of_mem_singleton Y1_in_finset,
        Y1_eq_Y.symm ▸ Y.2,  -- Y1 = Y is closed, so done. 
    ⟩ 
  )
  (-- Case of Y being not irreducible. 
    λ Y_not_irreducible, 
      -- If Y is not irreducible, 
      -- it is empty or union of two strictly smaller closed sets. 
      or.elim (induction_step Y.2 Y_not_irreducible)
      (λ Y_empty, -- If Y is empty, empty union works. 
        ⟨ ∅, 
          Y_empty.symm ▸ sUnion_empty, -- Empty union is empty
          λ C C_in_empty_finset, -- Everything in empty set is irreducible
            begin cases C_in_empty_finset, end, 
          λ C C_in_empty_finset, -- Everything in empty set is closed
            begin cases C_in_empty_finset, end, 
        ⟩)
      (-- Let C1, C2 be two closed sets that union to Y, 
        -- but are strictly smaller than Y. 
        λ ⟨C1, C2, C1_closed, C2_closed, Y_eq_C1_union_C2, 
        C1_ssub_Y, C2_ssub_Y⟩, 
        have C1_factorises : factorises ⟨C1,C1_closed⟩, 
          from induction_hypothesis ⟨C1,C1_closed⟩ C1_ssub_Y,
        have C2_factorises : factorises ⟨C2,C2_closed⟩, 
          from induction_hypothesis ⟨C2,C2_closed⟩ C2_ssub_Y,  
        let ⟨ι1, union_ι1_eq_C1, ι1_irr, ι1_closed⟩ := C1_factorises in  
        let ⟨ι2, union_ι2_eq_C2, ι2_irr, ι2_closed⟩ := C2_factorises in 
        ⟨-- the factorisation of Y is the union of factorisation of C1, C2. 
          ι1 ∪ ι2, -- the factorisation
          calc ⋃₀ (↑(ι1 ∪ ι2) : set _)-- Proof of union of factorisations is Y
              = ⋃₀ ( (↑ι1 : set _) ∪ (↑ι2 : set _) ) : by simp
          ... = ⋃₀ ι1.to_set ∪ ⋃₀ ι2.to_set : sUnion_union _ _
          ... = C1 ∪ ⋃₀ finset.to_set ι2 : union_ι1_eq_C1.symm ▸ rfl
          ... = C1 ∪ C2 : union_ι2_eq_C2.symm ▸ rfl  
          ... = Y.1 : Y_eq_C1_union_C2.symm, 
          λ (Ci : set X) (Ci_in_ι1_union_ι2), -- Proof of "factors" irreducible
            or.elim (finset.mem_union.1 Ci_in_ι1_union_ι2)
            (λ Ci_in_ι1, ι1_irr Ci Ci_in_ι1)
            (λ Ci_in_ι2, ι2_irr Ci Ci_in_ι2), 
          λ (Ci : set X) (Ci_in_ι1_union_ι2), -- Proof of "factors" closed
            or.elim (finset.mem_union.1 Ci_in_ι1_union_ι2)
            (λ Ci_in_ι1, ι1_closed Ci Ci_in_ι1)
            (λ Ci_in_ι2, ι2_closed Ci Ci_in_ι2)
        ⟩
      )
    )
end topological_space

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
-/

namespace topological_space

def closeds.compl {X : Type*} [topological_space X] : closeds X → opens X :=
λ C, ⟨-C.1, is_open_compl_iff.2 C.2⟩

def opens.compl {X : Type*} [topological_space X] : opens X → closeds X :=
λ C, ⟨-C.1, is_closed_compl_iff.2 C.2⟩

lemma continuous.subtype {X : Type*} [topological_space X] {Y : set X} :
  continuous (subtype.val : Y → X) := λ U hU, ⟨U, hU, rfl⟩

def closeds.comap {X : Type*} [topological_space X] (Y : set X) :
  closeds X → closeds Y :=
λ C, (continuous.subtype.comap (C.compl)).compl

lemma is_noetherian_subset (X : Type*) [topological_space X]
  (hX : is_noetherian X) (Y : set X) : is_noetherian Y :=
begin
  sorry
end

end topological_space

/-

Proposition 5.4. Let V be an affine algebraic set. Then:
(1) The union of the irreducible components of V is all of V .
(2) V has only finitely many irreducible components.

Lemma 5.5. Every affine algebraic set can be written as a union of finitely many
irreducible closed subsets.

Proposition 5.6. Let V be an affine algebraic set. Write V = V 1 ∪ · · · ∪ V r , where
the V i are irreducible closed subsets and ¬ V i ⊆ V j for ¬ i = j.
Then V 1 , . . . , V r are precisely the irreducible components of V .


-/

