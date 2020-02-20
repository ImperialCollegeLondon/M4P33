import affine_algebraic_set.V
import topology.opens
import affine_algebraic_set.V_and_I


namespace affine_algebraic_set

variables {k : Type*} [integral_domain k] {σ : Type*}

local notation `𝔸ⁿ` := σ → k

open set
open topological_space

instance Zariski_topology  :
  topological_space 𝔸ⁿ := 
{ -- First we need to define what an open is, in lean we need to give a function
  -- from set (n → k) → Prop i.e. a function which takes a set in k^n and
  -- determines if this is open or not.
  is_open := λ U, ∃ (S : set (mv_polynomial σ k)), U = -𝕍 (S),
  -- Secondly we show that univ, the whole set, is open.
  is_open_univ :=
  begin
    -- we know that the whole set will be the required set, so we "use univ"
    use (set.univ : set (mv_polynomial σ k)),
    -- Use fact that V(univ) = ∅
    rw 𝕍_univ,
    -- Putting goal into canonical form, i.e. use the frontend notations such
    -- as - instead of compl
    -- this is important because rewrites wont recognize definitionally
    -- equivalent statements as the same
    show set.univ = - ∅,
    -- Now that we are using canonical form, rewrites will work again.
    -- So we finish up by using fact
    -- that -(∅) = univ
    rw compl_empty,
  end,
  -- Now we show that being open is preserved by intersections.
  is_open_inter :=
  begin
    -- Let U, V be opens and let U_set be the fact that there is some S such
    -- that U = - 𝕍 (S). Similarly for V_set.
    intros U V U_set V_set,
    -- unpack U_set and V_set to access the underlying sets S and T
    cases U_set with S U_comp,
    cases V_set with T V_comp,
    -- Now we wish to show that S*T satisfies the goal
    use S*T,
    -- Use multiplicative property of 𝕍
    rw [𝕍_mul],
    -- TODO: explain convert
    convert (compl_union _ _).symm,
  end,
  -- Finally we wish to show that opens is preserved by arbitary unions
  is_open_sUnion :=
  begin
  -- Let opens be the set of opens that we wish to union over
  intros opens open_comp,
  -- Define H to be the set of sets of polynomials S s.t. - 𝕍 (S) is in opens.
  let H := {S : set (mv_polynomial σ k) | - 𝕍 (S) ∈ opens},
  -- We now want to show that union over H satisfies the goal
  use ⋃₀ H,
  -- converting from sUnion to Union so that we can use the lemma 𝕍_union
  rw @sUnion_eq_Union (mv_polynomial σ k) H,
  rw 𝕍_Union,
  -- putting goal in canonical form
  show ⋃₀ opens = - (⋂ (i : H), 𝕍 (i.val)),
  -- Now that we are using canonical form, rewrites will work again.
  rw compl_Inter,
  rw sUnion_eq_Union,
  -- We prove the two sides are equal by showing the double inclusion
  apply eq_of_subset_of_subset,
    {
      apply Union_subset_Union2,
      intro U,
      cases (open_comp U U.2) with S eq,
      use S,
      change ↑U = compl (𝕍 S) at eq,
        show compl (𝕍 S) ∈ opens, rw ←eq, exact U.2,
      show U.val ⊆ compl (𝕍 (S)),
      rw subset.antisymm_iff at eq,
      cases eq, exact eq_left,
    },
  apply Union_subset_Union2,
  intro S,
  use - 𝕍 S, exact S.2,
  show -𝕍 (S.1) ⊆ -𝕍 (S.1),
  refine set.subset.refl _,
  end
}

open_locale classical

lemma is_closed_iff (C : set 𝔸ⁿ) :
  is_closed C ↔ ∃ (S : set (mv_polynomial σ k)), C = 𝕍 S :=
begin
  unfold is_closed,
  show (∃ (S : set (mv_polynomial σ k)), (compl C) = compl (𝕍 S)) ↔ _,
  rw exists_congr,
  intro S,
  split,
    intro h, ext x, apply not_iff_not.1, rw [←mem_compl_iff, ←mem_compl_iff],
    congr', apply_instance, apply_instance,
  intro h, rw h,
end

#check neg_lt_neg

theorem compl_lt_compl {α : Type*} (U V : set α) : -U < -V → V < U :=
begin
intro H,
split,
  rw ←compl_subset_compl,
  exact H.1,
cases H, intro, apply H_right, 
rw [←compl_subset_compl, compl_compl, compl_compl],
exact a,
end

theorem zariski_wf {k : Type*} {n : Type*} [fintype n] [integral_domain k] [is_noetherian k k] :
  well_founded ((>) : (opens (n → k) → (opens (n → k)) → Prop)) :=
begin
  have subrel : ∀ (V U: opens (n → k)), U < V → 𝕀' (-↑U) < 𝕀' (-↑V),
    {
      intros U V lt,
      have exists_U_eq_𝕍_S := (is_closed_iff (-↑U)).1 (is_closed_compl_iff.2 U.2),
      cases exists_U_eq_𝕍_S with S U_eq_𝕍_S,
      have exists_V_eq_𝕍_T := (is_closed_iff (-↑V)).1 (is_closed_compl_iff.2 V.2),
      cases exists_V_eq_𝕍_T with T V_eq_𝕍_T,
      rw [U_eq_𝕍_S, V_eq_𝕍_T, submodule.lt_def],
      refine 𝕀_strantimono_on_𝕍 _,
      rw [←U_eq_𝕍_S, ←V_eq_𝕍_T],
      apply compl_lt_compl,
      rw [compl_compl, compl_compl],
      exact lt,
    },
  apply subrelation.wf subrel _,
  refine @inv_image.wf _ _ (>) (λ U : opens (n → k), 𝕀' (-(↑U : set (n → k)))) _,
  apply is_noetherian_iff_well_founded.1,
  refine @is_noetherian_ring_mv_polynomial_of_fintype _ _ _ _ _inst_4,
end

end affine_algebraic_set