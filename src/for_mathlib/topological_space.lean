
import topology.maps topology.subset_properties

example : ℕ := 691

open_locale classical

-- x ∈ closure S if and only if x ∈ C for all closed sets containing S.
lemma mem_closure_iff' {X : Type*} [topological_space X] {S : set X} {x : X} :
  x ∈ closure S ↔ ∀ C : set X, is_closed C → S ⊆ C → x ∈ C :=
begin
  rw mem_closure_iff,
  split,
  { intros h C hC hSC,
    replace h := h C.compl hC,
    by_contra hx,
    apply set.ne_empty_iff_nonempty.2 (h hx), clear h hx,
    rw set.eq_empty_iff_forall_not_mem,
    rintros x ⟨hxC, hxS⟩,
    apply hxC,
    apply hSC,
    assumption},
  { intros h U hU hxU,
    replace h := h (-U : set X) (is_closed_compl_iff.2 hU),
    rw ←set.ne_empty_iff_nonempty,
    intro hUS,
    apply h _ hxU,
    intros x hx hU,
    apply set.not_mem_empty x,
    rw ←hUS,
    split; assumption},
end

open set

/-- If X is compact then pr₂ : X × Y → Y is a closed map -/
theorem closed_pr2_of_compact
  {X : Type*} [topological_space X] [compact_space X]
  {Y : Type*} [topological_space Y] :
  is_closed_map (prod.snd : X × Y → Y) :=
begin
  intros C hC,
  rw ←is_open_compl_iff,
  rw is_open_iff_forall_mem_open,
  intros y hy,
  rcases generalized_tube_lemma (compact_univ : compact (set.univ : set X))
    (compact_singleton : compact {y}) (is_open_compl_iff.2 hC) _ with
    ⟨U, V, hU, hV, hXU, hyV, hUV⟩,
  { use V,
    split,
    { rintros v hvV ⟨uv, huv, rfl⟩,
      revert huv,
      apply hUV,
      rw set.mem_prod,
      split,
        apply hXU, apply set.mem_univ,
      exact hvV,
    },
    split, exact hV,
    apply hyV,
    apply set.mem_singleton,
  },
  { intros xy hxy,
    intro hxyC,
    apply hy,
    use xy,
    split, exact hxyC,
    rw mem_prod at hxy,
    cases hxy with hx hy,
    exact mem_singleton_iff.1 hy,  
  }
end

def filter_topology {X : Type*} (F : filter X) : topological_space (option X) :=
{ is_open := λ U, if none ∈ U then some ⁻¹' U ∈ F else true,
  is_open_univ := begin
    rw if_pos,
      rw preimage_univ,
      exact filter.univ_mem_sets,
    refine mem_univ (none : option X),
  end,
  is_open_inter := begin
    intros U V hU hV,
    split_ifs, swap, trivial,
    cases h with h0U h0V,
    rw if_pos at hU, swap, exact h0U,
    rw if_pos at hV, swap, exact h0V,
    show some ⁻¹' (U ∩ V) ∈ F,
    rw preimage_inter, 
    exact F.inter_sets hU hV,
  end,
  is_open_sUnion := begin
    intros I,
    intro hI,
    split_ifs, swap, trivial,
    rw mem_sUnion at h,
    rcases h with ⟨U, hU, h0U⟩,
    rw preimage_sUnion,
    replace hI := hI U hU,
    rw if_pos at hI, swap, exact h0U,
    refine filter.mem_sets_of_superset hI _,
    exact subset_bUnion_of_mem hU,
  end
}

instance compact_space_of_closed_pr2 {X : Type*} [topological_space X]
  (hclosed : ∀ (Y : Type*) [topological_space Y], is_closed_map (prod.snd : X × Y → Y)) :
  compact_space X :=
begin
  constructor,
  -- we will show that every proper filter has an adherent point
  intros F hF h, clear h,
  -- Let Y be the topological space defined above (X + extra point with nhds F)
  letI := filter_topology F,
  replace hclosed := hclosed (option X),
  -- Let D be the closure of {(x,x)} in X × Y.
  set D := closure (set.range (λ x : X, (⟨x, some x⟩ : X × option X))) with hD,
  -- Its image in Y is closed.
  replace hclosed := hclosed D (is_closed_closure),
  -- If the image contains the extra point
  by_cases hnone : none ∈ prod.snd '' D,
  { -- then (x, extra point) is in the closure of D
    rcases hnone with ⟨xy, hxy, hy⟩,
    -- and we claim this x works
    use xy.fst,
    split, exact mem_univ _,
    intro hbot,
    rw ←filter.empty_in_sets_eq_bot at hbot,
    rw filter.mem_inf_sets at hbot,
    rcases hbot with ⟨A, hA, U, hU, hAU⟩,
    rw subset_empty_iff at hAU,
    revert hAU,
    change A ∩ U ≠ ∅,
    rw set.ne_empty_iff_nonempty,
    rw mem_nhds_sets_iff at hU,
    rcases hU with ⟨U', hU'U, hU', hxyU'⟩,
    set V : set (X × option X) := set.prod U' (insert none (some '' A)),
    have hV : is_open V,
      apply is_open_prod hU',
      change if none ∈ (insert none (some '' A)) then some ⁻¹' (insert none (some '' A)) ∈ F else true,
      rw if_pos,
        convert hA using 1,
        ext a,
        simp,
      apply mem_insert,
    have hxyV : xy ∈ V,
      rw mem_prod,
      split, exact hxyU',
      rw hy,
      apply mem_insert,
    rw hD at hxy,
    rw mem_closure_iff at hxy,
    replace hxy := hxy V hV hxyV,
    rcases hxy with ⟨_, hp, p, rfl⟩,
    use p,
    rw mem_prod at hp,
    cases hp with hpU hpA,
    split,
      change some p ∈ _ at hpA,
      rw mem_insert_iff at hpA,
      cases hpA, cases hpA,
      rcases hpA with ⟨p', hp', hpp'⟩,
      convert hp',
      exact option.some_inj.1 hpp'.symm,
    apply hU'U,
    exact hpU
  },
  { -- And if the image doesn't contain the extra point then 
    -- in fact we can get a contradiction.
    exfalso,
    -- Indeed X is a subset of the image because (x,x) ∈ D
    have hX : range some ⊆ prod.snd '' D,
    { rintros _ ⟨x, rfl⟩,
      use ⟨x, some x⟩,
      split, swap, refl,
      apply subset_closure,
      use x
    },
    rw ←is_open_compl_iff at hclosed,
    change if none ∈ -(prod.snd '' D) then some ⁻¹' -(prod.snd '' D) ∈ F
      else true at hclosed,
    replace hnone := mem_compl hnone,
    rw if_pos hnone at hclosed,
    apply hF,
    rw ←filter.empty_in_sets_eq_bot,
    convert hclosed,
    symmetry,
    rw eq_empty_iff_forall_not_mem,
    intros x hx,
    apply hx,
    apply hX,
    use x,
  }  
end
