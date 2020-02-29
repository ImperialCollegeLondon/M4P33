
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
-- Let C be a closed set in X × Y  
λ C hC, begin
  -- It suffices to prove that every y in the complement of pr₂(C)
  -- is contained in an open neighbourhood which misses pr₂(C)
  rw [←is_open_compl_iff, is_open_iff_forall_mem_open],
  -- so take y in the complement
  intros y hy,
  -- and apply the generalised tube lemma to X × {y}
  -- which tells us that there exists a basic open U × V containing X × {y}
  -- which is disjoint from C (this is where we use compactness of X)
  rcases generalized_tube_lemma compact_univ
    (compact_singleton : compact {y}) (is_open_compl_iff.2 hC) _ with
    ⟨U, V, hU, hV, hXU, hyV, hUV⟩,
  { -- The set V is the neighbourhood of y we seek.
    use V,
    split,
    { rintros v hvV ⟨uv, huv, rfl⟩,
      exact hUV ⟨hXU (set.mem_univ _), hvV⟩ huv,
    },
    exact ⟨hV, hyV (set.mem_singleton _)⟩,
  },
  { -- and the proof is complete once we note that y ∉ pr₂(C) implies
    -- X × {y} is disjoint from C
    rintros xy ⟨hx, hyC⟩ hxyC,
    apply hy,
    existsi xy,
    exact ⟨hxyC, mem_singleton_iff.1 hyC⟩,  
  }
end

def filter_topology {X : Type*} (F : filter X) : topological_space (option X) :=
{ is_open := λ U, if none ∈ U then some ⁻¹' U ∈ F else true,
  is_open_univ := begin
    rw [if_pos, preimage_univ],
      exact filter.univ_mem_sets,
    exact mem_univ (none : option X),
  end,
  is_open_inter := λ U V hU hV,
    begin
    split_ifs, swap, trivial,
    cases h with h0U h0V,
    rw if_pos at hU, swap, exact h0U,
    rw if_pos at hV, swap, exact h0V,
    show some ⁻¹' (U ∩ V) ∈ F,
    rw preimage_inter, 
    exact F.inter_sets hU hV,
  end,
  is_open_sUnion := λ I hI, begin
    split_ifs, swap, trivial,
    rcases h with ⟨U, hU, h0U⟩,
    replace hI := hI U hU,
    rw preimage_sUnion,
    rw if_pos at hI,
      exact filter.mem_sets_of_superset hI (subset_bUnion_of_mem hU),
    exact h0U,
  end
}

/-- If F is not ⊥ then the closure of X in option X is all of option X -/
lemma closure_range_sum_eq_univ {X : Type*} {F : filter X} (hF : F ≠ ⊥) :
  @closure (option X) (filter_topology F) (range some) = univ :=
begin
  letI := filter_topology F,
  apply eq_univ_of_forall,
  rintro (_| x),
  -- Clearly X is a subset of the closure of X
  -- so it suffices to prove that the extra point is in the closure
    swap, exact subset_closure ⟨x, rfl⟩,
  -- Assume for a contradiction that it is not.
  by_contra hnone,
  -- Then the complement of the closure is open and contains the extra point
  set U := -(closure (range some) : set (option X)) with hUc,
  have HUO : is_open U := is_open_compl_iff.2 is_closed_closure,
  change if none ∈ U then some ⁻¹' U ∈ F else true at HUO,
  -- so the intersection of this complement with X must be in F
  rw if_pos at HUO, swap, rwa hUc,
  apply hF,
  rw ←filter.empty_in_sets_eq_bot,
  -- If this intersection is empty this contradicts the fact that F ≠ ⊥
  convert HUO, symmetry, rw eq_empty_iff_forall_not_mem,
  -- but the intersection is empty because X is a subset of its closure
  intros x hx,
  rw hUc at hx,
  refine hx (subset_closure _),
  use x,
end 

universe u

theorem compact_space_of_closed_pr2 {X : Type u} [topological_space X]
  (hclosed : ∀ (Y : Type u) [topological_space Y], is_closed_map (prod.snd : X × Y → Y)) :
  compact_space X :=
  -- we will show that every proper filter has an adherent point
⟨λ F hF h0, begin
  -- Let Y be the topological space defined above (X + extra point with nhds F)
  -- (we'll just call it `option X` here)
  letI := filter_topology F,
  -- Let D be the closure of {(x,x)} in X × Y.
  set D := closure (set.range (λ x : X, (⟨x, some x⟩ : X × option X))) with hD,
  -- Its image in Y is closed.
  replace hclosed := hclosed (option X) D (is_closed_closure),
  -- Now clearly the projection contains X
  have hX : range some ⊆ prod.snd '' D,
  { rintros _ ⟨x, rfl⟩,
    use ⟨x, some x⟩,
    split, swap, refl,
    refine subset_closure _,
    exact ⟨x, rfl⟩,
  },
  -- and it's closed, so by `closure_range_sum_eq_univ` the projection is everything
  -- and in particular contains the extra point
  have hnone : none ∈ prod.snd '' D,
    apply (closure_subset_iff_subset_of_is_closed hclosed).2 hX,
    rw closure_range_sum_eq_univ hF,
    exact mem_univ _,
  -- Hence (x, extra point) is in the closure of the diagonal
  rcases hnone with ⟨xy, hxy, hy⟩,
  -- and we claim this x works
  use xy.fst,
  split, exact mem_univ _,
  -- We have to show that every element of F meets every neighbourhood of X
  intro hbot,
  rw [←filter.empty_in_sets_eq_bot, filter.mem_inf_sets] at hbot,
  -- so let A be an element of the filter, and let U be a neighbourhood of x (=xy.fst)
  rcases hbot with ⟨A, hA, U, hU, hAU⟩,
  rw subset_empty_iff at hAU,
  revert hAU,
  -- and let's show A ∩ U is non-empty.
  change A ∩ U ≠ ∅,
  rw set.ne_empty_iff_nonempty,
  rw mem_nhds_sets_iff at hU,
  -- U is a neighbourhood of x so it contains an open neighbourhood U' of x
  rcases hU with ⟨U', hU'U, hU', hxyU'⟩,
  -- Let V be the basic open set U' x (point union A)
  set V : set (X × option X) := set.prod U' (insert none (some '' A)),
  have hV : is_open V,
  { apply is_open_prod hU',
    change if none ∈ (insert none (some '' A)) then some ⁻¹' (insert none (some '' A)) ∈ F else true,
    rw if_pos (mem_insert none _),
    convert hA using 1,
    ext a,
    simp,
  },
  -- Clearly (x,extra point) is in V
  have hxyV : xy ∈ V,
  { split, exact hxyU',
    rw hy,
    apply mem_insert
  },
  -- so V meets D and hence (because V is open) meets the diagonal
  rw [hD, mem_closure_iff] at hxy,
  replace hxy := hxy V hV hxyV,
  -- so say it meets the diagonal at (p,p)
  rcases hxy with ⟨_, hp, p, rfl⟩,
  -- then p is easily checked to be in the intersection and we're done
  use p,
  cases hp with hpU hpA,
  split,
    change some p ∈ _ at hpA,
    rw mem_insert_iff at hpA,
    cases hpA, cases hpA,
    rcases hpA with ⟨p', hp', hpp'⟩,
    convert hp',
    exact option.some_inj.1 hpp'.symm,
  exact hU'U hpU,
end⟩
