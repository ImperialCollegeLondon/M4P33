import data.finset

namespace finset

lemma diff_singleton_ssub {X : Type*} [decidable_eq X] {s : finset X} {x : X} (h : x ∈ s) : s \ {x} ⊂ s :=
finset.ssubset_iff.2 ⟨x, by simp,
  λ y hy, (mem_insert.1 hy).elim (λ hxy, hxy.symm ▸ h) (by simp {contextual := tt})⟩

-- open_locale classical

-- lemma ssub_of_diff {X : Type*} (S T : finset X)
--   (hST : S ∩ T = ∅) : S \ T ⊂ S :=
-- begin

-- end

end finset
