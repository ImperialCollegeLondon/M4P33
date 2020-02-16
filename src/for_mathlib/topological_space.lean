-- x ∈ closure S if and only if x ∈ C for all closed sets containing S.

import topology.basic

example : ℕ := 691

open_locale classical

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