import data.set.lattice

open set

theorem compl_lt_compl {α : Type*} (U V : set α) : -U < -V → V < U :=
λ H, ⟨compl_subset_compl.1 H.1, λ H1, H.2 (compl_subset_compl.2 H1)⟩