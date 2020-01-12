import data.polynomial
import analysis.complex.polynomial -- just a sanity check, probably shouldn't be imported

open polynomial

class algebraically_closed_field (k : Type*) extends discrete_field k :=
(exists_root' : ∀ (f : polynomial k) (hf : 0 < degree f),
   ∃ z : k, is_root f z)

namespace algebraically_closed_field

variables {k : Type*} [algebraically_closed_field k]

def exists_root {f : polynomial k} (hf : 0 < degree f) := ∃ z : k, is_root f z

-- sanity check
noncomputable example : algebraically_closed_field ℂ :=
{exists_root' := λ f hf, complex.exists_root hf,
..complex.discrete_field}

end algebraically_closed_field

def is_algebraically_closed (k : Type*) [discrete_field k] : Prop :=
  ∀ {f : polynomial k} (hf : 0 < degree f), ∃ z : k, is_root f z

-- sanity check
example : is_algebraically_closed ℂ := λ hf, complex.exists_root
