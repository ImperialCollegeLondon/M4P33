-- Some basic results about the relationship of 𝕍 and 𝕀 

-- Imports results about 𝕍 and 𝕀 
import affine_algebraic_set.V
import affine_algebraic_set.I

import data.mv_polynomial

open mv_polynomial

variables {k : Type*} [comm_ring k]

variable {σ : Type*}

open affine_algebraic_set

/-- For S ⊆ k[X₁,X₂,…,Xₙ] we have S ⊆ 𝕀(𝕍(S))--/
lemma 𝕀_of_𝕍_is_subset {S : set(mv_polynomial σ k)} :
S ⊆ 𝕀(𝕍(S)):=
begin
    -- assume s ∈ S
    intros s HS,
    -- apply Definition of 𝕀 
    rw mem_𝕀_iff,
    -- let x ∈ kⁿ be arbitrary 
    intro x,
    --apply Definition of 𝕍 
    rw mem_𝕍_iff,
    -- Assume Hypothesis
    intro H,
    -- Apply H to goal
    apply H,
    from HS,
end

/-- For S ⊆ k[X₁,X₂,…,Xₙ] we have 𝕍(𝕀(𝕍(S))) = 𝕍(S)
e.g. 𝕍(𝕀(U)) = U if U is an algebraic set --/
lemma 𝕀_of_𝕍 {S : set(mv_polynomial σ k)} : 
𝕍(𝕀(𝕍(S))) = 𝕍(S):=
begin
    -- ⊆ Inclusion: This follows from the fact that 𝕀(𝕍(S)) ⊆ S (shown above)
    -- And the antimonomity of 𝕍 
    apply set.subset.antisymm,
    apply 𝕍_antimono,
    from 𝕀_of_𝕍_is_subset,

    -- ⊇ Inclusion: I'm sorry, this is just a bunch of abstract nonsense
    -- We show that if x ∈ kⁿ vanishes for all f ∈ S (e.g. x ∈ 𝕍(S)), 
    -- it also vanishes for all g ∈ k[X₁,X₂,…,Xₙ] that vanish on 𝕍(S)
    -- Which is true by definition:
    
    -- Suppose y ∈ 𝕍(S)
    intros y HS,

    -- Apply definitions of 𝕍 and 𝕀
    rw mem_𝕍_iff,
    intro f,
    rw mem_𝕀_iff,

    -- Rewrite Goal
    intro Q,
    apply Q y,
    -- Use y ∈ 𝕍(S)
    from HS,
end

lemma 𝕀_inj_on_𝕍 {S T : set(mv_polynomial σ k)} : 𝕀(𝕍(S)) = 𝕀(𝕍(T)) → 𝕍(S) = 𝕍(T) :=
begin
intro H,
have H1 := congr_arg 𝕍 H,
rw [𝕀_of_𝕍, 𝕀_of_𝕍] at H1,
exact H1,
end

lemma 𝕀_strantimono_on_𝕍 {S T : set(mv_polynomial σ k)} :
  𝕍 S < 𝕍 T → 𝕀(𝕍(T)) < 𝕀(𝕍(S)) :=
begin
intro lt,
have H := 𝕀_antimono (𝕍 S) (𝕍 T) (le_of_lt lt),
cases (@eq_or_lt_of_le (set (mv_polynomial σ k)) _ _ _ H),
{
    exfalso,
    have H1 := 𝕀_inj_on_𝕍 h,
    apply ne_of_lt lt,
    apply H1.symm,
},
{ exact h },
end