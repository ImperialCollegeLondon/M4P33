-- Some basic results about the relationship of 𝕍 and 𝕀 

-- Imports results about 𝕍 and 𝕀 
import .V
import .I

import data.mv_polynomial

open mv_polynomial

variables {k : Type*} [comm_ring k]

variable {n : Type*}

open affine_algebraic_set

/-- For S ⊆ k[X₁,X₂,…,Xₙ] we have S ⊆ 𝕀(𝕍(S))--/
lemma 𝕀_of_𝕍_is_subset {S : set(mv_polynomial n k)} :
S ⊆ 𝕀(𝕍(S)):=
begin
    -- assume s ∈ S
    intros s HS,
    -- apply Definition of 𝕀 
    rw 𝕀.mem_𝕀_iff,
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
lemma 𝕀_of_𝕍 {S : set(mv_polynomial n k)} : 
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
    rw 𝕀.mem_𝕀_iff,

    -- Rewrite Goal
    intro Q,
    apply Q y,
    -- Use y ∈ 𝕍(S)
    from HS,
end
