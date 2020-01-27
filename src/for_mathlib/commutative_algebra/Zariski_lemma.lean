/-

Zariski's Lemma: if k is a field and K is a field finitely generated
as a k-algebra, then K is also finitely-generated as a k-module

-/

import ring_theory.integral_closure

theorem Zariskis_lemma
  -- let k be a field
  (k : Type*) [discrete_field k]
  -- and let k ⊆ K be another field
  (K : Type*) [discrete_field K] [algebra k K] 
  -- Assume that there's a finite subset s of K
  (s : set K) (hfs : s.finite)
  -- which generates K as a k-algebra
  -- (note: `⊤` is "the largest k-subalgebra of K", i.e., K)
  (hsgen : algebra.adjoin k s = ⊤)
  -- Then
  :
  -- K is finitely-generated as a k-vector space
(⊤ : submodule k K).fg
:= sorry
