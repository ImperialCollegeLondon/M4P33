/-
Copyright (c) 2020 Kevin Buzzard
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, and whoever else wants to join in.
-/

 -- need the definition of an affine alg set
import affine_algebraic_set.basic

 -- need so I can state that the kernel of the evaluation map is 𝕀
import affine_algebraic_set.I

/-!

# Regular functions

Let k be a field (or even an integral domain), and let V be an
affine algebraic subset of 𝔸ⁿ (where n can even be infinite).
A _regular function_ on V is a function V → k which is induced
by some polynomial F ∈ k[X₁, X₂, …, Xₙ]. Note that F itself
is not part of the data, and a regular function can be induced
by more than one polynomial in general.

-/

-- I think it might all work with commutative semirings but
-- let's let k be a commutative ring.
variables {k : Type*} [comm_ring k] {n : Type*}

local notation `𝔸ⁿ` := n → k
local notation `k[n]` := mv_polynomial n k

-- The idea: a mathematician shouldn't need to look at most of this file.
-- The plan would be that they just read the API in the comments above. 

-- They just need to know the API. 

-- Throughout this file, let V ⊆ 𝔸ⁿ be an affine algebraic subset.
variable {V : affine_algebraic_set k n}

local notation `subset_of` := set

open mv_polynomial

def is_regular2 (f : (V : subset_of 𝔸ⁿ) → k) : Prop :=
  ∃ F : k[n], ∀ (x : 𝔸ⁿ) (hx : x ∈ V), F.eval x = f ⟨x, hx⟩

def is_regular (f : (V : subset_of 𝔸ⁿ) → k) : Prop :=
  ∃ F : k[n], ∀ (x : (V : subset_of 𝔸ⁿ)), F.eval x = f x

/-- A "regular function" is a pair: a function V → k, and a proof that
it comes from a polynomial -/
structure regular_fun (V : affine_algebraic_set k n) :=
(to_fun : {x : 𝔸ⁿ // x ∈ (V : subset_of 𝔸ⁿ)} → k)
(is_regular' : is_regular to_fun)

local notation `k[V]` := regular_fun V

namespace regular_fun

/-- A regular function on V can be regarded as a function from V to k -/
instance : has_coe_to_fun (k[V]) :=
⟨_, regular_fun.to_fun⟩

variable {V}

/-- A regular function is induced from a polynomial -/
lemma is_regular (f : k[V]): ∃ F : k[n],
   ∀ (x : (V : subset_of 𝔸ⁿ)), F.eval x = f x := f.is_regular'

variable (V)

def mk' (V : affine_algebraic_set k n) (F : k[n]) : regular_fun V :=
{ to_fun := λ x, F.eval x, -- i.e. F(x)
  is_regular' := ⟨F, λ x, rfl⟩ }

variable {V}

def mk'.some_spec (F : k[n]) (x : (V : subset_of 𝔸ⁿ)) :
  (classical.some (mk' V F).is_regular).eval x = _ := classical.some_spec (mk' V F).is_regular x



/- Two regular functions are equal if and only if their
 underlying functions V → k are equal -/
@[ext] lemma ext (f g : k[V]) : (f : (V : set 𝔸ⁿ) → k) = g → f = g :=
begin
  intro h,
  cases f,
  cases g,
  congr',
end

/-- The iff is also sometimes helpful-/
lemma ext_iff (f g : k[V]) : f = g ↔ (f : (V : set 𝔸ⁿ) → k) = g :=
⟨λ h, h ▸ rfl, ext f g⟩

-- We prove the regular functions are naturally a ring.

def zero : k[V] :=
{ to_fun := λ x, 0,
  is_regular' := begin
    -- the function V → k sending everything to zero is a regular function
    use 0,
    intros,
    rw eval_zero,  
  end
}

instance : has_zero (k[V]) := ⟨zero⟩

def one : k[V] :=
{ to_fun := λ x, 1,
  is_regular' := begin
    -- the function V → k sending everything to zero is a regular function
    use 1,
    intros,
    rw eval_one,  
  end
}

instance : has_one (k[V]) := ⟨one⟩

def add (f g : k[V]) : k[V] :=
{ to_fun := λ x, f x + g x,
  is_regular' := begin
    -- sum of two regular functions is regular
    cases f.is_regular with F hF,
    cases g.is_regular with G hG,
    use F + G,
    intro x,
    rw eval_add,
    rw hF,
    rw hG,
  end
}

instance : has_add (k[V]) := ⟨add⟩

def neg (f : k[V]) : k[V] :=
{ to_fun := λ x, -(f x),
  is_regular' := begin
    -- additive inverse of a regular function is regular
    cases f.is_regular with F hF,
    use -F,
    intro x,
    rw eval_neg,
    rw hF,
  end
}

instance : has_neg (k[V]) := ⟨neg⟩

def mul (f g : k[V]) : k[V] :=
{ to_fun := λ x, (f x) * (g x),
  is_regular' := begin
    -- additive inverse of a regular function is regular
    cases f.is_regular with F hF,
    cases g.is_regular with G hG,
    use F * G,
    intro x,
    rw eval_mul,
    rw hF,
    rw hG,
  end
}

instance : has_mul (k[V]) := ⟨mul⟩

instance : comm_ring (k[V]) :=
{ add := (+),
  add_assoc := begin intros f g h, ext, apply add_assoc, end,
  zero := 0,
  zero_add := begin intro f, ext, apply zero_add, end,
  add_zero := begin intro f, ext, apply add_zero, end,
  neg := has_neg.neg,
  add_left_neg := begin intro f, ext, apply add_left_neg, end,
  add_comm := begin intros f g, ext, apply add_comm, end,
  mul := (*),
  mul_assoc := begin intros f g h, ext, apply mul_assoc, end,
  one := 1,
  one_mul := begin intro f, ext, apply one_mul, end,
  mul_one := begin intro f, ext, apply mul_one, end,
  left_distrib := begin intros f g h, ext, apply left_distrib, end,
  right_distrib := begin intros f g h, ext, apply right_distrib, end,
  mul_comm := begin intros f g, ext, apply mul_comm, end }

end regular_fun

/-- The ring homomorphism from k[X₁, X₂, …, Xₙ] to k[V] -/
noncomputable def mv_polynomial.to_regular_fun : mv_polynomial n k →+* k[V] :=
{ to_fun := λ F,
  { to_fun := λ x, F.eval x.1,
    is_regular' := ⟨F, λ x, rfl⟩
  },
  -- proof that it's a ring homomorphism
  map_one' := begin
    ext,
    apply eval_one,
  end,
  map_mul' := begin
    intros f g,
    ext,
    apply eval_mul,
  end,
  map_zero' := begin
    ext,
    unfold_coes, dsimp,
    apply eval_zero,
  end,
  map_add' := begin
    intros f g,
    ext,
    apply eval_add,
  end
}

namespace regular_fun

instance : has_scalar k k[V] :=
{ smul := λ t f,
  { to_fun := λ v, t * f v,
    is_regular' := begin
      cases f.is_regular with F hF,
      use (C t) * F,
      intro x,
      rw [eval_mul, eval_C, hF]
    end
  }
}

instance : is_ring_hom (λ t, mk' V (C t)) :=
{ map_one := begin
    ext x,
    unfold_coes,
    unfold mk',
    dsimp,
    rw eval_one,
    refl,
  end,
  map_mul := 
  begin
    intros s t,
    ext x,
    unfold_coes,
    unfold mk', 
    dsimp,
    rw eval_C,
    simp [eval_C],
    refl,
  end,
  map_add := 
  begin
    intros s t,
    ext x,
    unfold_coes,
    unfold mk',
    dsimp,
    simp [eval_C],
    refl
  end
}.

noncomputable instance : algebra k k[V] :=
{ to_fun := (λ t, mk' V (C t)),
  hom := by apply_instance,
  commutes' := begin
    intros r x,
    apply mul_comm,
  end,
  smul_def' := begin
    intros r f,
    ext x,
    show _ = mk' V (C r) x * f x,
    unfold_coes,
    unfold mk',
    simp only [eval_C],
    refl,
  end
}
end regular_fun

open mv_polynomial function

lemma mv_polynomial.to_regular_fun.surjective :
  surjective
    ((to_regular_fun : mv_polynomial n k →+* k[V]) : mv_polynomial n k → k[V]) :=
begin
  intro f,
  cases f.is_regular with F hF,
  use F,
  ext x,
  rw ←hF x,
  refl,
end

open affine_algebraic_set

lemma to_regular_fun.mem_kernel (F : mv_polynomial n k) :
  ((to_regular_fun : mv_polynomial n k →+* k[V]) : mv_polynomial n k → k[V]) F = 0
  ↔ F ∈ 𝕀 V :=
begin
  rw mem_𝕀_iff,
  rw regular_fun.ext_iff,
  rw funext_iff,
  split, -- sigh
  { intros f x hx, exact f ⟨x, hx⟩},
  { intros f x, exact f x.1 x.2}
end

-- let's prove it's a k-algebra hom
noncomputable def mv_polynomial.to_regular_fun_algebra_map : k[n] →ₐ[k] k[V] :=
{ to_fun := to_regular_fun.to_fun,
  map_one' := begin
    ext x,
    cases x with x hx,
    exact eval_one x
  end,
  map_mul' := begin
    intros f g,
    ext x,
    exact eval_mul,
  end,
  map_zero' := begin
    ext x,
    cases x with x hx,
    convert @eval_zero _ _ _ x,
  end,
  map_add' := begin
    intros f g,
    ext x,
    exact eval_add,
  end,
  commutes' := begin
    intro s,
    refl,
  end }

/-
TODO -- ask on Zulip why f is implicit and x explicit (note the trouble this caused me in map_zero')

mv_polynomial.eval_one : ∀ {X : Type u_2} {R : Type u_1} [_inst_1 : comm_semiring R] (x : X → R), eval x 1 = 1
mv_polynomial.eval_zero : ∀ {α : Type ?} {n : Type ?} [_inst_1 : comm_semiring α] {f : n → α}, eval f 0 = 0
-/
