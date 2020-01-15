# Notes about infinite unions.

Lean has the union of two sets, and it's called `union`.

Lean has lots of different ways of doing the union of infinitely
many sets though.

There is `Union`:

`def Union {I X : Type} (s : I → set X) : set X := ⋃ i, s i`

There is `bUnion`:

`def bUnion {I X : Type} {s : set I} {t : I → set X} := ⋃ x ∈ s, t x`


and there is `sUnion`:

`def sUnion {X : Type} {S : set (set X)} := ⋃₀ S`


