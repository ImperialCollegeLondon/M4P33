# M4P33
M4 algebraic geometry course in Lean

## What is this?

In Jan to March 2020 I am teaching an algebraic geometry course at Imperial College London, which covers the basics of the theory of algebraic varieties (note: no schemes involved).

Hendrik Lenstra once told me that you only really learn something when you teach it. I have never really learnt this theory properly up until now, and I thought that one way I could try and understand the material better would be to formalise it all in the Lean Theorem Prover. Many thanks to Hendrik for his years of sound advice.

I am following [the lecture notes of Martin Orr](https://homepages.warwick.ac.uk/staff/Martin.Orr/2017-8/alg-geom/). Thanks Martin for making such nice notes and also making them available.

If you just want to browse at some of the code, [here is what we talked about in Lecture 1](https://github.com/ImperialCollegeLondon/M4P33/blob/master/src/affine_algebraic_set/union.lean). If you want to go further, and learn about how to formalise this kind of level of algebraic geometry yourself, you could consider installing the repository, following the instructions below.

Kevin Buzzard

## Installation

### Step 1

[Install Lean](https://github.com/leanprover-community/mathlib/blob/master/README.md#installation).

### Step 2 

Assuming you followed the instructions in Step 1, and have access to a command line, and you have got your
PATH variable working correctly, then installing this project should be as simple as

```
git clone https://github.com/ImperialCollegeLondon/M4P33.git
cd M4P33
leanpkg configure
update-mathlib
```

and then an optional last two lines

```
cd src
lean --make
```

if you want to compile the project yourself.

[Prove a theorem. Write a function.](https://xenaproject.wordpress.com) The Xena project.
