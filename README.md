# W-types-in-setoids
This is the Coq 8.8.0 formalisation of the paper "W-types in setoids",
[arXiv:1809.02375v2](https://arxiv.org/abs/1809.02375v2).

Abstract:
W-types and their categorical analogue, initial algebras for polynomial endofunctors,
are an important tool in predicative systems to replace transfinite recursion on well-orderings.
Current arguments to obtain W-types in quotient completions rely on assumptions, like Uniqueness of Identity Proofs,
or on constructions that involve recursion into a universe, that limit their applicability to a specific setting.
We present an argument, verified in Coq,
that instead uses dependent W-types in the underlying type theory to construct W-types in the setoid model.
The immediate advantage is to have a proof more type-theoretic in flavour,
which directly uses recursion on the underlying W-type to prove initiality.
Furthermore, taking place in intensional type theory and not requiring any recursion into a universe,
it may be generalised to various categorical quotient completions,
with the aim of finding a uniform construction of extensional W-types.

The repository contains:

README.md  
This file

Wstd.v  
The construction of initial algebras for polynomial endofunctors.
Reference to the propositions in the paper is given.

Wstd_basics.v  
Definitions and basic properties of setoids and setoid families.
Mainly due to Erik Palmgren and Olov Wilander.
