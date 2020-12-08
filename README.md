# W-types-in-setoids
This is the Coq formalisation of the paper "W-types in setoids",
[arXiv:1809.02375](https://arxiv.org/abs/1809.02375).

Abstract:
We present a construction of W-types in the setoid model of extensional Martin-Löf type theory using dependent W-types in the underlying intensional theory. More precisely, we prove that the internal category of setoids has initial algebras for polynomial endofunctors. In particular, we characterise the setoid of algebra morphisms from the (candidate) initial algebra to a given algebra as a setoid on a dependent W-type. We conclude discussing the case of discrete (i.e. free) setoids. By using dependent W-types, we avoid other assumptions like elimination into a type universe or Uniqueness of Identity Proofs, that are used in constructions by Palmgren and by van den Berg, respectively. The results have been verified in Coq and a formalisation is available on the author's GitHub page.

The repository contains:

README.md  
This file

Wstd.v  
The construction of initial algebras for polynomial endofunctors.
Reference to the propositions in the paper is given.

freeWstd.v  
Proofs of the last section of the paper on discrete (or free) setoids.

Wstd_basics.v  
Definitions and basic properties of setoids and setoid families.
Mainly due to Erik Palmgren and Olov Wilander.

IdType.v  
Definition and basic properties of the identity type (in Paulin-Mohring's formulation).
