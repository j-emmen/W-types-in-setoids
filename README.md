# W-types-in-setoids
This is the Coq formalisation of the paper "W-types in setoids",
[arXiv:1809.02375](https://arxiv.org/abs/1809.02375).

Abstract:
We present a construction of W-types in the setoid model of extensional Martin-Löf type theory using dependent W-types in the underlying intensional theory. More precisely, we prove that the internal category of setoids has initial algebras for polynomial endofunctors. In particular, we characterise the setoid of algebra morphisms from the (candidate) initial algebra to a given algebra as a setoid on a dependent W-type. We conclude discussing the case of discrete (i.e. free) setoids. By using dependent W-types, we avoid other assumptions like elimination into a type universe or Uniqueness of Identity Proofs, that are used in constructions by Palmgren and by van den Berg, respectively. The results have been verified in Coq and a formalisation is available on the author's GitHub page.

Reference is given in the source files to definitions and statements in the paper.

The paper is mapped to this repository as follows:

Section n --> S(n-2)*.v

Not everything in Section 2 is formalised here.
In particular, the formalisation does not include proofs of Theorems 2.8 and 2.9.
For a Coq proof of the latter, see
[Palmgren, LCC setoids in Coq](https://github.com/erikhpalmgren/LCC_setoids_in_Coq).

N.B. The file S20_AlgGlue.v takes a little more time to type-check than the other files.
