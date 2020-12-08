(*--------------------------------------------------------------------------*)
(*                             Coq 8.8.0                                    *)
(*--------------------------------------------------------------------------*)
(* Construction of initial algebras for polynomial endofunctors in setoids  *)
(* using dependent W-types in the underlying type theory.                   *)
(*--------------------------------------------------------------------------*)
(* Author: Jacopo Emmenegger. 2018.                                         *)
(*--------------------------------------------------------------------------*)
(* References in comments are to JE, "W-types in setoids", arXiv:1809.02375 *)
(*--------------------------------------------------------------------------*)


Require Import Wstd_basics.

(* Section 2.1 *)

(*------------------*)
(* Standard W-types *)
(*------------------*)

Inductive Wty {A : Set}(B : A → Set) : Set :=
  sup : (∀ x : A, ∀ f : B(x) → (Wty B), Wty B).

Definition WtyIndex {A : Set}(B : A → Set) : Wty B → A.
  
  intros [a f]. apply a.
Defined.

Definition WtyBranches {A : Set}(B : A → Set)(w : Wty B):
  B (WtyIndex B w) → Wty B.
  
  destruct w as [a f]. apply f.
Defined.


(*-------------------*)
(* Dependent W-types *)
(*-------------------*)

Inductive DWty {I : Set}{A : I → Set}(B : ∀ i, A i → Set)
          (d : ∀ i a, B i a → I)(i : I) : Set :=
  supd : (∀ a : A i,
               ∀ f : (∀ b : B i a, DWty B d (d i a b)),
                 DWty B d i).

Definition DWtyIndex {I : Set}{A : I → Set}(B : ∀ i, A i → Set)
           (d : ∀ i a, B i a → I)(i : I) : DWty B d i → A i.

  intros [a f]. apply a.
Defined.

Definition DWtyBranches {I : Set}{A : I → Set}(B : ∀ i, A i → Set)
           (d : ∀ i a, B i a → I)(i : I)(r : DWty B d i) :
  ∀ b :B i (DWtyIndex B d i r), DWty B d (d i (DWtyIndex B d i r) b).
  
  destruct r as [a f]. apply f.
Defined.


(* Section 2.2 *)

(*---------------------*)
(* Polynomial functors *)
(*---------------------*)

Definition PolyObj {A : setoid}(B : setoidfamily A)(X : setoid) : setoid.

  apply (Build_setoid (∃ a, B a ⇒ X)
                      (λ z z', ∃ p : projT1 z ≈ projT1 z',
                          projT2 z ≈ projT2 z' ∘ B•p)).
  apply Build_setoidaxioms.
  intro z. exists (setoidrefl _ (projT1 z)). intro b.
  apply (setoidmapextensionality _ _ (projT2 z)). apply setoidfamilyrefgeneralinv.
  intros z z' H. set (p := projT1 H). set (q := projT2 H).
  exists (p ˢ). intro b'. apply setoidsym.
  apply setoidtra with (y := projT2 z' ∘ B•p (B•(p ˢ) b')). apply q.
  apply (setoidmapextensionality _ _ (projT2 z')). apply setoidfamilycmpinvert.
  intros z z' z'' H H'.
  set (p := projT1 H). set (q := projT2 H). set (p' := projT1 H'). set (q' := projT2 H').
  exists (p' ⊙ p). intro b.
  apply setoidtra with (y := projT2 z'' ∘ (B•p' ∘ B•p) b).
  apply ((q' (B•p b)) ⊙ (q b)). apply (setoidmapextensionality _ _ (projT2 z'')).
  apply setoidfamilycmpgeneral.
Defined.

Definition PolyArr_fnc {A : setoid}(B : setoidfamily A){X Y : setoid} :
  (X ⇒ Y) → PolyObj B X → PolyObj B Y.

  intros f F. set (a := projT1 F). set (h := projT2 F).
  exists a. apply (f ∘ h).
Defined.

Definition PolyArr  {A : setoid}(B : setoidfamily A){X Y : setoid} :
  (X ⇒ Y) → PolyObj B X ⇒ PolyObj B Y.

  intro f. apply (Build_setoidmap _ _ (PolyArr_fnc B f)).
  intros F F' H. set (a := projT1 F). set (h := projT2 F : B a ⇒ X).
  set (a' := projT1 F'). set (h' := projT2 F' : B a' ⇒ X).
  simpl. exists (projT1 H). intro b.
  apply setoidmapextensionality. apply (projT2 H).
Defined.


(* Section 3.1 *)

(*------------------------------*)
(* Underlying type of W-setoids *)
(*------------------------------*)

Definition WstdObj {A : setoid}(B : setoidfamily A) : Set :=
  Wty (setoidfamilyobj A B).

Definition WstdObjIndex {A : setoid}(B : setoidfamily A) : WstdObj B → A :=
  WtyIndex (setoidfamilyobj A B).

Definition WstdObjBranches {A : setoid}(B : setoidfamily A)(w : WstdObj B) :
           B (WstdObjIndex B w) → WstdObj B :=
  WtyBranches (setoidfamilyobj A B) w.


(*-----------------------------------------------------*)
(* Partial equivalence relation from dependent W-types *)
(*-----------------------------------------------------*)

Definition WstdPER_aux {A : setoid}(B : setoidfamily A) :
  (WstdObj B) ∧ (WstdObj B) → Set :=
  @DWty ((WstdObj B) ∧ (WstdObj B))
        (λ z : WstdObj B ∧ WstdObj B,
               WstdObjIndex B (fst z) ≈,{A} WstdObjIndex B (snd z))
        (λ (z : WstdObj B ∧ WstdObj B)
           (p : WstdObjIndex B (fst z) ≈,{A} WstdObjIndex B (snd z)),
         TotStdfamEq B p)
        (λ (z : WstdObj B ∧ WstdObj B)
           (p : WstdObjIndex B (fst z) ≈,{A} WstdObjIndex B (snd z))
           (v : TotStdfamEq B p),
         (WstdObjBranches B (fst z) (Unpack1 B p v),
          WstdObjBranches B (snd z) (Unpack2 B p v))).

Definition WstdPER {A : setoid}(B : setoidfamily A) :
  WstdObj B → WstdObj B → Set :=
  λ w w', WstdPER_aux B (w , w').


Definition isMatch {A : setoid}{B : setoidfamily A}{w w' : WstdObj B}
           (p : WstdObjIndex B w ≈ WstdObjIndex B w')
           (df : ∀ b b', b ≈[p] b' →
               WstdPER B (WstdObjBranches B w b)
                         (WstdObjBranches B w' b'))
  : WstdPER B w w'.

  apply (supd (λ (z : WstdObj B ∧ WstdObj B)
                 (p : WstdObjIndex B (fst z) ≈,{A} WstdObjIndex B (snd z)),
               TotStdfamEq B p)
              (λ (z : WstdObj B ∧ WstdObj B)
                 (p : WstdObjIndex B (fst z) ≈,{A} WstdObjIndex B (snd z))
                 (v : TotStdfamEq B p),
               (WstdObjBranches B (fst z) (Unpack1 B p v),
                WstdObjBranches B (snd z) (Unpack2 B p v)))
              (w , w') p).
  simpl. intro v. apply (df (Unpack1 B p v) (Unpack2 B p v) (UnpackEq B p v)).
Defined.


Definition WstdPER_Indices {A : setoid}(B : setoidfamily A)
           (w w' : WstdObj B) :
  WstdPER B w w' → WstdObjIndex B w ≈ WstdObjIndex B w' :=
  DWtyIndex _ _ (w , w').

Definition WstdPER_Branches {A : setoid}(B : setoidfamily A)
           (w w' : WstdObj B)
           (r : WstdPER B w w') :
  ∀ b b', b ≈[WstdPER_Indices B w w' r] b' →
          WstdPER B (WstdObjBranches B w b) (WstdObjBranches B w' b') :=
  λ b b' q, DWtyBranches _ _ (w , w') r (PackTotEq _ _ b b' q).


(*---------------------------*)
(* Symmetry and transitivity *)
(*---------------------------*)

(* Proposition 3.2 - Start *)

Lemma WstdPER_aux_symm {A : setoid}(B : setoidfamily A) :
  ∀ z, WstdPER_aux B z → WstdPER_aux B (snd z , fst z).
Proof.
  intros z r. induction r as [z p feq IH].
  assert (g : (∀ v : TotStdfamEq B (p ˢ),
             WstdPER_aux B (WstdObjBranches B (snd z) (Unpack1 B _ v),
                            WstdObjBranches B (fst z) (Unpack2 B _ v)) )).
  intro v. set (b' := Unpack1 B _ v). set (b := Unpack2 B _ v). set (q := UnpackEq B _ v).
  set (v' := PackTotEq B p b b' (EqRelOverIsIrr _ _ _ _ _ p _ _
                                         (EqRelOverIsSymm _ _ _ _ (p ˢ) _ _ q))).
  apply (IH v').
  apply (supd _ _ (snd z , fst z) p ˢ g).
Qed.

Lemma WstdPER_symm {A : setoid}(B : setoidfamily A) :
  ∀ w w', WstdPER B w w' → WstdPER B w' w.
Proof.
  intros w w'. apply WstdPER_aux_symm.
Qed.

Lemma WstdPER_aux_trans {A : setoid}(B : setoidfamily A) :
  ∀ z, WstdPER_aux B z →
       (∀ w, WstdPER B w (fst z) → WstdPER_aux B (w , snd z)).
Proof.
  intros z r. induction r as [z p' feq' IH].
  intros w r1. set (p := WstdPER_Indices B w (fst z) r1).
  set (feq := WstdPER_Branches B w (fst z) r1).
  apply supd with (i := (w , snd z))
                  (a := p'⊙p).
  intro vv. set (b := Unpack1 B _ vv). set (b' := Unpack2 B _ vv). set (q := UnpackEq B _ vv).
  simpl in *|-. simpl.
  specialize IH with (w := WstdObjBranches B w b).
  specialize (feq b (B•p b) (setoidrefl _ _)).
  set (v' := PackTotEq B p' (B•p b) b' (q⊙(setoidfamilycmpgeneral B _ _ _ p p' (p'⊙p) b))).
  specialize (feq' v'). specialize (IH v'). simpl in *|-.
  apply (IH feq).
Qed.

Lemma WstdPER_trans {A : setoid}(B : setoidfamily A) :
  ∀ w w' w'', WstdPER B w w' → WstdPER B w' w'' → WstdPER B w w''.
Proof.
  intros w w' w'' r r'. apply (WstdPER_aux_trans B (w', w'') r' w r).
Qed.

(* Proposition 3.2 - End *)


(*-----------*)
(* W-setoids *)
(*-----------*)

Definition WstdBase {A : setoid}(B : setoidfamily A) : Set :=
  ∃ w, WstdPER B w w.

Definition WstdEq {A : setoid}(B : setoidfamily A) :
  WstdBase B → WstdBase B → Set :=
  λ u u', WstdPER B (projT1 u) (projT1 u').

Definition Wstd {A : setoid}(B : setoidfamily A) : setoid.
  
  apply (Build_setoid (WstdBase B) (WstdEq B)).
  apply Build_setoidaxioms.
  intro u. apply (projT2 u).
  intros u u' r. apply WstdPER_symm. apply r.
  intros u u' u'' r r'. apply WstdPER_trans with (w' := projT1 u'). apply r. apply r'.
Defined.

Definition WstdSup {A : setoid}(B : setoidfamily A)
           (a : A)(f : B a → WstdObj B) :
  (∀ b b', b ≈ b' → WstdPER_aux B (f b,f b') ) → Wstd B.

  intro ext. exists (sup _ a f).
  apply supd with
      (d := λ z p v,
            (WstdObjBranches B (fst z) (Unpack1 B p v),
             WstdObjBranches B (snd z) (Unpack2 B p v)))
      (a0 := setoidrefl A a).
  intro v. set (b := Unpack1 B _ v). set (b' := Unpack2 B _ v). set (q := UnpackEq B _ v).
  simpl in *|-. simpl.
  apply (ext b b').
  apply setoidfamilyrefgeneral_tactical_rev with (p := setoidrefl _ a).
  apply q.
Defined.

Definition WstdIndex {A : setoid}(B : setoidfamily A) : Wstd B ⇒ A.
  
  apply (Build_setoidmap _ _ (λ u : Wstd B, WstdObjIndex _ (projT1 u))).
  intros u u' r. apply WstdPER_Indices. apply r.
Defined.

Definition WstdBranches_fnct {A : setoid}(B : setoidfamily A)(u : Wstd B) :
  B (WstdIndex B u) → Wstd B.
  
  intro b. exists (WstdObjBranches _ (projT1 u) b).
  apply WstdPER_Branches with (r := projT2 u).
  apply setoidfamilyrefgeneral.
Defined.

Definition WstdBranches {A : setoid}(B : setoidfamily A)(u : Wstd B) :
  B (WstdIndex B u) ⇒ Wstd B.
  
  apply (Build_setoidmap _ _ (WstdBranches_fnct B u)).
  intros b b' q. apply WstdPER_Branches with (r := projT2 u).
  apply setoidfamilyrefgeneral_tactical.
  apply q.
Defined.

(*WstdBranchesEq is called extb in the paper *)

Definition WstdBranchesEq {A : setoid}(B : setoidfamily A)
      {u u' : Wstd B}(r : u ≈ u') :
  WstdBranches B u ≈ (WstdBranches B u') ∘ (B•((WstdIndex B) ↱ r)).
Proof.
  intro b.
  apply (WstdPER_Branches B (projT1 u) (projT1 u') r). apply setoidrefl.
Defined.

Definition WstdBranchesEq_rev {A : setoid}(B : setoidfamily A)
      {u u' : Wstd B}(r : u ≈ u') :
  (WstdBranches B u') ∘ (B•((WstdIndex B) ↱ r)) ≈ WstdBranches B u.
Proof.
  apply setoidsym. apply WstdBranchesEq.
Defined.

Lemma WstdBranchesEq_tactical {A : setoid}(B : setoidfamily A){u u' : Wstd B}(r : u ≈ u') :
  ∀ b₁ b₂, WstdBranches B u b₁ ≈ WstdBranches B u b₂
           → WstdBranches B u' (B•((WstdIndex B) ↱ r) b₁) ≈ WstdBranches B u' (B•((WstdIndex B) ↱ r) b₂).
Proof.
  intros b₁ b₂ q.
  apply setoidtra with (y := WstdBranches B u b₁). apply WstdBranchesEq_rev.
  apply setoidtra with (y := WstdBranches B u b₂). apply q. apply WstdBranchesEq.
Qed.

Lemma WstdBranchesEqInv {A : setoid}(B : setoidfamily A)
      (u u' : Wstd B)(r : u ≈ u') :
  (WstdBranches B u) ∘ (B•((WstdIndex B) ↱ r ˢ)) ≈ (WstdBranches B u').
Proof.
  apply setoidtra with
      (y := (WstdBranches B u') ∘ (B•((WstdIndex B) ↱ r))
                                ∘ (B•((WstdIndex B) ↱ r ˢ))).
  intro b. apply (WstdBranchesEq B r).
  intro b. apply (setoidmapextensionality _ _ (WstdBranches B u')).
  apply setoidfamilycmpinvert.
Qed.

(* The following is (one direction of) Lemma 3.3 *)

Lemma WstdEqChar {A : setoid}(B : setoidfamily A)(w w' : Wstd B)
      (p : WstdIndex B w ≈ WstdIndex B w') :
  (∀ b, WstdBranches B w b ≈ WstdBranches B w' (B•p b)) → w ≈ w'.
Proof.
  intro r. apply supd with (i := (projT1 w, projT1 w'))
                           (a := p).
  intro v. set (b := Unpack1 B _ v). set (b' := Unpack2 B _ v).
  set (q := UnpackEq B _ v : b ≈[_] b').
  simpl in b. simpl in b'. simpl.
  apply ((WstdBranches B w' ↱ q) ⊙ (r b)).
Qed.


(*--------------------------------------*)
(* Algebra and coalgebra structure maps *)
(*--------------------------------------*)

(* Lemma 3.4 *)

Definition SupFnc {A : setoid}(B : setoidfamily A) :
  PolyObj B (Wstd B) → Wstd B.

  intros F. set (a := projT1 F). set (h := projT2 F : B a ⇒ Wstd B).
  set (f := λ y, projT1 (h y)). refine (existT _ (sup _ a f) _).
  apply supd with (i := (sup _ a f, sup _ a f)) (a0 := setoidrefl _ a).
  intro v. set (b := Unpack1 B _ v). set (b' := Unpack2 B _ v). set (q := UnpackEq B _ v : b ≈[_] b').
  simpl in * |-. simpl.
  apply (setoidmapextensionality _ _ h).
  apply setoidfamilyrefgeneral_tactical_rev with (p := setoidrefl A a).
  apply q.
Defined.

(* Lemma 3.5 *)

Definition SupMap {A : setoid}(B : setoidfamily A) :
  PolyObj B (Wstd B) ⇒ Wstd B.

  apply (Build_setoidmap _ _ (SupFnc B)).
  intros F F' H. set (a := projT1 F). set (h := projT2 F : B a ⇒ Wstd B).
  set (a' := projT1 F'). set (h' := projT2 F' : B a' ⇒ Wstd B).
  apply WstdEqChar with (p := projT1 H).
  apply (projT2 H).
Defined.

(* Proposition 3.6 - Start *)

Definition UnsupFnc {A : setoid}(B : setoidfamily A) :
  Wstd B → PolyObj B (Wstd B).
  
  intro u. exists (WstdIndex _ u).
  apply (Build_setoidmap _ _ (WstdBranches B u)).
  intros b b' q. apply setoidmapextensionality. apply q.
Defined.

Definition UnsupMap {A : setoid}(B : setoidfamily A) :
  Wstd B ⇒ PolyObj B (Wstd B).
  
  apply (Build_setoidmap _ _ (UnsupFnc B)).
  intros u u' r. simpl. exists (WstdIndex B ↱ r).
  apply (WstdBranchesEq B r).
Defined.


(*--------------------------------------------------*)
(* Wsetoids are fixed points of polynomial functors *)
(*--------------------------------------------------*)

Theorem SupUnsup2Id {A : setoid}(B : setoidfamily A) :
  (SupMap B) ∘ (UnsupMap B) ≈ idmap.
Proof.
  intro u. set (a := WstdIndex B u). set (f := WstdBranches B u).
  set (p := setoidrefl _ a : WstdIndex B (SupMap B (UnsupMap B u)) ≈ a).
  apply WstdEqChar with (p0 := p).
  intro b. apply (setoidmapextensionality _ _ (WstdBranches B u)).
  apply setoidfamilyrefgeneralinv.
Qed.

Theorem UnsupSup2Id {A : setoid}(B : setoidfamily A) :
  (UnsupMap B) ∘ (SupMap B) ≈ idmap.
Proof.
  intro F. set (a := projT1 F). set (h := projT2 F : B a ⇒ Wstd B).
  simpl. exists (setoidrefl A a). intro b.
  apply (setoidmapextensionality _ _ h). apply setoidfamilyrefgeneralinv.
Qed.

(* Proposition 3.6 - End *)


(* Section 3.2 *)

(*------------------------------*)
(* Family of immediate subtrees *)
(*------------------------------*)

(* Definition 3.7 - Start *)

Definition ImSubtree_std {A : setoid}(B : setoidfamily A)(u : Wstd B) : setoid.

  apply (Build_setoid (B (WstdIndex B u))
                      (λ b b', WstdBranches B u b ≈ WstdBranches B u b')).
  apply Build_setoidaxioms.
  intro b. apply setoidrefl.
  intros b b'. apply setoidsym.
  intros b b' b''. apply setoidtra.
Defined.

Definition ImSubtree_fnc {A : setoid}(B : setoidfamily A)(u u' : Wstd B) :
  u ≈ u' → ImSubtree_std B u → ImSubtree_std B u' :=
  λ r, B•(WstdIndex B ↱ r).

Definition ImSubtree_map {A : setoid}(B : setoidfamily A)(u u' : Wstd B) :
  u ≈ u' → ImSubtree_std B u ⇒ ImSubtree_std B u'.

  intro r. apply (Build_setoidmap _ _ (ImSubtree_fnc B u u' r)).
  intros s s' q. unfold ImSubtree_fnc.
  apply WstdBranchesEq_tactical. apply q.
Defined.

Definition ImSubtree {A : setoid}(B : setoidfamily A) : setoidfamily (Wstd B).

  apply (Build_setoidfamily (Wstd B) (ImSubtree_std B) (ImSubtree_map B)).
  apply Build_setoidfamilyaxioms.
  intros u s. apply setoidmapextensionality. apply setoidfamilyrefgeneral.
  intros u u' r r' s. apply (setoidmapextensionality _ _ (WstdBranches B u')).
  apply setoidfamilyirr.
  intros u u' u'' r r' s. apply (setoidmapextensionality _ _ (WstdBranches B u'')).
  apply setoidfamilycmpgeneral.
Defined.

(* Definition 3.7 - End *)

(* CanEpi B u is denoted eᵤ in the paper *)

Definition CanEpi {A : setoid}(B : setoidfamily A)(u : Wstd B) :
  B (WstdIndex B u) ⇒ ImSubtree_std B u.

  apply (Build_setoidmap (B (WstdIndex B u)) (ImSubtree_std B u) (λ b, b)).
  intros b b' q. apply setoidmapextensionality. apply q.
Defined.

(* ImSubtree2Tree B u is denoted mᵤ in the paper  *)

Definition ImSubtree2Tree {A : setoid}(B : setoidfamily A)(u : Wstd B) :
  ImSubtree B u ⇒ Wstd B.

  apply (Build_setoidmap _ _ (λ b : ImSubtree B u, WstdBranches B u b)).
  intros b b' q. apply q.
Defined.

(* A couple of useful functions. *)

Definition ImSubtreeIndex {A : setoid}(B : setoidfamily A)(u : Wstd B) :
  ImSubtree B u ⇒ A :=
  (WstdIndex B) ∘ (ImSubtree2Tree B u).


Lemma ImSubtreeIndexEq {A : setoid}(B : setoidfamily A)
      {u u' : Wstd B}(r : u ≈ u') :
  ImSubtreeIndex B u ≈ (ImSubtreeIndex B u') ∘ ((ImSubtree B)•r).
Proof.
  intro b. unfold ImSubtreeIndex.
  apply (setoidmapextensionality _ _ (WstdIndex B)). apply WstdBranchesEq.
Qed.


(*-------------------------------------------------*)
(* Coherent families of maps on immediate subtrees *)
(*-------------------------------------------------*)

(* Definition 3.8 - Start *)

Definition isCohFam {A : setoid}(B : setoidfamily A)(X : setoid)(u : Wstd B)
           (F : (∀ s : ImSubtree B u,
                    ImSubtree B (ImSubtree2Tree B u s) ⇒ X)) : Set :=
  (∀ s s' : ImSubtree B u, ∀ q : s ≈ s',
        (F s) ≈ (F s') ∘ ((ImSubtree B)•q)).

Definition CohFam_std {A : setoid}(B : setoidfamily A)(X : setoid)(u : Wstd B) : setoid.

  apply (Build_setoid (sigT (λ F, isCohFam B X u F)) (λ CF CF', ∀ s, projT1 CF s ≈ projT1 CF' s)).
  apply Build_setoidaxioms.
  intros F s. apply setoidrefl.
  intros F F' H s. apply setoidsym. apply H.
  intros F F' F'' H H' s. apply setoidtra with (y := projT1 F' s). apply H. apply H'.
Defined.

Definition CohFam_fnc {A : setoid}(B : setoidfamily A)(X : setoid){u u' : Wstd B} :
  u ≈ u' → CohFam_std B X u → CohFam_std B X u'.

  intros r CF. set (F := projT1 CF). set (C := projT2 CF : isCohFam B X u F). simpl in C. simpl.
  set (F' := λ s', (F ((ImSubtree B)•(r ˢ) s')) ∘ ((ImSubtree B)•(WstdBranchesEq B (r ˢ) s'))).
  exists F'.
  intros s'₁ s'₂ q' ss'. unfold F'.
  set (s₁ := (ImSubtree B)•r ˢ s'₁). set (s₂ := (ImSubtree B)•r ˢ s'₂). set (q := (ImSubtree B)•r ˢ ↱ q' : s₁ ≈ s₂).
  set (ss := (ImSubtree B)•(WstdBranchesEq B (r ˢ) s'₁) ss').
  
  specialize (C s₁ s₂ q ss).
  refine ( _ ⊙ C).
  apply (setoidmapextensionality _ _ (F s₂)).
  assert ( H1 : (ImSubtree B)•q ss ≈ (ImSubtree B)•(q ⊙ (WstdBranchesEq B (r ˢ) s'₁)) ss' ).
  apply setoidfamilycmpgeneral.
  refine (_ ⊙ H1).
  assert ( H2 : (ImSubtree B)•(WstdBranchesEq B (r ˢ) s'₂ ⊙ (ImSubtree2Tree B u' ↱ q')) ss'
                        ≈ (ImSubtree B)•(WstdBranchesEq B (r ˢ) s'₂) ((ImSubtree B)•q' ss')).
  apply setoidsym, setoidfamilycmpgeneral.
  refine (H2 ⊙ _).
  apply setoidfamilyirr.
Defined.

Definition CohFam_map {A : setoid}(B : setoidfamily A)(X : setoid)(u u' : Wstd B) :
  u ≈ u' → CohFam_std B X u ⇒ CohFam_std B X u'.

  intro r. apply (Build_setoidmap _ _ (CohFam_fnc B X r)).
  intros CF CF' R. intros s' ss'. apply (R ((ImSubtree B)•(r ˢ) s')).
Defined.

Definition CohFam {A : setoid}(B : setoidfamily A)(X : setoid) : setoidfamily (Wstd B).

  apply (Build_setoidfamily (Wstd B) (CohFam_std B X) (CohFam_map B X)).
  apply Build_setoidfamilyaxioms.
  intros u CF s. set (F := projT1 CF). set (C := λ s₁ s₂ q, (projT2 CF s₁ s₂ q) ˢ). apply C.
  
  intros u u' r r' CF s' ss'. set (F := projT1 CF).
  assert (q : ((ImSubtree B)•(r ˢ) s') ≈ ((ImSubtree B)•(r' ˢ) s')). apply setoidfamilyirr.
  apply setoidtra with (y := F ((ImSubtree B)•(r' ˢ) s') ∘ ((ImSubtree B)•q) ((ImSubtree B)•(WstdBranchesEq B (r ˢ) s') ss') ).
  apply (projT2 CF _ _ q).
  apply (setoidmapextensionality _ _ (F ((ImSubtree B)•(r' ˢ) s'))).
  apply setoidfamilycmpgeneral.
  
  intros u u' u'' r₁ r₂ CF s'' ss''. set (F := projT1 CF).
  assert (q : (ImSubtree B)•r₁ ˢ ((ImSubtree B)•r₂ ˢ s'') ≈ (ImSubtree B)•((r₂ ⊙ r₁) ˢ) s'').
  apply setoidfamilycmpgeneral.
  apply setoidtra with (y := F ((ImSubtree B)•((r₂ ⊙ r₁) ˢ) s'') ∘ ((ImSubtree B)•q)
                               ((ImSubtree B)•(WstdBranchesEq B (r₁ ˢ) ((ImSubtree B)•r₂ ˢ s''))
                                             ((ImSubtree B)•(WstdBranchesEq B (r₂ ˢ) s'') ss'')) ).
  apply (projT2 CF _ _ q).
  apply (setoidmapextensionality _ _ (F ((ImSubtree B) • (r₂ ⊙ r₁) ˢ s''))).

  set (M := (ImSubtree B)•q ((ImSubtree B)•( (WstdBranchesEq B r₁ ˢ ((ImSubtree B) • r₂ ˢ s''))
                                                                ⊙ (WstdBranchesEq B r₂ ˢ s'') )
                                          ss'')).
  assert (H1 : (ImSubtree B) • q ((ImSubtree B) • (WstdBranchesEq B r₁ ˢ ((ImSubtree B) • r₂ ˢ s''))
                                                ((ImSubtree B) • (WstdBranchesEq B r₂ ˢ s'') ss''))
                             ≈ M).
  apply setoidmapextensionality, setoidfamilycmpgeneral.
  assert (H2 : M ≈ (ImSubtree B) • (WstdBranchesEq B (r₂ ⊙ r₁) ˢ s'') ss'').
  apply setoidfamilycmpgeneral.
  apply (H2 ⊙ H1).
Defined.

Lemma CohFamEqChar {A : setoid}(B : setoidfamily A)(X : setoid)
      {u u' : Wstd B}(r : u ≈ u'){CF : CohFam B X u}{CF' : CohFam B X u'} :
  CF ≈[r] CF' → ∀ s, projT1 CF s
                            ≈ projT1 CF' ((ImSubtree B)•r s) ∘ (ImSubtree B)•(WstdBranchesEq B r s).
Proof.
  intros H s.
  apply setoidtra with ( y := projT1 CF ((ImSubtree B)•r ˢ ((ImSubtree B)•r s))
                                     ∘ (ImSubtree B)•((WstdBranchesEq B (r ˢ) ((ImSubtree B)•r s)) ⊙ (WstdBranchesEq B r s)) ).
  apply (projT2 CF).
  apply setoidtra with ( y := projT1 CF ((ImSubtree B)•r ˢ ((ImSubtree B)•r s))
                                     ∘ (ImSubtree B)•(WstdBranchesEq B (r ˢ) ((ImSubtree B)•r s))
                                     ∘ (ImSubtree B)•(WstdBranchesEq B r s) ).
  intro ss.
  apply (setoidmapextensionality _ _ (projT1 CF ((ImSubtree B) • r ˢ ((ImSubtree B) • r s)))).
  apply setoidsym, setoidfamilycmpgeneral.
  intro ss. apply (H ((ImSubtree B)•r s)).
Qed.

(* Definition 3.8 - End *)


(*---------------------------------------------------*)
(* One step extension from a coherent family of maps *)
(*---------------------------------------------------*)

(* Lemma 3.9 - Start *)

(* RecStep B algX u CF s = algX (Index s, λ b.(CF s)∘(CanEpi s) b) *)

Definition RecStep_fnc {A : setoid}(B : setoidfamily A)
           {X : setoid}(algX : PolyObj B X ⇒ X)
           (u : Wstd B)(CF : CohFam B X u) :
  ImSubtree B u → X :=
  λ s, algX ( existT _ (ImSubtreeIndex B u s) ((projT1 CF s) ∘ (CanEpi B (ImSubtree2Tree B u s))) ).

Definition RecStep {A : setoid}(B : setoidfamily A)
           {X : setoid}(algX : PolyObj B X ⇒ X)
           (u : Wstd B)(CF : CohFam B X u) :
  ImSubtree B u ⇒ X.

  apply (Build_setoidmap _ _ (RecStep_fnc B algX u CF)).
  intros s₁ s₂ q. apply setoidmapextensionality. simpl.
  exists (ImSubtreeIndex B u ↱ q). intro b.
  apply (projT2 CF).
Defined.

Lemma RecStepEq {A : setoid}(B : setoidfamily A){X : setoid}(algX : PolyObj B X ⇒ X)
      {u u' : Wstd B}(r : u ≈ u'){CF : CohFam B X u}{CF' : CohFam B X u'} :
  CF ≈[r] CF' → RecStep B algX u CF ≈ RecStep B algX u' CF' ∘ (ImSubtree B)•r.
Proof.
  intros H s. apply (setoidmapextensionality _ _ algX). simpl.
  exists (ImSubtreeIndexEq B r s).
  intro b.
  set (C := projT2 CF). simpl in C. unfold isCohFam in C.
  set (H' := CohFamEqChar B X r H).
  refine (_ ⊙ (H' s b)).
  apply (setoidmapextensionality _ _ (projT1 CF' ((ImSubtree B) • r s))).
  apply (setoidmapextensionality _ _ (CanEpi B _)), setoidfamilyirr.
Qed.

Lemma RecStepEqRefl {A : setoid}(B : setoidfamily A){X : setoid}(algX : PolyObj B X ⇒ X)
      {u : Wstd B}{CF : CohFam B X u}{CF' : CohFam B X u} :
  CF ≈ CF' → RecStep B algX u CF ≈ RecStep B algX u CF'.
Proof.
  intros H.
  apply setoidtra with (y := RecStep B algX u CF' ∘ (ImSubtree B)•(setoidrefl _ u)).
  apply RecStepEq. apply setoidfamilyrefgeneral_tactical. apply H.
  intro s. apply (setoidmapextensionality _ _ (RecStep B algX u CF')).
  apply setoidfamilyref.
Qed.

(* Lemma 3.9 - End *)


(* Section 3.3 *)

(*----------------------------------*)
(* Type of recursively defined maps *)
(*----------------------------------*)

(*
Canonical element of "RecDef B X algX (u,k)":
u : Wstd B.
k : ImSubtree B u ⇒ X.
CF : CohFam B X u = Σ (F : ∀ s, ImSubtree B s ⇒ X), isCohFam B X u F.
e : k ≈ RecStep B algX u CF.
brRD : (s : ImSubtree B u) → RecDef B X (WstdBranches B u s, CF s)
*)

Definition RecDef {A : setoid}(B : setoidfamily A)
           {X : setoid}(algX : PolyObj B X ⇒ X) :
  (∃ u : Wstd B, ImSubtree B u ⇒ X) → Set :=
  @DWty (∃ u : Wstd B, ImSubtree B u ⇒ X)
        (λ z, ∃ CF : CohFam B X (projT1 z),
            projT2 z ≈ RecStep B algX (projT1 z) CF)
        (λ z C, ImSubtree B (projT1 z))
        (λ z C s, existT _ (ImSubtree2Tree B (projT1 z) s)
                         (projT1 (projT1 C) s)).

Definition RecDefFam {A : setoid}(B : setoidfamily A)
           {X : setoid}(algX : PolyObj B X ⇒ X)
           (u : Wstd B)(k : ImSubtree B u ⇒ X) :
  RecDef B algX (existT _ u k) → CohFam B X u := λ d, projT1 (DWtyIndex _ _ (existT _ u k) d).

Definition RecDefEq {A : setoid}(B : setoidfamily A)
           {X : setoid}(algX : PolyObj B X ⇒ X)
           (u : Wstd B)(k : ImSubtree B u ⇒ X)
           (D : RecDef B algX (existT _ u k)) :
  k ≈ RecStep B algX u (RecDefFam B algX u k D) := projT2 (DWtyIndex _ _ (existT _ u k) D).

Definition RecDefBranches {A : setoid}(B : setoidfamily A)
           {X : setoid}(algX : PolyObj B X ⇒ X)
           (u : Wstd B)(k : ImSubtree B u ⇒ X)
           (D : RecDef B algX (existT _ u k)) :
  ∀ s : ImSubtree B u,
    RecDef B algX (existT _ (ImSubtree2Tree B u s)
                          (projT1 (RecDefFam B algX u k D) s)) := DWtyBranches _ _ (existT _ u k) D.

(* Lemma 3.10 *)

Definition RecDefTransp  {A : setoid}(B : setoidfamily A)
        {X : setoid}(algX : PolyObj B X ⇒ X)
        (z : ∃ u : Wstd B, ImSubtree B u ⇒ X) :
  RecDef B algX z →
  ∀ u', ∀ r' : u' ≈ projT1 z,
      RecDef B algX (existT _ u' ((projT2 z) ∘ (ImSubtree B)•r')).

  intro D. induction D as [z RD br IH]. set (u := projT1 z).
  set (CF := projT1 RD : CohFam B X u). set (k := projT2 z : ImSubtree B (projT1 z) ⇒ X).
  intros u' r.
  set (CF' := (CohFam B X)•r ˢ CF).
  assert (H : k ∘ ((ImSubtree B)•r) ≈ RecStep B algX u' CF').
  set (e1 := (λ s, (projT2 RD) ((ImSubtree B)•r s)) :
               k ∘ ((ImSubtree B)•r) ≈ (RecStep B algX u (projT1 RD)) ∘ (ImSubtree B) • r).
  refine (_ ⊙ e1).
  apply setoidtra with (y := ((RecStep B algX u' CF') ∘ (ImSubtree B)•r ˢ) ∘ (ImSubtree B)•r).
  intro ss'. apply RecStepEq with (r0 := r ˢ). apply setoidrefl.
  apply setoidmaprid_tactical with (f := RecStep B algX u' CF')
                                   (h := (ImSubtree B)•r ˢ ∘ (ImSubtree B)•r).
  intro ss'. apply setoidfamilycmpinvert.
  apply supd with (a := existT _ CF' H).
  intro s'. set (r' := r ˢ).
  specialize IH with (b := (ImSubtree B)•r' ˢ s')
                     (u' := ImSubtree2Tree B u' s')
                     (r' := WstdBranchesEq B r' ˢ s').
  apply IH.
Defined.

(* Lemma 3.11 - stated to use induction in the proof *)

Lemma RecDefUniq {A : setoid}(B : setoidfamily A)
        {X : setoid}(algX : PolyObj B X ⇒ X) :
  ∀ z : ∃ u : Wstd B, ImSubtree B u ⇒ X,
       RecDef B algX z
       → (∀ k, RecDef B algX (existT _ (projT1 z) k) → k ≈ projT2 z).
Proof.
  intros z d. induction d as [z RS ind IH]. set (u := projT1 z).
  intros k d.
  apply setoidtra with
      (y := RecStep B algX u (RecDefFam B algX u k d)).
  apply RecDefEq.
  apply setoidtra with
      (y := RecStep B algX u (projT1 RS)).
  apply RecStepEqRefl.
  intro s. apply IH, RecDefBranches.
  apply setoidsym, (projT2 RS).  
Qed.

(* Proposition 3.12 *)

Theorem RecDefUniqGen {A : setoid}(B : setoidfamily A)
        {X : setoid}(algX : PolyObj B X ⇒ X)
        {u u' : Wstd B}(r : u ≈ u')
        (k : ImSubtree B u ⇒ X)(k' : ImSubtree B u' ⇒ X) :
  RecDef B algX (existT _ u k) →
  RecDef B algX (existT _ u' k') → k ≈ k' ∘ (ImSubtree B)•r.
Proof.
  intros d d'.
  assert (RecDef B algX (existT _ u (k' ∘ (ImSubtree B)•r))).
  apply RecDefTransp with (z := existT _ u' k'). apply d'.
  apply (RecDefUniq B algX (existT _ u (k' ∘ (ImSubtree B)•r)) H k d).
Qed.

Theorem RecDefUniqGenInv {A : setoid}(B : setoidfamily A)
        {X : setoid}(algX : PolyObj B X ⇒ X)
        {u u' : Wstd B}(r : u ≈ u')
        (k : ImSubtree B u ⇒ X)(k' : ImSubtree B u' ⇒ X) :
  RecDef B algX (existT _ u k) →
  RecDef B algX (existT _ u' k') → k ∘ (ImSubtree B)•r ˢ ≈ k'.
Proof.
  intros d d'. apply setoidtra with (y := k' ∘ ((ImSubtree B)•r ∘ (ImSubtree B)•r ˢ)).
  intro s'. apply (RecDefUniqGen B algX r k k' d d' ((ImSubtree B)•r ˢ s')).
  apply setoidmaprid_tactical with (f := k'). intro s'. apply setoidfamilycmpinvert.
Qed.

(* Lemma 3.11 - stated as in the paper *)

Theorem RecDefUniqGenRef {A : setoid}(B : setoidfamily A)
        {X : setoid}(algX : PolyObj B X ⇒ X)
        (u : Wstd B)(k k' : ImSubtree B u ⇒ X) :
  RecDef B algX (existT _ u k) →
  RecDef B algX (existT _ u k') → k ≈ k'.
Proof.
  intros d d'.
  apply (RecDefUniq B algX (existT _ u k') d' k d).
Qed.


(*
Now we can do recursion on the underlying Wty using RecStep as the recursive step.
*)

(* Proposition 3.13 *)

Definition RecImS {A : setoid}(B : setoidfamily A){X : setoid}
           (algX : PolyObj B X ⇒ X)(u : Wstd B) :
  ∃ k : ImSubtree B u ⇒ X,
    RecDef B algX (existT _ u k).

  destruct u as [w refl]. induction w as [a f IH].
  set (w := sup _ a f).
  set (u := existT (λ x, WstdPER B x x) w refl).
  set (F := λ s, projT1 (IH s (setoidrefl (ImSubtree B u) s))).
  set (D := λ s, projT2 (IH s (setoidrefl ((ImSubtree B) u) s))).

  (* Building up data for applying RecStep *)  
  assert (C : isCohFam B X u F).
  unfold isCohFam. intros s s' q.
  apply RecDefUniqGen with (algX0 := algX)
                           (u0 := (ImSubtree2Tree B u s))
                           (u' := (ImSubtree2Tree B u s'))
                           (r := q).
  apply (D s). apply (D s').
  set (CF := existT _ F C : CohFam B X u).

  exists (RecStep B algX u CF).
  apply supd with (a0 := existT _ CF
                                (setoidrefl _ (RecStep B algX u CF))).
  apply D.
Defined.


(* Section 3.4 *)

(*-------------------------------------------------------------------*)
(* Characterisation of algebra morphisms as recursively defined ones *)
(*-------------------------------------------------------------------*)

Definition AlgMor {A : setoid}(B : setoidfamily A)
           {X : setoid}(algX : PolyObj B X ⇒ X) : setoid.

  apply (Build_setoid (sigT (λ l : Wstd B ⇒ X, l ∘ (SupMap B) ≈ algX ∘ (PolyArr B l)))
                      (λ M M', projT1 M ≈ projT1 M')).
  apply Build_setoidaxioms.
  intro M. apply setoidrefl.
  intros M M' H. apply setoidsym, H.
  intros M M' M'' H H'.
  apply setoidtra with (y := projT1 M'). apply H. apply H'.
Defined.

Definition RecFam {A : setoid}(B : setoidfamily A)
           {X : setoid}(algX : PolyObj B X ⇒ X) : setoid.
  
  apply (Build_setoid (sigT (λ F : (∀ u, ImSubtree B u ⇒ X),
                                   ∀ u, RecDef B algX (existT _ u (F u))))
                      (λ RF RF', ∀ u, projT1 RF u ≈ projT1 RF' u)).
  apply Build_setoidaxioms.
  intros RF u. apply setoidrefl.
  intros RF RF' H u. apply setoidsym, H.
  intros RF RF' RF'' H H' u.
  apply setoidtra with (y := projT1 RF' u). apply H. apply H'.
Defined.

Lemma CommAlt {A : setoid}(B : setoidfamily A)
        (X : setoid)(algX : PolyObj B X ⇒ X)
        (l : Wstd B ⇒ X) :
  l ∘ (SupMap B) ≈ algX ∘ (PolyArr B l)
    ↔ l ≈ algX ∘ (PolyArr B l) ∘ (UnsupMap B).
Proof.
  split.

  intro H.
  apply setoidtra with
      (y := l ∘ (SupMap B) ∘ (UnsupMap B)).
  intro u'. apply (setoidmapextensionality _ _ l).
  apply setoidsym. apply SupUnsup2Id.
  intro u'. apply H.

  intro H'.
  apply setoidtra with
      (y := (algX ∘ (PolyArr B l)) ∘ (UnsupMap B) ∘ (SupMap B)).
  intro u. apply H'.
  intro z. apply (setoidmapextensionality _ _ algX).
  apply setoidmapextensionality.
  apply UnsupSup2Id.
Qed.


(*----------------------------------------------------------------------*)
(* The restriction family of an algebra morphism is recursively defined *)
(*----------------------------------------------------------------------*)

(*
RestImS B X l u is called l|ᵤ in the paper.
*)

Definition RestImS {A : setoid}(B : setoidfamily A)
           (X : setoid)(l : Wstd B ⇒ X)(u : Wstd B) :
  ImSubtree B u ⇒ X := l ∘ (ImSubtree2Tree B u).

Definition SubRestFam {A : setoid}(B : setoidfamily A)
        (X : setoid)(l : Wstd B ⇒ X)(u : Wstd B) :
  ∀ s : ImSubtree B u,
    ImSubtree B (ImSubtree2Tree B u s) ⇒ X := λ s, RestImS B X l (ImSubtree2Tree B u s).

Definition SubRestFamCoh {A : setoid}(B : setoidfamily A)
        (X : setoid)(l : Wstd B ⇒ X)(u : Wstd B) :
  CohFam B X u.

  exists (SubRestFam B X l u).
  intros s s' q. unfold SubRestFam. unfold RestImS.
  intro s0. apply (setoidmapextensionality _ _ l).
  apply WstdBranchesEq with (r := q).
Defined.

(* Lemma 3.14 *)

Lemma AlgMIsRD {A : setoid}(B : setoidfamily A)
      {X : setoid}(algX : PolyObj B X ⇒ X)
      (AM : AlgMor B algX) :
∀ u, RecDef B algX (existT _ u (RestImS B X (projT1 AM) u)).

Proof.
  intro u.
  destruct u as [w refl]. induction w as [a f IH].
  set (w := sup (setoidfamilyobj A B) a f).
  set (u := existT (λ z, WstdPER B z z) w refl).
  set (l := projT1 AM).
  
 (* Restriction is obtained from the family of subrestrictions *)
  assert (H : RestImS B X l u ≈
          RecStep B algX u (SubRestFamCoh B X l u)).
  intro b. simpl.  
  apply CommAlt with (l0 := l).
  apply (projT2 AM).

(* Hence restriction is recursively defined using IH *)
  apply supd with
      (a0 := existT _ (SubRestFamCoh B X l u) H).
  intro b. simpl in b. set (s := CanEpi B u b).
  apply (IH s (setoidrefl _ s)).
Qed.


(* AM2RF B algX is called rest in the paper *)

Definition AM2RF {A : setoid}(B : setoidfamily A)
           {X : setoid}(algX : PolyObj B X ⇒ X) :
  AlgMor B algX ⇒ RecFam B algX.

  set (fnc := (λ AM : AlgMor B algX, existT _ (λ u, RestImS B X (projT1 AM) u)
                                            (AlgMIsRD B algX AM))  :
                 AlgMor B algX → RecFam B algX).
  apply (Build_setoidmap _ _ fnc).
  intros M M' H u. simpl in H. simpl. apply (λ x, H (WstdBranches B u x)).
Defined.


(*---------------------------------------------------------------------*)
(* Families of recursively defined maps give rise to algebra morphisms *)
(*---------------------------------------------------------------------*)

(* RecFamMap B algX is called (a_C ∘ cmprh _) in the paper *)

Definition RecFamMap_fnc {A : setoid}(B : setoidfamily A)
      {X : setoid}(algX : PolyObj B X ⇒ X)
      (RF : RecFam B algX) :
  Wstd B → X := λ u, algX (existT _ (WstdIndex B u) (projT1 RF u ∘ (CanEpi B u))).

Definition RecFamMap {A : setoid}(B : setoidfamily A)
      {X : setoid}(algX : PolyObj B X ⇒ X)
      (RF : RecFam B algX) :
  Wstd B ⇒ X.

  set (F := λ u, projT1 RF u). set (R := λ u, projT2 RF u).
  apply (Build_setoidmap _ _ (RecFamMap_fnc B algX RF)).
  intros u u' r. apply setoidmapextensionality.
  exists (WstdIndex B ↱ r). intro b. set (s := CanEpi B u b).
  refine (RecDefUniqGen B algX r (F u) (F u') _ _ s).
  apply (R u). apply (R u').
Defined.

(* Next one is later used to prove that RecFamMap produces an algebra morphism.  *)

Lemma RecFamMapRest {A : setoid}(B : setoidfamily A)
      {X : setoid}(algX : PolyObj B X ⇒ X)
      (RF : RecFam B algX)(u : Wstd B) :
  projT1 RF u ≈ RecFamMap B algX RF ∘ (ImSubtree2Tree B u).

Proof.
  apply RecDefUniqGenRef with (algX0 :=algX).
  apply (projT2 RF u).
  
(* The following part is essentially Lemma 3.15 *)
  set (SF := λ s, projT1 RF (ImSubtree2Tree B u s)).
  assert (cohSF : isCohFam B X u SF).
  intros s₁ s₂ q. apply RecDefUniqGen with (algX0 := algX).
  apply (projT2 RF (ImSubtree2Tree B u s₁)). apply (projT2 RF (ImSubtree2Tree B u s₂)).
  apply supd with
      (a := existT (λ CF, RestImS B X (RecFamMap B algX RF) u
                                   ≈ RecStep B algX u CF)
                   (existT _ SF cohSF)
                   (λ _, setoidrefl _ _)).
  intro s. cbn in s. apply (projT2 RF (ImSubtree2Tree B u s)).
Qed.

Definition RF2AM_fnc {A : setoid}(B : setoidfamily A)
      {X : setoid}(algX : PolyObj B X ⇒ X) :
      RecFam B algX → AlgMor B algX.

  intro RF.
  set (F := projT1 RF). set (R := projT2 RF). set (k := RecFamMap B algX RF).
  exists k.
  apply CommAlt with (l := k). unfold k. intro u. simpl.
  apply (setoidmapextensionality _ _ algX).
  exists (setoidrefl _ (WstdIndex B u)).
  unfold PolyArr_fnc.

  cut (projT1 RF u ≈ RecFamMap B algX RF ∘ (ImSubtree2Tree B u)).
  intro H. intro b. set (s := CanEpi B u b). simpl in b.
  refine (_ ⊙ (H s)).
  apply setoidmapcmp_tactical with (f := (RecFamMap B algX RF)
                                           ∘ (ImSubtree2Tree B u ∘ (CanEpi B u)))
                                   (f' := (RecFamMap B algX RF)
                                            ∘ ((projT2 (UnsupFnc B u))))
                                   (g := idmap)
                                   (g' := B•(setoidrefl A ((WstdIndex B) u))).
  apply setoidrefl.
  apply setoidsym. intro bb. apply setoidfamilyref.

  apply RecFamMapRest.  
Defined.  

Definition RF2AM {A : setoid}(B : setoidfamily A)
      {X : setoid}(algX : PolyObj B X ⇒ X) :
  RecFam B algX ⇒ AlgMor B algX.

  apply (Build_setoidmap _ _ (RF2AM_fnc B algX)).
  intros RF RF' H. simpl. intro u. apply (setoidmapextensionality _ _ algX).
  simpl.
  exists (setoidrefl _ _). intro b.
  apply setoidmapcmp_tactical with (f := (projT1 RF u))
                                   (f' := (projT1 RF' u))
                                   (g := CanEpi B u)
                                   (g' := CanEpi B u ∘
                                                 B•(setoidrefl A (WstdObjIndex B (projT1 u)))).
  apply H. apply setoidsym. apply setoidmaprid_tactical.
  intro. apply setoidfamilyref.
Defined.


(*-------------------------------------------------------*)
(* Algebra maps ≅ families of recursively defined maps   *)
(*-------------------------------------------------------*)

(* Theorem 3.17 - Start *)

Theorem AM2RF2AMisId {A : setoid}(B : setoidfamily A)
        {X : setoid}(algX : PolyObj B X ⇒ X) :
  (RF2AM B algX) ∘ (AM2RF B algX) ≈ idmap.

Proof.
  intro M. set (l := projT1 M).
  apply setoidsym.  
  apply CommAlt with (l0 := l). apply (projT2 M).
Qed.

Theorem RF2AM2RFisId {A : setoid}(B : setoidfamily A)
      {X : setoid}(algX : PolyObj B X ⇒ X) :
  (AM2RF B algX) ∘ (RF2AM B algX) ≈ idmap.

Proof.
  intro RF. apply setoidsym. intro u.
  apply RecFamMapRest.
Qed.

(* Theorem 3.17 - End *)

Corollary AM2RFisInj {A : setoid}(B : setoidfamily A)
          {X : setoid}(algX : PolyObj B X ⇒ X)
          (M M' : AlgMor B algX) :
  AM2RF B algX M ≈ AM2RF B algX M' → M ≈ M'.

Proof.
  intro H.
  apply setoidtra with
      (y := RF2AM B algX (AM2RF B algX M)).
  apply setoidsym, (AM2RF2AMisId B algX M).
  apply setoidtra with
      (y := RF2AM B algX (AM2RF B algX M')).
  apply setoidmapextensionality, H.
  apply (AM2RF2AMisId B algX M').
Qed.


(* Section 3.5 *)

(*-------------*)
(* Initiality  *)
(*-------------*)

Definition initWmap {A : setoid}(B : setoidfamily A)
           {X : setoid}(algX : PolyObj B X ⇒ X) :
  Wstd B ⇒ X
  := RecFamMap B algX (existT (λ F, ∀ u, RecDef B algX (existT _ u (F u)))
                              (λ u, projT1 (RecImS B algX u))
                              (λ u, projT2 (RecImS B algX u))).

Lemma initWcomm {A : setoid}(B : setoidfamily A)
      {X : setoid}(algX : PolyObj B X ⇒ X) :
  (initWmap B algX) ∘ (SupMap B) ≈ algX ∘ (PolyArr B (initWmap B algX)).

Proof.
  apply (projT2 (RF2AM B algX (existT (λ F, ∀ u, RecDef B algX (existT _ u (F u)))
                              (λ u, projT1 (RecImS B algX u))
                              (λ u, projT2 (RecImS B algX u))))).
Qed.

Lemma initWuniq {A : setoid}(B : setoidfamily A)
      {X : setoid}(algX : PolyObj B X ⇒ X)
      (l l' : Wstd B ⇒ X)  :
  l ∘ (SupMap B) ≈ algX ∘ (PolyArr B l)
  → l' ∘ (SupMap B) ≈ algX ∘ (PolyArr B l')
  → l ≈ l'.

Proof.
  intros H H'. apply AM2RFisInj with (algX0 := algX)
                                     (M := existT _ l H)
                                     (M' := existT _ l' H').
  intro u. set (RF := AM2RF B algX ( existT _ l H)).
  set (RF' := AM2RF B algX ( existT _ l' H')).
  apply RecDefUniqGenRef with (algX0 := algX).
  apply (projT2 RF). apply (projT2 RF').
Qed.

(* Theorem 3.18 *)

Theorem initW {A : setoid}(B : setoidfamily A)
        {X : setoid}(algX : PolyObj B X ⇒ X) :
  ∃ l : Wstd B ⇒ X,
    l ∘ (SupMap B) ≈ algX ∘ (PolyArr B l)
    ∧ ∀ l', (l' ∘ (SupMap B) ≈ algX ∘ (PolyArr B l') → l' ≈ l).

Proof.
  exists (initWmap B algX). split.
  apply initWcomm. intros l' H'.
  apply (initWuniq B algX).
  apply H'. apply initWcomm.
Qed.

