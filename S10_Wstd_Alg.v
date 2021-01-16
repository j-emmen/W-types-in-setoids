

Require Import S00_setoid_basics S01_Wty S02_PolyFun.


(* Section 3.1 *)

(*------------------------------*)
(* Underlying type of W-setoids *)
(*------------------------------*)

Definition WstdObj {A : setoid}(B : setoidfamily A) : Set
  := Wty (setoidfamilyobj A B).

(*
Definition WstdObjNode {A : setoid}(B : setoidfamily A) : WstdObj B → A
  := WtyNode (setoidfamilyobj A B).

Definition WstdObjIST {A : setoid}(B : setoidfamily A)(w : WstdObj B)
  : B (WtyNode _ w) → WstdObj B
  := @Wty_ist _ (setoidfamilyobj A B) w.
 *)

(*-----------------------------------------------------*)
(* Partial equivalence relation from dependent W-types *)
(*-----------------------------------------------------*)

(* Definition 3.1 *)

Definition WstdPER_aux {A : setoid}(B : setoidfamily A) :
  (WstdObj B) ∧ (WstdObj B) → Set :=
  @DWty ((WstdObj B) ∧ (WstdObj B))
        (λ z : WstdObj B ∧ WstdObj B,
               Wty_node _ (fst z) ≈,{A} Wty_node _ (snd z))
        (λ (z : WstdObj B ∧ WstdObj B)
           (p : Wty_node _ (fst z) ≈,{A} Wty_node _ (snd z)),
         TotStdfamEq B p)
        (λ (z : WstdObj B ∧ WstdObj B)
           (p : Wty_node _ (fst z) ≈,{A} Wty_node _ (snd z))
           (v : TotStdfamEq B p),
         (Wty_ist (fst z) (Unpack1 B p v),
          Wty_ist (snd z) (Unpack2 B p v))).

Definition WstdPER {A : setoid}(B : setoidfamily A) :
  WstdObj B → WstdObj B → Set :=
  λ w w', WstdPER_aux B (w , w').

(* Remark 3.2 *)

Definition isMatch {A : setoid}{B : setoidfamily A}{w w' : WstdObj B}
           (p : Wty_node _ w ≈ Wty_node _ w')
           (df : ∀ b b', b ≈[p] b' →
               WstdPER B (Wty_ist w b)
                         (Wty_ist w' b'))
  : WstdPER B w w'.

  apply (supd (λ (z : WstdObj B ∧ WstdObj B)
                 (p : Wty_node _ (fst z) ≈,{A} Wty_node _ (snd z)),
               TotStdfamEq B p)
              (λ (z : WstdObj B ∧ WstdObj B)
                 (p : Wty_node _ (fst z) ≈,{A} Wty_node _ (snd z))
                 (v : TotStdfamEq B p),
               (Wty_ist (fst z) (Unpack1 B p v),
                Wty_ist (snd z) (Unpack2 B p v)))
              (w , w') p).
  simpl. intro v. apply (df (Unpack1 B p v) (Unpack2 B p v) (UnpackEq B p v)).
Defined.

Definition WstdPER_node {A : setoid}(B : setoidfamily A)
           {w w' : WstdObj B}
  : WstdPER B w w' → Wty_node _ w ≈ Wty_node _ w'
  := DWty_node _ _ (w , w').

Definition WstdPER_ist {A : setoid}{B : setoidfamily A}{w w' : WstdObj B}(r : WstdPER B w w')
  : ∀ b b', b ≈[WstdPER_node B r] b' → WstdPER B (Wty_ist w b) (Wty_ist w' b')
  := λ b b' q, DWty_ist _ _ (w , w') r (PackTotEq _ _ b b' q).

(* Lemma 3.3 *)

Lemma ISTExt2Ext {A : setoid}{B : setoidfamily A}{w : WstdObj B}
      (ISTExt : ∀ b b', b ≈ b' → WstdPER B (Wty_ist w b) (Wty_ist w b'))
  : WstdPER B w w.
Proof.
  apply (isMatch (setoidrefl _ _)). intros b b' q. specialize (ISTExt b b').
  apply ISTExt. apply (setoidfamilyrefgeneral_tactical_rev B _ _ _ _ q).
Qed.

Lemma Ext2ISTExt {A : setoid}{B : setoidfamily A}{w : WstdObj B}(r : WstdPER B w w)
  : ∀ b b', b ≈ b' → WstdPER B (Wty_ist w b) (Wty_ist w b').
Proof.
  intros b b' q. apply (WstdPER_ist r b b').
  apply setoidfamilyrefgeneral_tactical. apply q.
Qed.

(* Proposition 3.4 - Start *)

Lemma WstdPER_aux_symm {A : setoid}(B : setoidfamily A) :
  ∀ z, WstdPER_aux B z → WstdPER_aux B (snd z , fst z).
Proof.
  intros z r. induction r as [z p feq IH].
  assert (g : (∀ v : TotStdfamEq B (p ˢ),
             WstdPER_aux B (Wty_ist (snd z) (Unpack1 B _ v),
                            Wty_ist (fst z) (Unpack2 B _ v)) )).
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
  intros w r1. set (p := WstdPER_node B r1).
  set (feq := WstdPER_ist r1).
  apply supd with (i := (w , snd z))
                  (a := p'⊙p).
  intro vv. set (b := Unpack1 B _ vv). set (b' := Unpack2 B _ vv). set (q := UnpackEq B _ vv).
  simpl in *|-. simpl.
  specialize IH with (w := Wty_ist w b).
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

(* Proposition 3.4 - End *)

(*---------------------------------*)
(* The setoid of extensional trees *)
(*---------------------------------*)

(* Definition 3.6 *)

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


Definition node {A : setoid}(B : setoidfamily A) : Wstd B ⇒ A.
  
  apply (Build_setoidmap _ _ (λ u : Wstd B, Wty_node _ (projT1 u))).
  intros u u' r. apply WstdPER_node. apply r.
Defined.

Definition ist_fnct {A : setoid}{B : setoidfamily A}(u : Wstd B)
  : B (node B u) → Wstd B.
  
  intro b. exists (Wty_ist (projT1 u) b).
  apply Ext2ISTExt. apply (projT2 u). apply setoidrefl.
Defined.

Definition ist {A : setoid}{B : setoidfamily A}(u : Wstd B) :
  B (node B u) ⇒ Wstd B.
  
  apply (Build_setoidmap _ _ (ist_fnct u)).
  intros b b' q. apply Ext2ISTExt. apply (projT2 u). apply q.
Defined.


(* Lemma 3.7 *)

Lemma easyMatch {A : setoid}{B : setoidfamily A}{u u' : Wstd B}
      (p : node B u ≈ node B u')
  : ist u ≈ ist u' ∘ B•p → u ≈ u'.
Proof.
  intro ISTeq. apply isMatch with (p0 := p). intros b b' q.
  apply WstdPER_trans with (w' := Wty_ist (projT1 u') (B•p b)).
  apply ISTeq. apply Ext2ISTExt. apply (projT2 u'). apply q.
Qed.

(* Proofs of coherence of the family ist *)

Lemma ist_coh {A : setoid}(B : setoidfamily A){u u' : Wstd B}(r : u ≈ u')
  : ist u ≈ ist u' ∘ B•(node B ↱ r).
Proof.
  intro b. apply (WstdPER_ist r). apply setoidrefl.
Defined.

Definition ist_coh_rev {A : setoid}(B : setoidfamily A){u u' : Wstd B}(r : u ≈ u')
  : ist u' ∘ B•(node B ↱ r) ≈ ist u.
Proof.
  apply setoidsym. apply ist_coh.
Defined.

Lemma ist_coh_tactical {A : setoid}(B : setoidfamily A){u u' : Wstd B}(r : u ≈ u')
  : ∀ b₁ b₂, ist u b₁ ≈ ist u b₂
           → ist u' (B•(node B ↱ r) b₁) ≈ ist u' (B•(node B ↱ r) b₂).
Proof.
  intros b₁ b₂ q.
  apply setoidtra with (y := ist u b₁). apply ist_coh_rev.
  apply setoidtra with (y := ist u b₂). apply q. apply ist_coh.
Qed.

Lemma ist_coh_inv {A : setoid}(B : setoidfamily A)(u u' : Wstd B)(r : u ≈ u')
  : ist u ∘ B•(node B ↱ r ˢ) ≈ ist u'.
Proof.
  apply setoidtra with
      (y := ist u' ∘ (B•(node B ↱ r)) ∘ (B•(node B ↱ r ˢ))).
  intro b. apply (ist_coh B r).
  intro b. apply (setoidmapextensionality _ _ (ist u')).
  apply setoidfamilycmpinvert.
Qed.
