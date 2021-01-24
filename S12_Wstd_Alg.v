Require Utf8.

Require Import S00_setoid_basics S01_Wty S02_PolyFun S10_Wstd_Obj S11_Wstd_Fam.

Section Algebra_Map.
  Context {A : setoid}(B : setoidfamily A).

  (* Section 3.3 *)

  (*--------------------------------------*)
  (* Algebra and coalgebra structure maps *)
  (*--------------------------------------*)

  Definition SupFnc : PolyObj B (Wstd B) → Wstd B.

    intros [a h]. set (f := λ y, projT1 (h y)).
    exists (sup _ a f).
    apply istExt2Ext. cbn. apply (setoidmapextensionality _ _ h).
  Defined.

  (* Lemma 3.10 *)

  Definition SupMap : PolyObj B (Wstd B) ⇒ Wstd B.

    apply (Build_setoidmap _ _ SupFnc).
    intros [a h] [a' h'] [p o]. cbn in p,o|-.
    set (F := existT _ a h). set (F' := existT _ a' h').
    set (pp := p : node B (SupFnc F) ≈ node B (SupFnc F')).
    apply (easyMatch pp o).
  Defined.

  (* Proposition 3.11 - Start *)

  Definition UnsupMap : Wstd B ⇒ PolyObj B (Wstd B)
    := InPoly (node B) (istCoh B).

  (*--------------------------------------------------*)
  (* Wsetoids are fixed points of polynomial functors *)
  (*--------------------------------------------------*)

  Theorem SupUnsup2Id : SupMap ∘ UnsupMap ≈ idmap.
  Proof.
    intro u. set (a := node B u). set (f := ist u).
    set (p := setoidrefl A a : node B (SupMap (UnsupMap u)) ≈ a).
    apply (easyMatch p). intro b. cbn in b.
    apply (setoidmapextensionality _ _ (ist u)).
    apply setoidfamilyrefgeneralinv.
  Qed.

  Theorem UnsupSup2Id : UnsupMap ∘ SupMap ≈ idmap.
  Proof.
    intros [a h]. set (F := existT _ a h).
    exists (setoidrefl A a). intro b.
    apply (setoidmapextensionality _ _ h). apply setoidfamilyrefgeneralinv.
  Qed.

  (* Proposition 3.11 - End *)

End Algebra_Map.
  
Lemma AlgSquareAlt {A : setoid}{B : setoidfamily A}{X : setoid}
      (algX : PolyObj B X ⇒ X)(l : Wstd B ⇒ X)
  : isAlgMor (SupMap B) algX l ↔ l ≈ algX ∘ PolyArr B l ∘ UnsupMap B.
Proof.
  split.
  intro H. apply setoidtra with (y := l ∘ (SupMap B) ∘ (UnsupMap B)).
  intro u'. apply (setoidmapextensionality _ _ l).
  apply setoidsym. apply SupUnsup2Id. intro u'. apply H.
  intro H'.
  apply setoidtra with (y := (algX ∘ (PolyArr B l)) ∘ (UnsupMap B) ∘ (SupMap B)).
  intro u. apply H'. intro z. apply (setoidmapextensionality _ _ algX).
  apply setoidmapextensionality. apply UnsupSup2Id.
Qed.
