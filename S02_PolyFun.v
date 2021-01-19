Require Utf8.

Require Import S00_setoid_basics.

(*---------------------*)
(* Polynomial functors *)
(*---------------------*)

Section PolyFun.
  Context {A : setoid}(B : setoidfamily A).
  
  (* Definition 2.10 *)

  Definition PolyObj (X : setoid) : setoid.

    apply (Build_setoid (∃ a, B a ⇒ X)
                        (λ z z', ∃ p : projT1 z ≈ projT1 z',
                            projT2 z ≈ projT2 z' ∘ B•p)).
    apply Build_setoidaxioms.
    intro z. exists (setoidrefl _ (projT1 z)). intro b.
    apply (setoidmapextensionality _ _ (projT2 z)). apply setoidfamilyrefgeneralinv.
    intros z z' H. set (p := projT1 H). set (q := projT2 H).
    exists (p ˢ). intro b'. apply setoidsym.
    apply setoidtra with (y := (projT2 z' ∘ B•p) (B•(p ˢ) b')). apply q.
    apply (setoidmapextensionality _ _ (projT2 z')). apply setoidfamilycmpinvert.
    intros z z' z'' H H'.
    set (p := projT1 H). set (q := projT2 H). set (p' := projT1 H'). set (q' := projT2 H').
    exists (p' ⊙ p). intro b.
    apply setoidtra with (y := (projT2 z'' ∘ (B•p' ∘ B•p)) b).
    apply ((q' (B•p b)) ⊙ (q b)). apply (setoidmapextensionality _ _ (projT2 z'')).
    apply setoidfamilycmpgeneral.
  Defined.

  Definition PolyArrAlt_fnc {X Y : setoid} : (X ⇒ Y) → PolyObj X → PolyObj Y.

    intros f F. set (a := projT1 F). set (h := projT2 F).
    exists a. apply (f ∘ h).
  Defined.

  Definition PolyArrAlt {X Y : setoid} : (X ⇒ Y) → PolyObj X ⇒ PolyObj Y.

    intro f. apply (Build_setoidmap _ _ (PolyArrAlt_fnc f)).
    intros F F' H. set (a := projT1 F). set (h := projT2 F : B a ⇒ X).
    set (a' := projT1 F'). set (h' := projT2 F' : B a' ⇒ X).
    simpl. exists (projT1 H). intro b.
    apply setoidmapextensionality. apply (projT2 H).
  Defined.

End PolyFun.

(*--------------------------------*)
(* Coherent families of functions *)
(*--------------------------------*)

(* Definition 2.12 *)

Definition isCoh {A : setoid}{B : setoidfamily A}{X : setoid}(F : ∀ a, B a ⇒ X) : Set
  := ∀ a a', ∀ p : a ≈ a', F a ≈ F a' ∘ B•p.

Definition CohFam {A : setoid}(B : setoidfamily A)(X : setoid) : setoid.

  apply (Build_setoid (sigT (λ F : ∀ a, B a ⇒ X, isCoh F))
                      (λ F F', ∀ a, projT1 F a ≈ projT1 F' a)).
  apply Build_setoidaxioms.
  swesetoid. swesetoid. swesetoid.
Defined.

Definition InPoly_fnc {A : setoid}{B : setoidfamily A}
           {A' : setoid}(f : A' ⇒ A){X : setoid}(F : ∀ a, B (f a) ⇒ X)
  : A' → PolyObj B X
  := λ a, existT _ (f a) (F a).

(* Lemmma 2.13 *)

Lemma FamCohIffInPolyExt {A : setoid}{B : setoidfamily A}
      {A' : setoid}(f : A' ⇒ A){X : setoid}(F : ∀ a, ridx_std f B a ⇒ X)
  : isCoh F ↔ ∀ a a', ∀ p : a ≈ a',
          InPoly_fnc f F a ≈ InPoly_fnc f F a'.
Proof.
  split.
  intros isC a a' p. exists (f ↱ p). apply (isC a a' p).
  intros isE a a' p. specialize (isE a a' p). cbn in isE. intro b.
  refine (_ ⊙ projT2 isE b). apply (setoidmapextensionality _ _ (F a')).
  apply setoidfamilyirr with (q := f ↱ p).
Qed.

Definition InPoly {A : setoid}{B : setoidfamily A}
           {A' : setoid}(f : A' ⇒ A){X : setoid}(CF : CohFam (ridx_std f B) X)
  : A' ⇒ PolyObj B X.

  apply (Build_setoidmap A' (PolyObj B X) (InPoly_fnc f (projT1 CF))).
  apply FamCohIffInPolyExt. apply (projT2 CF).
Defined.  

Definition Poly_node {A : setoid}{B : setoidfamily A}{X : setoid}
  : PolyObj B X ⇒ A.

  apply (Build_setoidmap (PolyObj B X) A (λ z, projT1 z)).
  intros z z' p. apply (projT1 p).
Defined.

Definition Poly_fam {A : setoid}{B : setoidfamily A}{X : setoid}
  : ∀ z : PolyObj B X, B (Poly_node z) ⇒ X.

  intro z. apply (projT2 z).
Defined.

Definition PolyArr_fnc {A : setoid}(B : setoidfamily A){X Y : setoid}
  : (X ⇒ Y) → PolyObj B X ⇒ PolyObj B Y.

  intro h.
  apply InPoly with (f := Poly_node).
  exists (λ z, h ∘ Poly_fam z).
  intros z z' pp b. apply (setoidmapextensionality _ _ h).
  cbn in pp. apply (projT2 pp b).
Defined.

Definition PolyArr {A : setoid}(B : setoidfamily A){X Y : setoid}
  : (X ⇒ Y) ⇒ PolyObj B X ⇒ PolyObj B Y.

  apply (Build_setoidmap _ _ (@PolyArr_fnc A B X Y)).
  intros h h' pp zz. exists (setoidrefl A _).
  apply setoidtra with (y := projT2 (PolyArr_fnc B h' zz)).
  intro b. apply pp.
  intro b. apply (setoidmapextensionality _ _ (projT2 (PolyArr_fnc B h' zz))).
  apply setoidfamilyrefgeneralinv.
Defined.

(*-----------------------------*)
(* Setoid of algebra moprhisms *)
(*-----------------------------*)

(* Definition 2.11 *)

Definition isAlgMor {A : setoid}{B : setoidfamily A}{X : setoid}
           (algX : PolyObj B X ⇒ X){Y : setoid}(algY : PolyObj B Y ⇒ Y)
  : X ⇒ Y → Set
  := λ l, l ∘ algX ≈ algY ∘ PolyArr B l.

Definition AlgMor {A : setoid}{B : setoidfamily A}
           {X : setoid}(algX : PolyObj B X ⇒ X){Y : setoid}(algY : PolyObj B Y ⇒ Y)
  : setoid.

  apply (Build_setoid (sigT (isAlgMor algX algY))
                      (λ AM AM', projT1 AM ≈ projT1 AM')).
  apply Build_setoidaxioms.
  swesetoid. swesetoid. swesetoid.
Defined.
