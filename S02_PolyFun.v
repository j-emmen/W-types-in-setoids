
Require Import S00_setoid_basics.

(*---------------------*)
(* Polynomial functors *)
(*---------------------*)

(* Definition 2.10 *)

Definition PolyObj {A : setoid}(B : setoidfamily A)(X : setoid) : setoid.

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

Definition PolyArr_fnc {A : setoid}(B : setoidfamily A){X Y : setoid}
  : (X ⇒ Y) → PolyObj B X → PolyObj B Y.

  intros f F. set (a := projT1 F). set (h := projT2 F).
  exists a. apply (f ∘ h).
Defined.

Definition PolyArr  {A : setoid}(B : setoidfamily A){X Y : setoid}
  : (X ⇒ Y) → PolyObj B X ⇒ PolyObj B Y.

  intro f. apply (Build_setoidmap _ _ (PolyArr_fnc B f)).
  intros F F' H. set (a := projT1 F). set (h := projT2 F : B a ⇒ X).
  set (a' := projT1 F'). set (h' := projT2 F' : B a' ⇒ X).
  simpl. exists (projT1 H). intro b.
  apply setoidmapextensionality. apply (projT2 H).
Defined.

(*-----------------------------*)
(* Setoid of algebra moprhisms *)
(*-----------------------------*)

(* Definition 2.11 *)

Definition AlgMor {A : setoid}(B : setoidfamily A)
           {X : setoid}(algX : PolyObj B X ⇒ X){Y}(algY : PolyObj B Y ⇒ Y)
  : setoid.

  apply (Build_setoid (sigT (λ l : X ⇒ Y, l ∘ algX ≈ algY ∘ (PolyArr B l)))
                      (λ M M', projT1 M ≈ projT1 M')).
  apply Build_setoidaxioms.
  intro M. apply setoidrefl.
  intros M M' H. apply setoidsym, H.
  intros M M' M'' H H'.
  apply setoidtra with (y := projT1 M'). apply H. apply H'.
Defined.

(*--------------------------------*)
(* Coherent families of functions *)
(*--------------------------------*)

(* Definition 2.12 *)

Definition isCoh {A : setoid}{B : setoidfamily A}{X : setoid}(F : ∀ a, B a ⇒ X) : Set
  := ∀ a a', ∀ p : a ≈ a', F a ≈ F a' ∘ B•p.

Definition TotSect {A : setoid}{B : setoidfamily A}{X : setoid}(F : ∀ a, B a ⇒ X)
  : A → PolyObj B X
  := λ a, existT _ a (F a).

(* Lemmma 2.13 *)

Lemma FamCohIffTotSectExt {A : setoid}{B : setoidfamily A}{X : setoid}(F : ∀ a, B a ⇒ X)
  : isCoh F ↔ ∀ a a', ∀ p : a ≈ a', TotSect F a ≈ TotSect F a'.
Proof.
  split.
  intros isC a a' p. exists p. apply (isC a a' p).
  intros isE a a' p. specialize (isE a a' p). cbn in isE. intro b.
  refine (_ ⊙ projT2 isE b). apply (setoidmapextensionality _ _ (F a')).
  apply setoidfamilyirr.
Qed.

  
  
  
