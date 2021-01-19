Require Utf8.

Require Import S00_setoid_basics S30_IdType.

(* Discrete setoids *)

Definition isDscrStd (A : setoid) : Set
  := ∀ x x' : A, x ≈ x' ↔ x == x'.

Definition dscrStd : Set → setoid.

  intro X. apply (Build_setoid X Identity).
  apply (Build_setoidaxioms).
  intro x. apply rfl.
  intros x x' p. apply (p ⁻¹).
  intros x x' x'' p p'. apply (p ⊙ᵐ p').
Defined.


(* Discrete setoid families *)

(* Definition 5.1 *)

Definition isDscrStdFam {X : Set}(B : setoidfamily (dscrStd X)) : Set
  := ∀ x, ∀ b b' : B x,
      b ≈ b' ↔ ∃ p : x == x, |B|•ᵐp b == b'.

(* Discrete setoid family of a type family *)

Section DscrStdF.
  Context {X : Set}(Y : X → Set).
  
  Definition dscrStdfam_std (x : X) : setoid.

    apply (Build_setoid (Y x) (λ y y', ∃ p : x == x, Y•ᵐp y == y')).
    apply (Build_setoidaxioms).
    intro y. exists rfl. apply rfl.
    intros y y' [p q]. exists (p ⁻¹). apply Identity_sym.
    apply transpflip. apply q.
    intros y y' y'' [p q] [p' q'].
    exists (p⊙ᵐp').
    apply (transpcmp Y p p' q q').
  Defined.

  Definition dscrStdfam_map {x x' : X}(p : x == x')
    : dscrStdfam_std x ⇒ dscrStdfam_std x'.

    apply (Build_setoidmap (dscrStdfam_std x) (dscrStdfam_std x') (transp Y p)).
    intros y y' [p' q].
    destruct p. cbn. exists p'. apply q.
  Defined.

  Definition dscrStdfam : setoidfamily (dscrStd X).

    apply (Build_setoidfamily (dscrStd X) dscrStdfam_std (λ x x' p, dscrStdfam_map p)).
    apply (Build_setoidfamilyaxioms).
    intros x y. cbn. exists rfl. apply rfl.
    intros x x' p p' y. cbn. exists (p ⁻¹ ⊙ᵐ p').
    destruct p. apply rfl.
    intros x x' x'' p p' y. cbn. exists rfl.
    apply Identity_sym. apply (Id2HΠ (transpIsFunct p p') y).
  Defined.
End DscrStdF.

(* Transport of setoid families over discrete setoids is *)
(* equal to transport of the underlying type families    *)

Lemma StdFamObj_aux {X : Set}(B : setoidfamily (dscrStd X)){x x' : X}(p : x == x')
  : ∀ b, B•p b ≈ |B|•ᵐp b.
Proof.
  intro b. induction p. simpl. apply (setoidfamilyref B).
Qed.

(* Equation (31) *)

Lemma trspDscrSF {X : Set}{B : setoidfamily (dscrStd X)}
       (isdscrsf : isDscrStdFam B){x x' : X}(p : x == x')
  : ∀ b, ∃ l : x' == x',
             |B|•ᵐl (B•p b) == |B|•ᵐp b.
Proof.
  intro b. set (eq := fst (isdscrsf x' _ _) (StdFamObj_aux B p b)).
  apply eq.
Qed.

