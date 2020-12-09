Require Utf8.

Require Import IdType setoid_basics Wstd.


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


(* Basics on the identity type of W-types  *)

Section IdWty.
  Context {X : Set}{Y : X → Set}.

  Definition WtyIndex_eq {w w' : Wty Y}
    : w == w' → WtyIndex Y w == WtyIndex Y w'
    := Identity_congr (WtyIndex Y) w w'.

  Definition WtyBranches_eq {w w' : Wty Y}(r : w == w')
    : WtyBranches Y w == WtyBranches Y w' · Y•ᵐ(WtyIndex_eq r).

    destruct r. apply rfl.
  Defined.

  Definition isIdWty_aux (z z' : sigT (λ x, Y x → Wty Y))
    : ∀ r : z == z', sup Y (projT1 z) (projT2 z) == sup Y (projT1 z') (projT2 z').

    intro r. apply (ap (f := λ z, sup Y (projT1 z) (projT2 z)) r).
  Defined.  

  Definition isIdWty {x x' : X}{f : Y x → Wty Y}{f' : Y x' → Wty Y}
    : ∀ p : x == x', f == f' · Y•ᵐp → sup Y x f == sup Y x' f'.

    intros p q. apply (isIdWty_aux (existT _ x f) (existT _ x' f')).
    apply extΣ. exists p. cbn. apply domtransp. apply q.
  Defined.

  Definition ηWty : ∀ w, sup Y (WtyIndex Y w) (WtyBranches Y w) == w.

    intros [x f]. apply rfl.
  Defined.
End IdWty.


(* Pointwise equality on W-types *)

Definition EqWty_aux {X : Set}(Y : X → Set) : Wty Y ∧ Wty Y → Set
  := @DWty (Wty Y ∧ Wty Y)
           (λ z, WtyIndex Y (fst z) == WtyIndex Y (snd z))
           (λ z p, TotEq Y p)
           (λ z p v, (WtyBranches Y (fst z) (fstTotEq Y v) , WtyBranches Y (snd z) (sndTotEq Y v))).

Definition EqWty {X : Set}(Y : X → Set) : Wty Y → Wty Y → Set
  := λ w w', EqWty_aux Y (w , w').


Section EqWty.
  Context {X : Set}{Y : X → Set}.

  Definition isEqWty {w w': Wty Y}(p : WtyIndex Y w == WtyIndex Y w')
             (br : ∀ v : TotEq Y p, EqWty Y (WtyBranches Y w (fstTotEq Y v))
                                          (WtyBranches Y w' (sndTotEq Y v)))
    : EqWty Y w w'.
    apply supd with (i := (w , w'))
                    (a := p).
    apply br.
  Defined.

  Definition nodeEqWty {w w': Wty Y}
    : EqWty Y w w' → WtyIndex Y w == WtyIndex Y w'
    := DWtyIndex _ _ (w , w').

  Definition subtEqWty {w w': Wty Y}(E : EqWty Y w w')
             {y : Y (WtyIndex Y w)}{y' : Y (WtyIndex Y w')}
    : y ==[nodeEqWty E] y' → EqWty Y (WtyBranches Y w y) (WtyBranches Y w' y')
    := λ q, DWtyBranches _ _ (w , w') E (isTotEq Y (nodeEqWty E) y y' q).

  Lemma EqWty_symm_aux : ∀ z, EqWty_aux Y z → EqWty_aux Y (snd z , fst z).
  Proof.
    intros z E. induction E as [[w w'] p br IH]. simpl in *|-. simpl.
    apply (isEqWty (w := w') (w' := w) (p ⁻¹)).
    cut (∀ y y', EqOver Y p y y' → EqWty_aux Y (WtyBranches Y w' y', WtyBranches Y w y)).
    intros H [[y' y] q]. simpl in *|-. cbn.
    apply (H y y'). unfold EqOver.
    apply (transpflip_inv Y). apply (q ⁻¹).
    intros y y' q. apply (IH (existT _ (y , y') q)).
  Qed.

  Lemma EqWty_symm : ∀ w w', EqWty Y w w' → EqWty Y w' w.
  Proof.
    intros w w'. apply EqWty_symm_aux.
  Qed.

  Lemma EqWty_trans_aux : ∀ z, EqWty_aux Y z
                         → (∀ w, EqWty Y w (fst z) → EqWty_aux Y (w , snd z)).
  Proof.
    intros z E. induction E as [[w' w''] p' br' IH]. intros w [p br]. simpl in *|-. simpl.
    apply supd with (i := (w , w''))
                    (a := p⊙ᵐp').
    cut (∀ y' y'', ∀ q' : EqOver Y p' y' y'', ∀ w : Wty Y,
                EqWty Y w (WtyBranches Y w' y')
                → EqWty_aux Y (w, WtyBranches Y w'' y'')).
    intros H [[y y''] qq]. cbn. simpl in *|-.
    apply (H (Y•ᵐp y) y''). unfold EqOver.
    apply transpfunct_rev. apply qq.
    apply (br (existT _ (y , Y•ᵐp y) rfl)).
    intros y' y'' q'. apply (IH (existT _ (y' , y'') q')).
  Qed.

  Lemma EqWty_trans : ∀ w w' w'', EqWty Y w w' → EqWty Y w' w'' → EqWty Y w w''.
  Proof.
    intros w w' w'' E E'. apply (EqWty_trans_aux (w', w'') E' w E).
  Qed.
End EqWty.


(* Lemma 5.3 *)

Lemma Id2EqWty {X : Set}(Y : X → Set){w : Wty Y}
  : forall {w'}, w == w' → EqWty Y w w'.
Proof.
  induction w as [a f IH]. set (w := sup Y a f).
  intros w' r. induction r. apply (isEqWty rfl).
  intros [[y y'] q]. cbn. simpl in q. unfold EqOver in q.
  apply IH. apply ap. apply q.
Qed.


(* Lemma 5.4 *)

Lemma EqWty2Id_aux (funext : forall {A : Set}, forall {B : A → Set}, forall {f f' : (∀ x, B x)},
                           (∀ x, f x =={B x} f' x) → f =={∀ x, B x} f')
                   {X : Set}(Y : X → Set)
  : ∀ z : Wty Y ∧ Wty Y, EqWty_aux Y z → fst z == snd z.
Proof.
  intros z E. induction E as [[w w'] p br IH]. simpl. simpl in IH. simpl in br. simpl in p.
  refine ((ηWty w) ⁻¹ ⊙ᵐ _ ⊙ᵐ ηWty w').
  apply isIdWty with (p0 := p).
  apply funext. intro y.
  apply (IH (existT _ (y , Y •ᵐ p y) rfl)).
Qed.

Lemma EqWty2Id (funext : forall {A : Set}, forall {B : A → Set}, forall {f f' : (∀ x, B x)},
                           (∀ x, f x =={B x} f' x) → f =={∀ x, B x} f')
                   {X : Set}(Y : X → Set){w w' : Wty Y}
  : EqWty Y w w' → w == w'.
Proof.
  intro E. apply (EqWty2Id_aux funext Y (w , w') E).
Qed.



(* Equivariant trees *)
(* Definition 5.5    *)

Definition isEquivariant {X : Set}(Y : X → Set) : Wty Y → Set
  := @DWty (Wty Y)
             (λ w, ∀ l : WtyIndex Y w == WtyIndex Y w, ∀ y,
                   EqWty Y (WtyBranches Y w (Y•ᵐl y)) (WtyBranches Y w y))
             (λ w eqvr, Y (WtyIndex Y w))
             (λ w eqvr y, WtyBranches Y w y).


Definition eqvrBr {X : Set}{Y : X → Set}{w : Wty Y}
  : isEquivariant Y w
    → ∀ l : WtyIndex Y w == WtyIndex Y w, ∀ y,
        EqWty Y (WtyBranches Y w (Y•ᵐl y)) (WtyBranches Y w y)
  := λ E, DWtyIndex _ _ w E.

Definition eqvrSubT {X : Set}{Y : X → Set}{w : Wty Y}
  : isEquivariant Y w
    → ∀ y : Y (WtyIndex Y w),
        isEquivariant Y (WtyBranches Y w y)
  := λ E, DWtyBranches _ _ w E.



(* Lemma 5.6(i) *)

Lemma WPER2EqWty_aux {X : Set}{B : setoidfamily (dscrStd X)}(isdscrsf : isDscrStdFam B)
  : ∀ z, WstdPER_aux B z → EqWty (|B|) (fst z) (snd z).
Proof.
  intros z r. induction r as [[w w'] p br IH]. simpl in p. simpl in br. simpl in IH. simpl.
  apply supd with (i := (w , w'))
                  (a := p).
  intros [[b b'] q]. simpl. simpl in *|-.
  set (l := projT1 (trspDscrSF isdscrsf p b)).
  set (qq := projT2 (trspDscrSF isdscrsf p b) ⊙ᵐ q).
  set (qqq := snd (isdscrsf _ (B • p b) b') (existT _ l qq)).
  set (H := existT _ (b , b') qqq : TotStdfamEq B p).
  apply (IH H).
Qed.

Lemma WPER2EqWty {X : Set}{B : setoidfamily (dscrStd X)}
      (isdscrsf : isDscrStdFam B){w w' : Wty (|B|)}
  : WstdPER B w w' → EqWty (|B|) w w'.
Proof.
  intro r. apply (WPER2EqWty_aux isdscrsf (w , w') r).
Qed.


(* The following lemma should go in Wstd.v *)

Lemma subtExtIsExt {A : setoid}(B : setoidfamily A){w : Wty (|B|)}
  : WstdPER B w w → ∀ b, WstdPER B (WtyBranches (|B|) w b) (WtyBranches (|B|) w b).
Proof.
  intros r b.
  apply (WstdPER_Branches B w w r). apply setoidfamilyrefgeneral.
Qed.


(* Lemma 5.6(ii) *)

Lemma ExtIsEqvr {X : Set}{B : setoidfamily (dscrStd X)}
      (isdscrsf : isDscrStdFam B){w : Wty (|B|)}
  : WstdPER B w w → isEquivariant (|B|) w.
Proof.
  induction w as [x f IH]. set (w := sup (|B|) x f). intro wext.
  refine (supd _ _ _ _ _).
  intros l b. cbn. cbn in *|-.
  apply (WPER2EqWty isdscrsf).
  apply (WstdPER_Branches B w w wext). apply setoidfamilyrefgeneral_tactical.
  apply isdscrsf.
  exists (l ⁻¹). apply (transpIsEqv2 (|B|) l).
  intro b. specialize (IH b (subtExtIsExt B wext b)).
  apply IH.
Qed.
    

(* Lemma 5.7 *)

Lemma eqvrEqWty2WPER {X : Set}{B : setoidfamily (dscrStd X)}
      (isdscrsf : isDscrStdFam B){w : Wty (|B|)}
      (E : isEquivariant (|B|) w)
  : ∀ w', isEquivariant (|B|) w' → EqWty (|B|) w w'
                → WstdPER B w w'.
Proof.
  induction E as [w eqvr br IH]. intros w' E' eq.
  set (p := nodeEqWty eq).
  apply (isMatch (A := dscrStd X) p).
  intros b b' q. cbn in *|-.
  specialize (IH b (WtyBranches (|B|) w' b')).
  apply IH. apply (DWtyBranches _ _ w' E' b').
  set (l := projT1 (trspDscrSF isdscrsf p b)).
  set (rr := Id2EqWty (|B|) (ap (f := WtyBranches (|B|) w') (projT2 (trspDscrSF isdscrsf p b)) ⁻¹)).
  (*   : EqWty (|B|) (WtyBranches (|B|) w' (|B|•ᵐp b)) (WtyBranches (|B|) w' (|B|•ᵐl (B•p b)))*)
  set (l' := projT1 (fst (isdscrsf _ (B•p b) b') q)).
  set (rr' := Id2EqWty (|B|) (ap (f := WtyBranches (|B|) w') (projT2 (fst (isdscrsf _ (B•p b) b') q)))).
(*   : WtyBranches (|B|) w' (|B|•ᵐl' (B•p b)) == WtyBranches (|B|) w' b'*)
  cbn in *|-.
  refine (EqWty_trans _ _ _ (subtEqWty eq rfl) _).
  refine (EqWty_trans _ _ _ rr _).
  refine (EqWty_trans _ _ _ (eqvrBr E' l (B•p b)) _).
  apply (EqWty_trans _ _ _ (EqWty_symm _ _ (eqvrBr E' l' (B•p b))) rr').
Qed.
