Require Utf8.

Require Import S00_setoid_basics S01_Wty S30_IdType S32_IdWty.

(* Pointwise equality on W-types *)

(* Definition 5.2 *)

Definition EqWty_aux {X : Set}(Y : X → Set) : Wty Y ∧ Wty Y → Set
  := @DWty (Wty Y ∧ Wty Y)
           (λ z, Wty_node Y (fst z) == Wty_node Y (snd z))
           (λ z p, TotEq Y p)
           (λ z p v, (Wty_ist (fst z) (fstTotEq Y v) , Wty_ist (snd z) (sndTotEq Y v))).

Definition EqWty {X : Set}(Y : X → Set) : Wty Y → Wty Y → Set
  := λ w w', EqWty_aux Y (w , w').

(* Useful functions and proof that it is an equivalence relation *)

Section EqWty.
  Context {X : Set}{Y : X → Set}.

  Definition isEqWty {w w': Wty Y}(p : Wty_node Y w == Wty_node Y w')
             (br : ∀ v : TotEq Y p, EqWty Y (Wty_ist w (fstTotEq Y v))
                                          (Wty_ist w' (sndTotEq Y v)))
    : EqWty Y w w'.
    apply supd with (i := (w , w'))
                    (a := p).
    apply br.
  Defined.

  Definition nodeEqWty {w w': Wty Y}
    : EqWty Y w w' → Wty_node Y w == Wty_node Y w'
    := DWty_node _ _ (w , w').

  Definition subtEqWty {w w': Wty Y}(E : EqWty Y w w')
             {y : Y (Wty_node Y w)}{y' : Y (Wty_node Y w')}
    : y ==[nodeEqWty E] y' → EqWty Y (Wty_ist w y) (Wty_ist w' y')
    := λ q, DWty_ist _ _ (w , w') E (isTotEq Y (nodeEqWty E) y y' q).

  Lemma EqWty_symm_aux : ∀ z, EqWty_aux Y z → EqWty_aux Y (snd z , fst z).
  Proof.
    intros z E. induction E as [[w w'] p br IH]. simpl in *|-. simpl.
    apply (isEqWty (w := w') (w' := w) (p ⁻¹)).
    cut (∀ y y', EqOver Y p y y' → EqWty_aux Y (Wty_ist w' y', Wty_ist w y)).
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
                EqWty Y w (Wty_ist w' y')
                → EqWty_aux Y (w, Wty_ist w'' y'')).
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

(* Setoid of pointwise equal trees *)

Definition PtwTrees {X : Set}(Y : X → Set) : setoid.

  apply (Build_setoid (Wty Y) (EqWty Y)).
  apply Build_setoidaxioms.
  intro w. apply Id2EqWty. apply rfl.
  apply EqWty_symm.
  apply EqWty_trans.
Defined.


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

(* End Lemma 5.4 *)
