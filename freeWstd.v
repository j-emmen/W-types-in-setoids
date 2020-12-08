Require Utf8.

Require Import IdType Wstd_basics Wstd.


Notation "| B |" := (setoidfamilyobj _ B)
                      (at level 70, no associativity, only parsing).

Definition freestd : Set → setoid.

  intro X. apply (Build_setoid X Identity).
  apply (Build_setoidaxioms).
  intro x. apply rfl.
  intros x x' p. apply (p ⁻¹).
  intros x x' x'' p p'. apply (p ⊙ᵐ p').
Defined.

Definition freeextfn {X Y : Set}(f : X → Y)
  : (freestd X) ⇒ (freestd Y).

  apply (Build_setoidmap (freestd X) (freestd Y) f).
  intros x x' p. apply ap. apply p.
Defined.


Definition freemin {X : Set}(A : setoid)(f : X → A)
  : (freestd X) ⇒ A.

  apply (Build_setoidmap (freestd X) A f).
  intros x x' p. induction p. apply setoidrefl.
Defined.
  

Definition freestdfam_std {X : Set}(Y : X → Set)(x : X) : setoid.

  apply (Build_setoid (Y x) (λ y y', ∃ p : x == x, Y•ᵐp y == y')).
  apply (Build_setoidaxioms).
  intro y. exists rfl. apply rfl.
  intros y y' [p q]. exists (p ⁻¹). apply Identity_sym.
  apply transpflip. apply q.
  intros y y' y'' [p q] [p' q'].
  exists (p⊙ᵐp').
  apply (transpcmp Y p p' q q').
Defined.

Definition freestdfam_map {X : Set}(Y : X → Set){x x' : X}(p : x == x')
  : freestdfam_std Y x ⇒ freestdfam_std Y x'.

  apply (Build_setoidmap (freestdfam_std Y x) (freestdfam_std Y x') (transp Y p)).
  intros y y' [p' q].
  destruct p. cbn. exists p'. apply q.
  (*exists (p⁻¹ᵐ⊙ᵐp'⊙ᵐp).
  apply transpfunct_rev.*)
Defined.

Definition freestdfam {X : Set}(Y : X → Set) : setoidfamily (freestd X).

  apply (Build_setoidfamily (freestd X) (freestdfam_std Y) (λ x x' p, freestdfam_map Y p)).
  apply (Build_setoidfamilyaxioms).
  intros x y. cbn. exists rfl. apply rfl.
  intros x x' p p' y. cbn. exists (p ⁻¹ ⊙ᵐ p').
  destruct p. apply rfl.
  intros x x' x'' p p' y. cbn. exists rfl.
  apply Identity_sym. apply (Id2HΠ (transpIsFunct p p') y).
Defined.


Definition isFreeStd (A : setoid) : Set
  := ∀ x x' : A, x ≈ x' ↔ x == x'.


Definition isFreeStdFam {X : Set}(B : setoidfamily (freestd X)) : Set
  := ∀ x, ∀ b b' : B x, b ≈ b' ↔ ∃ p : x == x, (setoidfamilyobj _ B)•ᵐp b == b'.


Lemma StdFamObj_aux {X : Set}(B : setoidfamily (freestd X)){x x' : X}(p : x == x')
  : ∀ b, B•p b ≈ (setoidfamilyobj (freestd X) B)•ᵐp b.
Proof.
  intro b. induction p. simpl. apply (setoidfamilyref B).
Qed.

Lemma trspFreeSF {X : Set}{B : setoidfamily (freestd X)}
       (isfreesf : isFreeStdFam B){x x' : X}(p : x == x')
  : ∀ b, ∃ l : x' == x',
             |B|•ᵐl (B•p b) == |B|•ᵐp b.
Proof.
  intro b. set (eq := fst (isfreesf x' _ _) (StdFamObj_aux B p b)).
  apply eq.
Qed.



Definition WtyIndex_eq {X : Set}(Y : X → Set){w w' : Wty Y}
  : w == w' → WtyIndex Y w == WtyIndex Y w'
  := ap.

Definition WtyBranches_eq {X : Set}(Y : X → Set){w w' : Wty Y}(r : w == w')
  : WtyBranches Y w == WtyBranches Y w' · Y•ᵐ(WtyIndex_eq Y r).
    (*(λ x, Y x → Wty Y)•ᵐ(WtyIndex_eq Y r) (WtyBranches Y w) == WtyBranches Y w'.*)
  destruct r. apply rfl.
Defined.


Definition supIdWty_aux {X : Set}(Y : X → Set)(z z' : sigT (λ x, Y x → Wty Y))
  : ∀ r : z == z', sup Y (projT1 z) (projT2 z) == sup Y (projT1 z') (projT2 z').

  intro r. apply (ap (f := λ z, sup Y (projT1 z) (projT2 z)) r).
Defined.  

Definition supIdWty {X : Set}(Y : X → Set){x x' : X}{f : Y x → Wty Y}{f' : Y x' → Wty Y}
  : ∀ p : x == x', f == f' · Y•ᵐp → sup Y x f == sup Y x' f'.

  intros p q. apply (supIdWty_aux Y (existT _ x f) (existT _ x' f')).
  apply extΣ. exists p. cbn. apply domtransp. apply q.
Defined.

Definition ηWty {X : Set}{Y : X → Set}(w : Wty Y)
  : sup Y (WtyIndex Y w) (WtyBranches Y w) == w.

  destruct w as [x f]. apply rfl.
Defined.


Definition EqWty_aux {X : Set}(Y : X → Set) : Wty Y ∧ Wty Y → Set
  := @DWty (Wty Y ∧ Wty Y)
           (λ z, WtyIndex Y (fst z) == WtyIndex Y (snd z))
           (λ z p, TotEq Y p)
           (λ z p v, (WtyBranches Y (fst z) (fstTotEq Y v) , WtyBranches Y (snd z) (sndTotEq Y v))).

Definition EqWty {X : Set}(Y : X → Set) : Wty Y → Wty Y → Set
  := λ w w', EqWty_aux Y (w , w').

Definition isEqWty {X : Set}(Y : X → Set){w w': Wty Y}
           (p : WtyIndex Y w == WtyIndex Y w')
           (br : ∀ v : TotEq Y p, EqWty Y (WtyBranches Y w (fstTotEq Y v))
                                        (WtyBranches Y w' (sndTotEq Y v)))
  : EqWty Y w w'.
  apply supd with (i := (w , w'))
                  (a := p).
  apply br.
Defined.

Definition nodeEqWty {X : Set}{Y : X → Set}{w w': Wty Y}
  : EqWty Y w w' → WtyIndex Y w == WtyIndex Y w'
  := DWtyIndex _ _ (w , w').

Definition subtEqWty {X : Set}{Y : X → Set}{w w': Wty Y}(E : EqWty Y w w')
           {y : Y (WtyIndex Y w)}{y' : Y (WtyIndex Y w')}
  : y ==[nodeEqWty E] y' → EqWty Y (WtyBranches Y w y) (WtyBranches Y w' y')
  := λ q, DWtyBranches _ _ (w , w') E (isTotEq Y (nodeEqWty E) y y' q).


Lemma EqWty_aux_symm {X : Set}(Y : X → Set) :
  ∀ z, EqWty_aux Y z → EqWty_aux Y (snd z , fst z).
Proof.
  intros z E. induction E as [[w w'] p br IH]. simpl in *|-. simpl.
  apply (isEqWty Y (w := w') (w' := w) (p ⁻¹)).
  cut (∀ y y', EqOver Y p y y' → EqWty_aux Y (WtyBranches Y w' y', WtyBranches Y w y)).
  intros H [[y' y] q]. simpl in *|-. cbn.
  apply (H y y'). unfold EqOver.
  apply (transpflip_inv Y). apply (q ⁻¹).
  intros y y' q. apply (IH (existT _ (y , y') q)).
Qed.

Lemma EqWty_symm {X : Set}(Y : X → Set) :
  ∀ w w', EqWty Y w w' → EqWty Y w' w.
Proof.
  intros w w'. apply EqWty_aux_symm.
Qed.

Lemma EqWty_aux_trans {X : Set}(Y : X → Set) :
  ∀ z, EqWty_aux Y z →
       (∀ w, EqWty Y w (fst z) → EqWty_aux Y (w , snd z)).
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

Lemma EqWty_trans {X : Set}(Y : X → Set) :
  ∀ w w' w'', EqWty Y w w' → EqWty Y w' w'' → EqWty Y w w''.
Proof.
  intros w w' w'' E E'. apply (EqWty_aux_trans Y (w', w'') E' w E).
Qed.


Lemma Id2EqWty {X : Set}(Y : X → Set){w : Wty Y}
  : forall {w'}, w == w' → EqWty Y w w'.
Proof.
  induction w as [a f IH]. set (w := sup Y a f).
  intros w' r. induction r. apply (isEqWty Y rfl).
  intros [[y y'] q]. cbn. simpl in q. unfold EqOver in q.
  apply IH. apply ap. apply q.
Qed.


Lemma EqWty2Id_aux (funext : forall {A : Set}, forall {B : A → Set}, forall {f f' : (∀ x, B x)},
                           (∀ x, f x =={B x} f' x) → f =={∀ x, B x} f')
                   {X : Set}(Y : X → Set)
  : ∀ z : Wty Y ∧ Wty Y, EqWty_aux Y z → fst z == snd z.
Proof.
  intros z E. induction E as [[w w'] p br IH]. simpl. simpl in IH. simpl in br. simpl in p.
  refine ((ηWty w) ⁻¹ ⊙ᵐ _ ⊙ᵐ ηWty w').
  apply supIdWty with (p0 := p).
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




Lemma WPER2EqWty_aux {X : Set}{B : setoidfamily (freestd X)}(isfreesf : isFreeStdFam B)
  : ∀ z, WstdPER_aux B z → EqWty (|B|) (fst z) (snd z).
Proof.
  intros z r. induction r as [[w w'] p br IH]. simpl in p. simpl in br. simpl in IH. simpl.
  apply supd with (i := (w , w'))
                  (a := p).
  intros [[b b'] q]. simpl. simpl in *|-.
  set (l := projT1 (trspFreeSF isfreesf p b)).
  set (qq := projT2 (trspFreeSF isfreesf p b) ⊙ᵐ q).
  set (qqq := snd (isfreesf _ (B • p b) b') (existT _ l qq)).
  set (H := existT _ (b , b') qqq : TotStdfamEq B p).
  apply (IH H).
Qed.

Lemma WPER2EqWty {X : Set}{B : setoidfamily (freestd X)}(isfreesf : isFreeStdFam B){w w' : Wty (|B|)}
  : WstdPER B w w' → EqWty (|B|) w w'.
Proof.
  intro r. apply (WPER2EqWty_aux isfreesf (w , w') r).
Qed.



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



Lemma subtExtIsExt {A : setoid}(B : setoidfamily A){w : Wty (|B|)}
  : WstdPER B w w → ∀ b, WstdPER B (WtyBranches (|B|) w b) (WtyBranches (|B|) w b).
Proof.
  intros r b.
  apply (WstdPER_Branches B w w r). apply setoidfamilyrefgeneral.
Qed.

Lemma ExtIsEqvr {X : Set}{B : setoidfamily (freestd X)}
      (isfreesf : isFreeStdFam B){w : Wty (|B|)}
  : WstdPER B w w → isEquivariant (|B|) w.
Proof.
  induction w as [x f IH]. set (w := sup (|B|) x f). intro wext.
  refine (supd _ _ _ _ _).
  intros l b. cbn. cbn in *|-.
  apply (WPER2EqWty isfreesf).
  apply (WstdPER_Branches B w w wext). apply setoidfamilyrefgeneral_tactical.
  apply isfreesf.
  exists (l ⁻¹). apply (transpIsEqv2 (|B|) l).
  intro b. specialize (IH b (subtExtIsExt B wext b)).
  apply IH.
Qed.
    
  
Lemma eqvrEqWty2WPER {X : Set}{B : setoidfamily (freestd X)}
      (isfreesf : isFreeStdFam B){w : Wty (|B|)}
      (E : isEquivariant (|B|) w)
  : ∀ w', isEquivariant (|B|) w' → EqWty (|B|) w w'
                → WstdPER B w w'.
Proof.
  induction E as [w eqvr br IH]. intros w' E' eq.
  set (p := nodeEqWty eq).
  apply (isMatch (A := freestd X) p).
  intros b b' q. cbn in *|-.
  specialize (IH b (WtyBranches (|B|) w' b')).
  apply IH. apply (DWtyBranches _ _ w' E' b').
  set (l := projT1 (trspFreeSF isfreesf p b)).
  set (rr := Id2EqWty (|B|) (ap (f := WtyBranches (|B|) w') (projT2 (trspFreeSF isfreesf p b)) ⁻¹)).
  (*   : EqWty (|B|) (WtyBranches (|B|) w' (|B|•ᵐp b)) (WtyBranches (|B|) w' (|B|•ᵐl (B•p b)))*)
  set (l' := projT1 (fst (isfreesf _ (B•p b) b') q)).
  set (rr' := Id2EqWty (|B|) (ap (f := WtyBranches (|B|) w') (projT2 (fst (isfreesf _ (B•p b) b') q)))).
(*   : WtyBranches (|B|) w' (|B|•ᵐl' (B•p b)) == WtyBranches (|B|) w' b'*)
  cbn in *|-.
  refine (EqWty_trans (|B|) _ _ _ (subtEqWty eq rfl) _).
  refine (EqWty_trans (|B|) _ _ _ rr _).
  refine (EqWty_trans (|B|) _ _ _ (eqvrBr E' l (B•p b)) _).
  apply (EqWty_trans (|B|) _ _ _ (EqWty_symm _ _ _ (eqvrBr E' l' (B•p b))) rr').
Qed.
