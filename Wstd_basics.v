(*-----------------------------------------------------------------*)
(*                             Coq 8.8.0                           *)
(*-----------------------------------------------------------------*)
(* Some Utf8 notations for Propositions-as-types at the Set level. *)
(*-----------------------------------------------------------------*)
(* Author: Olov Wilander. 2012                                     *)
(*-----------------------------------------------------------------*)
(*
N.B. Many of these notations conflict with the standard use in the
Utf8 and Utf8_core modules, where they are used at the Prop level.
*)

Notation "∀ x , P" := (forall x, P)
  (at level 200, x at level 0, right associativity) : type_scope.
Notation "∀ x y , P" := (forall x y, P)
  (at level 200, x, y at level 0, right associativity) : type_scope.
Notation "∀ x y z , P" := (forall x y z, P)
  (at level 200, x, y, z at level 0, right associativity) : type_scope.
Notation "∀ x y z w , P" := (forall x y z w, P)
  (at level 200, x, y, z, w at level 0, right associativity) : type_scope.
Notation "∀ x : X , P" := (forall x: X, P)
  (at level 200, x at level 0, right associativity) : type_scope.
Notation "∀ x y : X , P" := (forall x y: X, P)
  (at level 200, x, y at level 0, right associativity) : type_scope.
Notation "∀ x y z : X , P" := (forall x y z: X, P)
  (at level 200, x, y, z at level 0, right associativity) : type_scope.
Notation "∃ x , P" := (sigT (fun x => P))
  (at level 200, x at level 0, right associativity) : type_scope.
Notation "∃ x : y , P" := (sigT (fun x: y => P))
  (at level 200, x at level 0, right associativity) : type_scope.

Notation "x ∨ y" := (sum x y) (at level 85, right associativity) : type_scope.
Notation "x ∧ y" := (prod x y) (at level 80, right associativity) : type_scope.
Notation "x → y" := (x -> y) (at level 90, right associativity) : type_scope.
Notation "x ↔ y" := ((x → y) ∧ (y → x)) (at level 95, no associativity) : type_scope.

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..) (at level 200, x binder, y binder, right associativity).


(*-----------------------------------------------------*)
(* Swedish style setoids, under propositions-as-types. *)
(*-----------------------------------------------------*)
(* Authors: Erik Palmgren and Olov Wilander            *)
(*-----------------------------------------------------*)

Record setoidaxioms 
           (setoidbase:Set)
           (setoideq: setoidbase -> setoidbase -> Set):=
 {
    xsetoidrefl :  ∀x, setoideq x x;
    xsetoidsym  :  ∀x y, setoideq x y → setoideq y x;
    xsetoidtra  :  ∀x y z, setoideq x y → setoideq y z → setoideq x z
  }.

Record setoid: Type :=
  {
    setoidbase :> Set;
    setoideq   :  setoidbase → setoidbase → Set;
    setoidaxs: setoidaxioms setoidbase setoideq
  }.

Definition setoidrefl (A:setoid) := 
        xsetoidrefl (setoidbase A)(setoideq A)(setoidaxs A).

Definition setoidsym (A:setoid) := 
        xsetoidsym (setoidbase A)(setoideq A)(setoidaxs A).

Definition setoidtra (A:setoid) := 
        xsetoidtra (setoidbase A)(setoideq A)(setoidaxs A).

Notation "x ≈ y" := (setoideq _ x y) (at level 70, no associativity, only parsing).
Notation "x ≈,{ A  } y" := (setoideq A x y) (at level 70, no associativity).

Hint Resolve setoidrefl : swesetoid.
Hint Immediate setoidsym : swesetoid.
Hint Resolve setoidtra : swesetoid. (* The warning here is expected *)

Ltac swesetoid := simpl; eauto with swesetoid.

(* extensional functions *)

Record setoidmap (A B: setoid) :=
  {
    setoidmapfunction :> A → B;
    setoidmapextensionality : ∀x y: A, x ≈ y → setoidmapfunction x ≈ setoidmapfunction y
  }.

Hint Resolve setoidmapextensionality : swesetoid.

Definition setoidmaps (A B: setoid): setoid.
apply (Build_setoid (setoidmap A B) (λ f g, ∀x:A, f x ≈ g x)).
apply (Build_setoidaxioms (setoidmap A B) (λ f g : setoidmap A B, ∀x : A, f x ≈,{ B }g x)).
intros. apply setoidrefl.
intros. swesetoid.
intros. swesetoid.
Defined.

Notation "A ⇒ B" := (setoidmaps A B) (at level 55, right associativity).

Lemma binsetoidmap_helper {A B C: setoid} (f:A → B → C)
  (p: ∀a a', a ≈ a' → ∀b, f a b ≈ f a' b)
  (q: ∀a b b', b ≈ b' → f a b ≈ f a b')
  : A ⇒ B ⇒ C.
Proof.
  apply (Build_setoidmap A (B ⇒ C) (λ a, (Build_setoidmap B C (f a) (q a))) p).
Defined.

Lemma trinsetoidmap_helper {A B C D: setoid} (f: A → B → C → D)
  (p: ∀a a', a ≈ a' → ∀b c, f a b c ≈ f a' b c)
  (q: ∀a b b', b ≈ b' → ∀c, f a b c ≈ f a b' c)
  (r: ∀a b c c', c ≈ c' → f a b c ≈ f a b c')
  : A ⇒ B ⇒ C ⇒ D.
Proof.
  apply (Build_setoidmap A (B ⇒ C ⇒ D)) with (λ a, binsetoidmap_helper (f a) (q a) (r a));
    assumption.
Defined.

Definition idmap {A: setoid}: setoidmap A A.
apply (Build_setoidmap A A (λ x: A, x)); swesetoid.
Defined.

Definition comp {A B: setoid} (C: setoid): (B ⇒ C) ⇒ (A ⇒ B) ⇒ (A ⇒ C).
apply trinsetoidmap_helper with (λ f: B ⇒ C, λ g: A ⇒ B, λ a, f (g a));
  swesetoid.
Defined.

Notation "F ∘ G" := (comp _ F G) (at level 10).

Theorem setoidmap_composition_assoc {A B C D: setoid} (F: C ⇒ D) (G: B ⇒ C) (H: A ⇒ B)
  : F ∘ G ∘ H ≈ F ∘ (G ∘ H).
Proof.
  swesetoid.
Qed.

Theorem setoidmap_comp_id_left {A B: setoid} (F: A ⇒ B): idmap ∘ F ≈ F.
Proof.
  swesetoid.
Qed.

Theorem setoidmap_comp_id_right {A B: setoid} (F: A ⇒ B): F ∘ idmap ≈ F.
Proof.
  swesetoid.
Qed.

(* Additional lemmas *)

Lemma setoidmaprid_tactical {A B : setoid}(f : A ⇒ B)(h : A ⇒ A) :
  h ≈ idmap → f ∘ h ≈ f.
Proof.
  intros H a. apply (setoidmapextensionality _ _ f). apply H.
Qed.

Lemma setoidmapcmp_tactical {A B C : setoid}(f f' : B ⇒ A)(g g' : C ⇒ B) :
  f ≈ f' → g ≈ g' → f ∘ g ≈ f' ∘ g'.
Proof.
  intros H H'. apply setoidtra with (y := f' ∘ g).
  apply (setoidmapextensionality _ _ (comp _)). apply H.
  apply setoidmapextensionality. apply H'.
Qed.


(*------------------------------------------*)
(* Generalities about families of setoids   *)
(*------------------------------------------*)
(* Authors: Erik Palmgren and Olov Wilander *)
(*------------------------------------------*)

Notation "p ⁻¹" := (setoidsym _ _ _ p) (at level 3, no associativity).
Notation "p ⊙ q" := (setoidtra _ _ _ _ q p) (at level 34, right associativity).
Notation "F ↱ p" := (setoidmapextensionality _ _ F _ _ p) (at level 100).


Record setoidfamilyaxioms 
   (A: setoid)
   (setoidfamilyobj: A -> setoid)
   (setoidfamilymap :  ∀x y: A, ∀p: x ≈ y,
                         setoidfamilyobj x ⇒ setoidfamilyobj y) :=
  {
   xsetoidfamilyref :  ∀x: A, ∀y: setoidfamilyobj x,
      setoidfamilymap x x (setoidrefl A x) y ≈ y;
   xsetoidfamilyirr :  ∀x y: A, ∀p q: x ≈ y, ∀z: setoidfamilyobj x,
                         setoidfamilymap x y p z ≈ setoidfamilymap x y q z;
   xsetoidfamilycmp :  ∀x y z: A, ∀p: x ≈ y, ∀q: y ≈ z, ∀w: setoidfamilyobj x,
                         (setoidfamilymap y z q) ((setoidfamilymap x y p) w)
                           ≈ setoidfamilymap x z (q⊙p) w
  }.


Record setoidfamily (A: setoid) :=
  {
    setoidfamilyobj :> A → setoid;
    setoidfamilymap :  ∀x y: A, ∀p: x ≈ y,
                         setoidfamilyobj x ⇒ setoidfamilyobj y;
    setoidfamilyaxs: setoidfamilyaxioms A setoidfamilyobj setoidfamilymap
    }.

Definition setoidfamilyref {A:setoid}(F:setoidfamily A):=
xsetoidfamilyref A (setoidfamilyobj  A F)
(setoidfamilymap A F)(setoidfamilyaxs A F).

Definition setoidfamilyirr {A:setoid}(F:setoidfamily A):=
xsetoidfamilyirr A (setoidfamilyobj  A F)
(setoidfamilymap A F)(setoidfamilyaxs A F).

Definition setoidfamilycmp {A:setoid}(F:setoidfamily A):=
xsetoidfamilycmp A (setoidfamilyobj  A F)
(setoidfamilymap A F)(setoidfamilyaxs A F).


Notation "F • p" := (setoidfamilymap _ F _ _ p)
  (at level 9, right associativity).

Lemma setoidfamilyrefgeneral {A: setoid} (F: setoidfamily A):
  ∀x: A, ∀p: x ≈ x, ∀y: F x, F•p y ≈ y.
Proof.
  intros x p y.
  apply setoidtra with (F•(setoidrefl A x) y).
  eauto using setoidtra, setoidfamilyirr, setoidfamilyref, setoidrefl.
  apply setoidfamilyref.
Defined.

Lemma setoidfamilycmpgeneral {A: setoid} (F: setoidfamily A):
  ∀x y z: A, ∀p: x ≈ y, ∀q: y ≈ z, ∀r: x ≈ z, ∀w: F x, F•q (F•p w) ≈ F•r w.
Proof.
  intros x y z p q r w;
    eauto using setoidtra, setoidfamilyirr, setoidfamilycmp.
Defined.

(* some extra lemma for handling setoidfamilies *)

Lemma setoidfamilycmpinvert 
 {A: setoid} (F: setoidfamily A):
  ∀x y: A, ∀p: x ≈ y, ∀q: y ≈ x, ∀w: F x, F•q (F•p w) ≈ w.
Proof.
  intros x y p q w.
  assert  (F • q (F • p w) ≈,{ F x } F • (setoidrefl A x) w).
  apply setoidfamilycmpgeneral.  
  assert (F • (setoidrefl A x) w ≈,{ F x } w).
  apply setoidfamilyrefgeneral.
  swesetoid.
Defined.

Lemma setoidfamilycmpgeneral_3 
 {A: setoid} (F: setoidfamily A):   
 ∀ x: A,  ∀ v z: A, ∀ r: x ≈ v, ∀ s: v ≈ z,
   ∀u:F z , ∀w: F x, u ≈  F•(s⊙r) w -> u ≈  F•s (F•r w).
Proof.
  intros x v z r s u w H.
  assert (F•s (F•r w) ≈  F•(s⊙r) w).
  apply setoidfamilycmp.
  swesetoid.
Defined.

Lemma setoidfamilyirrgeneral 
  {A: setoid} (F: setoidfamily A):
  ∀ x y: A,  ∀ p q: x ≈ y, ∀u v: F x, 
  u  ≈ v ->  F•p u ≈ F•q v. 
Proof.
  intros x y p q u v H.
  assert (F • p u ≈,{ F y } F • q u).
  apply setoidfamilyirr.
  assert (F • p u ≈,{ F y } F • p v).
  swesetoid. swesetoid.
Defined. 

Lemma setoidfamilyirrrevgeneral 
  {A: setoid} (F: setoidfamily A):
  ∀ x y: A,  ∀ p q: x ≈ y, ∀u v: F x, 
    F•p u ≈ F•q v ->  u  ≈ v. 
Proof.
  intros x y p q u v H.
  assert (F • p ⁻¹ (F • p u) ≈  u).
  apply  setoidfamilycmpinvert.
  assert (F • q ⁻¹ (F • q v) ≈ v).
  apply setoidfamilycmpinvert.
  assert (F • q ⁻¹ (F • p u) ≈ F • q ⁻¹ (F • q v)).
  apply setoidmapextensionality.
  apply H.
  assert ( F • p ⁻¹ (F • p u) ≈ F • q ⁻¹ (F • p u)).
  apply setoidfamilyirr.
  swesetoid.
Defined.


Lemma setoidfamilyirrgeneraldouble 
  {A: setoid} (F: setoidfamily A):
  ∀ x y: A, ∀ z w: A, 
  ∀ p: x ≈ z,  ∀ p': z ≈ y, 
  ∀ q: x ≈ w,  ∀ q': w ≈ y, 
  ∀u v: F x, 
     u  ≈ v ->  F•p' (F•p u) ≈  F•q' (F•q v). 
Proof.
  intros x y z w p p' q q' u v H.
  assert (F • p' (F • p u) ≈  F • (p'⊙ p) u).
  apply setoidfamilycmp.
  assert (F • q' (F • q v) ≈  F • (q'⊙ q) v).
  apply setoidfamilycmp.
  assert (F • (p'⊙ p) u ≈  F • (q'⊙ q) v ).
  apply setoidfamilyirrgeneral.
  exact H. 
  swesetoid. 
Defined.

Lemma setoidfamilysideflip 
  {A: setoid} (F: setoidfamily A):
  ∀ x y: A, 
  ∀ p: x ≈ y,  
  ∀ q: y ≈ x, 
  ∀u: F x,  ∀v: F y, 
    u ≈   F•q v ->  F•p u ≈ v.
Proof.
intros x y p q u v H.
assert (F • p u ≈ F • p (F • q v)) as L1.
apply setoidmapextensionality.
apply H.
assert (F • p (F • q v) ≈ v) as L2.
apply setoidfamilycmpinvert.
apply (setoidtra _ _ _ _ L1 L2).
Defined.

Lemma setoidfamilyrefgeneral_tactical
  {A: setoid} (F: setoidfamily A):
  ∀ x: A, 
  ∀ p: x ≈ x,  
  ∀u v: F x, 
    u ≈  v ->  F•p u ≈ v.
Proof.
intros x p u v H.
assert (F • p u ≈ u) as L.
apply setoidfamilyrefgeneral.
apply (setoidtra _ _  _ _ L H).
Defined.

(* Additional lemmas on setoid families *)

Lemma setoidfamilyrefgeneralinv {A: setoid} (F: setoidfamily A):
  ∀x: A, ∀p: x ≈ x, ∀y: F x, y ≈ F•p y.
Proof.
  intros x p y.
  apply setoidtra with (F•(setoidrefl A x) y).
  apply setoidsym. apply setoidfamilyref.
  eauto using setoidtra, setoidfamilyirr, setoidfamilyref, setoidrefl.
Defined.

Lemma setoidfamilysideflip_rev
  {A: setoid} (F: setoidfamily A):
  ∀ x y: A, 
  ∀ p: x ≈ y,  
  ∀ q: y ≈ x, 
  ∀ u: F x, ∀v: F y, 
    F•p u ≈ v → u ≈ F•q v.
Proof.
intros x y p q u v H.
assert (F•q (F•p u) ≈ F•q v) as L1.
apply setoidmapextensionality.
apply H.
assert (u ≈ F•q (F•p u)) as L2.
apply setoidfamilycmpgeneral_3, setoidsym, setoidfamilyrefgeneral.
apply (setoidtra _ _ _ _ L2 L1).
Defined.

Lemma setoidfamilyrefgeneral_tactical_rev
  {A: setoid} (F: setoidfamily A):
  ∀ x: A, 
  ∀ p: x ≈ x,  
  ∀ u v: F x, 
    F•p u ≈ v → u ≈ v.
Proof.
intros x p u v H.
assert (u ≈ F • p u) as L.
apply setoidsym, setoidfamilyrefgeneral.
apply (setoidtra _ _  _ _ L H).
Defined.

Lemma setoidfamilyirrtransp
  {A: setoid} (F: setoidfamily A):
  ∀ x y : A,
  ∀ p q : x ≈ y,
  ∀ u : F x, ∀ v : F y,
    F•p u ≈ v → F•q u ≈ v.
Proof.
  intros x y p q u v H.
  apply setoidtra with (y := F•p u).
  apply setoidfamilyirr. apply H.
Defined.


(*-------------------------------------------------------------*)
(* Equivalence relation between elements in equivalent fibers. *)
(*-------------------------------------------------------------*)
(* Author : Jacopo Emmenegger                                  *)
(*-------------------------------------------------------------*)

Definition EqRelOver (A : setoid)(B : setoidfamily A)(x x' : A)(p : x ≈ x') :
  B x → B x' → Set :=
  fun y y' => B•p y ≈ y'.

Notation "y ≈[ p ]  y'" := (EqRelOver _ _ _ _ p y y') (at level 70).

Lemma EqRelOverIsIrr (A : setoid)(B : setoidfamily A)
      (x x' : A)(p q : x ≈ x')(y : B x)(y' : B x') :
  y ≈[p] y' → y ≈[q] y'.

Proof.
  intros. assert (B•q y ≈ B•p y).
  apply setoidfamilyirrgeneral. apply setoidrefl.
  apply setoidtra with (y := B•p y). assumption. assumption.
Qed.

Lemma EqRelOverIsRefl (A : setoid)(B : setoidfamily A)
      (x : A)(y : B x) :
  y ≈[setoidrefl A x] y.

Proof.
  apply setoidfamilyrefgeneral.
Qed.

Lemma EqRelOverIsSymm (A : setoid)(B : setoidfamily A)
      (x x' : A)(p : x ≈ x')(y : B x)(y' : B x') :
  y ≈[p] y' → y' ≈[p⁻¹] y.
Proof.
  intros. apply setoidsym.
  assert (B•(p⁻¹) (B•p y) ≈ B•(p⁻¹) y'). apply setoidfamilyirrgeneral. assumption.
  assert (y ≈ B•(p⁻¹) (B•p y)). apply setoidsym. apply setoidfamilycmpinvert.
  apply setoidtra with (y := B•(p⁻¹) (B•p y)). assumption. assumption.
Qed.

Lemma EqRelOverIsTrans (A : setoid)(B : setoidfamily A)
      (x x' x'' : A)(p : x ≈ x')(q : x' ≈ x'')(y : B x)(y' : B x')(y'' : B x'') :
  y ≈[p] y' → y' ≈[q] y'' → y ≈[(q⊙p)] y''.

Proof.
  intros. assert (B•q (B•p y) ≈ y'').
  eauto using setoidfamilyirrgeneral, setoidtra.
  assert (B•(q⊙p) y ≈ B•q (B•p y)).
  apply setoidfamilycmpgeneral_3.
  apply setoidrefl.
  apply setoidtra with (y := B•q (B•p y)). assumption. assumption.
Qed.

Definition TotStdfamEq {A : setoid}(B : setoidfamily A)
           {a a' : A} : a ≈ a' → Set :=
  λ p, sigT (λ z : B a ∧ B a', fst z ≈[p] snd z).

Definition PackTotEq {A : setoid}(B : setoidfamily A)
           {a a' : A}(p : a ≈ a') :
  ∀ b : B a, ∀ b' : B a', b ≈[p] b' → TotStdfamEq B p :=
  λ b b' q, existT _ (b, b') q.

Definition Unpack1 {A : setoid}(B : setoidfamily A)
           {a a' : A}(p : a ≈ a') :
  TotStdfamEq B p → B a :=
  λ v, fst (projT1 v).

Definition Unpack2 {A : setoid}(B : setoidfamily A)
           {a a' : A}(p : a ≈ a') :
  TotStdfamEq B p → B a' :=
  λ v, snd (projT1 v).

Definition UnpackEq {A : setoid}(B : setoidfamily A)
           {a a' : A}(p : a ≈ a') :
  ∀ v : TotStdfamEq B p, Unpack1 B p v ≈[p] Unpack2 B p v :=
  λ v, projT2 v.
