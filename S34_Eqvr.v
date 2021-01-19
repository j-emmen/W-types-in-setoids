Require Utf8.

Require Import S00_setoid_basics S01_Wty S30_IdType S33_PtwEq.

(* Equivariant trees *)

(* Definition 5.5 *)

Definition isEquivariant {X : Set}(Y : X → Set) : Wty Y → Set
  := @DWty (Wty Y)
             (λ w, ∀ l : Wty_node Y w == Wty_node Y w, ∀ y,
                   EqWty Y (Wty_ist w (Y•ᵐl y)) (Wty_ist w y))
             (λ w eqvr, Y (Wty_node Y w))
             (λ w eqvr y, Wty_ist w y).

Definition eqvrBr {X : Set}{Y : X → Set}{w : Wty Y}
  : isEquivariant Y w
    → ∀ l : Wty_node Y w == Wty_node Y w, ∀ y,
        EqWty Y (Wty_ist w (Y•ᵐl y)) (Wty_ist w y)
  := λ E, DWty_node _ _ w E.

Definition eqvrSubT {X : Set}{Y : X → Set}{w : Wty Y}
  : isEquivariant Y w
    → ∀ y : Y (Wty_node Y w),
        isEquivariant Y (Wty_ist w y)
  := λ E, DWty_ist _ _ w E.

Definition eqvr_inj_fnc {X : Set}(Y : X → Set) : sigT (isEquivariant Y) → PtwTrees Y
  := λ ew, projT1 ew.

Definition EqvrTrees {X : Set}(Y : X → Set) : setoid.

  apply (Build_setoid (sigT (isEquivariant Y)) (λ ew ew', eqvr_inj_fnc Y ew ≈ eqvr_inj_fnc Y ew')).
  apply Build_setoidaxioms.
  intro. apply setoidrefl.
  intros. apply setoidsym. apply H.
  intros ew ew' ew''. apply setoidtra with (y := eqvr_inj_fnc Y ew').
Defined.

Definition eqvr_inj {X : Set}(Y : X → Set) : EqvrTrees Y ⇒ PtwTrees Y.

  apply (Build_setoidmap (EqvrTrees Y) (PtwTrees Y) (eqvr_inj_fnc Y)).
  intros ew ew' p. apply p.
Defined.
