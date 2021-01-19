Require Utf8.

Require Import S00_setoid_basics S01_Wty S30_IdType.

(* Basics on the identity type of W-types  *)

Section IdWty.
  Context {X : Set}{Y : X → Set}.

  Definition Wty_node_eq {w w' : Wty Y}
    : w == w' → Wty_node Y w == Wty_node Y w'
    := Identity_congr (Wty_node Y) w w'.

  Definition Wty_ist_eq {w w' : Wty Y}(r : w == w')
    : Wty_ist w == Wty_ist w' · Y•ᵐ(Wty_node_eq r).

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

  Definition ηWty : ∀ w, sup Y (Wty_node Y w) (Wty_ist w) == w.

    intros [x f]. apply rfl.
  Defined.
End IdWty.
