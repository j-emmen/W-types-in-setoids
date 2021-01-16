
Require Import S00_setoid_basics.

(*------------------*)
(* Standard W-types *)
(*------------------*)

Inductive Wty {A : Set}(B : A → Set) : Set
  := sup : (∀ x : A, ∀ f : B(x) → (Wty B), Wty B).

Definition Wty_node {A : Set}(B : A → Set) : Wty B → A.
  
  intros [a f]. apply a.
Defined.


Definition Wty_ist {A : Set}{B : A → Set}(w : Wty B)
  : B (Wty_node B w) → Wty B.
  
  destruct w as [a f]. apply f.
Defined.


(*-------------------*)
(* Dependent W-types *)
(*-------------------*)

Inductive DWty {I : Set}{A : I → Set}(B : ∀ i, A i → Set)
          (d : ∀ i a, B i a → I)(i : I) : Set
  := supd : (∀ a : A i,
               ∀ f : (∀ b : B i a, DWty B d (d i a b)),
                 DWty B d i).

Definition DWty_node {I : Set}{A : I → Set}(B : ∀ i, A i → Set)
           (d : ∀ i a, B i a → I)(i : I) : DWty B d i → A i.

  intros [a f]. apply a.
Defined.

Definition DWty_ist {I : Set}{A : I → Set}(B : ∀ i, A i → Set)
           (d : ∀ i a, B i a → I)(i : I)(r : DWty B d i)
  : ∀ b :B i (DWty_node B d i r), DWty B d (d i (DWty_node B d i r) b).
  
  destruct r as [a f]. apply f.
Defined.
