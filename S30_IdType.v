Require Utf8.

Require Import S00_setoid_basics.

Inductive Identity {A: Set}(x: A) : A -> Set
  := Identity_refl : Identity x x.

Notation "x == y" := (Identity x y)
                       (at level 70, no associativity, only parsing).

Notation "x =={ A } y" := (@Identity A x y)
                            (at level 70, no associativity, only parsing).

Definition rfl {A : Set}{x : A} : x == x
  := Identity_refl x.

Theorem Identity_congr {A B: Set}(f:A -> B)(x y:A):
Identity x y -> Identity (f x) (f y).
Proof.
  intro P. destruct P. apply rfl.
Defined.

Definition Identity_trans  {A: Set}{a b c:A}: 
Identity a b -> Identity b c -> Identity a c.
  intros p q. destruct p. apply q.
Defined.

Definition Identity_sym  {A: Set}{a b:A}: 
Identity a b -> Identity b a.
  intros p. destruct p. apply rfl.
Defined.

Notation "p ⁻¹" := (Identity_sym p)
                     (at level 3, no associativity).

Notation "p ⊙ᵐ q" := (Identity_trans p q)
                      (at level 34, right associativity).

Notation "f ↱ᵐ p" := (Identity_congr f _ _ p)
                      (at level 100).

Definition ap {A B : Set}{f : A → B}{x x' : A}
  : x == x' → f x == f x'
  := Identity_congr f x x'.

Definition setcmp {A B C : Set}
  : (A → B) → (B → C) → A → C
  := fun f g x => g (f x).

Notation "g · f" := (setcmp f g) (at level 34, right associativity).

Definition transp {A : Set}(B : A → Set){x x' : A} :
  x == x' → B x → B x'.

  intro p. destruct p. apply (λ y, y).
Defined.

Notation "B •ᵐ p" := (transp B p)
                      (at level 9, right associativity).

Definition Identity_congr_dep {A : Set}(B : A → Set)
           (f : ∀ x, B x){x x' : A} :
  ∀ u : x == x', (B•ᵐu (f x)) == (f x').

  intro u. destruct u. apply Identity_refl.
Defined.

Notation "f ↱ᵈᵐ p" := (Identity_congr_dep _ f p)
                        (at level 100).                        

Definition HIdΠ {A : Set}{B : A → Set}(f f' : ∀ x : A, B x) : Set :=
  ∀ x, f x == f' x.

Definition Id2HΠ {A : Set}{B : A → Set}{f f' : ∀ x : A, B x} :
  f == f' → HIdΠ f f'.

intro p. destruct p. unfold HIdΠ. apply (λ x, Identity_refl (f x)).
Defined.



Definition transpCongr {A : Set}{B : A → Set}{x x' : A}(p : x == x'){y y' : B x}
  : y == y' → B•ᵐp y == B•ᵐp y'.

  intros q. destruct p. apply q.
Defined.  

Definition transpIsFunct {A : Set}{B : A → Set}{x x' x'' : A}
           (p : x == x')(q : x' == x'') :
  B•ᵐ(p⊙ᵐq) == B•ᵐq · B•ᵐp.

  destruct p. apply Identity_refl.
Defined.


Definition transpfunct {A : Set}{B : A → Set}{x x' x'' : A}
           (p : x == x')(q : x' == x'')
  : ∀ y y', (B•ᵐq · B•ᵐp) y == y' → B•ᵐ(p⊙ᵐq) y == y'.
  
  intros y y' r. apply (Identity_trans (b := (B•ᵐq · B•ᵐp) y)).
  apply (Id2HΠ (transpIsFunct p q) y). apply r.
  (*destruct p. apply r.*)
Defined.

  
Definition transpfunct_rev {A : Set}{B : A → Set}{x x' x'' : A}
           (p : x == x')(q : x' == x''){y : B x}{y' : B x''}
  : B•ᵐ(p⊙ᵐq) y == y' → (B•ᵐq · B•ᵐp) y == y'.
  
  intros r. apply (Identity_trans (b := B•ᵐ(p⊙ᵐq) y)).
  apply Identity_sym. apply (Id2HΠ (transpIsFunct p q) y).
  apply r.
Defined.

Definition transpEq {A : Set}(B : A → Set){x x' : A}
           (p p' : x == x')(h : p == p') :
  B•ᵐp == B•ᵐp'.

  apply ((λ u, B•ᵐu)↱ᵐh).
Defined.

Definition transpIsEqv1 {A : Set}(B : A → Set){x x' : A}
           (p : x == x') :
  ∀ y, B•ᵐp (B•ᵐp⁻¹ y) == y.

  destruct p. apply Identity_refl.
Defined.

Definition transpIsEqv2 {A : Set}(B : A → Set){x x' : A}
           (p : Identity x x') :
  ∀ y, B•ᵐp⁻¹ (B•ᵐp y) == y.

  destruct p. apply Identity_refl.
Defined.


Definition transpflip {A : Set}(B : A → Set){x x' : A}
           (p : Identity x x')
  : ∀ y y', B•ᵐp y == y' → y == B•ᵐp⁻¹ y'.

  intros y y' q. destruct p. apply q.
Defined.

Definition transpflip_inv {A : Set}(B : A → Set){x x' : A}
           (p : Identity x x')
  : ∀ y y', y == B•ᵐp⁻¹ y' → B•ᵐp y == y'.

  intros y y' q. destruct p. apply q.
Defined.

Definition transpcmp {A : Set}(B : A → Set){x x' x'' : A}
           (p : x == x')(q : x' == x''){y : B x}{y' : B x'}{y'' : B x''}
  : B•ᵐp y == y' → B•ᵐq y' == y'' → B•ᵐ(p⊙ᵐq) y == y''.

  intros r s. apply transpfunct.
  refine (_⊙ᵐs).
  apply transpCongr. apply r.
Defined.


Definition HIdΣ {A : Set}{B : A → Set}(z z' : sigT B) : Set :=
  ∃ p : projT1 z == projT1 z', B•ᵐp (projT2 z) == projT2 z'.

Definition extΣ {A : Set}{B : A → Set}(z z' : sigT B) :
              HIdΣ z z' → z == z'.

  destruct z as [a b]. destruct z' as [a' b'].
  intro r. destruct r as [p q]. simpl in *|-.
  destruct p. destruct q.
  apply rfl.
Defined.


Definition EqOver {A : Set}(B : A → Set){x x' : A}(p : x == x')
  : B x → B x' → Set
  := λ y y', B•ᵐp y == y'.

Notation "y ==[ p ] y'" := (EqOver _ p y y')
  (at level 70, no associativity, only parsing).


Definition TotEq {A : Set}(B : A → Set){x x' : A}
  : x == x' → Set
  := λ p, (sigT (λ z, EqOver B p (fst z) (snd z))).


Definition isTotEq {A : Set}(B : A → Set){x x' : A}(p : x == x')
  : ∀ y : B x, ∀ y' : B x', y ==[p] y' → TotEq B p
  :=  λ y y' q, existT _ (y , y') q.

Definition fstTotEq {A : Set}(B : A → Set){x x' : A}{p : x == x'}
  : TotEq B p → B x
  := λ v, fst (projT1 v).

Definition sndTotEq {A : Set}(B : A → Set){x x' : A}{p : x == x'}
  : TotEq B p → B x'
  := λ v, snd (projT1 v).

Definition eqTotEq {A : Set}(B : A → Set){x x' : A}{p : x == x'}(v : TotEq B p)
  : fstTotEq B v ==[p] sndTotEq B v
  := projT2 v.


Lemma domtransp  {A Y : Set}{B : A → Set}{x x' : A}(p : x == x')
  : ∀ f f', f == f' · B•ᵐp → (λ x, B x → Y)•ᵐp f == f'.
Proof.
  intros f f' q. destruct p. apply q.
Qed.
