Require Utf8.

Require Import S00_setoid_basics S01_Wty S02_PolyFun S10_Wstd_Obj
         S30_IdType S31_DiscStd S32_IdWty S33_PtwEq S34_Eqvr.

(* The setoid of extensional trees is isomorphic to
   the subsetoid of pointwise equal trees on the equivariant ones. *)

Section Extensional_as_Equivariant.
  Context {X : Set}{B : setoidfamily (dscrStd X)}(isdscrsf : isDscrStdFam B).

  (* Lemma 5.6(i) *)

  Lemma WPER2EqWty_aux : ∀ z, WstdPER_aux B z → EqWty (|B|) (fst z) (snd z).
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

  Lemma WPER2EqWty {w w' : Wty (|B|)}
    : WstdPER B w w' → EqWty (|B|) w w'.
  Proof.
    intro r. apply (WPER2EqWty_aux (w , w') r).
  Qed.

  (* Lemma 5.6(ii) *)

  Lemma ExtIsEqvr {w : Wty (|B|)}
    : WstdPER B w w → isEquivariant (|B|) w.
  Proof.
    induction w as [a f IH]. set (w := sup (|B|) a f).
    intro wext. set (u := (existT (λ x, WstdPER B x x) w wext) : Wstd B).
    refine (supd _ _ _ _ _).
    intros l b. cbn. cbn in *|-.
    apply WPER2EqWty.
    apply (WstdPER_ist wext). apply setoidfamilyrefgeneral_tactical.
    apply isdscrsf.
    exists (l ⁻¹). apply (transpIsEqv2 (|B|) l).
    intro b. specialize (IH b (ist u ↱ setoidrefl (B a) b)).
    apply IH.
  Qed.

  Definition jmap_fnc : Wstd B → EqvrTrees (|B|)
    := λ u, existT _ (projT1 u) (ExtIsEqvr (projT2 u)).

  Definition jmap : Wstd B ⇒ EqvrTrees (|B|).

    apply (Build_setoidmap (Wstd B) (EqvrTrees (|B|)) jmap_fnc).
    intros u u' r. apply (WPER2EqWty r).
  Defined.    

  (* Lemma 5.7 *)

  Lemma eqvrEqWty2WPER {w : Wty (|B|)}(E : isEquivariant (|B|) w)
    : ∀ w', isEquivariant (|B|) w'
            → EqWty (|B|) w w' → WstdPER B w w'.
  Proof.
    induction E as [w eqvr br IH]. intros w' E' eq.
    set (p := nodeEqWty eq).
    apply (isMatch (A := dscrStd X) p).
    intros b b' q. cbn in *|-.
    specialize (IH b (Wty_ist w' b')).
    apply IH. apply (DWty_ist _ _ w' E' b').
    set (l := projT1 (trspDscrSF isdscrsf p b)).
    set (rr := Id2EqWty (|B|) (ap (f := Wty_ist w') (projT2 (trspDscrSF isdscrsf p b)) ⁻¹)).
    (*   : EqWty (|B|) (Wty_ist (|B|) w' (|B|•ᵐp b)) (Wty_ist (|B|) w' (|B|•ᵐl (B•p b)))*)
    set (l' := projT1 (fst (isdscrsf _ (B•p b) b') q)).
    set (rr' := Id2EqWty (|B|) (ap (f := Wty_ist w') (projT2 (fst (isdscrsf _ (B•p b) b') q)))).
  (*   : Wty_ist (|B|) w' (|B|•ᵐl' (B•p b)) == Wty_ist (|B|) w' b'*)
    cbn in *|-.
    refine (EqWty_trans _ _ _ (subtEqWty eq rfl) _).
    refine (EqWty_trans _ _ _ rr _).
    refine (EqWty_trans _ _ _ (eqvrBr E' l (B•p b)) _).
    apply (EqWty_trans _ _ _ (EqWty_symm _ _ (eqvrBr E' l' (B•p b))) rr').
  Qed.

  Definition jinv_fnc : EqvrTrees (|B|) → Wstd B
    := λ ew, existT (λ w, WstdPER B w w)
                    (projT1 ew)
                    (eqvrEqWty2WPER (projT2 ew) (projT1 ew) (projT2 ew)
                                    (setoidrefl (PtwTrees (|B|)) (projT1 ew))).

  Definition jinv : EqvrTrees (|B|) ⇒ Wstd B.

    apply (Build_setoidmap (EqvrTrees (|B|)) (Wstd B) jinv_fnc).
    intros ew ew' ptw. apply (eqvrEqWty2WPER (projT2 ew) (projT1 ew') (projT2 ew') ptw).
  Defined.

  (* Theorem 5.8 *)

  Theorem jiso : jmap ∘ jinv ≈ idmap ∧ jinv ∘ jmap ≈ idmap.
  Proof.
    split.
    intro ew. apply (setoidrefl (EqvrTrees (|B|)) ew).
    intro u. apply (setoidrefl (Wstd B) u).
  Qed.

End Extensional_as_Equivariant.
