Require Utf8.

Require Import S00_setoid_basics S01_Wty S02_PolyFun S10_Wstd_Obj S11_Wstd_Fam S12_Wstd_Alg S20_AlgGlue.

(*---------------------*)
(* Telescopic families *)
(*---------------------*)

Section TelFam.
  Context  {A : setoid}{B : setoidfamily A}{X : setoid}(algX : PolyObj B X ⇒ X).

  (* Definition 4.7 *)
  
  Definition isTelescopic : sigT (λ u, ImSubTrees B u ⇒ X) → Set :=
    @DWty (sigT (λ u, ImSubTrees B u ⇒ X))
          (λ K, sigT (λ CF, projT2 K ≈ subglue algX (projT1 K) CF))
          (λ K CFE, ImSubTrees B (projT1 K))
          (λ K CFE s, existT _ (M_ist (projT1 K) s) (projT1 (projT1 CFE) s)).

  Definition isTel_CFam {u : Wstd B}{k : ImSubTrees B u ⇒ X}(tel : isTelescopic (existT _ u k))
    : CohFam (SubSubTrees u) X
    := projT1 (DWty_node _ _ (existT _ u k) tel).

  Definition isTel_Eq {u : Wstd B}{k : ImSubTrees B u ⇒ X}(tel : isTelescopic (existT _ u k))
    : k ≈ subglue algX u (isTel_CFam tel)
    := projT2 (DWty_node _ _ (existT _ u k) tel).

  Definition isTel_TFam {u : Wstd B}{k : ImSubTrees B u ⇒ X}(tel : isTelescopic (existT _ u k))
    : ∀ s : ImSubTrees B u,
      isTelescopic (existT _ (M_ist u s) (projT1 (isTel_CFam tel) s))
    := DWty_ist _ _ (existT _ u k) tel.

  (* Definition 4.8 *)
  
  Definition TelFam : setoid.

    apply (Build_setoid (sigT (λ F : ∀ u, ImSubTrees B u ⇒ X,
                                 ∀ u, isTelescopic (existT _ u (F u))))
                        (λ TF TF', ∀ u, projT1 TF u ≈ projT1 TF' u)).
    apply (Build_setoidaxioms).
    swesetoid. swesetoid. swesetoid.
  Defined.

  Definition Tel_CFam : TelFam → ∀ u, CohFam (SubSubTrees u) X
    := λ TF u, isTel_CFam (projT2 TF u).

  Definition Tel_Eq (TF : TelFam) : ∀ u, projT1 TF u ≈ subglue algX u (Tel_CFam TF u)
    := λ u, isTel_Eq (projT2 TF u).

  Definition Tel_TFam (TF : TelFam)
    : ∀ u, ∀ s : ImSubTrees B u,
        isTelescopic (existT _ (M_ist u s) (projT1 (Tel_CFam TF u) s))
    := λ u, isTel_TFam (projT2 TF u).

End TelFam.

(* Various results about telescopic families *)

Section Tel_Prop.
  Context  {A : setoid}{B : setoidfamily A}{X : setoid}(algX : PolyObj B X ⇒ X).

  (* Lemma 4.11 *)

  Lemma TelUniq_aux (K : ∃ u : Wstd B, ImSubTrees B u ⇒ X)(tel : isTelescopic algX K)
    : ∀ k : ImSubTrees B (projT1 K) ⇒ X,
      isTelescopic algX (existT _ (projT1 K) k) → k ≈ projT2 K.
  Proof.
    induction tel as [K CFE TF IH].
    set (u := projT1 K).
    set (CF := projT1 CFE).
    set (glEq := projT2 CFE).
    intros k tel'.
    apply setoidtra with (y := subglue algX u (isTel_CFam algX tel')).
    apply isTel_Eq.
    apply setoidtra with (y := subglue algX u CF).
    2: { apply setoidsym, glEq. }
    apply (setoidmapextensionality _ _ (subglue algX u)).
    intros s ss. apply IH. cbn. apply (isTel_TFam algX tel').
  Qed.

  Theorem TelUniq (u : Wstd B)(k k' : ImSubTrees B u ⇒ X)
    : isTelescopic algX (existT _ u k) → isTelescopic algX (existT _ u k')
      → k ≈ k'.
  Proof.
    intros tel tel'.
    apply (TelUniq_aux (existT _ u k') tel' k tel).
  Qed.

  (* End Lemma 4.11 *)

  (* Corollary 4.12 *)

  Lemma TelFam_subsing (TF TF' : TelFam algX) : TF ≈ TF'.
  Proof.
    intro u.
    apply TelUniq.
    apply (projT2 TF u). apply (projT2 TF' u).
  Qed.
  
  (* Lemma 4.13 *)
  
  Lemma transpIsTel (K : ∃ u : Wstd B, ImSubTrees B u ⇒ X)(tel : isTelescopic algX K)
    : ∀ u', ∀ r' : u' ≈ projT1 K,
        isTelescopic algX (existT _ u' (projT2 K ∘ (ImSubTrees B)•r')).
  Proof.
    induction tel as [K CFE TF IH].
    set (u := projT1 K).
    set (k := projT2 K : ImSubTrees B u ⇒ X).
    set (CF := projT1 CFE).
    set (glEq := projT2 CFE).
    
    intros u' r'.
    set (CF' := CohFamSST_trsp r' CF).
    assert (H : k ∘ (ImSubTrees B)•r' ≈ subglue algX u' CF').
    intro s'. refine (_ ⊙ glEq ((ImSubTrees B)•r' s')).
    apply setoidsym. apply (subglue_coh algX r').
    intro s''. apply setoidrefl.
    apply supd with (a := existT _ CF' H).
    intro s'. cbn in s'. set (r := r' ˢ).
    specialize IH with (b := (ImSubTrees B)•r' s')
                       (u' := M_ist u' s')
                       (r' := M_ist_coh r' s').
    apply IH.
  Qed.

  (* Lemma 4.14 *)

  Theorem TelUniqGen {u u' : Wstd B}(r : u ≈ u')
          (k : ImSubTrees B u ⇒ X)(k' : ImSubTrees B u' ⇒ X)
    : isTelescopic algX (existT _ u k) → isTelescopic algX (existT _ u' k')
      → k ≈ k' ∘ (ImSubTrees B)•r.
  Proof.
    intros tel tel'.
    assert (H : isTelescopic algX (existT _ u (k' ∘ (ImSubTrees B)•r))).
    apply (transpIsTel (existT _ u' k') tel').
    apply (TelUniq u k (k' ∘ (ImSubTrees B)•r) tel H).
  Qed.

  Theorem TelUniqGenInv {u u' : Wstd B}(r : u ≈ u')
          (k : ImSubTrees B u ⇒ X)(k' : ImSubTrees B u' ⇒ X)
    : isTelescopic algX (existT _ u k) → isTelescopic algX (existT _ u' k')
    → k ∘ (ImSubTrees B)•(r ˢ) ≈ k'.
  Proof.
    intros tel tel'. apply setoidtra with (y := k' ∘ ((ImSubTrees B)•r ∘ (ImSubTrees B)•(r ˢ))).
    intro s'. apply (TelUniqGen r k k' tel tel' ((ImSubTrees B)•(r ˢ) s')).
    apply setoidmaprid_tactical with (f := k'). intro s'. apply setoidfamilycmpinvert.
  Qed.
                 
End Tel_Prop.

(* Telescopic families are coherent *)

(* Corollary 4.15 *)

Theorem  Tel_is_Coh {A : setoid}{B : setoidfamily A}{X : setoid}(algX : PolyObj B X ⇒ X)
         (TF : TelFam algX) : isCoh (projT1 TF).
Proof.
  intros u u' r.
  apply (TelUniqGen algX).
  apply (projT2 TF u). apply (projT2 TF u').
Qed.

Definition TF2CF {A : setoid}{B : setoidfamily A}{X : setoid}(algX : PolyObj B X ⇒ X)
  : TelFam algX ⇒ CohFam (ImSubTrees B) X.

  apply (Build_setoidmap (TelFam algX) (CohFam (ImSubTrees B) X)
                         (λ TF, existT _ (projT1 TF) (Tel_is_Coh algX TF))).
  intros TF TF' pp. apply pp.
Defined.

(* A telescopic family *)

(* Proposition 4.19 *)

Definition telfam_aux {A : setoid}{B : setoidfamily A}{X : setoid}(algX : PolyObj B X ⇒ X)
  (u : Wstd B) : ∃ k : ImSubTrees B u ⇒ X, isTelescopic algX (existT _ u k).

  destruct u as [w refl]. induction w as [a f IH].
  set (w := sup _ a f). set (u := existT (λ x, WstdPER B x x) w refl).
  set (F := λ b, projT1 (IH b (ist u ↱ setoidrefl (B a) b))).
  set (tel := λ b, projT2 (IH b (setoidrefl ((ImSubTrees B) u) b))).
  assert (C : isCoh (B := SubSubTrees u) F).
  intros s s' q.
  apply TelUniqGen with (algX0 := algX)
                        (u0 := (M_ist u s))
                        (u' := (M_ist u s'))
                        (r := q).
  apply (tel s). apply (tel s').
  set (CF := existT _ F C : CohFam (SubSubTrees u) X).
  set (k := subglue algX u CF).
  exists k.
  apply supd with (a0 := existT _ CF (setoidrefl _ k)).
  apply tel.
Defined.

Definition telfam {A : setoid}{B : setoidfamily A}{X : setoid}(algX : PolyObj B X ⇒ X)
  : TelFam algX
  := existT (λ F, ∀ u, isTelescopic algX (existT _ u (F u)))
            (λ u, projT1 (telfam_aux algX u))
            (λ u, projT2 (telfam_aux algX u)).

(* End Proposition 4.19 *)
