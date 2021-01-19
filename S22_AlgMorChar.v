Require Utf8.

Require Import S00_setoid_basics S01_Wty S02_PolyFun S10_Wstd_Obj S11_Wstd_Fam S12_Wstd_Alg S20_AlgGlue S21_TelFam.


(*--------------------------------------------------------------*)
(* Characterisation of algerba morphisms as telescopic families *)
(*--------------------------------------------------------------*)

Section AlgMorChar.
  Context {A : setoid}{B : setoidfamily A}{X : setoid}(algX : PolyObj B X ⇒ X).
  (* Lemma 4.10 *)

  Lemma restrAlgMIsTel (AM : AlgMor (SupMap B) algX) :
    ∀ u, isTelescopic algX (existT _ u (restr_fnc (projT1 AM) u)).
  Proof.
    intros [w refl].
    induction w as [a f IH].
    set (w := sup (setoidfamilyobj A B) a f).
    set (u := existT (λ z, WstdPER B z z) w refl).
    set (l := projT1 AM).
    (* Restriction is the glueing of subrestrictions along algX *)
    assert (H : projT1 (restr l) u ≈ subglue algX u (subrestr l u)).
    intro b. simpl.  
    apply (AlgSquareAlt algX l).
    apply (projT2 AM).
    (* Hence restriction is recursively defined using IH *)
    apply supd with
        (a0 := existT _ (subrestr l u) H).
    intro b. cbn in b. set (s := E_ist u b).
    apply (IH s (setoidrefl _ s)).
  Qed.

  Definition restrTel : AlgMor (SupMap B) algX ⇒ TelFam algX.

    apply (Build_setoidmap (AlgMor (SupMap B) algX) (TelFam algX)
                           (λ AM, existT _ (restr_fnc (projT1 AM)) (restrAlgMIsTel AM))).
    intros AM AM' pp u. cbn.
    intro s. apply pp.
  Defined.

  (* End Lemma 4.10 *)


  (* Lemma 4.16 *)

  Lemma RGisTel (TF : TelFam algX)(u : Wstd B)
    : isTelescopic algX (existT _ u (restr_fnc (glue algX (TF2CF algX TF)) u)).
  Proof.
    set (SF := λ s, projT1 TF (M_ist u s)).
    assert (SF_coh : isCoh (B := SubSubTrees u) SF).
    intros s s' q.
    apply (TelUniqGen algX).
    apply (projT2 TF (M_ist u s)). apply (projT2 TF (M_ist u s')).
    set (SF_eq := (λ _, setoidrefl _ _)
                  : restr_fnc (glue algX (TF2CF algX TF)) u
                              ≈ subglue algX u (existT _ SF SF_coh)).
    apply supd with (a := existT _ (existT _ SF SF_coh) (SF_eq)).
    intro s. cbn in s.
    apply (projT2 TF (M_ist u s)).
  Qed.

  (* Corollary 4.17 *)

  Lemma Tel_is_RGfix (TF : TelFam algX)
    : restr (glue algX (TF2CF algX TF)) ≈ TF2CF algX TF.
  Proof.
    intro u.
    apply (TelUniq algX). apply (RGisTel TF u). apply (projT2 TF u).
  Qed.

  Definition glueTel : TelFam algX ⇒ AlgMor (SupMap B) algX.

    apply (Build_setoidmap (TelFam algX) (AlgMor (SupMap B) algX)
                           (λ TF,  existT _ (glue_fnc algX (TF2CF algX TF))
                                          (RGfix2AlgMor algX (TF2CF algX TF) (Tel_is_RGfix TF)))).
    intros TF TF' pp.
    apply (glue algX ↱ (TF2CF algX ↱ pp)).
  Defined.

  (* Theorem 4.18 *)

  Theorem GRisId : glueTel ∘ restrTel ≈ idmap.
  Proof.
    intro AM.
    apply setoidsym. apply (AlgSquareAlt algX (projT1 AM)).
    apply (projT2 AM).
  Qed.

  Theorem RGisId : restrTel ∘ glueTel ≈ idmap.
  Proof.
    intro TF. apply (Tel_is_RGfix TF).
  Qed.

  (* End Theorem 4.18 *)

End AlgMorChar.
