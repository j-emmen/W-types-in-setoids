Require Utf8.

Require Import S00_setoid_basics S01_Wty S02_PolyFun S10_Wstd_Obj S11_Wstd_Fam S12_Wstd_Alg S20_AlgGlue S21_TelFam S22_AlgMorChar.

(*-------------*)
(* Initiality  *)
(*-------------*)

Section InitWstd.
  Context  {A : setoid}{B : setoidfamily A}{X : setoid}(algX : PolyObj B X ⇒ X).
  
  Definition initWmap : Wstd B ⇒ X
    := projT1 (glueTel algX (telfam algX)).

  Lemma initWcomm : initWmap ∘ SupMap B ≈ algX ∘ PolyArr B initWmap.
  Proof.
    apply (projT2 (glueTel algX (telfam algX))).
  Qed.

  Lemma initWuniq : ∀ l,
      isAlgMor (SupMap B) algX l → l ≈ initWmap.
  Proof.
    intros l isAM. set (AM := existT _ l isAM).
    cut (glueTel algX (restrTel algX AM) ≈  glueTel algX (telfam algX)).
    intros H u. refine (H u ⊙ _).
    apply setoidsym. apply (GRfixIffAlgMor algX l). apply isAM.
    apply setoidmapextensionality.
    apply TelFam_subsing.
  Qed.
  
  Lemma AlgMorSup_subsing (AM AM' : AlgMor (SupMap B) algX)
    : AM ≈ AM'.
  Proof.
    cut (glueTel algX (restrTel algX AM) ≈  glueTel algX (restrTel algX AM')).
    intro H. refine (_ ⊙ H ⊙ _).
    apply setoidsym. apply (GRfixIffAlgMor algX (projT1 AM)). apply (projT2 AM).
    apply (GRfixIffAlgMor algX (projT1 AM')). apply (projT2 AM').
    apply setoidmapextensionality.
    apply TelFam_subsing.
  Qed.

  (* Theorem 4.20 *)

  Theorem initW : ∃ l : Wstd B ⇒ X,
      isAlgMor (SupMap B) algX l
      ∧ (∀ l', isAlgMor (SupMap B) algX l' → l' ≈ l).

  Proof.
    exists initWmap.
    split. apply initWcomm.
    apply initWuniq.
  Qed.

End InitWstd.
