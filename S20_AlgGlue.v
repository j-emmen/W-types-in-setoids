Require Utf8.

Require Import S00_setoid_basics S01_Wty S02_PolyFun S10_Wstd_Obj S11_Wstd_Fam S12_Wstd_Alg.

(*--------------------------*)
(* Glue and restr functions *)
(*--------------------------*)

Section Restriction.
  Context  {A : setoid}{B : setoidfamily A}{X : setoid}.
  
  (* Definition 4.1(17) *)
  
  Definition restr_fnc : (Wstd B ⇒ X) → ∀ u, ImSubTrees B u ⇒ X
    := λ h u, h ∘ M_ist u.

  (* Proposition 4.2(i) *)
  
  Definition restrIsCoh (h : Wstd B ⇒ X) : isCoh (restr_fnc h).

    intros s s' q ss. apply (setoidmapextensionality _ _ h).
    apply (M_ist_coh q ss).
  Defined.

  (* Proposition 4.2(iii) *)
  
  Definition restr : (Wstd B ⇒ X) ⇒ CohFam (ImSubTrees B) X.

    apply (Build_setoidmap (Wstd B ⇒ X) (CohFam (ImSubTrees B) X)
                           (λ h, existT _ (restr_fnc h) (restrIsCoh h))).
    intros h h' p u s. cbn. apply (p (ist u s)).
  Defined.
  
  Definition subrestr : (Wstd B ⇒ X) → ∀ u, CohFam (SubSubTrees (B := B) u) X.      

    intros h u. exists (λ s, restr_fnc h (M_ist u s)).
    intros s s' q ss. apply (setoidmapextensionality _ _ h).
    apply M_ist_coh with (r := q).
  Defined.

End Restriction.

Section Glueing_along_Algebra.
  Context  {A : setoid}{B : setoidfamily A}{X : setoid}(algX : PolyObj B X ⇒ X).
  
  (* Definition 4.1(18) and Proposition 4.2(ii,iv) *)
  
  Definition glue_fnc : CohFam (ImSubTrees B) X → Wstd B ⇒ X
    := λ  CF, algX ∘ InPoly (node B) (E_action CF).
  
  Definition glue : CohFam (ImSubTrees B) X ⇒ Wstd B ⇒ X.

    apply (Build_setoidmap _ _ glue_fnc).
    intros CF CF' p u. apply (setoidmapextensionality _ _ algX).
    exists (setoidrefl _ (node B u)). cbn. intro b.
    refine (_ ⊙ (p u b)). apply (setoidmapextensionality _ _ (projT1 CF' u)).
    apply setoidmapextensionality. apply setoidfamilyrefgeneralinv.
  Defined.

  (* Proposition 4.2(v) *)

  Lemma GRfixIffAlgMor (h : Wstd B ⇒ X)
    : glue (restr h) ≈ h ↔ isAlgMor (SupMap B) algX h.
  Proof.
    split.
    intro H. apply (AlgSquareAlt algX h). apply (H ˢ).
    intro H. apply setoidsym. apply (AlgSquareAlt algX h). apply H.
  Qed.

  (* Proposition 4.2(vi) *)
  
  Lemma RGfix2AlgMor (CF : CohFam (ImSubTrees B) X)
    : restr (glue CF) ≈ CF → isAlgMor (SupMap B) algX (glue CF).
  Proof.
    intro H. intros [a f]. set (u := SupFnc B (existT _ a f)).
    apply (setoidmapextensionality _ _ algX).
    exists (setoidrefl _ a).
    intro b. specialize (H u b).
    refine (_ ⊙ H ˢ).
    apply setoidtra with (y := projT2 (PolyArr B (glue CF) (existT _ a f)) b).
    2: { apply (setoidmapextensionality _ _ (projT2 (PolyArr B (glue CF) (existT _ a f)))).
         apply setoidfamilyrefgeneralinv. }
    assert (K : PolyArr B (glue CF) (UnsupMap B u)
                   ≈ PolyArr B (glue CF) (existT (λ a0 : A, B a0 ⇒ Wstd B) a f)).
    apply (setoidmapextensionality _ _ (PolyArr B (glue CF))).
    exists (setoidrefl _ _). intro bb. cbn in bb. apply (setoidmapextensionality _ _ f).
    apply setoidfamilyrefgeneralinv.
    apply setoidfamilyrefgeneralfunction_rev with (f0 := projT2 (PolyArr B (glue CF) (UnsupMap B u)))
                                                  (f' := projT2 (PolyArr B (glue CF) (existT (λ a0 : A, B a0 ⇒ Wstd B) a f)))
                                                  (p := projT1 K).
    apply (projT2 K).
Qed.    
  
  (* CohFamSST_trsp only needed in Lemma 4.13 *)
  
  Definition CohFamSST_trsp {u u' : Wstd B}(r : u ≈ u')
    : CohFam (SubSubTrees u') X → CohFam (SubSubTrees u) X.

    intro CF'. exists (λ s, projT1 CF' ((ImSubTrees B)•r s) ∘ (ImSubTrees B)•(M_ist_coh r s)).
    cbn in CF'. unfold isCoh in CF'.
    intros s₁ s₂ q ss.
    set (s'₁ := (ImSubTrees B)•r s₁). set (s'₂ := (ImSubTrees B)•r s₂).
    set (q' := (ImSubTrees B)•r ↱ q : s'₁ ≈ s'₂).
    set (ss' := (ImSubTrees B)•(M_ist_coh r s₁) ss).
    set (C' := projT2 CF' s'₁ s'₂ q').
    refine (_ ⊙ C' ss').
    apply (setoidmapextensionality _ _ (projT1 CF' s'₂)).
    assert ( H1 : (ImSubTrees B)•q' ss' ≈ (ImSubTrees B)•(q' ⊙ (M_ist_coh r s₁)) ss ).
    apply setoidfamilycmpgeneral.
    refine (_ ⊙ H1).
    assert ( H2 : (ImSubTrees B)•(M_ist_coh r s₂ ⊙ (M_ist u ↱ q)) ss
                          ≈ (ImSubTrees B)•(M_ist_coh r s₂) ((ImSubTrees B)•q ss)).
    apply setoidsym, setoidfamilycmpgeneral.
    refine (H2 ⊙ _).
    apply setoidfamilyirr.
  Defined.

  
  (*------------------------------------*)
  (* Glueing of families on subsubtrees *)
  (*------------------------------------*)
  
  (* Lemma 4.5(i) *)

  Definition subglue_fnc (u : Wstd B)
    : CohFam (SubSubTrees u) X → ImSubTrees B u ⇒ X
    := λ CF, algX ∘ InPoly (node B ∘ M_ist (B := B) u) (subE_action (B := B) u CF).

  (* Lemma 4.5(ii) *)
                                           
  Definition subglue (u : Wstd B)             
    : CohFam (SubSubTrees u) X ⇒ ImSubTrees B u ⇒ X.

    apply (Build_setoidmap (CohFam (SubSubTrees u) X) (ImSubTrees B u ⇒ X) (subglue_fnc u)).
    intros CF CF' pp s. apply (setoidmapextensionality (PolyObj B X) X algX).
    set (rn := setoidrefl A (node B (M_ist u s))).
    exists rn. cbn.
    intro bb. refine (_ ⊙ pp s bb).
    apply (setoidmapextensionality (B (node B (M_ist u s))) X
                                   (projT1 CF' s ∘ E_ist (M_ist u s))).
    apply setoidfamilyrefgeneralinv with (F := B)
                                         (x := node B (M_ist u s))
                                         (p := rn)
                                         (y := bb).
  Defined.

  (* Lemma 4.5(iii) *)
  
  Lemma subglue_coh {u u' : Wstd B}(r : u ≈ u')
        {CF : CohFam (SubSubTrees u) X}{CF' : CohFam (SubSubTrees u') X}
    : (∀ s, projT1 CF s ≈ projT1 CF' ((ImSubTrees B)•r s) ∘ (ImSubTrees B)•(M_ist_coh r s))
           → subglue_fnc u CF ≈ subglue_fnc u' CF' ∘ (ImSubTrees B)•r.
  Proof.
    intros H s. apply (setoidmapextensionality _ _ algX).
    exists (node B ↱ (M_ist_coh r s)).
    intro ss. refine (_ ⊙ H s ss).
    apply (setoidmapextensionality _ _ (projT1 CF' ((ImSubTrees B)•r s))).
    apply setoidrefl.
  Qed.
  
End Glueing_along_Algebra.
