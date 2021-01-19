Require Utf8.

Require Import S00_setoid_basics S01_Wty S02_PolyFun S10_Wstd_Obj.


(* Section 3.2 *)


(*--------------------*)
(* Family of branches *)
(*--------------------*)

Definition Branches {A : setoid}(B : setoidfamily A) : setoidfamily (Wstd B).

  apply (Build_setoidfamily (Wstd B) (λ u, B (node B u)) (λ u u' r, B•(node B ↱ r))).
  apply Build_setoidfamilyaxioms.
  intros u s. apply setoidfamilyrefgeneral.
  intros u u' r r' s. apply setoidfamilyirr.
  intros u u' u'' r r' s. apply setoidfamilycmpgeneral.
Defined.

(*------------------------------*)
(* Family of immediate subtrees *)
(*------------------------------*)

(* Definition 3.8 - Start *)

Definition ImSubTrees_std {A : setoid}(B : setoidfamily A)(u : Wstd B) : setoid.

  apply (Build_setoid (B (node B u))
                      (λ b b', ist u b ≈ ist u b')).
  apply Build_setoidaxioms.
  intro b. apply setoidrefl.
  intros b b'. apply setoidsym.
  intros b b' b''. apply setoidtra.
Defined.

Definition ImSubTrees_fnc {A : setoid}(B : setoidfamily A){u u' : Wstd B}(r : u ≈ u')
  : ImSubTrees_std B u → ImSubTrees_std B u'
  := B•(node B ↱ r).

Definition ImSubTrees_map {A : setoid}(B : setoidfamily A){u u' : Wstd B}(r : u ≈ u')
  : ImSubTrees_std B u ⇒ ImSubTrees_std B u'.

  apply (Build_setoidmap (ImSubTrees_std B u) (ImSubTrees_std B u') (ImSubTrees_fnc B r)).
  intros s s' q. apply ist_coh_tactical. apply q.
Defined.

Definition ImSubTrees {A : setoid}(B : setoidfamily A) : setoidfamily (Wstd B).

  apply (Build_setoidfamily (Wstd B) (ImSubTrees_std B) (@ImSubTrees_map A B)).
  apply Build_setoidfamilyaxioms.
  intros u s. apply setoidmapextensionality. apply setoidfamilyrefgeneral.
  intros u u' r r' s. apply (setoidmapextensionality _ _ (ist u')).
  apply setoidfamilyirr.
  intros u u' u'' r r' s. apply (setoidmapextensionality _ _ (ist u'')).
  apply setoidfamilycmpgeneral.
Defined.

(* Definition 3.8 - End *)

(* Remark 3.9 *)

Section Factorisation.
  Context {A : setoid}{B : setoidfamily A}.
(* 'E_ist u' is eᵤ in the remark *)
(* 'M_ist u' is mᵤ in the remark *)
  
  Definition E_ist (u : Wstd B)
    : B (node B u) ⇒ ImSubTrees B u.

    apply (Build_setoidmap (B (node B u)) (ImSubTrees B u) (λ b, b)).
    intros b b' q. apply setoidmapextensionality. apply q.
  Defined.

  Definition M_ist (u : Wstd B)
    : ImSubTrees B u ⇒ Wstd B.

    apply (Build_setoidmap _ _ (λ b : ImSubTrees B u, ist u b)).
    intros b b' q. apply q.
  Defined.

  Lemma ist_fact (u : Wstd B)
    : M_ist u ∘ E_ist u ≈ ist u.
  Proof.
    intro b. apply setoidrefl.
  Qed.

End Factorisation.

(*------------------------------------------------------------*)
(* Families of immediate subsubtrees of immediate subsubtrees *)
(*------------------------------------------------------------*)

Definition SubSubTrees {A : setoid}{B : setoidfamily A}(u : Wstd B)
  : setoidfamily (ImSubTrees B u)
  := ridx_std (M_ist u) (ImSubTrees B).

Definition SubBranches {A : setoid}{B : setoidfamily A}(u : Wstd B)
  : setoidfamily (ImSubTrees B u)
  := ridx_std (M_ist u) (Branches B).

        
(* Remark 3.10 *)

Section Coherence_stuff.
  Context {A : setoid}{B : setoidfamily A}.
  
  Lemma M_ist_coh {u u' : Wstd B}(r : u ≈ u')
        : M_ist u ≈ M_ist u' ∘ (ImSubTrees B)•r.
  Proof.
    apply ist_coh.
  Qed.
  
  Lemma E_ist_coh {u u' : Wstd B}(r : u ≈ u')
    : (ImSubTrees B)•r ∘ E_ist u ≈ E_ist u' ∘ (Branches  B)•r.
  Proof.
    intro b. apply setoidrefl.
  Qed.
  Lemma E_ist_coh_tact {X : setoid}{F : ∀ u, ImSubTrees B u ⇒ X}
    : isCoh F → isCoh (B := Branches B) (λ u, F u ∘ E_ist u).
  Proof.
    intro FC. apply FC.
  Qed.

  Definition E_action_fnc {X : setoid} : CohFam (ImSubTrees B) X → CohFam (Branches B) X
    := λ CF, existT _ (λ u, projT1 CF u ∘ E_ist u) (projT2 CF).

  Definition E_action {X : setoid}
    : CohFam (ImSubTrees B) X ⇒ CohFam (Branches B) X.

    apply (Build_setoidmap _ _ E_action_fnc).
    intros CF CF' p u b. apply (p u b).
  Defined.
  
  Definition subE_action (u : Wstd B){X : setoid}
    : CohFam (SubSubTrees u) X ⇒ CohFam (SubBranches u) X.

    apply (Build_setoidmap (CohFam (SubSubTrees u) X) (CohFam (SubBranches u) X)
                           (λ CF, existT _ (λ s, projT1 CF s ∘ E_ist (M_ist u s)) (projT2 CF))).
    intros CF CF' pp. apply pp.
  Defined.

End Coherence_stuff.

Lemma istIsCoh {A : setoid}(B : setoidfamily A) : isCoh (B := Branches B) ist.
Proof.
  intros u u' r. apply ist_coh.
Qed.

Lemma M_istIsCoh {A : setoid}(B : setoidfamily A) : isCoh (B := ImSubTrees B) M_ist.
Proof.
  intros u u' r. apply M_ist_coh.
Qed.

Definition istCoh {A : setoid}(B : setoidfamily A) : CohFam (Branches B) (Wstd B)
  := existT _ ist (istIsCoh B).

Definition M_istCoh {A : setoid}(B : setoidfamily A) : CohFam (ImSubTrees B) (Wstd B)
  := existT _ M_ist (M_istIsCoh B).

(* A couple of useful functions. *)

Definition ist_node {A : setoid}{B : setoidfamily A}(u : Wstd B)
  : ImSubTrees B u ⇒ A
  := node B ∘ M_ist u.

Lemma ist_node_coh {A : setoid}{B : setoidfamily A}
      {u u' : Wstd B}(r : u ≈ u') :
  ist_node u ≈ ist_node u' ∘ (ImSubTrees B)•r.
Proof.
  intro b. unfold ist_node.
  apply (setoidmapextensionality _ _ (node B)). apply ist_coh.
Qed.
