

Require Import S00_setoid_basics S01_Wty S02_PolyFun S10_Wstd_Alg.


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

(*
Definition ImSubTrees_fnc {A : setoid}(B : setoidfamily A)(u u' : Wstd B)
  : u ≈ u' → ImSubTrees_std B u → ImSubTrees_std B u'
  := λ r, B•(node B ↱ r).
 *)

Definition ImSubTrees_map {A : setoid}(B : setoidfamily A)(u u' : Wstd B) :
  u ≈ u' → ImSubTrees_std B u ⇒ ImSubTrees_std B u'.

  intro r. apply (Build_setoidmap (ImSubTrees_std B u) (ImSubTrees_std B u') (B•(node B ↱ r))).
  intros s s' q. apply ist_coh_tactical. apply q.
Defined.

Definition ImSubTrees {A : setoid}(B : setoidfamily A) : setoidfamily (Wstd B).

  apply (Build_setoidfamily (Wstd B) (ImSubTrees_std B) (ImSubTrees_map B)).
  apply Build_setoidfamilyaxioms.
  intros u s. apply setoidmapextensionality. apply setoidfamilyrefgeneral.
  intros u u' r r' s. apply (setoidmapextensionality _ _ (ist u')).
  apply setoidfamilyirr.
  intros u u' u'' r r' s. apply (setoidmapextensionality _ _ (ist u'')).
  apply setoidfamilycmpgeneral.
Defined.

(* Definition 3.8 - End *)

(* Remark 3.9 *)
(* 'E_ist u' is eᵤ in the remark *)
(* 'M_ist u' is mᵤ in the remark *)

Definition E_ist {A : setoid}{B : setoidfamily A}(u : Wstd B)
  : B (node B u) ⇒ ImSubTrees B u.

  apply (Build_setoidmap (B (node B u)) (ImSubTrees B u) (λ b, b)).
  intros b b' q. apply setoidmapextensionality. apply q.
Defined.

Definition M_ist {A : setoid}{B : setoidfamily A}(u : Wstd B)
  : ImSubTrees B u ⇒ Wstd B.

  apply (Build_setoidmap _ _ (λ b : ImSubTrees B u, ist u b)).
  intros b b' q. apply q.
Defined.

Lemma ist_fact  {A : setoid}{B : setoidfamily A}(u : Wstd B)
  : M_ist u ∘ E_ist u ≈ ist u.
Proof.
  intro b. apply setoidrefl.
Qed.

Lemma E_ist_coh {A : setoid}{B : setoidfamily A}{u u' : Wstd B}(r : u ≈ u')
  : (ImSubTrees B)•r ∘ E_ist u ≈ E_ist u' ∘ (Branches  B)•r.
Proof.
  intro b. apply setoidrefl.
Qed.

(* Remark 3.10 *)

Lemma istIsCoh {A : setoid}(B : setoidfamily A) : isCoh (B := Branches B) ist.
Proof.
  intros u u' r. apply ist_coh.
Qed.
  
Lemma M_istIsCoh {A : setoid}(B : setoidfamily A) : isCoh (B := ImSubTrees B) M_ist.
Proof.
  intros u u' r. apply ist_coh.
Qed.

(* A couple of useful functions. *)

Definition IST_node {A : setoid}{B : setoidfamily A}(u : Wstd B)
  : ImSubTrees B u ⇒ A
  := node B ∘ M_ist u.

Lemma IST_node_coh {A : setoid}{B : setoidfamily A}
      {u u' : Wstd B}(r : u ≈ u') :
  IST_node u ≈ IST_node u' ∘ (ImSubTrees B)•r.
Proof.
  intro b. unfold IST_node.
  apply (setoidmapextensionality _ _ (node B)). apply ist_coh.
Qed.



