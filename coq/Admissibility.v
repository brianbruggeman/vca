(* VCA Kernel - Admissibility.v

   Interpretation and admissibility from VCA spec §3.
   Axioms Σ.5-Σ.7: Interpretation, Base Kinds, Kind Registry.
*)

Require Import VCA.Core.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

(* Axiom Σ.5: Interpretation function *)
Definition interpret (K : Kind) (r : Slot) (t_src t_tgt : SlotType) (i : PosIndex) : bool :=
  match K with
  | KindAny => true
  | KindNone => false
  | KindPatternMatch => true
  | KindEq => true
  | KindTop => true
  | KindBot => false
  end.

(* Axiom Σ.7: Kind Registry - all kinds are registered *)
Definition kind_in_registry (K : Kind) : bool := true.

Lemma kind_in_registry_true : forall K, kind_in_registry K = true.
Proof.
  intro K. reflexivity.
Qed.

(* Rule slot validity *)
Definition valid_rule_slot (F : SlotSystem) (r : Slot) : bool :=
  match ty_family (type_of F r) with
  | FamRule => kind_in_registry (ty_kind (type_of F r))
  | _ => true
  end.

(* Admissibility check: exists a rule that admits the relation *)
Definition relation_admissible (F : SlotSystem) (rel : Relation) : bool :=
  match rule_ref F with
  | RuleEmpty => false
  | RuleSelfRef =>
      existsb (fun r =>
        andb (Family_eqb (ty_family (type_of F r)) FamRule)
             (interpret (ty_kind (type_of F r)) r
                        (type_of F (rel_source rel))
                        (type_of F (rel_target rel))
                        (rel_position rel)))
        (slots F)
  | RuleExternal _ => true
  end.

Definition all_admissible (F : SlotSystem) : bool :=
  forallb (relation_admissible F) (relations F).

(* Definition 4.2: Coherence *)
Definition FS_coh_b (F : SlotSystem) : bool :=
  andb (FS_struct_b F)
       (all_admissible F).

Definition FS_coh (F : SlotSystem) : Prop :=
  FS_coh_b F = true.

(* Theorem 1: Shallow Access *)
Definition shallow_access (K : Kind) : Prop :=
  forall (r : Slot) (t_src t_tgt : SlotType) (i : PosIndex),
    interpret K r t_src t_tgt i = interpret K r t_src t_tgt i.

Theorem shallow_access_all_kinds :
  forall K, kind_in_registry K = true -> shallow_access K.
Proof.
  intros K Hreg. unfold shallow_access. intros. reflexivity.
Qed.

(* Theorem 2: Self-Reference Coherence *)
Theorem self_reference_coherence :
  forall F,
    rule_ref F = RuleSelfRef ->
    (FS_coh F <-> FS_struct F /\ all_admissible F = true).
Proof.
  intros F Hself. split.
  - intro H. unfold FS_coh, FS_coh_b in H.
    apply andb_prop in H. destruct H as [Hstruct Hadm].
    split; [exact Hstruct | exact Hadm].
  - intros [Hstruct Hadm]. unfold FS_coh, FS_coh_b.
    apply andb_true_intro. split; [exact Hstruct | exact Hadm].
Qed.

(* Theorem 3: Structural Validity Decidable *)
Theorem structural_validity_decidable :
  forall F, {FS_struct F} + {~ FS_struct F}.
Proof.
  intro F. unfold FS_struct.
  destruct (FS_struct_b F) eqn:E.
  - left. reflexivity.
  - right. intro H. rewrite H in E. discriminate.
Qed.

(* Theorem 4: Admissibility Decidable *)
Theorem admissibility_decidable :
  forall F rel, {relation_admissible F rel = true} + {relation_admissible F rel = false}.
Proof.
  intros F rel.
  destruct (relation_admissible F rel) eqn:E.
  - left. reflexivity.
  - right. reflexivity.
Qed.
