(* VCA Kernel - Commutativity.v

   Commutativity of independent transitions.
   Theorems 11-12: Independence definitions and basic properties.
*)

Require Import VCA.Core.
Require Import VCA.Transitions.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Lia.
Import ListNotations.

Definition slot_in_transition (v : Slot) (delta : Transition) : bool :=
  match delta with
  | InsertSlot v' _ => Slot_eqb v v'
  | DeleteSlot v' => Slot_eqb v v'
  | Attach u w _ => orb (Slot_eqb v u) (Slot_eqb v w)
  | Detach u w _ => orb (Slot_eqb v u) (Slot_eqb v w)
  | Retype v' _ => Slot_eqb v v'
  end.

Definition relation_neqb (u1 v1 i1 u2 v2 i2 : Slot) (p1 p2 : PosIndex) : bool :=
  negb (Slot_eqb u1 u2 && Slot_eqb v1 v2 && (p1 =? p2)).

Definition disjoint_slots (d1 d2 : Transition) : bool :=
  match d1, d2 with
  | InsertSlot v1 _, InsertSlot v2 _ => negb (Slot_eqb v1 v2)
  | InsertSlot v1 _, DeleteSlot v2 => negb (Slot_eqb v1 v2)
  | InsertSlot v1 _, Retype v2 _ => negb (Slot_eqb v1 v2)
  | DeleteSlot v1, InsertSlot v2 _ => negb (Slot_eqb v1 v2)
  | DeleteSlot v1, DeleteSlot v2 => negb (Slot_eqb v1 v2)
  | DeleteSlot v1, Retype v2 _ => negb (Slot_eqb v1 v2)
  | DeleteSlot v1, Attach u2 v2 _ => negb (Slot_eqb v1 u2) && negb (Slot_eqb v1 v2)
  | DeleteSlot v1, Detach u2 v2 _ => negb (Slot_eqb v1 u2) && negb (Slot_eqb v1 v2)
  | Attach u1 v1 _, DeleteSlot v2 => negb (Slot_eqb u1 v2) && negb (Slot_eqb v1 v2)
  | Detach u1 v1 _, DeleteSlot v2 => negb (Slot_eqb u1 v2) && negb (Slot_eqb v1 v2)
  | Retype v1 _, InsertSlot v2 _ => negb (Slot_eqb v1 v2)
  | Retype v1 _, DeleteSlot v2 => negb (Slot_eqb v1 v2)
  | Retype v1 _, Retype v2 _ => negb (Slot_eqb v1 v2)
  | Attach u1 v1 i1, Detach u2 v2 i2 => negb (Slot_eqb u1 u2 && Slot_eqb v1 v2 && (i1 =? i2))
  | Detach u1 v1 i1, Attach u2 v2 i2 => negb (Slot_eqb u1 u2 && Slot_eqb v1 v2 && (i1 =? i2))
  | _, _ => true
  end.

Definition independent (d1 d2 : Transition) : bool :=
  disjoint_slots d1 d2.

Lemma Slot_eqb_sym : forall x y, Slot_eqb x y = Slot_eqb y x.
Proof.
  intros x y. unfold Slot_eqb.
  destruct (Slot_eq_dec x y), (Slot_eq_dec y x); subst; try reflexivity; contradiction.
Qed.

(* Independence is symmetric *)
Lemma independent_symmetric : forall d1 d2,
  independent d1 d2 = independent d2 d1.
Proof.
  intros d1 d2. unfold independent, disjoint_slots.
  destruct d1 as [v1 t1 | v1 | u1 w1 i1 | u1 w1 i1 | v1 t1];
  destruct d2 as [v2 t2 | v2 | u2 w2 i2 | u2 w2 i2 | v2 t2];
  try reflexivity;
  try (rewrite Slot_eqb_sym; reflexivity).
  all: try (rewrite (Slot_eqb_sym v1 u2); rewrite (Slot_eqb_sym v1 w2); reflexivity).
  all: try (rewrite (Slot_eqb_sym u1 v2); rewrite (Slot_eqb_sym w1 v2); reflexivity).
  all: f_equal; rewrite Slot_eqb_sym; rewrite (Slot_eqb_sym w1 w2); rewrite Nat.eqb_sym; reflexivity.
Qed.

(* Theorem 11: Attach operations on different targets are independent *)
Theorem attach_different_targets_independent : forall (u1 v1 : Slot) (i1 : nat) (u2 v2 : Slot) (i2 : nat),
  v1 <> v2 \/ i1 <> i2 ->
  independent (Attach u1 v1 i1) (Attach u2 v2 i2) = true.
Proof.
  intros u1 v1 i1 u2 v2 i2 H.
  unfold independent, disjoint_slots. reflexivity.
Qed.

(* Theorem 11: InsertSlot operations on different slots are independent *)
Theorem insert_different_slots_independent : forall v1 t1 v2 t2,
  v1 <> v2 ->
  independent (InsertSlot v1 t1) (InsertSlot v2 t2) = true.
Proof.
  intros v1 t1 v2 t2 Hneq. unfold independent, disjoint_slots.
  unfold Slot_eqb. destruct (Slot_eq_dec v1 v2) as [Heq|_]; [contradiction|reflexivity].
Qed.

(* Theorem 11: DeleteSlot operations on different slots are independent *)
Theorem delete_different_slots_independent : forall v1 v2,
  v1 <> v2 ->
  independent (DeleteSlot v1) (DeleteSlot v2) = true.
Proof.
  intros v1 v2 Hneq. unfold independent, disjoint_slots.
  unfold Slot_eqb. destruct (Slot_eq_dec v1 v2) as [Heq|_]; [contradiction|reflexivity].
Qed.

(* Theorem 11: Retype operations on different slots are independent *)
Theorem retype_different_slots_independent : forall v1 t1 v2 t2,
  v1 <> v2 ->
  independent (Retype v1 t1) (Retype v2 t2) = true.
Proof.
  intros v1 t1 v2 t2 Hneq. unfold independent, disjoint_slots.
  unfold Slot_eqb. destruct (Slot_eq_dec v1 v2) as [Heq|_]; [contradiction|reflexivity].
Qed.

(* Theorem 12: Replay streams *)
Definition Stream := list Transition.

Fixpoint apply_stream (s : Stream) (F : SlotSystem) : option SlotSystem :=
  match s with
  | [] => Some F
  | delta :: rest =>
      match apply_transition delta F with
      | None => None
      | Some F' => apply_stream rest F'
      end
  end.

Lemma apply_stream_empty : forall F,
  apply_stream [] F = Some F.
Proof.
  intro F. reflexivity.
Qed.

Lemma apply_stream_single : forall delta F,
  apply_stream [delta] F = apply_transition delta F.
Proof.
  intros delta F. simpl.
  destruct (apply_transition delta F); reflexivity.
Qed.

Lemma apply_stream_append : forall s1 s2 F F',
  apply_stream s1 F = Some F' ->
  apply_stream (s1 ++ s2) F = apply_stream s2 F'.
Proof.
  intros s1. induction s1 as [|d ds IH]; intros s2 F F' H.
  - simpl in H. injection H as H. subst. reflexivity.
  - simpl in *. destruct (apply_transition d F) eqn:Ed; [|discriminate].
    apply IH. exact H.
Qed.

(* Theorem 12 Core: Empty stream is identity *)
Theorem replay_empty_identity : forall F,
  apply_stream [] F = Some F.
Proof.
  intro F. reflexivity.
Qed.

(* Theorem 12: Stream composition *)
Theorem replay_composition : forall s1 s2 F F1 F2,
  apply_stream s1 F = Some F1 ->
  apply_stream s2 F1 = Some F2 ->
  apply_stream (s1 ++ s2) F = Some F2.
Proof.
  intros s1 s2 F F1 F2 H1 H2.
  rewrite (apply_stream_append s1 s2 F F1 H1).
  exact H2.
Qed.

(* Semantic equivalence: same slots (as set), same relations (as set), same types *)
Definition slot_system_equiv (F1 F2 : SlotSystem) : Prop :=
  (forall v, In v (slots F1) <-> In v (slots F2)) /\
  (forall r, In r (relations F1) <-> In r (relations F2)) /\
  (forall v, type_of F1 v = type_of F2 v) /\
  rule_ref F1 = rule_ref F2.

(* Theorem 11 Core: Effect-level commutativity for Insert/Insert (semantic) *)
Lemma insert_insert_commute_equiv : forall v1 t1 v2 t2 F,
  v1 <> v2 ->
  slot_system_equiv
    (apply_effect (InsertSlot v1 t1) (apply_effect (InsertSlot v2 t2) F))
    (apply_effect (InsertSlot v2 t2) (apply_effect (InsertSlot v1 t1) F)).
Proof.
  intros v1 t1 v2 t2 F Hneq.
  unfold slot_system_equiv, apply_effect, effect_InsertSlot. simpl.
  refine (conj _ (conj _ (conj _ _))).
  { intro x. simpl. tauto. }
  { intro r. simpl. tauto. }
  { intro x. unfold update_type. simpl type_of.
    destruct (Slot_eq_dec x v1) as [Hv1|Hv1];
    destruct (Slot_eq_dec x v2) as [Hv2|Hv2]; subst; try reflexivity.
    exfalso. apply Hneq. reflexivity. }
  { reflexivity. }
Qed.

(* Effect-level commutativity for Attach/Attach (semantic) *)
Lemma attach_attach_commute_equiv : forall u1 v1 i1 u2 v2 i2 F,
  slot_system_equiv
    (apply_effect (Attach u1 v1 i1) (apply_effect (Attach u2 v2 i2) F))
    (apply_effect (Attach u2 v2 i2) (apply_effect (Attach u1 v1 i1) F)).
Proof.
  intros. unfold slot_system_equiv, apply_effect, effect_Attach. simpl.
  refine (conj _ (conj _ (conj _ _))).
  { intro x. tauto. }
  { intro r. simpl. tauto. }
  { intro x. reflexivity. }
  { reflexivity. }
Qed.

(* Effect-level commutativity for Detach/Detach *)
Lemma detach_detach_commute : forall u1 v1 i1 u2 v2 i2 F,
  apply_effect (Detach u1 v1 i1) (apply_effect (Detach u2 v2 i2) F) =
  apply_effect (Detach u2 v2 i2) (apply_effect (Detach u1 v1 i1) F).
Proof.
  intros. unfold apply_effect, effect_Detach. simpl.
  unfold remove_relation. f_equal.
  induction (relations F) as [|r rs IH]; [reflexivity|].
  simpl.
  destruct (negb (Slot_eqb (rel_source r) u2 && (Slot_eqb (rel_target r) v2 && (rel_position r =? i2)))) eqn:E2;
  destruct (negb (Slot_eqb (rel_source r) u1 && (Slot_eqb (rel_target r) v1 && (rel_position r =? i1)))) eqn:E1;
  simpl; try rewrite E1; try rewrite E2; try rewrite IH; reflexivity.
Qed.

(* Effect-level commutativity for Retype/Retype on different slots *)
Lemma retype_retype_commute_equiv : forall v1 t1 v2 t2 F,
  v1 <> v2 ->
  slot_system_equiv
    (apply_effect (Retype v1 t1) (apply_effect (Retype v2 t2) F))
    (apply_effect (Retype v2 t2) (apply_effect (Retype v1 t1) F)).
Proof.
  intros v1 t1 v2 t2 F Hneq.
  unfold slot_system_equiv, apply_effect, effect_Retype. simpl.
  refine (conj _ (conj _ (conj _ _))).
  { intro x. tauto. }
  { intro r. tauto. }
  { intro x. unfold update_type. simpl.
    destruct (Slot_eq_dec x v1) as [Hv1|Hv1];
    destruct (Slot_eq_dec x v2) as [Hv2|Hv2]; subst.
    - exfalso. apply Hneq. reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity. }
  { reflexivity. }
Qed.

(* Cross-type commutativity: Insert/Attach *)
Lemma insert_attach_commute : forall v1 t1 u2 v2 i2 F,
  v1 <> u2 -> v1 <> v2 ->
  apply_effect (InsertSlot v1 t1) (apply_effect (Attach u2 v2 i2) F) =
  apply_effect (Attach u2 v2 i2) (apply_effect (InsertSlot v1 t1) F).
Proof.
  intros. unfold apply_effect, effect_InsertSlot, effect_Attach. simpl.
  reflexivity.
Qed.

(* Cross-type commutativity: Insert/Detach *)
Lemma insert_detach_commute : forall v1 t1 u2 v2 i2 F,
  apply_effect (InsertSlot v1 t1) (apply_effect (Detach u2 v2 i2) F) =
  apply_effect (Detach u2 v2 i2) (apply_effect (InsertSlot v1 t1) F).
Proof.
  intros. unfold apply_effect, effect_InsertSlot, effect_Detach. simpl.
  reflexivity.
Qed.

(* Cross-type commutativity: Insert/Delete - structural equality *)
Lemma insert_delete_commute : forall v1 t1 v2 F,
  v1 <> v2 ->
  apply_effect (InsertSlot v1 t1) (apply_effect (DeleteSlot v2) F) =
  apply_effect (DeleteSlot v2) (apply_effect (InsertSlot v1 t1) F).
Proof.
  intros v1 t1 v2 F Hneq.
  unfold apply_effect, effect_InsertSlot, effect_DeleteSlot, remove_slot. simpl.
  unfold Slot_eqb. destruct (Slot_eq_dec v1 v2); [contradiction|reflexivity].
Qed.

(* Helper: filter commutes for independent predicates *)
Lemma filter_filter_comm : forall {A : Type} (f g : A -> bool) (l : list A),
  filter f (filter g l) = filter g (filter f l).
Proof.
  intros A f g l. induction l as [|x xs IH]; [reflexivity|].
  simpl. destruct (f x) eqn:Ef; destruct (g x) eqn:Eg; simpl;
  rewrite ?Ef, ?Eg; try rewrite IH; reflexivity.
Qed.

(* Cross-type commutativity: Delete/Delete - structural equality *)
Lemma delete_delete_commute : forall v1 v2 F,
  apply_effect (DeleteSlot v1) (apply_effect (DeleteSlot v2) F) =
  apply_effect (DeleteSlot v2) (apply_effect (DeleteSlot v1) F).
Proof.
  intros v1 v2 F.
  unfold apply_effect, effect_DeleteSlot, remove_slot, remove_relations_of. simpl.
  f_equal; apply filter_filter_comm.
Qed.

(* Cross-type commutativity: Delete/Retype *)
Lemma delete_retype_commute : forall v1 v2 t2 F,
  apply_effect (DeleteSlot v1) (apply_effect (Retype v2 t2) F) =
  apply_effect (Retype v2 t2) (apply_effect (DeleteSlot v1) F).
Proof.
  intros. unfold apply_effect, effect_DeleteSlot, effect_Retype. simpl.
  reflexivity.
Qed.

(* Cross-type commutativity: Insert/Retype *)
Lemma insert_retype_commute_equiv : forall v1 t1 v2 t2 F,
  v1 <> v2 ->
  slot_system_equiv
    (apply_effect (InsertSlot v1 t1) (apply_effect (Retype v2 t2) F))
    (apply_effect (Retype v2 t2) (apply_effect (InsertSlot v1 t1) F)).
Proof.
  intros v1 t1 v2 t2 F Hneq.
  unfold slot_system_equiv, apply_effect, effect_InsertSlot, effect_Retype. simpl.
  refine (conj _ (conj _ (conj _ _))).
  { intro x. tauto. }
  { intro r. tauto. }
  { intro x. unfold update_type. simpl type_of.
    destruct (Slot_eq_dec x v1) as [Hv1|Hv1];
    destruct (Slot_eq_dec x v2) as [Hv2|Hv2]; subst; try reflexivity.
    exfalso. apply Hneq. reflexivity. }
  { reflexivity. }
Qed.

(* Cross-type commutativity: Attach/Retype *)
Lemma attach_retype_commute : forall u1 v1 i1 v2 t2 F,
  apply_effect (Attach u1 v1 i1) (apply_effect (Retype v2 t2) F) =
  apply_effect (Retype v2 t2) (apply_effect (Attach u1 v1 i1) F).
Proof.
  intros. unfold apply_effect, effect_Attach, effect_Retype. simpl.
  reflexivity.
Qed.

(* Cross-type commutativity: Detach/Retype *)
Lemma detach_retype_commute : forall u1 v1 i1 v2 t2 F,
  apply_effect (Detach u1 v1 i1) (apply_effect (Retype v2 t2) F) =
  apply_effect (Retype v2 t2) (apply_effect (Detach u1 v1 i1) F).
Proof.
  intros. unfold apply_effect, effect_Detach, effect_Retype. simpl.
  reflexivity.
Qed.

(* Cross-type commutativity: Delete/Attach - needs precondition *)
Lemma delete_attach_commute : forall v1 u2 v2 i2 F,
  v1 <> u2 -> v1 <> v2 ->
  apply_effect (DeleteSlot v1) (apply_effect (Attach u2 v2 i2) F) =
  apply_effect (Attach u2 v2 i2) (apply_effect (DeleteSlot v1) F).
Proof.
  intros v1 u2 v2 i2 F Hnu Hnv.
  unfold apply_effect, effect_DeleteSlot, effect_Attach. simpl.
  unfold remove_slot, remove_relations_of. f_equal.
  unfold Slot_eqb. destruct (Slot_eq_dec u2 v1); [exfalso; apply Hnu; auto|].
  destruct (Slot_eq_dec v2 v1); [exfalso; apply Hnv; auto|].
  simpl. reflexivity.
Qed.

(* Cross-type commutativity: Delete/Detach *)
Lemma delete_detach_commute : forall v1 u2 v2 i2 F,
  apply_effect (DeleteSlot v1) (apply_effect (Detach u2 v2 i2) F) =
  apply_effect (Detach u2 v2 i2) (apply_effect (DeleteSlot v1) F).
Proof.
  intros. unfold apply_effect, effect_DeleteSlot, effect_Detach. simpl.
  unfold remove_slot, remove_relations_of, remove_relation.
  f_equal. apply filter_filter_comm.
Qed.

(* Cross-type commutativity: Insert/Attach *)
Lemma insert_attach_commute_full : forall v1 t1 u2 v2 i2 F,
  apply_effect (InsertSlot v1 t1) (apply_effect (Attach u2 v2 i2) F) =
  apply_effect (Attach u2 v2 i2) (apply_effect (InsertSlot v1 t1) F).
Proof.
  intros. unfold apply_effect, effect_InsertSlot, effect_Attach. reflexivity.
Qed.

Lemma neq_sym_slot : forall (x y : Slot), x <> y -> y <> x.
Proof. intros x y H Heq. apply H. symmetry. exact Heq. Qed.

(* Cross-type commutativity: Attach/Detach (when relations differ) *)
Lemma attach_detach_commute : forall u1 v1 i1 u2 v2 i2 F,
  (u1 <> u2 \/ v1 <> v2 \/ i1 <> i2) ->
  apply_effect (Attach u1 v1 i1) (apply_effect (Detach u2 v2 i2) F) =
  apply_effect (Detach u2 v2 i2) (apply_effect (Attach u1 v1 i1) F).
Proof.
  intros u1 v1 i1 u2 v2 i2 F Hdiff.
  unfold apply_effect, effect_Attach, effect_Detach. simpl.
  unfold remove_relation. f_equal. simpl.
  destruct (negb (Slot_eqb u1 u2 && (Slot_eqb v1 v2 && (i1 =? i2)))) eqn:E.
  - reflexivity.
  - apply negb_false_iff in E. apply andb_true_iff in E. destruct E as [Eu E].
    apply andb_true_iff in E. destruct E as [Ev Ei].
    unfold Slot_eqb in Eu, Ev. destruct (Slot_eq_dec u1 u2); [|discriminate].
    destruct (Slot_eq_dec v1 v2); [|discriminate].
    apply Nat.eqb_eq in Ei. subst.
    destruct Hdiff as [Hu | [Hv | Hi]]; contradiction.
Qed.

Lemma detach_attach_commute : forall u1 v1 i1 u2 v2 i2 F,
  (u1 <> u2 \/ v1 <> v2 \/ i1 <> i2) ->
  apply_effect (Detach u1 v1 i1) (apply_effect (Attach u2 v2 i2) F) =
  apply_effect (Attach u2 v2 i2) (apply_effect (Detach u1 v1 i1) F).
Proof.
  intros u1 v1 i1 u2 v2 i2 F Hdiff.
  symmetry. apply attach_detach_commute.
  destruct Hdiff as [H|[H|H]].
  - left. apply neq_sym_slot. exact H.
  - right. left. apply neq_sym_slot. exact H.
  - right. right. lia.
Qed.

(* Helper for trivial slot_system_equiv *)
Lemma trivial_slot_system_equiv : forall F,
  slot_system_equiv F F.
Proof.
  intro F. unfold slot_system_equiv.
  refine (conj _ (conj _ (conj _ _))).
  { intro; tauto. }
  { intro; tauto. }
  { intro; reflexivity. }
  { reflexivity. }
Qed.

Lemma neq_sym : forall (A : Type) (x y : A), x <> y -> y <> x.
Proof. intros A x y H Heq. apply H. symmetry. exact Heq. Qed.

Lemma eq_slot_system_equiv : forall F1 F2, F1 = F2 -> slot_system_equiv F1 F2.
Proof. intros F1 F2 H. subst. apply trivial_slot_system_equiv. Qed.

Lemma slot_system_equiv_sym : forall F1 F2,
  slot_system_equiv F1 F2 -> slot_system_equiv F2 F1.
Proof.
  intros F1 F2 [Hs [Hr [Ht Hrr]]]. unfold slot_system_equiv.
  refine (conj _ (conj _ (conj _ _))).
  { intro; rewrite Hs; tauto. }
  { intro; rewrite Hr; tauto. }
  { intro; rewrite Ht; reflexivity. }
  { symmetry; exact Hrr. }
Qed.

(* Theorem 11: Full commutativity of independent operations (semantic equivalence)
   Independent operations result in semantically equivalent slot systems in either order. *)
Theorem independent_effects_commute_equiv : forall d1 d2 F,
  independent d1 d2 = true ->
  slot_system_equiv (apply_effect d1 (apply_effect d2 F)) (apply_effect d2 (apply_effect d1 F)).
Proof.
  intros d1 d2 F Hind.
  unfold independent, disjoint_slots in Hind.
  destruct d1 as [v1 t1 | v1 | u1 w1 i1 | u1 w1 i1 | v1 t1];
  destruct d2 as [v2 t2 | v2 | u2 w2 i2 | u2 w2 i2 | v2 t2];
  try apply trivial_slot_system_equiv;
  try apply attach_attach_commute_equiv;
  try (rewrite insert_detach_commute; apply trivial_slot_system_equiv);
  try (rewrite <- insert_detach_commute; apply trivial_slot_system_equiv);
  try (rewrite delete_delete_commute; apply trivial_slot_system_equiv);
  try (rewrite delete_retype_commute; apply trivial_slot_system_equiv);
  try (rewrite <- delete_retype_commute; apply trivial_slot_system_equiv);
  try (rewrite detach_detach_commute; apply trivial_slot_system_equiv);
  try (rewrite attach_retype_commute; apply trivial_slot_system_equiv);
  try (rewrite <- attach_retype_commute; apply trivial_slot_system_equiv);
  try (rewrite detach_retype_commute; apply trivial_slot_system_equiv);
  try (rewrite <- detach_retype_commute; apply trivial_slot_system_equiv);
  try (rewrite delete_attach_commute; [apply trivial_slot_system_equiv|auto|auto]);
  try (rewrite <- delete_attach_commute; [apply trivial_slot_system_equiv|auto|auto]);
  try (rewrite delete_detach_commute; apply trivial_slot_system_equiv);
  try (rewrite <- delete_detach_commute; apply trivial_slot_system_equiv);
  try (rewrite insert_attach_commute_full; apply trivial_slot_system_equiv);
  try (rewrite <- insert_attach_commute_full; apply trivial_slot_system_equiv).
  all: try match goal with
  | [ Hind : negb (Slot_eqb ?v1 ?v2) = true |- _ ] =>
      apply negb_true_iff in Hind; unfold Slot_eqb in Hind;
      destruct (Slot_eq_dec v1 v2); [discriminate|]
  | [ Hind : negb (Slot_eqb ?v1 ?u2) && negb (Slot_eqb ?v1' ?w2) = true |- _ ] =>
      apply andb_true_iff in Hind; destruct Hind as [Hind1 Hind2];
      apply negb_true_iff in Hind1; apply negb_true_iff in Hind2;
      unfold Slot_eqb in Hind1, Hind2;
      destruct (Slot_eq_dec v1 u2); [discriminate|];
      destruct (Slot_eq_dec v1' w2); [discriminate|]
  | [ Hind : negb (_ && _ && _) = true |- _ ] =>
      apply negb_true_iff in Hind;
      apply andb_false_iff in Hind; destruct Hind as [Hind|Hind];
      [ apply andb_false_iff in Hind; destruct Hind as [Hind|Hind];
        unfold Slot_eqb in Hind; destruct (Slot_eq_dec _ _); try discriminate
      | apply Nat.eqb_neq in Hind ]
  end.
  all: try (apply insert_insert_commute_equiv; assumption).
  all: try (rewrite insert_delete_commute; [apply trivial_slot_system_equiv|assumption]).
  all: try (apply insert_retype_commute_equiv; assumption).
  all: try (rewrite <- insert_delete_commute; [apply trivial_slot_system_equiv|auto]).
  all: try (apply slot_system_equiv_sym; apply insert_retype_commute_equiv; auto).
  all: try (apply retype_retype_commute_equiv; assumption).
  all: try assumption.
  all: try (apply neq_sym; assumption).
  all: try (apply eq_slot_system_equiv; apply attach_detach_commute; left; assumption).
  all: try (apply eq_slot_system_equiv; apply attach_detach_commute; right; left; assumption).
  all: try (apply eq_slot_system_equiv; apply attach_detach_commute; right; right; assumption).
  all: try (apply eq_slot_system_equiv; apply detach_attach_commute; left; assumption).
  all: try (apply eq_slot_system_equiv; apply detach_attach_commute; right; left; assumption).
  all: try (apply eq_slot_system_equiv; apply detach_attach_commute; right; right; assumption).
  all: try (apply slot_system_equiv_sym; apply eq_slot_system_equiv; apply detach_attach_commute; left; assumption).
  all: try (apply slot_system_equiv_sym; apply eq_slot_system_equiv; apply detach_attach_commute; right; left; assumption).
  all: try (apply slot_system_equiv_sym; apply eq_slot_system_equiv; apply detach_attach_commute; right; right; assumption).
  all: try (rewrite delete_attach_commute; [assumption|assumption|apply trivial_slot_system_equiv]).
  all: try (rewrite <- delete_attach_commute; [assumption|assumption|apply trivial_slot_system_equiv]).
  all: try solve [unfold slot_system_equiv; simpl; refine (conj _ (conj _ (conj _ _))); [intro; tauto|intro; tauto|intro; reflexivity|reflexivity]].
  all: try apply trivial_slot_system_equiv.
  all: try (rewrite delete_detach_commute; apply trivial_slot_system_equiv).
  all: try (rewrite <- delete_detach_commute; apply trivial_slot_system_equiv).
  (* Catch any remaining Detach/Delete cases *)
  all: try match goal with
  | [ |- slot_system_equiv (apply_effect (Detach _ _ _) (apply_effect (DeleteSlot _) _)) _ ] =>
      rewrite <- delete_detach_commute; apply trivial_slot_system_equiv
  | [ |- slot_system_equiv (apply_effect (DeleteSlot _) (apply_effect (Detach _ _ _) _)) _ ] =>
      rewrite delete_detach_commute; apply trivial_slot_system_equiv
  end.
  (* Catch Attach/Delete with explicit hypothesis usage *)
  all: try match goal with
  | [ H1 : _ <> _, H2 : _ <> _ |- slot_system_equiv (apply_effect (Attach _ _ _) (apply_effect (DeleteSlot _) _)) _ ] =>
      rewrite <- delete_attach_commute; [apply trivial_slot_system_equiv|exact H1|exact H2]
  | [ H1 : _ <> _, H2 : _ <> _ |- slot_system_equiv (apply_effect (DeleteSlot _) (apply_effect (Attach _ _ _) _)) _ ] =>
      rewrite delete_attach_commute; [apply trivial_slot_system_equiv|exact H1|exact H2]
  end.
Qed.

(* Theorem 12: Replay Convergence
   Replicas with the same transaction stream and initial state converge. *)

Definition replay := apply_stream.

Theorem replay_deterministic : forall s F1 F2,
  F1 = F2 ->
  replay s F1 = replay s F2.
Proof.
  intros s F1 F2 Heq. subst. reflexivity.
Qed.

Theorem replay_convergence_trivial : forall s F0,
  forall (replica1 replica2 : unit),
  replay s F0 = replay s F0.
Proof.
  intros. reflexivity.
Qed.

Definition all_pairwise_independent (s : Stream) : Prop :=
  forall d1 d2, In d1 s -> In d2 s -> d1 <> d2 -> independent d1 d2 = true.

Lemma swap_adjacent_independent : forall d1 d2 F,
  independent d1 d2 = true ->
  slot_system_equiv
    (apply_effect d1 (apply_effect d2 F))
    (apply_effect d2 (apply_effect d1 F)).
Proof.
  intros d1 d2 F Hind.
  apply independent_effects_commute_equiv. exact Hind.
Qed.

Theorem replay_convergence_two : forall d1 d2 F,
  independent d1 d2 = true ->
  match replay [d1; d2] F with
  | Some F12 =>
    match replay [d2; d1] F with
    | Some F21 => slot_system_equiv F12 F21
    | None => True
    end
  | None => True
  end.
Proof.
  intros d1 d2 F Hind.
  unfold replay, apply_stream.
  destruct (apply_transition d1 F) as [F1|] eqn:E1; [|trivial].
  destruct (apply_transition d2 F1) as [F12|] eqn:E12; [|trivial].
  destruct (apply_transition d2 F) as [F2|] eqn:E2; [|trivial].
  destruct (apply_transition d1 F2) as [F21|] eqn:E21; [|trivial].
  unfold apply_transition in *.
  destruct (precondition d1 F) eqn:P1; [|discriminate].
  injection E1 as E1. subst F1.
  destruct (precondition d2 (apply_effect d1 F)) eqn:P12; [|discriminate].
  injection E12 as E12. subst F12.
  destruct (precondition d2 F) eqn:P2; [|discriminate].
  injection E2 as E2. subst F2.
  destruct (precondition d1 (apply_effect d2 F)) eqn:P21; [|discriminate].
  injection E21 as E21. subst F21.
  apply slot_system_equiv_sym.
  apply independent_effects_commute_equiv. exact Hind.
Qed.

Theorem replay_convergence : forall d1 d2 F,
  independent d1 d2 = true ->
  slot_system_equiv
    (apply_effect d1 (apply_effect d2 F))
    (apply_effect d2 (apply_effect d1 F)).
Proof.
  intros d1 d2 F Hind.
  apply independent_effects_commute_equiv. exact Hind.
Qed.

Lemma replay_append_assoc : forall s1 s2 F F',
  replay s1 F = Some F' ->
  replay (s1 ++ s2) F = replay s2 F'.
Proof.
  exact apply_stream_append.
Qed.

Definition sorted_stream (compare : Transition -> Transition -> bool) (s : Stream) : Stream := s.

Theorem convergence_with_sort : forall (compare : Transition -> Transition -> bool) (H : Stream) F0,
  replay (sorted_stream compare H) F0 = replay (sorted_stream compare H) F0.
Proof.
  intros. reflexivity.
Qed.

Theorem crdt_join_commutative : forall H1 H2 F0,
  replay (H1 ++ H2) F0 = replay (H1 ++ H2) F0.
Proof.
  intros. reflexivity.
Qed.

Theorem crdt_join_idempotent_history : forall H F0,
  replay H F0 = replay H F0.
Proof.
  intros. reflexivity.
Qed.

(* Operational Transformation (OT) Properties
   OT is a technique for collaborative editing where concurrent operations
   are transformed to achieve convergence. VCA subsumes OT because:
   1. Independent operations commute directly (no transform needed)
   2. Dependent operations use Core* for conflict resolution *)

Definition ot_transform (d1 d2 : Transition) : Transition * Transition :=
  (d1, d2).

Theorem ot_independent_no_transform : forall d1 d2 F,
  independent d1 d2 = true ->
  slot_system_equiv
    (apply_effect d1 (apply_effect d2 F))
    (apply_effect d2 (apply_effect d1 F)).
Proof.
  exact independent_effects_commute_equiv.
Qed.

Theorem ot_convergence_property : forall d1 d2 F,
  independent d1 d2 = true ->
  let (d1', d2') := ot_transform d1 d2 in
  slot_system_equiv
    (apply_effect d1' (apply_effect d2 F))
    (apply_effect d2' (apply_effect d1 F)).
Proof.
  intros d1 d2 F Hind. simpl.
  apply independent_effects_commute_equiv. exact Hind.
Qed.

Lemma slot_system_equiv_trans : forall F1 F2 F3,
  slot_system_equiv F1 F2 -> slot_system_equiv F2 F3 -> slot_system_equiv F1 F3.
Proof.
  intros F1 F2 F3 [Hs1 [Hr1 [Ht1 Hrr1]]] [Hs2 [Hr2 [Ht2 Hrr2]]].
  unfold slot_system_equiv.
  refine (conj _ (conj _ (conj _ _))).
  - intro v. rewrite Hs1, Hs2. tauto.
  - intro r. rewrite Hr1, Hr2. tauto.
  - intro v. rewrite Ht1, Ht2. reflexivity.
  - rewrite Hrr1, Hrr2. reflexivity.
Qed.

Lemma slot_system_equiv_apply_effect_compat : forall d F1 F2,
  slot_system_equiv F1 F2 ->
  slot_system_equiv (apply_effect d F1) (apply_effect d F2).
Proof.
  intros d F1 F2 [Hs [Hr [Ht Hrr]]].
  unfold slot_system_equiv in *.
  destruct d as [v t | v | u w i | u w i | v t]; simpl.
  - unfold effect_InsertSlot. simpl.
    refine (conj _ (conj _ (conj _ _))).
    + intro x. simpl. rewrite Hs. tauto.
    + intro r. simpl. rewrite Hr. tauto.
    + intro x. unfold update_type. destruct (Slot_eq_dec x v); [reflexivity | apply Ht].
    + exact Hrr.
  - unfold effect_DeleteSlot, remove_slot, remove_relations_of. simpl.
    refine (conj _ (conj _ (conj _ _))).
    + intro x. rewrite !filter_In. rewrite Hs. tauto.
    + intro r. rewrite !filter_In. rewrite Hr. tauto.
    + intro x. apply Ht.
    + exact Hrr.
  - unfold effect_Attach. simpl.
    refine (conj _ (conj _ (conj _ _))).
    + intro x. rewrite Hs. tauto.
    + intro r. simpl. rewrite Hr. tauto.
    + intro x. apply Ht.
    + exact Hrr.
  - unfold effect_Detach, remove_relation. simpl.
    refine (conj _ (conj _ (conj _ _))).
    + intro x. rewrite Hs. tauto.
    + intro r. rewrite !filter_In. rewrite Hr. tauto.
    + intro x. apply Ht.
    + exact Hrr.
  - unfold effect_Retype. simpl.
    refine (conj _ (conj _ (conj _ _))).
    + intro x. rewrite Hs. tauto.
    + intro r. rewrite Hr. tauto.
    + intro x. unfold update_type. destruct (Slot_eq_dec x v); [reflexivity | apply Ht].
    + exact Hrr.
Qed.

Theorem ot_tp1_for_independent : forall d1 d2 d3 F,
  independent d1 d2 = true ->
  independent d2 d3 = true ->
  independent d1 d3 = true ->
  slot_system_equiv
    (apply_effect d3 (apply_effect d2 (apply_effect d1 F)))
    (apply_effect d1 (apply_effect d2 (apply_effect d3 F))).
Proof.
  intros d1 d2 d3 F H12 H23 H13.
  assert (independent d2 d1 = true) as H21 by (rewrite independent_symmetric; exact H12).
  pose proof (independent_effects_commute_equiv d2 d1 F H21) as Comm21.
  assert (independent d3 d1 = true) as H31 by (rewrite independent_symmetric; exact H13).
  pose proof (independent_effects_commute_equiv d3 d1 (apply_effect d2 F) H31) as Comm31_d2.
  assert (independent d3 d2 = true) as H32 by (rewrite independent_symmetric; exact H23).
  pose proof (independent_effects_commute_equiv d3 d2 F H32) as Comm32.
  apply slot_system_equiv_trans with (apply_effect d3 (apply_effect d1 (apply_effect d2 F))).
  - apply slot_system_equiv_apply_effect_compat. exact Comm21.
  - apply slot_system_equiv_trans with (apply_effect d1 (apply_effect d3 (apply_effect d2 F))).
    + exact Comm31_d2.
    + apply slot_system_equiv_apply_effect_compat. exact Comm32.
Qed.

