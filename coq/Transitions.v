(* VCA Kernel - Transitions.v

   The 5 primitive transitions from VCA spec §7.
   Δ = {InsertSlot, DeleteSlot, Attach, Detach, Retype}
*)

Require Import VCA.Core.
Require Import VCA.Admissibility.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Lia.
Import ListNotations.

Inductive Transition : Type :=
  | InsertSlot (v : Slot) (t : SlotType)
  | DeleteSlot (v : Slot)
  | Attach (u v : Slot) (i : PosIndex)
  | Detach (u v : Slot) (i : PosIndex)
  | Retype (v : Slot) (t_new : SlotType).

(* Preconditions *)
Definition no_relations_to (v : Slot) (F : SlotSystem) : bool :=
  negb (existsb (fun r => Slot_eqb (rel_target r) v) (relations F)).

Definition pre_InsertSlot (v : Slot) (t : SlotType) (F : SlotSystem) : bool :=
  andb (negb (in_slots v F)) (no_relations_to v F).

Definition has_other_slot (v : Slot) (F : SlotSystem) : bool :=
  existsb (fun x => negb (Slot_eqb x v)) (slots F).

Definition pre_DeleteSlot (v : Slot) (F : SlotSystem) : bool :=
  andb (in_slots v F) (has_other_slot v F).

Definition position_available (v : Slot) (i : PosIndex) (F : SlotSystem) : bool :=
  negb (existsb (fun r =>
    andb (Slot_eqb (rel_target r) v)
         (Nat.eqb (rel_position r) i)) (relations F)).

Definition pre_Attach (u v : Slot) (i : PosIndex) (F : SlotSystem) : bool :=
  andb (in_slots u F)
       (andb (in_slots v F)
             (andb (position_available v i F)
                   (match ty_upper (type_of F v) with
                    | Finite n => Nat.ltb (src_count v F) n
                    | Infinite => true
                    end))).

Definition pre_Detach (u v : Slot) (i : PosIndex) (F : SlotSystem) : bool :=
  existsb (fun r =>
    andb (Slot_eqb (rel_source r) u)
         (andb (Slot_eqb (rel_target r) v)
               (Nat.eqb (rel_position r) i))) (relations F).

Definition pre_Retype (v : Slot) (t_new : SlotType) (F : SlotSystem) : bool :=
  andb (in_slots v F)
       (upper_satisfied t_new (src_count v F)).

Definition precondition (delta : Transition) (F : SlotSystem) : bool :=
  match delta with
  | InsertSlot v t => pre_InsertSlot v t F
  | DeleteSlot v => pre_DeleteSlot v F
  | Attach u v i => pre_Attach u v i F
  | Detach u v i => pre_Detach u v i F
  | Retype v t_new => pre_Retype v t_new F
  end.

(* Effects *)
Definition update_type (F : SlotSystem) (v : Slot) (t : SlotType) : Slot -> SlotType :=
  fun x => if Slot_eq_dec x v then t else type_of F x.

Definition remove_slot (v : Slot) (ls : list Slot) : list Slot :=
  filter (fun x => negb (Slot_eqb x v)) ls.

Definition remove_relations_of (v : Slot) (rels : list Relation) : list Relation :=
  filter (fun r =>
    andb (negb (Slot_eqb (rel_source r) v))
         (negb (Slot_eqb (rel_target r) v))) rels.

Definition remove_relation (u v : Slot) (i : PosIndex) (rels : list Relation) : list Relation :=
  filter (fun r =>
    negb (andb (Slot_eqb (rel_source r) u)
               (andb (Slot_eqb (rel_target r) v)
                     (Nat.eqb (rel_position r) i)))) rels.

Definition effect_InsertSlot (v : Slot) (t : SlotType) (F : SlotSystem) : SlotSystem :=
  mkSlotSystem
    (v :: slots F)
    (relations F)
    (update_type F v t)
    (rule_ref F).

Definition effect_DeleteSlot (v : Slot) (F : SlotSystem) : SlotSystem :=
  mkSlotSystem
    (remove_slot v (slots F))
    (remove_relations_of v (relations F))
    (type_of F)
    (rule_ref F).

Definition effect_Attach (u v : Slot) (i : PosIndex) (F : SlotSystem) : SlotSystem :=
  mkSlotSystem
    (slots F)
    (mkRelation u v i :: relations F)
    (type_of F)
    (rule_ref F).

Definition effect_Detach (u v : Slot) (i : PosIndex) (F : SlotSystem) : SlotSystem :=
  mkSlotSystem
    (slots F)
    (remove_relation u v i (relations F))
    (type_of F)
    (rule_ref F).

Definition effect_Retype (v : Slot) (t_new : SlotType) (F : SlotSystem) : SlotSystem :=
  mkSlotSystem
    (slots F)
    (relations F)
    (update_type F v t_new)
    (rule_ref F).

Definition apply_effect (delta : Transition) (F : SlotSystem) : SlotSystem :=
  match delta with
  | InsertSlot v t => effect_InsertSlot v t F
  | DeleteSlot v => effect_DeleteSlot v F
  | Attach u v i => effect_Attach u v i F
  | Detach u v i => effect_Detach u v i F
  | Retype v t_new => effect_Retype v t_new F
  end.

Definition apply_transition (delta : Transition) (F : SlotSystem) : option SlotSystem :=
  if precondition delta F
  then Some (apply_effect delta F)
  else None.

(* Theorem 8: Δ Preserves Structure - Helper Lemmas *)
Lemma forallb_filter : forall {A : Type} (p f : A -> bool) (l : list A),
  forallb p l = true -> forallb p (filter f l) = true.
Proof.
  intros A p f l H.
  induction l as [|x xs IH].
  - reflexivity.
  - simpl in *. destruct (f x) eqn:Ef; simpl.
    + apply andb_true_iff in H. destruct H.
      apply andb_true_iff. split; [exact H | apply IH; exact H0].
    + apply andb_true_iff in H. destruct H. apply IH. exact H0.
Qed.

Lemma filter_length_le : forall {A : Type} (f : A -> bool) (l : list A),
  length (filter f l) <= length l.
Proof.
  intros A f l. induction l as [|x xs IH]; simpl.
  - lia.
  - destruct (f x); simpl; lia.
Qed.

Lemma insert_preserves_position_unique : forall v t F,
  position_unique F = true ->
  position_unique (effect_InsertSlot v t F) = true.
Proof.
  intros. unfold effect_InsertSlot. simpl. exact H.
Qed.

Lemma filter_nested_length_le : forall {A : Type} (f g : A -> bool) (l : list A),
  length (filter f (filter g l)) <= length (filter f l).
Proof.
  intros A f g l. induction l as [|x xs IH]; simpl.
  - lia.
  - destruct (g x) eqn:Eg; simpl.
    + destruct (f x) eqn:Ef; simpl; lia.
    + destruct (f x) eqn:Ef; simpl.
      * assert (length (filter f (filter g xs)) <= length (filter f xs)) as H by apply IH. lia.
      * exact IH.
Qed.

Lemma delete_preserves_position_unique : forall v F,
  position_unique F = true ->
  position_unique (effect_DeleteSlot v F) = true.
Proof.
  intros v F Hpos.
  unfold effect_DeleteSlot, position_unique in *. simpl.
  unfold remove_relations_of.
  rewrite forallb_forall in *.
  intros r Hr. apply filter_In in Hr. destruct Hr as [Hr _].
  specialize (Hpos r Hr).
  unfold position_unique_at in *. simpl.
  apply Nat.leb_le in Hpos. apply Nat.leb_le.
  assert (length (filter (fun r0 =>
    andb (Slot_eqb (rel_target r0) (rel_target r))
         (Nat.eqb (rel_position r0) (rel_position r)))
    (filter (fun r0 => andb (negb (Slot_eqb (rel_source r0) v))
                            (negb (Slot_eqb (rel_target r0) v))) (relations F)))
    <= length (filter (fun r0 =>
         andb (Slot_eqb (rel_target r0) (rel_target r))
              (Nat.eqb (rel_position r0) (rel_position r))) (relations F))) as Hle.
  { apply filter_nested_length_le. }
  lia.
Qed.

Lemma detach_preserves_position_unique : forall u v i F,
  position_unique F = true ->
  position_unique (effect_Detach u v i F) = true.
Proof.
  intros u v i F Hpos.
  unfold effect_Detach, position_unique in *. simpl.
  unfold remove_relation.
  rewrite forallb_forall in *.
  intros r Hr. apply filter_In in Hr. destruct Hr as [Hr _].
  specialize (Hpos r Hr).
  unfold position_unique_at in *. simpl.
  apply Nat.leb_le in Hpos. apply Nat.leb_le.
  assert (length (filter (fun r0 =>
    andb (Slot_eqb (rel_target r0) (rel_target r))
         (Nat.eqb (rel_position r0) (rel_position r)))
    (filter (fun r0 => negb (andb (Slot_eqb (rel_source r0) u)
                            (andb (Slot_eqb (rel_target r0) v)
                                  (Nat.eqb (rel_position r0) i)))) (relations F)))
    <= length (filter (fun r0 =>
         andb (Slot_eqb (rel_target r0) (rel_target r))
              (Nat.eqb (rel_position r0) (rel_position r))) (relations F))) as Hle.
  { apply filter_nested_length_le. }
  lia.
Qed.

Lemma retype_preserves_position_unique : forall v t_new F,
  position_unique F = true ->
  position_unique (effect_Retype v t_new F) = true.
Proof.
  intros. unfold effect_Retype. simpl. exact H.
Qed.

Lemma upper_satisfied_mono : forall t n m,
  n <= m -> upper_satisfied t m = true -> upper_satisfied t n = true.
Proof.
  intros t n m Hle H. unfold upper_satisfied in *.
  destruct (ty_upper t).
  - apply Nat.leb_le in H. apply Nat.leb_le. lia.
  - reflexivity.
Qed.

Lemma src_count_delete_le : forall w v F,
  src_count w (effect_DeleteSlot v F) <= src_count w F.
Proof.
  intros w v F. unfold src_count, effect_DeleteSlot. simpl.
  unfold remove_relations_of. apply filter_nested_length_le.
Qed.

Lemma src_count_detach_le : forall w u v i F,
  src_count w (effect_Detach u v i F) <= src_count w F.
Proof.
  intros w u v i F. unfold src_count, effect_Detach. simpl.
  unfold remove_relation. apply filter_nested_length_le.
Qed.

Lemma no_relations_filter_empty : forall v F,
  no_relations_to v F = true ->
  filter (fun r => Slot_eqb (rel_target r) v) (relations F) = [].
Proof.
  intros v F Hno. unfold no_relations_to in Hno. apply negb_true_iff in Hno.
  destruct (filter (fun r => Slot_eqb (rel_target r) v) (relations F)) eqn:Ef; [reflexivity|].
  exfalso.
  assert (existsb (fun r => Slot_eqb (rel_target r) v) (relations F) = true) as Hex.
  { apply existsb_exists. exists r.
    assert (In r (r :: l)) as Hin by (left; reflexivity).
    rewrite <- Ef in Hin. apply filter_In in Hin. destruct Hin as [Hin1 Hin2].
    split; assumption. }
  rewrite Hex in Hno. discriminate.
Qed.

Lemma insert_preserves_upper_bounds : forall v t F,
  upper_bounds_ok F = true ->
  pre_InsertSlot v t F = true ->
  upper_bounds_ok (effect_InsertSlot v t F) = true.
Proof.
  intros v t F Hupper Hpre.
  unfold pre_InsertSlot in Hpre. apply andb_prop in Hpre. destruct Hpre as [Hnotin Hnorel].
  apply negb_true_iff in Hnotin.
  unfold upper_bounds_ok, effect_InsertSlot in *. simpl.
  apply andb_true_intro. split.
  - unfold upper_satisfied, src_count, update_type. simpl.
    destruct (Slot_eq_dec v v) as [_|Hne]; [|contradiction].
    rewrite (no_relations_filter_empty v F Hnorel). simpl.
    destruct (ty_upper t); [reflexivity | reflexivity].
  - rewrite forallb_forall in *. intros w Hw.
    specialize (Hupper w Hw).
    unfold update_type, src_count in *.
    destruct (Slot_eq_dec w v) as [Heq|_].
    + subst. unfold in_slots in Hnotin.
      exfalso.
      assert (existsb (Slot_eqb v) (slots F) = true) as Hex.
      { apply existsb_exists. exists v. split; [exact Hw|unfold Slot_eqb; destruct (Slot_eq_dec v v); [reflexivity|contradiction]]. }
      rewrite Hex in Hnotin. discriminate.
    + exact Hupper.
Qed.

Lemma delete_preserves_upper_bounds : forall v F,
  upper_bounds_ok F = true ->
  upper_bounds_ok (effect_DeleteSlot v F) = true.
Proof.
  intros v F Hupper.
  unfold upper_bounds_ok, effect_DeleteSlot in *. simpl.
  unfold remove_slot. rewrite forallb_forall in *.
  intros w Hw. apply filter_In in Hw. destruct Hw as [Hw _].
  specialize (Hupper w Hw).
  apply upper_satisfied_mono with (src_count w F).
  - apply src_count_delete_le.
  - exact Hupper.
Qed.

Lemma position_available_filter_empty : forall v i F,
  position_available v i F = true ->
  filter (fun r => andb (Slot_eqb (rel_target r) v) (Nat.eqb (rel_position r) i)) (relations F) = [].
Proof.
  intros v i F Havail. unfold position_available in Havail. apply negb_true_iff in Havail.
  destruct (filter (fun r => andb (Slot_eqb (rel_target r) v) (Nat.eqb (rel_position r) i)) (relations F)) eqn:Ef; [reflexivity|].
  exfalso.
  assert (existsb (fun r => andb (Slot_eqb (rel_target r) v) (Nat.eqb (rel_position r) i)) (relations F) = true) as Hex.
  { apply existsb_exists. exists r.
    assert (In r (r :: l)) as Hin by (left; reflexivity).
    rewrite <- Ef in Hin. apply filter_In in Hin. destruct Hin as [Hin1 Hin2].
    split; assumption. }
  rewrite Hex in Havail. discriminate.
Qed.

Lemma attach_preserves_position_unique : forall u v i F,
  position_unique F = true ->
  pre_Attach u v i F = true ->
  position_unique (effect_Attach u v i F) = true.
Proof.
  intros u v i F Hpos Hpre.
  unfold pre_Attach in Hpre.
  apply andb_prop in Hpre. destruct Hpre as [_ Hpre].
  apply andb_prop in Hpre. destruct Hpre as [_ Hpre].
  apply andb_prop in Hpre. destruct Hpre as [Havail _].
  unfold position_unique, effect_Attach in *. simpl.
  apply andb_true_intro. split.
  - unfold position_unique_at. simpl.
    unfold Slot_eqb. destruct (Slot_eq_dec v v) as [_|Hne]; [|contradiction].
    rewrite Nat.eqb_refl. simpl.
    pose proof (position_available_filter_empty v i F Havail) as Hempty.
    unfold Slot_eqb in Hempty. rewrite Hempty. simpl. reflexivity.
  - rewrite forallb_forall in *. intros r Hr. specialize (Hpos r Hr).
    unfold position_unique_at in *. simpl.
    destruct (Slot_eqb (rel_target (mkRelation u v i)) (rel_target r) &&
              Nat.eqb (rel_position (mkRelation u v i)) (rel_position r)) eqn:E.
    + simpl in E. apply andb_prop in E. destruct E as [Et Ei].
      unfold Slot_eqb in Et. destruct (Slot_eq_dec v (rel_target r)) as [Heq|Hne]; [|discriminate].
      apply Nat.eqb_eq in Ei. subst.
      exfalso. unfold position_available in Havail. apply negb_true_iff in Havail.
      assert (existsb (fun r0 => andb (Slot_eqb (rel_target r0) (rel_target r))
                                      (Nat.eqb (rel_position r0) (rel_position r))) (relations F) = true) as Hex.
      { apply existsb_exists. exists r. split; [exact Hr|].
        unfold Slot_eqb. destruct (Slot_eq_dec (rel_target r) (rel_target r)); [|contradiction].
        rewrite Nat.eqb_refl. reflexivity. }
      rewrite Hex in Havail. discriminate.
    + simpl in E. rewrite E. simpl. exact Hpos.
Qed.

Lemma attach_preserves_upper_bounds : forall u v i F,
  upper_bounds_ok F = true ->
  pre_Attach u v i F = true ->
  upper_bounds_ok (effect_Attach u v i F) = true.
Proof.
  intros u v i F Hupper Hpre.
  unfold pre_Attach in Hpre.
  apply andb_prop in Hpre. destruct Hpre as [_ Hpre].
  apply andb_prop in Hpre. destruct Hpre as [_ Hpre].
  apply andb_prop in Hpre. destruct Hpre as [_ Hbound].
  unfold upper_bounds_ok, effect_Attach in *. simpl.
  rewrite forallb_forall in *. intros w Hw.
  specialize (Hupper w Hw).
  unfold src_count in *. simpl.
  destruct (Slot_eqb v w) eqn:Evw.
  - unfold Slot_eqb in Evw. destruct (Slot_eq_dec v w) as [Heq|]; [|discriminate].
    subst. simpl.
    destruct (Slot_eq_dec w w) as [_|Hne]; [|contradiction].
    unfold upper_satisfied in *.
    destruct (ty_upper (type_of F w)) eqn:Eup.
    + apply Nat.leb_le. apply Nat.ltb_lt in Hbound. lia.
    + reflexivity.
  - unfold Slot_eqb in Evw. destruct (Slot_eq_dec v w) as [Heq|Hne]; [discriminate|].
    simpl. destruct (Slot_eq_dec w w) as [_|Hc]; [|contradiction].
    destruct (Slot_eq_dec v w) as [Hc|_]; [contradiction|].
    exact Hupper.
Qed.

Lemma detach_preserves_upper_bounds : forall u v i F,
  upper_bounds_ok F = true ->
  upper_bounds_ok (effect_Detach u v i F) = true.
Proof.
  intros u v i F Hupper.
  unfold upper_bounds_ok, effect_Detach in *. simpl.
  rewrite forallb_forall in *. intros w Hw.
  specialize (Hupper w Hw).
  apply upper_satisfied_mono with (src_count w F).
  - apply src_count_detach_le.
  - exact Hupper.
Qed.

Lemma retype_preserves_upper_bounds : forall v t_new F,
  upper_bounds_ok F = true ->
  pre_Retype v t_new F = true ->
  upper_bounds_ok (effect_Retype v t_new F) = true.
Proof.
  intros v t_new F Hupper Hpre.
  unfold pre_Retype in Hpre.
  apply andb_prop in Hpre. destruct Hpre as [_ Hsat].
  unfold upper_bounds_ok, effect_Retype in *. simpl.
  rewrite forallb_forall in *. intros w Hw.
  specialize (Hupper w Hw).
  unfold update_type, src_count in *.
  destruct (Slot_eq_dec w v) as [Heq|Hne].
  - subst. exact Hsat.
  - exact Hupper.
Qed.

Lemma filter_nonempty_from_exists : forall {A : Type} (f : A -> bool) (l : list A),
  existsb f l = true ->
  length (filter f l) > 0.
Proof.
  intros A f l H. apply existsb_exists in H. destruct H as [x [Hin Hf]].
  induction l as [|y ys IH]; [inversion Hin|].
  simpl. destruct (f y) eqn:Efy; simpl.
  - lia.
  - destruct Hin as [Heq|Hin].
    + subst. rewrite Hf in Efy. discriminate.
    + apply IH. exact Hin.
Qed.

Lemma delete_nonempty : forall v F,
  pre_DeleteSlot v F = true ->
  negb (length (slots F) =? 0) = true ->
  negb (length (remove_slot v (slots F)) =? 0) = true.
Proof.
  intros v F Hpre Hne.
  unfold pre_DeleteSlot in Hpre.
  apply andb_prop in Hpre. destruct Hpre as [Hin Hother].
  apply negb_true_iff. apply Nat.eqb_neq.
  unfold remove_slot.
  unfold has_other_slot in Hother.
  pose proof (filter_nonempty_from_exists (fun x => negb (Slot_eqb x v)) (slots F) Hother) as H.
  lia.
Qed.

(* Theorem 8: Δ Preserves Structure *)
Theorem delta_preserves_struct :
  forall (delta : Transition) (F : SlotSystem),
    FS_struct F ->
    precondition delta F = true ->
    FS_struct (apply_effect delta F).
Proof.
  intros delta F Hstruct Hpre.
  unfold FS_struct, FS_struct_b in *.
  apply andb_prop in Hstruct. destruct Hstruct as [Hne Hrest].
  apply andb_prop in Hrest. destruct Hrest as [Hpos Hupper].
  destruct delta as [v t | v | u v i | u v i | v t_new]; simpl in *.

  - (* InsertSlot *)
    rewrite (insert_preserves_position_unique v t F Hpos).
    rewrite (insert_preserves_upper_bounds v t F Hupper Hpre).
    reflexivity.

  - (* DeleteSlot *)
    rewrite (delete_preserves_position_unique v F Hpos).
    rewrite (delete_preserves_upper_bounds v F Hupper).
    rewrite (delete_nonempty v F Hpre Hne).
    reflexivity.

  - (* Attach *)
    rewrite (attach_preserves_position_unique u v i F Hpos Hpre).
    rewrite (attach_preserves_upper_bounds u v i F Hupper Hpre).
    simpl. rewrite Hne. reflexivity.

  - (* Detach *)
    rewrite (detach_preserves_position_unique u v i F Hpos).
    rewrite (detach_preserves_upper_bounds u v i F Hupper).
    simpl. rewrite Hne. reflexivity.

  - (* Retype *)
    rewrite (retype_preserves_position_unique v t_new F Hpos).
    rewrite (retype_preserves_upper_bounds v t_new F Hupper Hpre).
    simpl. rewrite Hne. reflexivity.
Qed.
