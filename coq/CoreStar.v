(* VCA Kernel - CoreStar.v

   Core* operator for restoring coherence.
   Theorems 9-10: Core* Produces Coherent, Core* Idempotent.
*)

Require Import VCA.Core.
Require Import VCA.Admissibility.
Require Import VCA.Transitions.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Lia.
Import ListNotations.

Definition filter_valid_rules (F : SlotSystem) : list Slot :=
  filter (valid_rule_slot F) (slots F).

Definition relations_in_slots (rels : list Relation) (vs : list Slot) : list Relation :=
  filter (fun r =>
    andb (existsb (Slot_eqb (rel_source r)) vs)
         (existsb (Slot_eqb (rel_target r)) vs)) rels.

Definition core_R (F : SlotSystem) : SlotSystem :=
  let vs := filter_valid_rules F in
  mkSlotSystem
    vs
    (relations_in_slots (relations F) vs)
    (type_of F)
    (rule_ref F).

Definition admissible_relations (F : SlotSystem) : list Relation :=
  filter (relation_admissible F) (relations F).

Definition core (F : SlotSystem) : SlotSystem :=
  mkSlotSystem
    (slots F)
    (admissible_relations F)
    (type_of F)
    (rule_ref F).

Fixpoint core_star_iter (F : SlotSystem) (fuel : nat) : SlotSystem :=
  match fuel with
  | 0 => F
  | S n =>
      let F' := core (core_R F) in
      if andb (Nat.eqb (length (slots F')) (length (slots F)))
              (Nat.eqb (length (relations F')) (length (relations F)))
      then F
      else core_star_iter F' n
  end.

Definition core_star (F : SlotSystem) : SlotSystem :=
  core_star_iter F (length (slots F) + length (relations F)).

Lemma core_preserves_slots : forall F,
  slots (core F) = slots F.
Proof.
  intro F. unfold core. reflexivity.
Qed.

Lemma core_relations_admissible : forall F r,
  In r (relations (core F)) ->
  relation_admissible F r = true.
Proof.
  intros F r H. unfold core in H. simpl in H.
  unfold admissible_relations in H. apply filter_In in H.
  destruct H as [_ H]. exact H.
Qed.

Lemma core_relations_subset : forall F r,
  In r (relations (core F)) ->
  In r (relations F).
Proof.
  intros F r H. unfold core in H. simpl in H.
  unfold admissible_relations in H. apply filter_In in H.
  destruct H as [H _]. exact H.
Qed.

Lemma filter_preserves_position_unique : forall f F,
  position_unique F = true ->
  position_unique (mkSlotSystem (slots F) (filter f (relations F)) (type_of F) (rule_ref F)) = true.
Proof.
  intros f F H. unfold position_unique in *. simpl.
  rewrite forallb_forall in *. intros r Hr.
  apply filter_In in Hr. destruct Hr as [Hr _].
  specialize (H r Hr). unfold position_unique_at in *. simpl.
  apply Nat.leb_le in H. apply Nat.leb_le.
  pose proof (filter_nested_length_le
    (fun r0 => Slot_eqb (rel_target r0) (rel_target r) && (rel_position r0 =? rel_position r))
    f (relations F)) as Hle.
  lia.
Qed.

Lemma filter_preserves_upper_bounds : forall f F,
  upper_bounds_ok F = true ->
  upper_bounds_ok (mkSlotSystem (slots F) (filter f (relations F)) (type_of F) (rule_ref F)) = true.
Proof.
  intros f F H. unfold upper_bounds_ok in *. simpl.
  rewrite forallb_forall in *. intros v Hv.
  specialize (H v Hv). unfold upper_satisfied, src_count in *. simpl.
  destruct (ty_upper (type_of F v)) eqn:Eup.
  - apply Nat.leb_le in H. apply Nat.leb_le.
    pose proof (filter_nested_length_le (fun r => Slot_eqb (rel_target r) v) f (relations F)) as Hle.
    lia.
  - reflexivity.
Qed.

Lemma core_preserves_struct : forall F,
  FS_struct F ->
  FS_struct (core F).
Proof.
  intros F H. unfold FS_struct, FS_struct_b in *.
  apply andb_prop in H. destruct H as [Hne Hrest].
  apply andb_prop in Hrest. destruct Hrest as [Hpos Hupper].
  unfold core. simpl.
  apply andb_true_intro. split.
  - exact Hne.
  - apply andb_true_intro. split.
    + apply filter_preserves_position_unique. exact Hpos.
    + apply filter_preserves_upper_bounds. exact Hupper.
Qed.

Lemma core_all_admissible : forall F,
  all_admissible (core F) = true.
Proof.
  intro F. unfold core, all_admissible, admissible_relations. simpl.
  rewrite forallb_forall. intros r Hr.
  apply filter_In in Hr. destruct Hr as [Hr Hadm].
  unfold relation_admissible in *. unfold core. simpl.
  exact Hadm.
Qed.

Theorem core_produces_coherent : forall F,
  FS_struct F ->
  rule_ref F = RuleSelfRef ->
  FS_coh (core F).
Proof.
  intros F Hstruct Hself.
  unfold FS_coh, FS_coh_b.
  apply andb_true_intro. split.
  - apply core_preserves_struct. exact Hstruct.
  - apply core_all_admissible.
Qed.

Lemma filter_all_true : forall {A : Type} (f : A -> bool) (l : list A),
  (forall x, In x l -> f x = true) ->
  filter f l = l.
Proof.
  intros A f l H. induction l as [|x xs IH]; simpl.
  - reflexivity.
  - assert (f x = true) as Hx by (apply H; left; reflexivity).
    rewrite Hx. f_equal. apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Theorem core_idempotent_on_coherent : forall F,
  FS_coh F ->
  relations (core F) = relations F.
Proof.
  intros F H. unfold FS_coh, FS_coh_b in H.
  apply andb_prop in H. destruct H as [Hstruct Hadm].
  unfold core, admissible_relations. simpl.
  unfold all_admissible in Hadm.
  apply filter_all_true. intros r Hr.
  rewrite forallb_forall in Hadm. exact (Hadm r Hr).
Qed.

Theorem core_fixpoint_on_coherent : forall F,
  FS_coh F ->
  slots (core F) = slots F /\ relations (core F) = relations F.
Proof.
  intros F H. split.
  - apply core_preserves_slots.
  - apply core_idempotent_on_coherent. exact H.
Qed.

Lemma core_R_slots_le : forall F,
  length (slots (core_R F)) <= length (slots F).
Proof.
  intro F. unfold core_R, filter_valid_rules. simpl.
  apply filter_length_le.
Qed.

Lemma core_R_relations_le : forall F,
  length (relations (core_R F)) <= length (relations F).
Proof.
  intro F. unfold core_R, relations_in_slots. simpl.
  apply filter_length_le.
Qed.

Lemma core_relations_le : forall F,
  length (relations (core F)) <= length (relations F).
Proof.
  intro F. unfold core, admissible_relations. simpl.
  apply filter_length_le.
Qed.

Lemma core_core_R_decreasing : forall F,
  length (slots (core (core_R F))) + length (relations (core (core_R F))) <=
  length (slots F) + length (relations F).
Proof.
  intro F.
  assert (length (slots (core (core_R F))) <= length (slots (core_R F))) as Hs.
  { rewrite core_preserves_slots. lia. }
  assert (length (slots (core_R F)) <= length (slots F)) as Hs'.
  { apply core_R_slots_le. }
  assert (length (relations (core (core_R F))) <= length (relations (core_R F))) as Hr.
  { apply core_relations_le. }
  assert (length (relations (core_R F)) <= length (relations F)) as Hr'.
  { apply core_R_relations_le. }
  lia.
Qed.

Definition endpoints_in_slots (F : SlotSystem) : bool :=
  forallb (fun r =>
    andb (existsb (Slot_eqb (rel_source r)) (slots F))
         (existsb (Slot_eqb (rel_target r)) (slots F))) (relations F).

Definition no_invalid_rules (F : SlotSystem) : Prop :=
  forall v, In v (slots F) -> ty_family (type_of F v) = FamRule ->
    ty_kind (type_of F v) <> KindInvalid.

Lemma valid_rule_slot_of_non_invalid : forall F r,
  (ty_family (type_of F r) = FamRule -> ty_kind (type_of F r) <> KindInvalid) ->
  valid_rule_slot F r = true.
Proof.
  intros F r H. unfold valid_rule_slot.
  destruct (ty_family (type_of F r)) eqn:Ef; try reflexivity.
  apply kind_in_registry_valid. apply H. reflexivity.
Qed.

Lemma filter_valid_rules_id : forall F,
  no_invalid_rules F ->
  filter_valid_rules F = slots F.
Proof.
  intros F Hnir. unfold filter_valid_rules.
  apply filter_all_true. intros x Hx.
  apply valid_rule_slot_of_non_invalid.
  intro Hfam. exact (Hnir x Hx Hfam).
Qed.

Definition well_formed (F : SlotSystem) : Prop :=
  FS_struct F /\ endpoints_in_slots F = true /\ no_invalid_rules F.

Lemma filter_length_eq_all_true : forall {A : Type} (f : A -> bool) (l : list A),
  length (filter f l) = length l ->
  forall x, In x l -> f x = true.
Proof.
  intros A f l Hlen x Hin.
  induction l as [|y ys IH].
  - inversion Hin.
  - simpl in Hlen. destruct (f y) eqn:Efy.
    + simpl in Hlen. injection Hlen as Hlen.
      destruct Hin as [Heq | Hin].
      * subst. exact Efy.
      * apply IH; [exact Hlen | exact Hin].
    + assert (length (filter f ys) <= length ys) as Hle by apply filter_length_le.
      lia.
Qed.

Lemma all_valid_implies_core_R_slots_eq : forall F,
  length (slots (core_R F)) = length (slots F) ->
  slots (core_R F) = slots F.
Proof.
  intros F Hlen.
  unfold core_R, filter_valid_rules in *. simpl in *.
  apply filter_all_true.
  apply filter_length_eq_all_true. exact Hlen.
Qed.

Lemma relations_in_all_slots : forall rels vs,
  (forall r, In r rels -> In (rel_source r) vs /\ In (rel_target r) vs) ->
  relations_in_slots rels vs = rels.
Proof.
  intros rels vs H.
  unfold relations_in_slots.
  apply filter_all_true. intros r Hr.
  destruct (H r Hr) as [Hs Ht].
  apply andb_true_intro. split.
  - apply existsb_exists. exists (rel_source r). split; [exact Hs|].
    unfold Slot_eqb. destruct (Slot_eq_dec (rel_source r) (rel_source r)); [reflexivity|contradiction].
  - apply existsb_exists. exists (rel_target r). split; [exact Ht|].
    unfold Slot_eqb. destruct (Slot_eq_dec (rel_target r) (rel_target r)); [reflexivity|contradiction].
Qed.

Lemma endpoints_in_slots_impl : forall F r,
  endpoints_in_slots F = true ->
  In r (relations F) ->
  In (rel_source r) (slots F) /\ In (rel_target r) (slots F).
Proof.
  intros F r Hwf Hr.
  unfold endpoints_in_slots in Hwf.
  rewrite forallb_forall in Hwf.
  specialize (Hwf r Hr).
  apply andb_prop in Hwf. destruct Hwf as [Hsrc Htgt].
  split.
  - apply existsb_exists in Hsrc. destruct Hsrc as [s [Hin Heq]].
    unfold Slot_eqb in Heq. destruct (Slot_eq_dec (rel_source r) s); [subst; exact Hin | discriminate].
  - apply existsb_exists in Htgt. destruct Htgt as [t [Hin Heq]].
    unfold Slot_eqb in Heq. destruct (Slot_eq_dec (rel_target r) t); [subst; exact Hin | discriminate].
Qed.

Lemma core_R_preserves_relations_when_all_valid : forall F,
  length (slots (core_R F)) = length (slots F) ->
  endpoints_in_slots F = true ->
  relations (core_R F) = relations F.
Proof.
  intros F Hslots Hwf.
  pose proof (all_valid_implies_core_R_slots_eq F Hslots) as Hslots_eq.
  unfold core_R. simpl.
  assert (filter_valid_rules F = slots F) as Hfvr.
  { unfold core_R, filter_valid_rules in Hslots_eq. simpl in Hslots_eq. exact Hslots_eq. }
  rewrite Hfvr.
  apply relations_in_all_slots.
  intros r Hr. apply endpoints_in_slots_impl; assumption.
Qed.

Lemma core_R_equiv_when_fixpoint : forall F,
  slots (core_R F) = slots F ->
  relations (core_R F) = relations F ->
  forall r, relation_admissible (core_R F) r = relation_admissible F r.
Proof.
  intros F Hslots Hrels r.
  unfold relation_admissible.
  assert (type_of (core_R F) = type_of F) as Hty by reflexivity.
  assert (rule_ref (core_R F) = rule_ref F) as Hrr by reflexivity.
  rewrite Hslots, Hty, Hrr. reflexivity.
Qed.

Lemma fixpoint_implies_all_admissible : forall F,
  length (slots (core (core_R F))) = length (slots F) ->
  length (relations (core (core_R F))) = length (relations F) ->
  endpoints_in_slots F = true ->
  all_admissible F = true.
Proof.
  intros F Hslots Hrels Hwf.
  rewrite core_preserves_slots in Hslots.
  pose proof (all_valid_implies_core_R_slots_eq F Hslots) as Hslots_eq.
  assert (relations (core_R F) = relations F) as Hrels_core_R.
  { apply core_R_preserves_relations_when_all_valid; assumption. }
  assert (forall r, relation_admissible (core_R F) r = relation_admissible F r) as Hadm_eq.
  { apply core_R_equiv_when_fixpoint.
    - unfold core_R. simpl. unfold filter_valid_rules.
      unfold core_R, filter_valid_rules in Hslots_eq. simpl in Hslots_eq.
      exact Hslots_eq.
    - exact Hrels_core_R. }
  unfold core in Hrels. simpl in Hrels.
  unfold admissible_relations in Hrels.
  rewrite Hrels_core_R in Hrels.
  unfold all_admissible. apply forallb_forall.
  intros r Hr.
  assert (forall x, In x (relations F) ->
          (fun x0 => relation_admissible (core_R F) x0) x = true ->
          relation_admissible F x = true) as Himpl.
  { intros x _ Hadmx. rewrite <- Hadm_eq. exact Hadmx. }
  apply Himpl; [exact Hr|].
  apply filter_length_eq_all_true with (x := r) in Hrels; [exact Hrels | exact Hr].
Qed.

Lemma fixpoint_implies_coherent : forall F,
  well_formed F ->
  rule_ref F = RuleSelfRef ->
  length (slots (core (core_R F))) = length (slots F) ->
  length (relations (core (core_R F))) = length (relations F) ->
  FS_coh F.
Proof.
  intros F [Hstruct [Hwf _]] Hself Hslots Hrels.
  unfold FS_coh, FS_coh_b.
  apply andb_true_intro. split.
  - unfold FS_struct, FS_struct_b in *. exact Hstruct.
  - apply fixpoint_implies_all_admissible; assumption.
Qed.

Lemma filter_nonempty_if_exists : forall {A : Type} (f : A -> bool) (l : list A),
  existsb f l = true ->
  filter f l <> [].
Proof.
  intros A f l H.
  apply existsb_exists in H. destruct H as [x [Hin Hfx]].
  intro Hcontra.
  assert (In x (filter f l)) as Hx.
  { apply filter_In. split; assumption. }
  rewrite Hcontra in Hx. inversion Hx.
Qed.

Lemma no_invalid_rules_core_R : forall F,
  no_invalid_rules (core_R F).
Proof.
  intro F. unfold no_invalid_rules, core_R. simpl.
  intros v Hv Hfam Hinv.
  unfold filter_valid_rules in Hv. apply filter_In in Hv. destruct Hv as [_ Hvr].
  unfold valid_rule_slot in Hvr. rewrite Hfam in Hvr.
  rewrite Hinv in Hvr. simpl in Hvr. discriminate.
Qed.

Lemma no_invalid_rules_core : forall F,
  no_invalid_rules F -> no_invalid_rules (core F).
Proof.
  intros F Hnir v Hv Hfam.
  unfold core in Hv. simpl in Hv. exact (Hnir v Hv Hfam).
Qed.

Lemma core_R_slots_eq : forall F,
  no_invalid_rules F ->
  slots (core_R F) = slots F.
Proof.
  intros F Hnir. unfold core_R. simpl. apply filter_valid_rules_id. exact Hnir.
Qed.

Lemma relations_in_slots_id : forall F,
  endpoints_in_slots F = true ->
  relations_in_slots (relations F) (slots F) = relations F.
Proof.
  intros F Hwf. apply relations_in_all_slots.
  intros r Hr. apply endpoints_in_slots_impl; assumption.
Qed.

Lemma core_R_relations_eq : forall F,
  no_invalid_rules F ->
  endpoints_in_slots F = true ->
  relations (core_R F) = relations F.
Proof.
  intros F Hnir Hwf. unfold core_R. simpl. rewrite (filter_valid_rules_id F Hnir).
  apply relations_in_slots_id. exact Hwf.
Qed.

Lemma core_R_eq : forall F,
  no_invalid_rules F ->
  endpoints_in_slots F = true ->
  slots (core_R F) = slots F /\ relations (core_R F) = relations F.
Proof.
  intros F Hnir Hwf. split.
  - apply core_R_slots_eq. exact Hnir.
  - apply core_R_relations_eq; assumption.
Qed.

Lemma core_R_preserves_well_formed : forall F,
  well_formed F ->
  well_formed (core_R F).
Proof.
  intros F [Hstruct [Hwf Hnir]].
  split; [|split].
  - unfold core_R, FS_struct, FS_struct_b in *. simpl.
    rewrite (filter_valid_rules_id F Hnir).
    apply andb_prop in Hstruct. destruct Hstruct as [Hne Hrest].
    apply andb_prop in Hrest. destruct Hrest as [Hpos Hupper].
    apply andb_true_intro. split.
    + exact Hne.
    + apply andb_true_intro. split.
      * unfold position_unique, relations_in_slots in *.
        rewrite forallb_forall in *. intros r Hr.
        apply filter_In in Hr. destruct Hr as [Hr _].
        specialize (Hpos r Hr).
        unfold position_unique_at in *. simpl.
        apply Nat.leb_le in Hpos. apply Nat.leb_le.
        pose proof (filter_nested_length_le
          (fun r0 => Slot_eqb (rel_target r0) (rel_target r) && (rel_position r0 =? rel_position r))
          (fun r0 => existsb (Slot_eqb (rel_source r0)) (slots F) &&
                     existsb (Slot_eqb (rel_target r0)) (slots F))
          (relations F)) as Hle.
        lia.
      * unfold upper_bounds_ok, relations_in_slots in *.
        rewrite forallb_forall in *. intros v Hv.
        specialize (Hupper v Hv).
        unfold upper_satisfied, src_count in *. simpl.
        destruct (ty_upper (type_of F v)) eqn:Eup.
        -- apply Nat.leb_le in Hupper. apply Nat.leb_le.
           pose proof (filter_nested_length_le
             (fun r => Slot_eqb (rel_target r) v)
             (fun r => existsb (Slot_eqb (rel_source r)) (slots F) &&
                       existsb (Slot_eqb (rel_target r)) (slots F))
             (relations F)) as Hle.
           lia.
        -- reflexivity.
  - unfold endpoints_in_slots, core_R, relations_in_slots in *. simpl.
    rewrite (filter_valid_rules_id F Hnir).
    rewrite forallb_forall in *. intros r Hr.
    apply filter_In in Hr. destruct Hr as [_ Hr].
    exact Hr.
  - apply no_invalid_rules_core_R.
Qed.

Lemma core_preserves_well_formed : forall F,
  well_formed F ->
  well_formed (core F).
Proof.
  intros F [Hstruct [Hwf Hnir]].
  split; [|split].
  - apply core_preserves_struct. exact Hstruct.
  - unfold endpoints_in_slots, core, admissible_relations in *. simpl.
    rewrite forallb_forall in *. intros r Hr.
    apply filter_In in Hr. destruct Hr as [Hr _].
    exact (Hwf r Hr).
  - apply no_invalid_rules_core. exact Hnir.
Qed.

Lemma relation_admissible_ext : forall F r,
  relation_admissible (mkSlotSystem (slots F) (relations F) (type_of F) (rule_ref F)) r =
  relation_admissible F r.
Proof.
  intros F r. unfold relation_admissible. simpl.
  destruct F. reflexivity.
Qed.

Lemma relation_admissible_core_R : forall F,
  no_invalid_rules F ->
  forall r, relation_admissible (core_R F) r = relation_admissible F r.
Proof.
  intros F Hnir r. unfold core_R. simpl.
  rewrite (filter_valid_rules_id F Hnir).
  apply relation_admissible_ext.
Qed.

Lemma core_core_R_simplified : forall F,
  no_invalid_rules F ->
  endpoints_in_slots F = true ->
  slots (core (core_R F)) = slots F /\
  relations (core (core_R F)) = admissible_relations F.
Proof.
  intros F Hnir Hwf. split.
  - rewrite core_preserves_slots. apply core_R_slots_eq. exact Hnir.
  - unfold core, admissible_relations. simpl.
    unfold core_R. simpl. rewrite (filter_valid_rules_id F Hnir).
    rewrite relations_in_slots_id by exact Hwf.
    apply filter_ext_in. intros r Hr. apply relation_admissible_ext.
Qed.

Lemma core_star_iter_coherent_aux : forall fuel F,
  well_formed F ->
  rule_ref F = RuleSelfRef ->
  length (slots F) + length (relations F) <= fuel ->
  FS_coh (core_star_iter F fuel).
Proof.
  intros fuel. induction fuel as [|n IH]; intros F Hwf Hself Hbound.
  - destruct Hwf as [Hstruct _].
    unfold FS_struct, FS_struct_b in Hstruct.
    apply andb_prop in Hstruct. destruct Hstruct as [Hne _].
    apply negb_true_iff in Hne. apply Nat.eqb_neq in Hne.
    simpl in Hbound. lia.
  - simpl.
    destruct Hwf as [Hstruct [Hendpoints Hnir]].
    destruct (andb (Nat.eqb (length (filter_valid_rules F)) (length (slots F)))
                   (Nat.eqb (length (admissible_relations (core_R F))) (length (relations F)))) eqn:Hfix.
    + apply andb_prop in Hfix. destruct Hfix as [Hslots Hrels].
      apply Nat.eqb_eq in Hslots. apply Nat.eqb_eq in Hrels.
      rewrite (filter_valid_rules_id F Hnir) in Hslots.
      unfold admissible_relations in Hrels.
      pose proof (core_R_relations_eq F Hnir Hendpoints) as Hr_eq.
      rewrite Hr_eq in Hrels.
      assert (forall r, relation_admissible (core_R F) r = relation_admissible F r) as Hadm_eq.
      { intro r. apply (relation_admissible_core_R F Hnir). }
      rewrite (filter_ext _ _ Hadm_eq) in Hrels.
      apply (fixpoint_implies_coherent F).
      * split; [exact Hstruct | split; [exact Hendpoints | exact Hnir]].
      * exact Hself.
      * pose proof (core_core_R_simplified F Hnir Hendpoints) as [Hs _]. rewrite Hs. reflexivity.
      * pose proof (core_core_R_simplified F Hnir Hendpoints) as [_ Hr].
        rewrite Hr. unfold admissible_relations. exact Hrels.
    + apply IH.
      * apply core_preserves_well_formed. apply core_R_preserves_well_formed.
        split; [exact Hstruct | split; [exact Hendpoints | exact Hnir]].
      * unfold core, core_R. simpl. exact Hself.
      * pose proof (core_core_R_decreasing F) as Hdec.
        apply Bool.andb_false_iff in Hfix.
        destruct Hfix as [Hslots | Hrels].
        -- rewrite (filter_valid_rules_id F Hnir) in Hslots. apply Nat.eqb_neq in Hslots. lia.
        -- apply Nat.eqb_neq in Hrels.
           unfold admissible_relations in Hrels.
           pose proof (core_R_relations_eq F Hnir Hendpoints) as Hr_eq.
           rewrite Hr_eq in Hrels.
           assert (filter (relation_admissible (core_R F)) (relations F) =
                   filter (relation_admissible F) (relations F)) as Hfilter_eq.
           { apply filter_ext_in. intros r _. apply (relation_admissible_core_R F Hnir). }
           rewrite Hfilter_eq in Hrels.
           pose proof (filter_length_le (relation_admissible F) (relations F)) as Hle.
           assert (length (relations (core (core_R F))) <= length (relations F)) as Hle2.
           { pose proof (core_relations_le (core_R F)) as Hle1.
             pose proof (core_R_relations_le F) as Hle3. lia. }
           assert (length (relations (core (core_R F))) < length (relations F)) as Hlt.
           { pose proof (core_core_R_simplified F Hnir Hendpoints) as [_ Hr].
             rewrite Hr. unfold admissible_relations. lia. }
           pose proof (core_core_R_simplified F Hnir Hendpoints) as [Hs _].
           rewrite Hs. lia.
Qed.

Lemma core_star_iter_coherent : forall fuel F,
  well_formed F ->
  rule_ref F = RuleSelfRef ->
  length (slots F) + length (relations F) <= fuel ->
  FS_coh (core_star_iter F fuel).
Proof.
  exact core_star_iter_coherent_aux.
Qed.

Theorem core_star_produces_coherent : forall F,
  well_formed F ->
  rule_ref F = RuleSelfRef ->
  FS_coh (core_star F).
Proof.
  intros F Hwf Hself.
  unfold core_star.
  apply core_star_iter_coherent; try assumption.
  lia.
Qed.

Lemma core_R_on_coherent : forall F,
  FS_coh F ->
  no_invalid_rules F ->
  endpoints_in_slots F = true ->
  slots (core_R F) = slots F.
Proof.
  intros F _ Hnir _. apply core_R_slots_eq. exact Hnir.
Qed.

Lemma core_core_R_on_coherent : forall F,
  FS_coh F ->
  endpoints_in_slots F = true ->
  no_invalid_rules F ->
  core (core_R F) = F.
Proof.
  intros F Hcoh Hwf Hnir.
  pose proof (core_idempotent_on_coherent F Hcoh) as Hrels.
  unfold core, admissible_relations in Hrels. simpl in Hrels.
  unfold core, core_R, admissible_relations. simpl.
  rewrite (filter_valid_rules_id F Hnir).
  rewrite relations_in_slots_id by exact Hwf.
  assert (filter (relation_admissible
            (mkSlotSystem (slots F) (relations F) (type_of F) (rule_ref F)))
            (relations F) =
          filter (relation_admissible F) (relations F)) as Hfilt.
  { apply filter_ext_in. intros r _. apply relation_admissible_ext. }
  rewrite Hfilt. rewrite Hrels.
  destruct F as [vs rels ty rr]. reflexivity.
Qed.

Lemma coherent_implies_well_formed : forall F,
  FS_coh F ->
  endpoints_in_slots F = true ->
  no_invalid_rules F ->
  well_formed F.
Proof.
  intros F Hcoh Hwf Hnir.
  split; [|split].
  - unfold FS_coh, FS_coh_b in Hcoh.
    apply andb_prop in Hcoh. destruct Hcoh as [Hstruct _]. exact Hstruct.
  - exact Hwf.
  - exact Hnir.
Qed.

Lemma core_star_preserves_endpoints : forall F,
  well_formed F ->
  endpoints_in_slots (core_star F) = true.
Proof.
  intros F Hwf.
  unfold core_star.
  generalize (length (slots F) + length (relations F)) as fuel.
  intro fuel. generalize dependent F.
  induction fuel as [|n IH]; intros F [Hstruct [Hendpoints Hnir]].
  - simpl. exact Hendpoints.
  - simpl.
    destruct (andb (Nat.eqb (length (filter_valid_rules F)) (length (slots F)))
                   (Nat.eqb (length (admissible_relations (core_R F))) (length (relations F)))) eqn:Hfix.
    + exact Hendpoints.
    + apply IH. apply core_preserves_well_formed. apply core_R_preserves_well_formed.
      split; [exact Hstruct | split; [exact Hendpoints | exact Hnir]].
Qed.

Lemma core_star_preserves_no_invalid_rules : forall F,
  well_formed F ->
  no_invalid_rules (core_star F).
Proof.
  intros F Hwf.
  unfold core_star.
  generalize (length (slots F) + length (relations F)) as fuel.
  intro fuel. generalize dependent F.
  induction fuel as [|n IH]; intros F [Hstruct [Hendpoints Hnir]].
  - simpl. exact Hnir.
  - simpl.
    destruct (andb (Nat.eqb (length (filter_valid_rules F)) (length (slots F)))
                   (Nat.eqb (length (admissible_relations (core_R F))) (length (relations F)))) eqn:Hfix.
    + exact Hnir.
    + apply IH. apply core_preserves_well_formed. apply core_R_preserves_well_formed.
      split; [exact Hstruct | split; [exact Hendpoints | exact Hnir]].
Qed.

Lemma core_star_fixpoint : forall F,
  FS_coh F ->
  endpoints_in_slots F = true ->
  no_invalid_rules F ->
  core_star F = F.
Proof.
  intros F Hcoh Hwf Hnir.
  unfold core_star, core_star_iter.
  pose proof (core_core_R_on_coherent F Hcoh Hwf Hnir) as Heq.
  assert (length (slots F) + length (relations F) > 0 \/ length (slots F) + length (relations F) = 0) as [Hgt|H0].
  { destruct (length (slots F) + length (relations F)); [right | left]; lia. }
  - destruct (length (slots F) + length (relations F)) eqn:Efuel.
    + lia.
    + simpl.
      assert (slots (core (core_R F)) = slots F) as Hs.
      { rewrite core_preserves_slots. apply core_R_slots_eq. exact Hnir. }
      assert (relations (core (core_R F)) = relations F) as Hr.
      { pose proof (core_core_R_simplified F Hnir Hwf) as [_ Hr].
        rewrite Hr. unfold admissible_relations.
        pose proof (core_idempotent_on_coherent F Hcoh) as Hrels.
        unfold core, admissible_relations in Hrels. simpl in Hrels.
        transitivity (filter (relation_admissible F) (relations F)).
        - apply filter_ext_in. intros r _. apply relation_admissible_ext.
        - exact Hrels. }
      rewrite (filter_valid_rules_id F Hnir).
      unfold admissible_relations, core_R. simpl. rewrite (filter_valid_rules_id F Hnir).
      rewrite relations_in_slots_id by exact Hwf.
      assert (forall r, relation_admissible (mkSlotSystem (slots F) (relations F) (type_of F) (rule_ref F)) r =
                        relation_admissible F r) as Hadm by (intro; apply relation_admissible_ext).
      rewrite (filter_ext _ _ Hadm).
      pose proof (core_idempotent_on_coherent F Hcoh) as Hrels.
      unfold core, admissible_relations in Hrels. simpl in Hrels.
      rewrite Hrels.
      assert (length (slots F) =? length (slots F) = true) as E1 by apply Nat.eqb_refl.
      assert (length (relations F) =? length (relations F) = true) as E2 by apply Nat.eqb_refl.
      rewrite E1, E2. simpl. destruct F. reflexivity.
  - unfold FS_coh, FS_coh_b in Hcoh.
    apply andb_prop in Hcoh. destruct Hcoh as [Hstruct _].
    unfold FS_struct, FS_struct_b in Hstruct.
    apply andb_prop in Hstruct. destruct Hstruct as [Hne _].
    apply negb_true_iff in Hne. apply Nat.eqb_neq in Hne.
    lia.
Qed.

Theorem core_star_idempotent : forall F,
  well_formed F ->
  rule_ref F = RuleSelfRef ->
  core_star (core_star F) = core_star F.
Proof.
  intros F Hwf Hself.
  pose proof (core_star_produces_coherent F Hwf Hself) as Hcoh.
  pose proof (core_star_preserves_endpoints F Hwf) as Hendpoints.
  pose proof (core_star_preserves_no_invalid_rules F Hwf) as Hnir.
  apply core_star_fixpoint; assumption.
Qed.
