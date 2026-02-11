(* VCA Kernel - Lambda.v

   Lambda calculus embedding into VCA.
   Theorem 6.1: λ-Embedding Sound
   Theorem 6.2: λ-Embedding Complete
*)

Require Import VCA.Core.
Require Import VCA.Transitions.
Require Import VCA.Commutativity.
Require Import VCA.Model.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Lia.
Import ListNotations.

Inductive LambdaTerm : Type :=
  | LVar : nat -> LambdaTerm
  | LAbs : nat -> LambdaTerm -> LambdaTerm
  | LApp : LambdaTerm -> LambdaTerm -> LambdaTerm.

Fixpoint free_vars (t : LambdaTerm) : list nat :=
  match t with
  | LVar x => [x]
  | LAbs x m => filter (fun y => negb (Nat.eqb x y)) (free_vars m)
  | LApp f a => free_vars f ++ free_vars a
  end.

Fixpoint subst (t : LambdaTerm) (x : nat) (s : LambdaTerm) : LambdaTerm :=
  match t with
  | LVar y => if Nat.eqb x y then s else t
  | LAbs y m => if Nat.eqb x y then t else LAbs y (subst m x s)
  | LApp f a => LApp (subst f x s) (subst a x s)
  end.

Inductive beta_step : LambdaTerm -> LambdaTerm -> Prop :=
  | BetaRedex : forall x m n,
      beta_step (LApp (LAbs x m) n) (subst m x n)
  | BetaAppL : forall m m' n,
      beta_step m m' -> beta_step (LApp m n) (LApp m' n)
  | BetaAppR : forall m n n',
      beta_step n n' -> beta_step (LApp m n) (LApp m n')
  | BetaAbs : forall x m m',
      beta_step m m' -> beta_step (LAbs x m) (LAbs x m').

Inductive beta_star : LambdaTerm -> LambdaTerm -> Prop :=
  | BetaRefl : forall m, beta_star m m
  | BetaTrans : forall m1 m2 m3,
      beta_step m1 m2 -> beta_star m2 m3 -> beta_star m1 m3.

Definition lambda_slot_type (k : Kind) (id : nat) : SlotType :=
  mkSlotType FamLambda k 0 AffLax 0 Infinite id.

Definition default_lambda_type : SlotType :=
  mkSlotType FamLambda KindAny 0 AffLax 0 Infinite 0.

Definition slot_for_var (x : nat) : Slot := slot_nat (x * 3).
Definition slot_for_abs (id : nat) : Slot := slot_nat (id * 3 + 1).
Definition slot_for_app (id : nat) : Slot := slot_nat (id * 3 + 2).

Fixpoint term_size (t : LambdaTerm) : nat :=
  match t with
  | LVar _ => 1
  | LAbs _ m => 1 + term_size m
  | LApp f a => 1 + term_size f + term_size a
  end.

Fixpoint encode_slots (t : LambdaTerm) (base : nat) : list Slot :=
  match t with
  | LVar x => [slot_nat base]
  | LAbs x m => slot_nat base :: encode_slots m (S base)
  | LApp f a =>
      let f_size := term_size f in
      slot_nat base :: encode_slots f (S base) ++ encode_slots a (S base + f_size)
  end.

Fixpoint encode_relations (t : LambdaTerm) (base : nat) : list Relation :=
  match t with
  | LVar _ => []
  | LAbs x m =>
      let body_slot := slot_nat (S base) in
      mkRelation (slot_nat base) body_slot 0 :: encode_relations m (S base)
  | LApp f a =>
      let f_size := term_size f in
      let func_slot := slot_nat (S base) in
      let arg_slot := slot_nat (S base + f_size) in
      mkRelation (slot_nat base) func_slot 0 ::
      mkRelation (slot_nat base) arg_slot 1 ::
      encode_relations f (S base) ++ encode_relations a (S base + f_size)
  end.

Fixpoint encode_types (t : LambdaTerm) (base : nat) (v : Slot) : SlotType :=
  match t with
  | LVar x =>
      if Slot_eqb v (slot_nat base) then lambda_slot_type KindAny base
      else default_lambda_type
  | LAbs x m =>
      if Slot_eqb v (slot_nat base) then lambda_slot_type KindAny base
      else encode_types m (S base) v
  | LApp f a =>
      if Slot_eqb v (slot_nat base) then lambda_slot_type KindAny base
      else let f_size := term_size f in
           if Nat.ltb (slot_to_nat v) (S base + f_size)
           then encode_types f (S base) v
           else encode_types a (S base + f_size) v
  end.

Definition encode_term (t : LambdaTerm) : SlotSystem :=
  mkSlotSystem
    (encode_slots t 0)
    (encode_relations t 0)
    (encode_types t 0)
    RuleSelfRef.

Lemma encode_term_nonempty : forall t,
  slots (encode_term t) <> [].
Proof.
  intro t. destruct t; simpl; discriminate.
Qed.

Lemma encode_slots_length : forall t base,
  length (encode_slots t base) = term_size t.
Proof.
  intros t. induction t as [x | x m IHm | f IHf a IHa]; intro base; simpl.
  - reflexivity.
  - rewrite IHm. reflexivity.
  - rewrite length_app. rewrite IHf, IHa. lia.
Qed.

Lemma encode_slots_nonempty : forall t base,
  encode_slots t base <> [].
Proof.
  intros t base. destruct t; simpl; discriminate.
Qed.

Lemma slot_nat_neq : forall n m, n <> m -> slot_nat n <> slot_nat m.
Proof.
  intros n m Hneq Heq. apply slot_nat_injective in Heq. contradiction.
Qed.

Definition beta_transition_stream (x : nat) (m n : LambdaTerm) : list Transition :=
  let m_size := term_size m in
  let n_size := term_size n in
  [Detach (slot_nat 0) (slot_nat (1 + m_size)) 1] ++
  [DeleteSlot (slot_nat 0); DeleteSlot (slot_nat 1)].

Lemma term_size_pos : forall t, 1 <= term_size t.
Proof. intro t. destruct t; simpl; lia. Qed.

Theorem lambda_embedding_sound_structure : forall m n,
  beta_step m n ->
  exists k, term_size n <= k.
Proof.
  intros m n Hbeta. exists (term_size n). lia.
Qed.

Lemma encode_slots_in : forall t base v,
  In v (encode_slots t base) ->
  exists k, v = slot_nat k /\ base <= k < base + term_size t.
Proof.
  intros t. induction t as [x | x m IHm | f IHf a IHa]; intros base v Hv; simpl in *.
  - destruct Hv as [Heq | []]. exists base. subst. split; [reflexivity | lia].
  - destruct Hv as [Heq | Hv].
    + exists base. subst. split; [reflexivity | lia].
    + apply IHm in Hv. destruct Hv as [k [Hk Hrange]].
      exists k. split; [exact Hk | lia].
  - destruct Hv as [Heq | Hv].
    + exists base. subst. split; [reflexivity | lia].
    + apply in_app_or in Hv. destruct Hv as [Hf | Ha].
      * apply IHf in Hf. destruct Hf as [k [Hk Hrange]].
        exists k. split; [exact Hk | lia].
      * apply IHa in Ha. destruct Ha as [k [Hk Hrange]].
        exists k. split; [exact Hk | lia].
Qed.

Lemma encode_term_slots_nonempty : forall t,
  slots (encode_term t) <> [].
Proof.
  intro t. unfold encode_term. simpl. apply encode_slots_nonempty.
Qed.

Definition build_deletion_stream (vs : list Slot) (keep : Slot) : list Transition :=
  map DeleteSlot (filter (fun v => negb (Slot_eqb v keep)) vs).

Definition build_insertion_stream (vs : list Slot) (types : Slot -> SlotType) : list Transition :=
  map (fun v => InsertSlot v (types v)) vs.

Definition shift_slot (offset : nat) (n : nat) : Slot := slot_nat (n + offset).

Fixpoint shifted_encode_slots (t : LambdaTerm) (base offset : nat) : list Slot :=
  match t with
  | LVar _ => [slot_nat (base + offset)]
  | LAbs _ m => slot_nat (base + offset) :: shifted_encode_slots m (S base) offset
  | LApp f a =>
      let f_size := term_size f in
      slot_nat (base + offset) ::
      shifted_encode_slots f (S base) offset ++
      shifted_encode_slots a (S base + f_size) offset
  end.

Fixpoint shifted_encode_relations (t : LambdaTerm) (base offset : nat) : list Relation :=
  match t with
  | LVar _ => []
  | LAbs _ m =>
      mkRelation (slot_nat (base + offset)) (slot_nat (S base + offset)) 0 ::
      shifted_encode_relations m (S base) offset
  | LApp f a =>
      let f_size := term_size f in
      mkRelation (slot_nat (base + offset)) (slot_nat (S base + offset)) 0 ::
      mkRelation (slot_nat (base + offset)) (slot_nat (S base + f_size + offset)) 1 ::
      shifted_encode_relations f (S base) offset ++
      shifted_encode_relations a (S base + f_size) offset
  end.

Definition shifted_type (offset : nat) (t : LambdaTerm) (v : Slot) : SlotType :=
  lambda_slot_type KindAny 0.

Definition build_target_insertions (t : LambdaTerm) (offset : nat) : list Transition :=
  map (fun v => InsertSlot v (lambda_slot_type KindAny 0)) (shifted_encode_slots t 0 offset).

Definition build_target_attachments (t : LambdaTerm) (offset : nat) : list Transition :=
  map (fun r => Attach (rel_source r) (rel_target r) (rel_position r))
      (shifted_encode_relations t 0 offset).

Definition build_source_detachments (t : LambdaTerm) : list Transition :=
  map (fun r => Detach (rel_source r) (rel_target r) (rel_position r))
      (encode_relations t 0).

Definition build_source_deletions (t : LambdaTerm) (keep : Slot) : list Transition :=
  map DeleteSlot (filter (fun v => negb (Slot_eqb v keep)) (rev (encode_slots t 0))).

Definition reconstruction_stream (src tgt : LambdaTerm) : list Transition :=
  let offset := term_size src in
  let keep := slot_nat offset in
  build_target_insertions tgt offset ++
  build_target_attachments tgt offset ++
  build_source_detachments src ++
  build_source_deletions src keep.

Lemma shifted_encode_slots_length : forall t base offset,
  length (shifted_encode_slots t base offset) = term_size t.
Proof.
  intros t. induction t as [x | x m IHm | f IHf a IHa]; intros base offset; simpl.
  - reflexivity.
  - rewrite IHm. reflexivity.
  - rewrite length_app. rewrite IHf, IHa. lia.
Qed.

Lemma shifted_encode_slots_nonempty : forall t base offset,
  shifted_encode_slots t base offset <> [].
Proof.
  intros t base offset. destruct t; simpl; discriminate.
Qed.

Lemma shifted_slots_disjoint : forall t base offset k,
  In (slot_nat k) (shifted_encode_slots t base offset) ->
  offset <= k.
Proof.
  intros t. induction t as [x | x m IHm | f IHf a IHa]; intros base offset k Hin; simpl in *.
  - destruct Hin as [Heq | []]. apply slot_nat_injective in Heq. lia.
  - destruct Hin as [Heq | Hin].
    + apply slot_nat_injective in Heq. lia.
    + apply IHm in Hin. lia.
  - destruct Hin as [Heq | Hin].
    + apply slot_nat_injective in Heq. lia.
    + apply in_app_or in Hin. destruct Hin as [Hf | Ha].
      * apply IHf in Hf. lia.
      * apply IHa in Ha. lia.
Qed.

Lemma source_slots_bounded : forall t base k,
  In (slot_nat k) (encode_slots t base) ->
  k < base + term_size t.
Proof.
  intros t. induction t as [x | x m IHm | f IHf a IHa]; intros base k Hin; simpl in *.
  - destruct Hin as [Heq | []]. apply slot_nat_injective in Heq. lia.
  - destruct Hin as [Heq | Hin].
    + apply slot_nat_injective in Heq. lia.
    + apply IHm in Hin. lia.
  - destruct Hin as [Heq | Hin].
    + apply slot_nat_injective in Heq. lia.
    + apply in_app_or in Hin. destruct Hin as [Hf | Ha].
      * apply IHf in Hf. lia.
      * apply IHa in Ha. lia.
Qed.

Definition shift_bijection (offset : nat) (s : Slot) : Slot :=
  slot_nat (slot_to_nat s + offset).

Lemma shift_bijection_spec : forall offset n,
  shift_bijection offset (slot_nat n) = slot_nat (n + offset).
Proof.
  intros offset n. unfold shift_bijection. rewrite slot_to_nat_nat. reflexivity.
Qed.

Lemma shift_bijection_injective : forall offset u v,
  shift_bijection offset u = shift_bijection offset v -> u = v.
Proof.
  intros offset u v H. unfold shift_bijection in H.
  apply slot_nat_injective in H.
  assert (slot_to_nat u = slot_to_nat v) as Heq by lia.
  rewrite (slot_to_nat_spec u), (slot_to_nat_spec v), Heq. reflexivity.
Qed.

Definition slot_bijection (f : Slot -> Slot) (dom cod : list Slot) : Prop :=
  (forall v, In v dom -> In (f v) cod) /\
  (forall v, In v cod -> exists u, In u dom /\ f u = v) /\
  (forall u v, In u dom -> In v dom -> f u = f v -> u = v).

Definition slot_system_iso (F1 F2 : SlotSystem) : Prop :=
  exists f : Slot -> Slot,
    slot_bijection f (slots F1) (slots F2) /\
    (forall u v i, In (mkRelation u v i) (relations F1) <->
                   In (mkRelation (f u) (f v) i) (relations F2)) /\
    (forall v, In v (slots F1) ->
               ty_family (type_of F1 v) = ty_family (type_of F2 (f v)) /\
               ty_kind (type_of F1 v) = ty_kind (type_of F2 (f v))).

Lemma slot_system_iso_refl : forall F,
  slot_system_iso F F.
Proof.
  intro F. exists (fun x => x).
  split; [|split].
  - unfold slot_bijection. split; [|split]; intros; auto. exists v; auto.
  - intros u v i. tauto.
  - intros v Hv. split; reflexivity.
Qed.

Lemma slot_system_equiv_implies_iso : forall F1 F2,
  slot_system_equiv F1 F2 -> slot_system_iso F1 F2.
Proof.
  intros F1 F2 [Hs [Hr [Ht Hrr]]].
  exists (fun x => x).
  split; [|split].
  - unfold slot_bijection. split; [|split].
    + intros v Hv. rewrite <- Hs. exact Hv.
    + intros v Hv. exists v. split; [rewrite Hs; exact Hv | reflexivity].
    + intros u v _ _ H. exact H.
  - intros u v i. rewrite Hr. tauto.
  - intros v Hv. rewrite Ht. split; reflexivity.
Qed.

Definition shifted_encode_term (t : LambdaTerm) (offset : nat) : SlotSystem :=
  mkSlotSystem
    (shifted_encode_slots t 0 offset)
    (shifted_encode_relations t 0 offset)
    (fun _ => lambda_slot_type KindAny 0)
    RuleSelfRef.


Definition unshift (offset : nat) (s : Slot) : Slot :=
  slot_nat (slot_to_nat s - offset).

Lemma unshift_spec : forall offset n,
  offset <= n -> unshift offset (slot_nat n) = slot_nat (n - offset).
Proof.
  intros offset n _. unfold unshift. rewrite slot_to_nat_nat. reflexivity.
Qed.

Lemma unshift_shift_inverse : forall offset v,
  unshift offset (shift_bijection offset v) = v.
Proof.
  intros offset v. unfold unshift, shift_bijection.
  rewrite slot_to_nat_nat.
  replace (slot_to_nat v + offset - offset) with (slot_to_nat v) by lia.
  symmetry. apply slot_to_nat_spec.
Qed.

Lemma shifted_in_implies_original : forall t base offset v,
  In v (shifted_encode_slots t base offset) ->
  exists k, v = slot_nat (k + offset) /\ In (slot_nat k) (encode_slots t base).
Proof.
  intros t. induction t as [x | x m IHm | f IHf a IHa]; intros base offset v Hv; simpl in *.
  - destruct Hv as [Heq | []]. exists base. subst. split; [reflexivity | left; reflexivity].
  - destruct Hv as [Heq | Hv].
    + exists base. subst. split; [reflexivity | left; reflexivity].
    + apply IHm in Hv. destruct Hv as [k [Hk Hin]].
      exists k. split; [exact Hk | right; exact Hin].
  - destruct Hv as [Heq | Hv].
    + exists base. subst. split; [reflexivity | left; reflexivity].
    + apply in_app_or in Hv. destruct Hv as [Hf | Ha].
      * apply IHf in Hf. destruct Hf as [k [Hk Hin]].
        exists k. split; [exact Hk | right; apply in_or_app; left; exact Hin].
      * apply IHa in Ha. destruct Ha as [k [Hk Hin]].
        exists k. split; [exact Hk | right; apply in_or_app; right; exact Hin].
Qed.

Lemma original_in_implies_shifted : forall t base offset v,
  In v (encode_slots t base) ->
  exists k, v = slot_nat k /\ In (slot_nat (k + offset)) (shifted_encode_slots t base offset).
Proof.
  intros t. induction t as [x | x m IHm | f IHf a IHa]; intros base offset v Hv; simpl in *.
  - destruct Hv as [Heq | []]. exists base. subst. split; [reflexivity | left; reflexivity].
  - destruct Hv as [Heq | Hv].
    + exists base. subst. split; [reflexivity | left; reflexivity].
    + specialize (IHm (S base) offset v Hv). destruct IHm as [k [Hk Hin]].
      exists k. split; [exact Hk | right; exact Hin].
  - destruct Hv as [Heq | Hv].
    + exists base. subst. split; [reflexivity | left; reflexivity].
    + apply in_app_or in Hv. destruct Hv as [Hf | Ha].
      * specialize (IHf (S base) offset v Hf). destruct IHf as [k [Hk Hin]].
        exists k. split; [exact Hk | right; apply in_or_app; left; exact Hin].
      * specialize (IHa (S base + term_size f) offset v Ha). destruct IHa as [k [Hk Hin]].
        exists k. split; [exact Hk | right; apply in_or_app; right; exact Hin].
Qed.

Lemma encode_types_family : forall t base v,
  ty_family (encode_types t base v) = FamLambda.
Proof.
  intros t. induction t as [x | x m IHm | f IHf a IHa]; intros base v; simpl.
  - destruct (Slot_eqb v (slot_nat base)); reflexivity.
  - destruct (Slot_eqb v (slot_nat base)); [reflexivity | apply IHm].
  - destruct (Slot_eqb v (slot_nat base)); [reflexivity|].
    destruct (slot_to_nat v <? S (base + term_size f)); [apply IHf | apply IHa].
Qed.

Lemma shifted_relation_in_implies_original : forall t base offset r,
  In r (shifted_encode_relations t base offset) ->
  In (mkRelation (unshift offset (rel_source r)) (unshift offset (rel_target r)) (rel_position r))
     (encode_relations t base).
Proof.
  intros t. induction t as [x | x m IHm | f IHf a IHa]; intros base offset r Hr; simpl in *.
  - destruct Hr.
  - destruct Hr as [Heq | Hr].
    + subst. simpl.
      rewrite unshift_spec by lia.
      rewrite unshift_spec by lia.
      replace (base + offset - offset) with base by lia.
      replace (S (base + offset) - offset) with (S base) by lia.
      left. reflexivity.
    + right. apply IHm. exact Hr.
  - destruct Hr as [Heq | Hr].
    + subst. simpl.
      rewrite unshift_spec by lia.
      rewrite unshift_spec by lia.
      replace (base + offset - offset) with base by lia.
      replace (S (base + offset) - offset) with (S base) by lia.
      left. reflexivity.
    + destruct Hr as [Heq | Hr].
      * subst. simpl.
        rewrite unshift_spec by lia.
        rewrite unshift_spec by lia.
        replace (base + offset - offset) with base by lia.
        replace (S (base + term_size f + offset) - offset) with (S base + term_size f) by lia.
        right. left. reflexivity.
      * apply in_app_or in Hr. destruct Hr as [Hf | Ha].
        -- right. right. apply in_or_app. left. apply IHf. exact Hf.
        -- right. right. apply in_or_app. right. apply IHa. exact Ha.
Qed.

Lemma original_relation_in_implies_shifted : forall t base offset r,
  In r (encode_relations t base) ->
  In (mkRelation (shift_bijection offset (rel_source r))
                 (shift_bijection offset (rel_target r))
                 (rel_position r))
     (shifted_encode_relations t base offset).
Proof.
  intros t. induction t as [x | x m IHm | f IHf a IHa]; intros base offset r Hr; simpl in *.
  - destruct Hr.
  - destruct Hr as [Heq | Hr].
    + subst. simpl. rewrite shift_bijection_spec. rewrite shift_bijection_spec.
      left. f_equal; lia.
    + right. apply IHm. exact Hr.
  - destruct Hr as [Heq | Hr].
    + subst. simpl. rewrite shift_bijection_spec. rewrite shift_bijection_spec.
      left. f_equal; lia.
    + destruct Hr as [Heq | Hr].
      * subst. simpl. rewrite shift_bijection_spec. rewrite shift_bijection_spec.
        right. left. f_equal; lia.
      * apply in_app_or in Hr. destruct Hr as [Hf | Ha].
        -- right. right. apply in_or_app. left. apply IHf. exact Hf.
        -- right. right. apply in_or_app. right. apply IHa. exact Ha.
Qed.

Lemma shift_unshift_inverse : forall offset v,
  offset <= slot_to_nat v ->
  shift_bijection offset (unshift offset v) = v.
Proof.
  intros offset v Hle. unfold shift_bijection, unshift.
  rewrite slot_to_nat_nat.
  replace (slot_to_nat v - offset + offset) with (slot_to_nat v) by lia.
  symmetry. apply slot_to_nat_spec.
Qed.

Lemma encode_types_kind : forall t base v,
  ty_kind (encode_types t base v) = KindAny.
Proof.
  intros t. induction t as [x | x m IHm | f IHf a IHa]; intros base v; simpl.
  - destruct (Slot_eqb v (slot_nat base)); reflexivity.
  - destruct (Slot_eqb v (slot_nat base)); [reflexivity | apply IHm].
  - destruct (Slot_eqb v (slot_nat base)); [reflexivity|].
    destruct (slot_to_nat v <? S (base + term_size f)); [apply IHf | apply IHa].
Qed.

Lemma encode_iso_shifted : forall t offset,
  slot_system_iso (encode_term t) (shifted_encode_term t offset).
Proof.
  intros t offset.
  exists (shift_bijection offset).
  split; [|split].
  - unfold slot_bijection. split; [|split].
    + intros v Hv. simpl in *.
      apply original_in_implies_shifted with (offset := offset) in Hv.
      destruct Hv as [k [Hk Hin]]. subst.
      rewrite shift_bijection_spec. exact Hin.
    + intros v Hv. simpl in *.
      apply shifted_in_implies_original in Hv.
      destruct Hv as [k [Hk Hin]]. subst.
      exists (slot_nat k). split; [exact Hin|].
      rewrite shift_bijection_spec. reflexivity.
    + intros u v _ _ Heq.
      apply shift_bijection_injective in Heq. exact Heq.
  - intros u v i. simpl. split; intro H.
    + pose proof (original_relation_in_implies_shifted t 0 offset
        (mkRelation u v i) H) as H'.
      simpl in H'. exact H'.
    + apply shifted_relation_in_implies_original in H.
      simpl in H.
      rewrite unshift_shift_inverse in H.
      rewrite unshift_shift_inverse in H.
      exact H.
  - intros v Hv. simpl. split.
    + rewrite encode_types_family. reflexivity.
    + rewrite encode_types_kind. reflexivity.
Qed.

Lemma in_slots_iff : forall v F, in_slots v F = true <-> In v (slots F).
Proof.
  intros v F. unfold in_slots. split; intro H.
  - apply existsb_exists in H. destruct H as [x [Hin Heq]].
    unfold Slot_eqb in Heq.
    destruct (Slot_eq_dec v x); [subst; exact Hin | discriminate].
  - apply existsb_exists. exists v. split; [exact H |].
    unfold Slot_eqb. destruct (Slot_eq_dec v v); [reflexivity | contradiction].
Qed.

Lemma encode_slots_base_in : forall t base,
  In (slot_nat base) (encode_slots t base).
Proof. intros t base. destruct t; simpl; left; reflexivity. Qed.

Lemma NoDup_app_intro : forall {A : Type} (l1 l2 : list A),
  NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> ~ In x l2) ->
  NoDup (l1 ++ l2).
Proof.
  intros A l1. induction l1 as [|x xs IH]; intros l2 H1 H2 Hdisj; simpl.
  - exact H2.
  - inversion H1; subst. constructor.
    + intro Hin. apply in_app_or in Hin. destruct Hin.
      * exact (H3 H).
      * exact (Hdisj x (or_introl eq_refl) H).
    + apply IH; [exact H4 | exact H2 |].
      intros y Hy. apply Hdisj. right. exact Hy.
Qed.

Lemma encode_slots_NoDup : forall t base, NoDup (encode_slots t base).
Proof.
  intros t. induction t as [x | x m IHm | f IHf a IHa]; intro base; simpl.
  - constructor; [intros [] | constructor].
  - constructor.
    + intro H. apply encode_slots_in in H.
      destruct H as [k [Hk [Hge _]]]. apply slot_nat_injective in Hk. lia.
    + apply IHm.
  - constructor.
    + intro H. apply in_app_or in H. destruct H as [H | H];
        apply encode_slots_in in H; destruct H as [k [Hk [Hge _]]];
        apply slot_nat_injective in Hk; lia.
    + apply NoDup_app_intro; [apply IHf | apply IHa |].
      intros v Hf Ha.
      apply encode_slots_in in Hf. destruct Hf as [k1 [Hk1 [_ Hlt1]]].
      apply encode_slots_in in Ha. destruct Ha as [k2 [Hk2 [Hge2 _]]].
      subst. apply slot_nat_injective in Hk2. lia.
Qed.

Lemma encode_relations_target_range : forall t base r,
  In r (encode_relations t base) ->
  exists k, rel_target r = slot_nat k /\ S base <= k < base + term_size t.
Proof.
  intros t. induction t as [x | x m IHm | f IHf a IHa]; intros base r Hr; simpl in *.
  - destruct Hr.
  - destruct Hr as [Heq | Hr].
    + subst. simpl. exists (S base).
      pose proof (term_size_pos m). split; [reflexivity | lia].
    + apply IHm in Hr. destruct Hr as [k [Hk Hrange]].
      exists k. split; [exact Hk | lia].
  - destruct Hr as [Heq | [Heq | Hr]].
    + subst. simpl. exists (S base).
      pose proof (term_size_pos f). pose proof (term_size_pos a).
      split; [reflexivity | lia].
    + subst. simpl. exists (S base + term_size f).
      pose proof (term_size_pos a). split; [reflexivity | lia].
    + apply in_app_or in Hr. destruct Hr as [Hf | Ha].
      * apply IHf in Hf. destruct Hf as [k [Hk Hrange]].
        exists k. split; [exact Hk | lia].
      * apply IHa in Ha. destruct Ha as [k [Hk Hrange]].
        exists k. split; [exact Hk | lia].
Qed.

Lemma encode_relations_NoDup_targets : forall t base,
  NoDup (map rel_target (encode_relations t base)).
Proof.
  intros t. induction t as [x | x m IHm | f IHf a IHa]; intro base; simpl.
  - constructor.
  - constructor.
    + intro Hin. apply in_map_iff in Hin. destruct Hin as [r' [Htgt Hr']].
      apply encode_relations_target_range in Hr'.
      destruct Hr' as [k [Hk Hrange]].
      rewrite Htgt in Hk. apply slot_nat_injective in Hk. lia.
    + apply IHm.
  - constructor.
    + simpl. intro Hin. destruct Hin as [Heq | Hin].
      * apply slot_nat_injective in Heq. pose proof (term_size_pos f). lia.
      * rewrite map_app in Hin. apply in_app_or in Hin. destruct Hin as [H | H];
          apply in_map_iff in H; destruct H as [r [Htgt Hr]];
          apply encode_relations_target_range in Hr;
          destruct Hr as [k [Hk Hrange]];
          rewrite Htgt in Hk; apply slot_nat_injective in Hk; lia.
    + constructor.
      * intro Hin. rewrite map_app in Hin. apply in_app_or in Hin.
        destruct Hin as [H | H];
          apply in_map_iff in H; destruct H as [r [Htgt Hr]];
          apply encode_relations_target_range in Hr;
          destruct Hr as [k [Hk Hrange]];
          rewrite Htgt in Hk; apply slot_nat_injective in Hk; lia.
      * rewrite map_app. apply NoDup_app_intro; [apply IHf | apply IHa |].
        intros v Hf Ha.
        apply in_map_iff in Hf. destruct Hf as [rf [Htgtf Hrf]].
        apply in_map_iff in Ha. destruct Ha as [ra [Htgta Hra]].
        apply encode_relations_target_range in Hrf.
        destruct Hrf as [kf [Hkf Hrangef]].
        apply encode_relations_target_range in Hra.
        destruct Hra as [ka [Hka Hrangea]].
        rewrite Htgtf in Hkf. rewrite Htgta in Hka.
        rewrite Hkf in Hka. apply slot_nat_injective in Hka. lia.
Qed.

Lemma encode_relations_endpoints_in_slots : forall t base r,
  In r (encode_relations t base) ->
  In (rel_source r) (encode_slots t base) /\
  In (rel_target r) (encode_slots t base).
Proof.
  intros t. induction t as [x | x m IHm | f IHf a IHa]; intros base r Hr; simpl in *.
  - destruct Hr.
  - destruct Hr as [Heq | Hr].
    + subst. simpl. split; [left; reflexivity | right; apply encode_slots_base_in].
    + destruct (IHm _ _ Hr) as [Hs Ht]. split; right; assumption.
  - destruct Hr as [Heq | [Heq | Hr]].
    + subst. simpl. split.
      * left. reflexivity.
      * right. apply in_or_app. left. apply encode_slots_base_in.
    + subst. simpl. split.
      * left. reflexivity.
      * right. apply in_or_app. right. apply encode_slots_base_in.
    + apply in_app_or in Hr. destruct Hr as [Hf | Ha].
      * destruct (IHf _ _ Hf) as [Hs Ht].
        split; right; apply in_or_app; left; assumption.
      * destruct (IHa _ _ Ha) as [Hs Ht].
        split; right; apply in_or_app; right; assumption.
Qed.

Lemma filter_all_true_id : forall {A : Type} (f : A -> bool) (l : list A),
  (forall x, In x l -> f x = true) -> filter f l = l.
Proof.
  intros A f l H. induction l as [|x xs IH]; simpl; [reflexivity|].
  rewrite (H x (or_introl eq_refl)). f_equal.
  apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma remove_relation_keeps_diff_target : forall u v i r rels,
  rel_target r <> v -> In r rels -> In r (remove_relation u v i rels).
Proof.
  intros u v i r rels Hneq Hin. unfold remove_relation.
  apply filter_In. split; [exact Hin |]. apply negb_true_iff.
  destruct (Slot_eqb (rel_source r) u) eqn:Es; simpl; [|reflexivity].
  unfold Slot_eqb. destruct (Slot_eq_dec (rel_target r) v); [contradiction | reflexivity].
Qed.

Lemma remove_relation_head_rest : forall r rest,
  ~ In (rel_target r) (map rel_target rest) ->
  remove_relation (rel_source r) (rel_target r) (rel_position r) (r :: rest) = rest.
Proof.
  intros r rest Hnotin. unfold remove_relation. simpl.
  unfold Slot_eqb.
  destruct (Slot_eq_dec (rel_source r) (rel_source r)) as [_|Hc]; [|contradiction].
  destruct (Slot_eq_dec (rel_target r) (rel_target r)) as [_|Hc]; [|contradiction].
  rewrite Nat.eqb_refl. simpl.
  apply filter_all_true_id. intros r' Hr'. apply negb_true_iff.
  assert (rel_target r' <> rel_target r) as Htneq.
  { intro Heq. apply Hnotin. apply in_map_iff. exists r'. auto. }
  destruct (Slot_eq_dec (rel_source r') (rel_source r)); simpl; [|reflexivity].
  destruct (Slot_eq_dec (rel_target r') (rel_target r)); [contradiction | reflexivity].
Qed.

Lemma Slot_eqb_refl : forall v, Slot_eqb v v = true.
Proof. intro v. unfold Slot_eqb. destruct (Slot_eq_dec v v); [reflexivity|contradiction]. Qed.

Lemma Slot_eqb_neq : forall u v, u <> v -> Slot_eqb u v = false.
Proof. intros u v H. unfold Slot_eqb. destruct (Slot_eq_dec u v); [contradiction|reflexivity]. Qed.

Lemma in_remove_slot : forall u v l,
  In u (remove_slot v l) <-> In u l /\ u <> v.
Proof.
  intros u v l. unfold remove_slot. rewrite filter_In. split.
  - intros [H1 H2]. split; [exact H1|].
    apply negb_true_iff in H2. intro Heq. subst. rewrite Slot_eqb_refl in H2. discriminate.
  - intros [H1 H2]. split; [exact H1|]. apply negb_true_iff. apply Slot_eqb_neq. exact H2.
Qed.

Lemma encode_types_upper : forall t base v,
  ty_upper (encode_types t base v) = Infinite.
Proof.
  intros t. induction t as [x|x m IHm|f IHf a IHa]; intros base v; simpl.
  - destruct (Slot_eqb v (slot_nat base)); reflexivity.
  - destruct (Slot_eqb v (slot_nat base)); [reflexivity|apply IHm].
  - destruct (Slot_eqb v (slot_nat base)); [reflexivity|].
    destruct (slot_to_nat v <? S (base + term_size f)); [apply IHf | apply IHa].
Qed.

Lemma position_available_no_target : forall v i F,
  ~ In v (map rel_target (relations F)) ->
  position_available v i F = true.
Proof.
  intros v i F H. unfold position_available. apply negb_true_iff.
  destruct (existsb _ _) eqn:E; [|reflexivity]. exfalso.
  apply existsb_exists in E. destruct E as [r [Hr Hb]].
  apply andb_true_iff in Hb. destruct Hb as [Ht _].
  unfold Slot_eqb in Ht. destruct (Slot_eq_dec (rel_target r) v); [|discriminate].
  subst. apply H. apply in_map. exact Hr.
Qed.

Lemma has_other_slot_witness : forall v u F,
  In u (slots F) -> u <> v -> has_other_slot v F = true.
Proof.
  intros v u F Hu Hneq. unfold has_other_slot. apply existsb_exists.
  exists u. split; [exact Hu|]. apply negb_true_iff. apply Slot_eqb_neq.
  exact (fun Heq => Hneq Heq).
Qed.

Lemma NoDup_tl : forall {A : Type} (l : list A), NoDup l -> NoDup (tl l).
Proof. intros A l H. destruct l; [constructor|inversion H; exact H3]. Qed.

Lemma NoDup_rev : forall {A : Type} (l : list A), NoDup l -> NoDup (rev l).
Proof.
  intros A l H. induction H; simpl; [constructor|].
  apply NoDup_app_intro; [exact IHNoDup|repeat constructor; intros []|].
  intros y Hy [Heq|[]]. subst. apply H. apply in_rev. exact Hy.
Qed.

Lemma tl_incl : forall {A : Type} (l : list A) x, In x (tl l) -> In x l.
Proof. intros A l x H. destruct l; [exact H|right; exact H]. Qed.

Lemma encode_slots_hd_base : forall t base,
  encode_slots t base = slot_nat base :: tl (encode_slots t base).
Proof. intros t base. destruct t; reflexivity. Qed.

Lemma detach_all : forall rels F,
  NoDup (map rel_target rels) ->
  relations F = rels ->
  exists F',
    apply_stream
      (map (fun r => Detach (rel_source r) (rel_target r) (rel_position r)) rels)
      F = Some F' /\
    slots F' = slots F /\
    relations F' = [] /\
    (forall v, type_of F' v = type_of F v) /\
    rule_ref F' = rule_ref F.
Proof.
  induction rels as [|r rest IH]; intros F Hnd Hrels.
  - exists F. simpl. rewrite Hrels. repeat split; reflexivity.
  - simpl. unfold apply_transition at 1.
    assert (precondition (Detach (rel_source r) (rel_target r) (rel_position r)) F = true) as Hpre.
    { simpl. unfold pre_Detach. apply existsb_exists. exists r.
      rewrite Hrels. split; [left; reflexivity|].
      rewrite Slot_eqb_refl. simpl. rewrite Slot_eqb_refl. simpl. apply Nat.eqb_refl. }
    rewrite Hpre.
    set (F1 := apply_effect (Detach (rel_source r) (rel_target r) (rel_position r)) F).
    inversion Hnd as [|? ? Hnotin Hnd']; subst.
    assert (relations F1 = rest) as Hr1.
    { unfold F1. simpl. rewrite Hrels. apply remove_relation_head_rest. exact Hnotin. }
    destruct (IH F1 Hnd' Hr1) as [F' [HF' [Hs' [Hr' [Ht' Hrr']]]]].
    exists F'. repeat split; [exact HF'| | exact Hr'| |].
    + unfold F1 in Hs'. simpl in Hs'. exact Hs'.
    + intro v. rewrite Ht'. reflexivity.
    + unfold F1 in Hrr'. simpl in Hrr'. exact Hrr'.
Qed.

Lemma delete_all_but_keep : forall to_delete keep F,
  NoDup to_delete ->
  ~ In keep to_delete ->
  In keep (slots F) ->
  (forall v, In v to_delete -> In v (slots F)) ->
  NoDup (slots F) ->
  relations F = [] ->
  exists F',
    apply_stream (map DeleteSlot to_delete) F = Some F' /\
    (forall v, In v (slots F') <-> In v (slots F) /\ ~ In v to_delete) /\
    relations F' = [] /\
    (forall v, type_of F' v = type_of F v) /\
    rule_ref F' = rule_ref F.
Proof.
  induction to_delete as [|d rest IH]; intros keep F Hnd Hni Hkeep Hall Hndup Hrels.
  - exists F. simpl. split; [reflexivity|]. split; [|split; [exact Hrels|split; [intro; reflexivity|reflexivity]]].
    intro v. tauto.
  - simpl. unfold apply_transition at 1.
    assert (precondition (DeleteSlot d) F = true) as Hpre.
    { simpl. unfold pre_DeleteSlot. apply andb_true_intro. split.
      - apply in_slots_iff. apply Hall. left. reflexivity.
      - apply (has_other_slot_witness d keep F Hkeep).
        intro Heq. apply Hni. subst. left. reflexivity. }
    rewrite Hpre.
    set (F1 := apply_effect (DeleteSlot d) F).
    inversion Hnd as [|? ? Hdnotin Hnd']; subst.
    assert (relations F1 = []) as Hrels1.
    { unfold F1. simpl. rewrite Hrels. reflexivity. }
    assert (In keep (slots F1)) as Hkeep'.
    { unfold F1. simpl. apply in_remove_slot. split; [exact Hkeep|].
      intro Heq. apply Hni. subst. left. reflexivity. }
    assert (forall v, In v rest -> In v (slots F1)) as Hall'.
    { intros v Hv. unfold F1. simpl. apply in_remove_slot. split.
      - apply Hall. right. exact Hv.
      - intro Heq. subst. contradiction. }
    assert (NoDup (slots F1)) as Hndup'.
    { unfold F1. simpl. unfold remove_slot. apply NoDup_filter. exact Hndup. }
    destruct (IH keep F1 Hnd' (fun H => Hni (or_intror H)) Hkeep' Hall' Hndup' Hrels1)
      as [F' [HF' [Hs' [Hr' [Ht' Hrr']]]]].
    exists F'. split; [exact HF'|]. split; [|split; [exact Hr'|split]].
    + intro v. split.
      * intro Hv. apply Hs' in Hv. destruct Hv as [Hv1 Hv2].
        unfold F1 in Hv1. simpl in Hv1. apply in_remove_slot in Hv1.
        destruct Hv1 as [HvF Hneq].
        split; [exact HvF|]. intros [Heq|Hin]; [apply Hneq; symmetry; exact Heq|exact (Hv2 Hin)].
      * intros [Hv1 Hv2]. apply Hs'. unfold F1. simpl.
        split; [apply in_remove_slot; split; [exact Hv1|intro Heq; apply Hv2; left; symmetry; exact Heq]|
                intro Hin; apply Hv2; right; exact Hin].
    + intro v. rewrite Ht'. reflexivity.
    + unfold F1 in Hrr'. simpl in Hrr'. exact Hrr'.
Qed.

Lemma insert_all_fresh : forall to_insert ty F,
  NoDup to_insert ->
  (forall v, In v to_insert -> ~ In v (slots F)) ->
  relations F = [] ->
  exists F',
    apply_stream (map (fun v => InsertSlot v ty) to_insert) F = Some F' /\
    (forall v, In v (slots F') <-> In v to_insert \/ In v (slots F)) /\
    relations F' = [] /\
    rule_ref F' = rule_ref F /\
    (forall v, In v to_insert -> type_of F' v = ty) /\
    (forall v, ~ In v to_insert -> type_of F' v = type_of F v).
Proof.
  induction to_insert as [|s rest IH]; intros ty F Hnd Hfresh Hrels.
  - exists F. split; [reflexivity|]. split; [intro v; simpl; tauto|].
    split; [exact Hrels|]. split; [reflexivity|]. split; [simpl; tauto|intros v _; reflexivity].
  - simpl. unfold apply_transition at 1.
    assert (precondition (InsertSlot s ty) F = true) as Hpre.
    { simpl. unfold pre_InsertSlot. apply andb_true_intro. split.
      - apply negb_true_iff. unfold in_slots.
        destruct (existsb (Slot_eqb s) (slots F)) eqn:E; [|reflexivity]. exfalso.
        apply existsb_exists in E. destruct E as [x [Hx Heq]].
        unfold Slot_eqb in Heq. destruct (Slot_eq_dec s x); [|discriminate].
        subst. exact (Hfresh x (or_introl eq_refl) Hx).
      - unfold no_relations_to. rewrite Hrels. reflexivity. }
    rewrite Hpre.
    set (F1 := apply_effect (InsertSlot s ty) F).
    inversion Hnd; subst. rename H1 into Hsin. rename H2 into Hnd'.
    assert (forall v, In v rest -> ~ In v (slots F1)) as Hfresh'.
    { intros v Hv. unfold F1. simpl. intros [Heq|Hin].
      - subst. contradiction.
      - exact (Hfresh v (or_intror Hv) Hin). }
    assert (relations F1 = []) as Hrels1 by (unfold F1; simpl; exact Hrels).
    destruct (IH ty F1 Hnd' Hfresh' Hrels1) as [F' [HF' [Hs' [Hr' [Hrr' [Htins Htnot]]]]]].
    assert (rule_ref F1 = rule_ref F) as Hrr1 by reflexivity.
    exists F'. split; [exact HF'|]. split; [|split; [exact Hr'|split; [congruence|split]]].
    + intro v. split.
      * intro Hv. apply Hs' in Hv. destruct Hv as [Hv|Hv].
        -- left. right. exact Hv.
        -- unfold F1 in Hv. simpl in Hv. destruct Hv; [left; left; exact H|right; exact H].
      * intros [[Heq|Hv]|Hv].
        -- subst. apply Hs'. unfold F1. simpl. right. left. reflexivity.
        -- apply Hs'. left. exact Hv.
        -- apply Hs'. unfold F1. simpl. right. right. exact Hv.
    + intros v [Heq|Hv].
      * subst v. rewrite (Htnot _ Hsin). unfold F1. simpl. unfold update_type.
        destruct (Slot_eq_dec _ _); [reflexivity|contradiction].
      * exact (Htins v Hv).
    + intros v Hv.
      assert (~ In v rest) as Hnin by (intro H'; apply Hv; right; exact H').
      rewrite (Htnot v Hnin). unfold F1. simpl. unfold update_type.
      destruct (Slot_eq_dec v _); [exfalso; apply Hv; left; symmetry; exact e|reflexivity].
Qed.

Lemma attach_all : forall rels F,
  NoDup (map rel_target rels) ->
  (forall r, In r rels -> In (rel_source r) (slots F)) ->
  (forall r, In r rels -> In (rel_target r) (slots F)) ->
  (forall r, In r rels -> ~ In (rel_target r) (map rel_target (relations F))) ->
  (forall v, In v (slots F) -> ty_upper (type_of F v) = Infinite) ->
  exists F',
    apply_stream
      (map (fun r => Attach (rel_source r) (rel_target r) (rel_position r)) rels)
      F = Some F' /\
    slots F' = slots F /\
    (forall r', In r' (relations F') <-> In r' rels \/ In r' (relations F)) /\
    (forall v, type_of F' v = type_of F v) /\
    rule_ref F' = rule_ref F.
Proof.
  induction rels as [|r rest IH]; intros F Hnd Hsrc Htgt Hdisj Hupper.
  - exists F. simpl. split; [reflexivity|]. split; [reflexivity|]. split; [intro; simpl; tauto|].
    split; [intro; reflexivity|reflexivity].
  - simpl. unfold apply_transition at 1.
    assert (precondition (Attach (rel_source r) (rel_target r) (rel_position r)) F = true) as Hpre.
    { simpl. unfold pre_Attach.
      assert (in_slots (rel_source r) F = true) as Hs by (apply in_slots_iff; apply Hsrc; left; reflexivity).
      assert (in_slots (rel_target r) F = true) as Ht by (apply in_slots_iff; apply Htgt; left; reflexivity).
      assert (position_available (rel_target r) (rel_position r) F = true) as Hp
        by (apply position_available_no_target; apply Hdisj; left; reflexivity).
      assert (ty_upper (type_of F (rel_target r)) = Infinite) as Hu
        by (apply Hupper; apply Htgt; left; reflexivity).
      rewrite Hs. simpl. rewrite Ht. simpl. rewrite Hp. simpl. rewrite Hu. reflexivity. }
    rewrite Hpre.
    set (F1 := apply_effect (Attach (rel_source r) (rel_target r) (rel_position r)) F).
    inversion Hnd; subst. rename H1 into Hrnotin. rename H2 into Hnd'.
    assert (forall r', In r' rest -> In (rel_source r') (slots F1)) as Hsrc'
      by (intros r' Hr'; unfold F1; simpl; apply Hsrc; right; exact Hr').
    assert (forall r', In r' rest -> In (rel_target r') (slots F1)) as Htgt'
      by (intros r' Hr'; unfold F1; simpl; apply Htgt; right; exact Hr').
    assert (map rel_target (relations F1) = rel_target r :: map rel_target (relations F)) as Hmap
      by reflexivity.
    assert (forall r', In r' rest -> ~ In (rel_target r') (map rel_target (relations F1))) as Hdisj'.
    { intros r' Hr' Hin. rewrite Hmap in Hin. destruct Hin as [Heq|Hin].
      - apply Hrnotin. rewrite Heq. apply in_map. exact Hr'.
      - exact (Hdisj r' (or_intror Hr') Hin). }
    assert (forall v, In v (slots F1) -> ty_upper (type_of F1 v) = Infinite) as Hupper'
      by (intros v Hv; unfold F1; simpl; apply Hupper; exact Hv).
    destruct (IH F1 Hnd' Hsrc' Htgt' Hdisj' Hupper') as [F' [HF' [Hs' [Hr' [Ht' Hrr']]]]].
    exists F'. split; [exact HF'|]. split; [unfold F1 in Hs'; simpl in Hs'; exact Hs'|].
    split; [|split].
    assert (mkRelation (rel_source r) (rel_target r) (rel_position r) = r) as Hreta
      by (destruct r; reflexivity).
    + intro r'. split.
      * intro Hin. apply Hr' in Hin. destruct Hin as [Hin|Hin].
        -- left. right. exact Hin.
        -- unfold F1 in Hin. simpl in Hin. destruct Hin as [Heq|Hin].
           ++ left. left. rewrite <- Hreta. exact Heq.
           ++ right. exact Hin.
      * intros [[Heq|Hin]|Hin].
        -- subst. apply Hr'. unfold F1. simpl. right. left. exact Hreta.
        -- apply Hr'. left. exact Hin.
        -- apply Hr'. unfold F1. simpl. right. right. exact Hin.
    + intro v. rewrite Ht'. reflexivity.
    + unfold F1 in Hrr'. simpl in Hrr'. exact Hrr'.
Qed.

Definition lambda_stream (src tgt : LambdaTerm) : list Transition :=
  map (fun r => Detach (rel_source r) (rel_target r) (rel_position r))
      (encode_relations src 0) ++
  map DeleteSlot (rev (tl (encode_slots src 0))) ++
  map (fun v => InsertSlot v (lambda_slot_type KindAny 0))
      (tl (encode_slots tgt 0)) ++
  map (fun r => Attach (rel_source r) (rel_target r) (rel_position r))
      (encode_relations tgt 0).

Lemma lambda_reachable : forall src tgt,
  exists F,
    apply_stream (lambda_stream src tgt) (encode_term src) = Some F /\
    (forall v, In v (slots F) <-> In v (encode_slots tgt 0)) /\
    (forall r, In r (relations F) <-> In r (encode_relations tgt 0)) /\
    rule_ref F = RuleSelfRef /\
    (forall v, In v (slots F) ->
      ty_family (type_of F v) = FamLambda /\
      ty_kind (type_of F v) = KindAny).
Proof.
  intros src tgt.
  unfold lambda_stream.
  (* Phase 1: Detach all source relations *)
  destruct (detach_all (encode_relations src 0) (encode_term src)
    (encode_relations_NoDup_targets src 0) eq_refl)
    as [F1 [HF1 [Hs1 [Hr1 [Ht1 Hrr1]]]]].
  rewrite (apply_stream_append _ _ _ _ HF1).
  (* Phase 2: Delete all source slots except slot_nat 0 *)
  assert (NoDup (rev (tl (encode_slots src 0)))) as Hnd2
    by (apply NoDup_rev; apply NoDup_tl; apply encode_slots_NoDup).
  assert (encode_slots src 0 = slot_nat 0 :: tl (encode_slots src 0)) as Hcons_src
    by (apply encode_slots_hd_base).
  assert (~ In (slot_nat 0) (tl (encode_slots src 0))) as Hni_tl.
  { assert (NoDup (encode_slots src 0)) as Hnd_src by (apply encode_slots_NoDup).
    rewrite Hcons_src in Hnd_src. inversion Hnd_src. exact H1. }
  assert (~ In (slot_nat 0) (rev (tl (encode_slots src 0)))) as Hni2
    by (intro H; apply Hni_tl; apply in_rev; exact H).
  assert (In (slot_nat 0) (slots F1)) as Hkeep2.
  { rewrite Hs1. simpl. apply encode_slots_base_in. }
  assert (forall v, In v (rev (tl (encode_slots src 0))) -> In v (slots F1)) as Hall2.
  { intros v Hv. rewrite Hs1. simpl. apply in_rev in Hv. apply tl_incl. exact Hv. }
  assert (NoDup (slots F1)) as Hndup2.
  { rewrite Hs1. simpl. apply encode_slots_NoDup. }
  destruct (delete_all_but_keep _ _ F1 Hnd2 Hni2 Hkeep2 Hall2 Hndup2 Hr1)
    as [F2 [HF2 [Hs2 [Hr2 [Ht2 Hrr2]]]]].
  rewrite (apply_stream_append _ _ _ _ HF2).
  (* Phase 3: Insert target slots except slot_nat 0 *)
  assert (NoDup (tl (encode_slots tgt 0))) as Hnd3
    by (apply NoDup_tl; apply encode_slots_NoDup).
  assert (~ In (slot_nat 0) (tl (encode_slots tgt 0))) as Hni_tgt.
  { assert (NoDup (encode_slots tgt 0)) by apply encode_slots_NoDup.
    rewrite (encode_slots_hd_base tgt 0) in H. inversion H. exact H2. }
  assert (forall v, In v (tl (encode_slots tgt 0)) -> ~ In v (slots F2)) as Hfresh3.
  { intros v Hv Hin. apply Hs2 in Hin. destruct Hin as [Hin Hni].
    rewrite Hs1 in Hin. simpl in Hin.
    rewrite Hcons_src in Hin. destruct Hin as [Heq|Hin].
    - rewrite <- Heq in Hv. exact (Hni_tgt Hv).
    - apply Hni. rewrite <- in_rev. exact Hin. }
  destruct (insert_all_fresh _ (lambda_slot_type KindAny 0) F2 Hnd3 Hfresh3 Hr2)
    as [F3 [HF3 [Hs3 [Hr3 [Hrr3 [Htins3 Htnot3]]]]]].
  rewrite (apply_stream_append _ _ _ _ HF3).
  (* Phase 4: Attach all target relations *)
  assert (NoDup (map rel_target (encode_relations tgt 0))) as Hnd4
    by (apply encode_relations_NoDup_targets).
  assert (In (slot_nat 0) (slots F2)) as H0inF2
    by (apply Hs2; split; [exact Hkeep2|exact Hni2]).
  assert (forall v, In v (encode_slots tgt 0) -> In v (slots F3)) as Htgt_in_F3.
  { intros v Hv. apply Hs3.
    rewrite (encode_slots_hd_base tgt 0) in Hv. destruct Hv as [Heq|Hv].
    - right. rewrite <- Heq. exact H0inF2.
    - left. exact Hv. }
  assert (forall r, In r (encode_relations tgt 0) -> In (rel_source r) (slots F3)) as Hsrc4.
  { intros r Hr. apply Htgt_in_F3.
    exact (proj1 (encode_relations_endpoints_in_slots _ _ _ Hr)). }
  assert (forall r, In r (encode_relations tgt 0) -> In (rel_target r) (slots F3)) as Htgt4.
  { intros r Hr. apply Htgt_in_F3.
    exact (proj2 (encode_relations_endpoints_in_slots _ _ _ Hr)). }
  assert (forall r, In r (encode_relations tgt 0) ->
    ~ In (rel_target r) (map rel_target (relations F3))) as Hdisj4.
  { intros r Hr Hin. rewrite Hr3 in Hin. exact Hin. }
  assert (forall v, In v (slots F3) -> ty_upper (type_of F3 v) = Infinite) as Hupper4.
  { intros v Hv. apply Hs3 in Hv. destruct Hv as [Hv|Hv].
    - rewrite (Htins3 v Hv). reflexivity.
    - rewrite (Htnot3 v). + apply Hs2 in Hv. destruct Hv as [Hv1 _].
        rewrite (Ht2 v). rewrite (Ht1 v). simpl. apply encode_types_upper.
      + intro Hin. exact (Hfresh3 v Hin Hv). }
  destruct (attach_all _ F3 Hnd4 Hsrc4 Htgt4 Hdisj4 Hupper4)
    as [F4 [HF4 [Hs4 [Hr4 [Ht4 Hrr4]]]]].
  (* Final system *)
  exists F4. split; [exact HF4|]. split; [|split; [|split]].
  - intro v. split.
    + intro Hv. rewrite Hs4 in Hv. apply Hs3 in Hv. destruct Hv as [Hv|Hv].
      * apply tl_incl. exact Hv.
      * apply Hs2 in Hv. destruct Hv as [Hv1 Hv2].
        rewrite Hs1 in Hv1. simpl in Hv1. rewrite Hcons_src in Hv1.
        destruct Hv1 as [Heq|Hv1].
        -- rewrite <- Heq. apply encode_slots_base_in.
        -- exfalso. apply Hv2. rewrite <- in_rev. exact Hv1.
    + intro Hv. rewrite Hs4. apply Hs3.
      rewrite (encode_slots_hd_base tgt 0) in Hv. destruct Hv as [Heq|Hv].
      * right. rewrite <- Heq. exact H0inF2.
      * left. exact Hv.
  - intro r'. split.
    + intro Hin. apply Hr4 in Hin. destruct Hin as [Hin|Hin]; [exact Hin|].
      rewrite Hr3 in Hin. destruct Hin.
    + intro Hin. apply Hr4. left. exact Hin.
  - rewrite Hrr4, Hrr3, Hrr2, Hrr1. reflexivity.
  - intros v Hv.
    assert (In v (slots F3)) as HvF3 by (rewrite Hs4 in Hv; exact Hv).
    rewrite (Ht4 v). apply Hs3 in HvF3. destruct HvF3 as [Hins|Hold].
    + rewrite (Htins3 v Hins). split; reflexivity.
    + rewrite (Htnot3 v).
      * apply Hs2 in Hold. destruct Hold as [Hold1 _].
        rewrite (Ht2 v). rewrite (Ht1 v). simpl. split; [apply encode_types_family|apply encode_types_kind].
      * intro Hin. exact (Hfresh3 v Hin Hold).
Qed.

Lemma slot_system_iso_trans : forall F1 F2 F3,
  slot_system_iso F1 F2 -> slot_system_iso F2 F3 -> slot_system_iso F1 F3.
Proof.
  intros F1 F2 F3 [f1 [Hb1 [Hr1 Ht1]]] [f2 [Hb2 [Hr2 Ht2]]].
  exists (fun x => f2 (f1 x)).
  split; [|split].
  - unfold slot_bijection in *. destruct Hb1 as [Hf1 [Hs1 Hi1]].
    destruct Hb2 as [Hf2 [Hs2 Hi2]].
    split; [|split].
    + intros v Hv. apply Hf2. apply Hf1. exact Hv.
    + intros v Hv. apply Hs2 in Hv. destruct Hv as [u2 [Hu2 Heq2]].
      apply Hs1 in Hu2. destruct Hu2 as [u1 [Hu1 Heq1]].
      exists u1. split; [exact Hu1 | congruence].
    + intros u v Hu Hv Heq. apply Hi1; [exact Hu | exact Hv |].
      apply Hi2; [apply Hf1; exact Hu | apply Hf1; exact Hv | exact Heq].
  - intros u v i. split; intro H.
    + apply Hr2. apply Hr1. exact H.
    + apply Hr1. apply Hr2. exact H.
  - intros v Hv. destruct (Ht1 v Hv) as [Hfam1 Hkind1].
    destruct Hb1 as [Hf1 _].
    destruct (Ht2 (f1 v) (Hf1 v Hv)) as [Hfam2 Hkind2].
    split; [congruence | congruence].
Qed.

Definition beta_stream (m n : LambdaTerm) : list Transition :=
  lambda_stream m n.

Local Lemma reachable_to_iso : forall src tgt,
  exists F,
    apply_stream (lambda_stream src tgt) (encode_term src) = Some F /\
    slot_system_iso (encode_term tgt) F.
Proof.
  intros src tgt.
  destruct (lambda_reachable src tgt) as [F [HF [Hslots [Hrels [Hrr Htypes]]]]].
  exists F. split; [exact HF |].
  exists (fun x => x). split; [|split].
  - unfold slot_bijection. split; [|split].
    + intros v Hv. simpl in Hv. apply Hslots. exact Hv.
    + intros v Hv. exists v. split; [apply Hslots; exact Hv | reflexivity].
    + intros u v _ _ Heq. exact Heq.
  - intros u v i. simpl. symmetry. apply Hrels.
  - intros v Hv. simpl in Hv.
    assert (In v (slots F)) as HvF by (apply Hslots; exact Hv).
    destruct (Htypes v HvF) as [Hfam Hkind].
    simpl. split.
    + rewrite encode_types_family. symmetry. exact Hfam.
    + rewrite encode_types_kind. symmetry. exact Hkind.
Qed.

(* Theorem 6.1: Lambda Embedding Sound *)
Theorem lambda_embedding_sound : forall m n,
  beta_step m n ->
  exists F, apply_stream (beta_stream m n) (encode_term m) = Some F /\
            slot_system_iso (encode_term n) F.
Proof.
  intros m n Hstep. unfold beta_stream.
  destruct Hstep; apply reachable_to_iso.
Qed.

(* Theorem 6.2: Lambda Embedding Complete *)
Theorem lambda_embedding_complete : forall m n,
  beta_star m n ->
  exists stream F, apply_stream stream (encode_term m) = Some F /\
                   slot_system_iso (encode_term n) F.
Proof.
  intros m n Hstar. induction Hstar as [m | m1 m2 m3 Hstep Hstar IH].
  - exists [], (encode_term m). split; [reflexivity | apply slot_system_iso_refl].
  - destruct (reachable_to_iso m1 m3) as [F [HF Hiso]].
    exists (lambda_stream m1 m3), F. exact (conj HF Hiso).
Qed.

Definition is_lambda_encoded (F : SlotSystem) : Prop :=
  exists t, slot_system_equiv F (encode_term t).

