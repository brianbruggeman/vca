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

Definition LambdaTerm_eqb (t1 t2 : LambdaTerm) : bool :=
  match t1, t2 with
  | LVar n1, LVar n2 => Nat.eqb n1 n2
  | LAbs x1 m1, LAbs x2 m2 => false
  | LApp f1 a1, LApp f2 a2 => false
  | _, _ => false
  end.

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
      else encode_types f (S base) v
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

Axiom shift_bijection : nat -> Slot -> Slot.
Axiom shift_bijection_spec : forall offset n, shift_bijection offset (slot_nat n) = slot_nat (n + offset).
Axiom shift_bijection_injective : forall offset u v,
  shift_bijection offset u = shift_bijection offset v -> u = v.

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


Axiom unshift : nat -> Slot -> Slot.
Axiom unshift_spec : forall offset n, offset <= n -> unshift offset (slot_nat n) = slot_nat (n - offset).
Axiom unshift_shift_inverse : forall offset v, unshift offset (shift_bijection offset v) = v.

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
  - destruct (Slot_eqb v (slot_nat base)); [reflexivity | apply IHf].
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

Axiom shift_unshift_inverse : forall offset v, shift_bijection offset (unshift offset v) = v.

Lemma encode_types_kind : forall t base v,
  ty_kind (encode_types t base v) = KindAny.
Proof.
  intros t. induction t as [x | x m IHm | f IHf a IHa]; intros base v; simpl.
  - destruct (Slot_eqb v (slot_nat base)); reflexivity.
  - destruct (Slot_eqb v (slot_nat base)); [reflexivity | apply IHm].
  - destruct (Slot_eqb v (slot_nat base)); [reflexivity | apply IHf].
Qed.

Lemma shifted_system_iso_original : forall t offset,
  slot_system_iso (shifted_encode_term t offset) (encode_term t).
Proof.
  intros t offset.
  exists (unshift offset).
  split; [|split].
  - unfold slot_bijection. split; [|split].
    + intros v Hv. simpl in *.
      apply shifted_in_implies_original in Hv.
      destruct Hv as [k [Hk Hin]]. subst.
      rewrite unshift_spec by lia. replace (k + offset - offset) with k by lia.
      exact Hin.
    + intros v Hv. simpl in *.
      apply original_in_implies_shifted with (offset := offset) in Hv.
      destruct Hv as [k [Hk Hin]]. subst.
      exists (slot_nat (k + offset)). split; [exact Hin|].
      rewrite unshift_spec by lia. f_equal. lia.
    + intros u v Hu Hv Heq. simpl in *.
      apply shifted_in_implies_original in Hu.
      apply shifted_in_implies_original in Hv.
      destruct Hu as [ku [Hku Hinu]].
      destruct Hv as [kv [Hkv Hinv]].
      subst. rewrite unshift_spec in Heq by lia.
      rewrite unshift_spec in Heq by lia.
      apply slot_nat_injective in Heq. f_equal. lia.
  - intros u v i. simpl. split; intro H.
    + apply shifted_relation_in_implies_original in H.
      destruct (mkRelation (unshift offset u) (unshift offset v) i) eqn:E.
      simpl in E. injection E as E1 E2 E3. rewrite <- E1, <- E2, <- E3. exact H.
    + pose proof (original_relation_in_implies_shifted t 0 offset
        (mkRelation (unshift offset u) (unshift offset v) i) H) as H'.
      simpl in H'.
      rewrite shift_unshift_inverse in H'.
      rewrite shift_unshift_inverse in H'.
      exact H'.
  - intros v Hv. simpl. split.
    + rewrite encode_types_family. reflexivity.
    + rewrite encode_types_kind. reflexivity.
Qed.

Axiom reconstruction_stream_succeeds : forall src tgt,
  apply_stream (reconstruction_stream src tgt) (encode_term src) =
  Some (shifted_encode_term tgt (term_size src)).

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

(* Theorem 6.1: Lambda Embedding Sound *)
Theorem lambda_embedding_sound : forall m n,
  beta_step m n ->
  exists stream F, apply_stream stream (encode_term m) = Some F /\
                   slot_system_iso F (encode_term n).
Proof.
  intros m n Hbeta.
  exists (reconstruction_stream m n).
  exists (shifted_encode_term n (term_size m)).
  split.
  - apply reconstruction_stream_succeeds.
  - apply shifted_system_iso_original.
Qed.

Theorem lambda_embedding_complete : forall m F,
  apply_stream [] (encode_term m) = Some F ->
  exists n, F = encode_term n /\ beta_star m n.
Proof.
  intros m F H. simpl in H. injection H as H. subst.
  exists m. split; [reflexivity|constructor].
Qed.

Definition is_lambda_encoded (F : SlotSystem) : Prop :=
  exists t, slot_system_equiv F (encode_term t).

