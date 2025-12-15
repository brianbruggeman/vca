(* VCA Kernel - Towers.v

   Tower coherence and related theorems.
   Theorems 5-7: Tower Independence, Tower Coherence Coinductive, Finite Prefix Decidable.
*)

Require Import VCA.Core.
Require Import VCA.Admissibility.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Lia.
Import ListNotations.

Definition Tower := nat -> SlotSystem.

Definition tower_level (T : Tower) (n : nat) : SlotSystem := T n.

Definition local_coh_0 (F : SlotSystem) : bool :=
  FS_coh_b F.

Definition all_admissible_external (F_n F_prev : SlotSystem) : bool :=
  forallb (fun rel =>
    existsb (fun r =>
      andb (Family_eqb (ty_family (type_of F_prev r)) FamRule)
           (interpret (ty_kind (type_of F_prev r)) r
                      (type_of F_n (rel_source rel))
                      (type_of F_n (rel_target rel))
                      (rel_position rel)))
      (slots F_prev))
    (relations F_n).

Definition local_coh_n (F_n F_prev : SlotSystem) : bool :=
  andb (FS_struct_b F_n) (all_admissible_external F_n F_prev).

Definition local_coh (T : Tower) (n : nat) : bool :=
  match n with
  | 0 => local_coh_0 (T 0)
  | S m => andb (FS_struct_b (T n)) (all_admissible_external (T n) (T m))
  end.

Definition tower_coh_prefix (T : Tower) (n : nat) : bool :=
  forallb (fun k => local_coh T k) (seq 0 (S n)).

(* Theorem 5: Tower Independence
   Coherence at level n depends only on levels n and n-1 (for n > 0).
   Formalized: local_coh T n only accesses T n and T (n-1). *)
Lemma minus_succ : forall m, S m - 1 = m.
Proof. intro m. lia. Qed.

Theorem tower_independence : forall T n,
  n > 0 ->
  forall T',
    T n = T' n ->
    T (n - 1) = T' (n - 1) ->
    local_coh T n = local_coh T' n.
Proof.
  intros T n Hn T' Heq_n Heq_prev.
  destruct n as [|m]; [lia|].
  unfold local_coh.
  rewrite minus_succ in Heq_prev.
  rewrite Heq_n, Heq_prev. reflexivity.
Qed.

(* Theorem 5 Corollary: Level 0 is self-contained *)
Theorem tower_independence_0 : forall T T',
  T 0 = T' 0 ->
  local_coh T 0 = local_coh T' 0.
Proof.
  intros T T' Heq. simpl. rewrite Heq. reflexivity.
Qed.

(* Theorem 6: Tower Coherence is Coinductive
   Tower_coh = gfp(Φ) where Φ checks local coherence.
   We express this as: T is coherent iff all prefixes are coherent. *)
Definition tower_coherent (T : Tower) : Prop :=
  forall n, local_coh T n = true.

Theorem tower_coherence_coinductive : forall T,
  tower_coherent T <-> (forall n, tower_coh_prefix T n = true).
Proof.
  intro T. split.
  - intro Hcoh. intro n. unfold tower_coh_prefix.
    apply forallb_forall. intros k Hk.
    apply in_seq in Hk. destruct Hk as [_ Hk].
    apply Hcoh.
  - intro Hprefix. intro n. unfold tower_coherent.
    specialize (Hprefix n). unfold tower_coh_prefix in Hprefix.
    apply forallb_forall with (x := n) in Hprefix.
    + exact Hprefix.
    + apply in_seq. lia.
Qed.

(* Theorem 7: Finite Prefix Decidable
   For any n, tower_coh_prefix T n is decidable. *)
Theorem finite_prefix_decidable : forall T n,
  {tower_coh_prefix T n = true} + {tower_coh_prefix T n = false}.
Proof.
  intros T n. unfold tower_coh_prefix.
  destruct (forallb (fun k => local_coh T k) (seq 0 (S n))) eqn:E.
  - left. reflexivity.
  - right. reflexivity.
Qed.

(* Corollary: Each local_coh check is decidable *)
Theorem local_coh_decidable : forall T n,
  {local_coh T n = true} + {local_coh T n = false}.
Proof.
  intros T n. destruct (local_coh T n) eqn:E.
  - left. reflexivity.
  - right. reflexivity.
Qed.

(* Constant tower is coherent if base system is coherent *)
Definition constant_tower (F : SlotSystem) : Tower := fun _ => F.

Lemma constant_tower_local_coh_0 : forall F,
  FS_coh F ->
  local_coh (constant_tower F) 0 = true.
Proof.
  intros F H. unfold local_coh, local_coh_0, constant_tower.
  unfold FS_coh in H. exact H.
Qed.

Lemma all_admissible_implies_external : forall F,
  rule_ref F = RuleSelfRef ->
  all_admissible F = true ->
  all_admissible_external F F = true.
Proof.
  intros F Hself Hadm.
  unfold all_admissible, all_admissible_external in *.
  rewrite forallb_forall in *. intros rel Hrel.
  specialize (Hadm rel Hrel).
  unfold relation_admissible in Hadm. rewrite Hself in Hadm.
  exact Hadm.
Qed.

Lemma constant_tower_local_coh_n : forall F n,
  FS_coh F ->
  rule_ref F = RuleSelfRef ->
  local_coh (constant_tower F) (S n) = true.
Proof.
  intros F n H Hself. unfold local_coh, constant_tower.
  unfold FS_coh, FS_coh_b in H. apply andb_prop in H. destruct H as [Hstruct Hadm].
  apply andb_true_intro. split.
  - exact Hstruct.
  - apply all_admissible_implies_external; assumption.
Qed.

Theorem constant_tower_coherent : forall F,
  FS_coh F ->
  rule_ref F = RuleSelfRef ->
  tower_coherent (constant_tower F).
Proof.
  intros F H Hself n. destruct n.
  - apply constant_tower_local_coh_0. exact H.
  - apply constant_tower_local_coh_n; assumption.
Qed.
