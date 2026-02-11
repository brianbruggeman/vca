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
           (interpret (ty_kind (type_of F_prev r)) (type_of F_prev r)
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

Theorem tower_independence : forall T n (default : SlotSystem),
  n > 0 ->
  local_coh T n = local_coh (fun k =>
    if (Nat.eqb k n || Nat.eqb k (n-1))%bool then T k
    else default) n.
Proof.
  intros T n default Hn.
  destruct n as [|m]; [lia|].
  replace (S m - 1) with m by lia.
  assert (forall T', T' (S m) = T (S m) -> T' m = T m ->
          local_coh T (S m) = local_coh T' (S m)) as Hind.
  { intros T' Eq1 Eq2. unfold local_coh. rewrite Eq1, Eq2. reflexivity. }
  apply Hind.
  - cbv beta. rewrite Nat.eqb_refl. reflexivity.
  - cbv beta.
    assert (Nat.eqb m (S m) = false) as H by (apply Nat.eqb_neq; lia).
    rewrite H, Nat.eqb_refl. reflexivity.
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

CoInductive tower_coherent_co : Tower -> nat -> Prop :=
  | tc_step : forall T n,
      local_coh T n = true ->
      tower_coherent_co T (S n) ->
      tower_coherent_co T n.

Lemma tower_coherent_co_advance : forall T n k,
  tower_coherent_co T n -> tower_coherent_co T (n + k).
Proof.
  intros T n k. revert n.
  induction k; intros n H.
  - replace (n + 0) with n by lia. exact H.
  - replace (n + S k) with (S n + k) by lia.
    apply IHk. destruct H. exact H0.
Qed.

Theorem tower_coherence_co_equiv : forall T,
  tower_coherent T <-> tower_coherent_co T 0.
Proof.
  intro T. split.
  - intro Hcoh.
    cofix IH.
    assert (forall n, tower_coherent_co T n) as Hgen.
    { cofix IH2. intro n.
      apply tc_step; [apply Hcoh | apply IH2]. }
    apply Hgen.
  - intro Hco. intro n.
    assert (tower_coherent_co T n) as Hn.
    { replace n with (0 + n) by lia. apply tower_coherent_co_advance. exact Hco. }
    destruct Hn. exact H.
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
