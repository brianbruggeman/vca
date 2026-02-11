(* VCA Kernel - Replay.v

   Deterministic replay for distributed VCA systems.
   Theorem 12: Replay Determinism.
*)

Require Import VCA.Core.
Require Import VCA.Transitions.
Require Import VCA.Admissibility.
Require Import VCA.CoreStar.
Require Import VCA.Commutativity.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
Import ListNotations.

Definition VectorClock := list (nat * nat).

Record Transaction := mkTransaction {
  tx_ops : list Transition;
  tx_origin : nat;
  tx_vc : VectorClock;
  tx_seq : nat;
}.

Fixpoint vc_to_nats (vc : VectorClock) : list nat :=
  match vc with
  | [] => []
  | (r, v) :: rest => r :: v :: vc_to_nats rest
  end.

Definition tx_key (t : Transaction) : list nat :=
  vc_to_nats (tx_vc t) ++ [tx_origin t; tx_seq t].

Fixpoint lex_leb (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
    if Nat.ltb x y then true
    else if Nat.ltb y x then false
    else lex_leb xs ys
  end.

Fixpoint lex_le (l1 l2 : list nat) : Prop :=
  match l1, l2 with
  | [], _ => True
  | _ :: _, [] => False
  | x :: xs, y :: ys => x < y \/ (x = y /\ lex_le xs ys)
  end.

Lemma lex_leb_iff : forall l1 l2,
  lex_leb l1 l2 = true <-> lex_le l1 l2.
Proof.
  induction l1 as [| x xs IH]; destruct l2 as [| y ys]; simpl.
  - split; tauto.
  - split; tauto.
  - split; [discriminate | tauto].
  - destruct (Nat.ltb x y) eqn:Exy.
    + split; [intros _; left; apply Nat.ltb_lt; exact Exy | tauto].
    + destruct (Nat.ltb y x) eqn:Eyx.
      * apply Nat.ltb_lt in Eyx. apply Nat.ltb_ge in Exy. split;
          [discriminate | intros [Hlt | [Heq _]]; lia].
      * apply Nat.ltb_ge in Exy. apply Nat.ltb_ge in Eyx.
        assert (x = y) as Hxy by lia. rewrite IH. split.
        -- intro H. right. exact (conj Hxy H).
        -- intros [Hlt | [_ H]]; [lia | exact H].
Qed.

Lemma lex_leb_refl : forall l, lex_leb l l = true.
Proof.
  induction l as [| x xs IH]; simpl; [reflexivity |].
  assert (Nat.ltb x x = false) as H by (apply Nat.ltb_irrefl).
  rewrite H. exact IH.
Qed.

Lemma lex_le_trans : forall l1 l2 l3,
  lex_le l1 l2 -> lex_le l2 l3 -> lex_le l1 l3.
Proof.
  induction l1 as [| x xs IH]; simpl; [tauto |].
  destruct l2 as [| y ys]; simpl; [tauto |].
  destruct l3 as [| z zs]; simpl; [tauto |].
  intros [Hlt1 | [Heq1 Hle1]] [Hlt2 | [Heq2 Hle2]].
  - left; lia.
  - left; lia.
  - left; lia.
  - right; split; [lia | exact (IH _ _ Hle1 Hle2)].
Qed.

Lemma lex_leb_trans : forall l1 l2 l3,
  lex_leb l1 l2 = true -> lex_leb l2 l3 = true -> lex_leb l1 l3 = true.
Proof.
  intros l1 l2 l3 H1 H2. apply lex_leb_iff.
  apply lex_leb_iff in H1. apply lex_leb_iff in H2.
  exact (lex_le_trans _ _ _ H1 H2).
Qed.

Lemma lex_leb_antisym : forall l1 l2,
  lex_leb l1 l2 = true -> lex_leb l2 l1 = true -> l1 = l2.
Proof.
  induction l1 as [| x xs IH]; destruct l2 as [| y ys];
    simpl; intros H1 H2; try reflexivity; try discriminate.
  destruct (x <? y) eqn:Exy, (y <? x) eqn:Eyx;
    simpl in H1, H2; try discriminate.
  - apply Nat.ltb_lt in Exy. apply Nat.ltb_lt in Eyx. lia.
  - apply Nat.ltb_ge in Exy. apply Nat.ltb_ge in Eyx.
    assert (x = y) by lia. subst. f_equal. exact (IH _ H1 H2).
Qed.

Lemma lex_leb_total : forall l1 l2,
  lex_leb l1 l2 = true \/ lex_leb l2 l1 = true.
Proof.
  induction l1 as [| x xs IH]; destruct l2 as [| y ys]; simpl.
  - left; reflexivity.
  - left; reflexivity.
  - right; reflexivity.
  - destruct (Nat.ltb x y) eqn:Exy.
    + left; reflexivity.
    + destruct (Nat.ltb y x) eqn:Eyx.
      * right; reflexivity.
      * exact (IH ys).
Qed.

Definition tx_leb (t1 t2 : Transaction) : bool :=
  lex_leb (tx_key t1) (tx_key t2).

Lemma tx_leb_refl : forall t, tx_leb t t = true.
Proof. intro t. unfold tx_leb. apply lex_leb_refl. Qed.

Lemma tx_leb_trans : forall t1 t2 t3,
  tx_leb t1 t2 = true -> tx_leb t2 t3 = true -> tx_leb t1 t3 = true.
Proof.
  intros t1 t2 t3. unfold tx_leb. apply lex_leb_trans.
Qed.

Lemma tx_leb_antisym : forall t1 t2,
  tx_leb t1 t2 = true -> tx_leb t2 t1 = true -> tx_key t1 = tx_key t2.
Proof.
  intros t1 t2. unfold tx_leb. apply lex_leb_antisym.
Qed.

Lemma tx_leb_total : forall t1 t2,
  tx_leb t1 t2 = true \/ tx_leb t2 t1 = true.
Proof.
  intros t1 t2. unfold tx_leb. apply lex_leb_total.
Qed.

Fixpoint eval_tx (ops : list Transition) (F : SlotSystem) : SlotSystem :=
  match ops with
  | [] => F
  | op :: rest =>
    match apply_transition op F with
    | Some F' => eval_tx rest F'
    | None => eval_tx rest F
    end
  end.

Definition replay_sorted (txs : list Transaction) (F : SlotSystem) : SlotSystem :=
  fold_left (fun acc tx => eval_tx (tx_ops tx) acc) txs F.

Inductive Sorted : list Transaction -> Prop :=
  | Sorted_nil : Sorted []
  | Sorted_cons : forall t l,
      Forall (fun t' => tx_leb t t' = true) l ->
      Sorted l ->
      Sorted (t :: l).

Fixpoint insert_tx (t : Transaction) (l : list Transaction) : list Transaction :=
  match l with
  | [] => [t]
  | h :: rest =>
    if tx_leb t h then t :: h :: rest
    else h :: insert_tx t rest
  end.

Fixpoint sort_txs (l : list Transaction) : list Transaction :=
  match l with
  | [] => []
  | h :: rest => insert_tx h (sort_txs rest)
  end.

Definition replay (txs : list Transaction) (F : SlotSystem) : SlotSystem :=
  replay_sorted (sort_txs txs) F.

Lemma insert_tx_forall : forall t h l,
  tx_leb h t = true ->
  Forall (fun t' => tx_leb h t' = true) l ->
  Forall (fun t' => tx_leb h t' = true) (insert_tx t l).
Proof.
  intros t h l Hht Hfa. induction l as [| a rest IH]; simpl.
  - constructor; [exact Hht | constructor].
  - inversion Hfa; subst. destruct (tx_leb t a).
    + repeat constructor; assumption.
    + constructor; [exact H1 | exact (IH H2)].
Qed.

Lemma insert_tx_sorted : forall t l,
  Sorted l -> Sorted (insert_tx t l).
Proof.
  intros t l Hs. induction Hs as [| h rest Hfa Hsorted IH]; simpl.
  - constructor; [constructor | constructor].
  - destruct (tx_leb t h) eqn:Eth.
    + constructor.
      * { constructor; [exact Eth |].
          eapply Forall_impl; [| exact Hfa].
          simpl. intros a Ha. exact (tx_leb_trans t h a Eth Ha). }
      * constructor; [exact Hfa | exact Hsorted].
    + assert (tx_leb h t = true) as Hht
        by (destruct (tx_leb_total t h); [rewrite H in Eth; discriminate | exact H]).
      constructor; [apply insert_tx_forall; [exact Hht | exact Hfa] | exact IH].
Qed.

Lemma sort_txs_sorted : forall l, Sorted (sort_txs l).
Proof.
  induction l as [| h rest IH]; simpl.
  - constructor.
  - apply insert_tx_sorted. exact IH.
Qed.

Lemma insert_tx_perm : forall t l,
  Permutation (t :: l) (insert_tx t l).
Proof.
  intros t l. induction l as [| h rest IH]; simpl.
  - apply Permutation_refl.
  - destruct (tx_leb t h).
    + apply Permutation_refl.
    + apply Permutation_trans with (h :: t :: rest).
      * apply perm_swap.
      * apply perm_skip. exact IH.
Qed.

Lemma sort_txs_perm : forall l, Permutation l (sort_txs l).
Proof.
  induction l as [| h rest IH]; simpl.
  - apply perm_nil.
  - apply Permutation_trans with (h :: sort_txs rest).
    + apply perm_skip. exact IH.
    + apply insert_tx_perm.
Qed.

Lemma sorted_head_le : forall t t' l,
  Sorted (t :: l) -> In t' l -> tx_leb t t' = true.
Proof.
  intros t t' l Hs Hin. inversion Hs; subst.
  rewrite Forall_forall in H1. exact (H1 t' Hin).
Qed.

Lemma sorted_perm_unique : forall l1 l2,
  Sorted l1 -> Sorted l2 -> Permutation l1 l2 ->
  (forall t1 t2, In t1 l1 -> In t2 l1 ->
    tx_leb t1 t2 = true -> tx_leb t2 t1 = true -> t1 = t2) ->
  l1 = l2.
Proof.
  induction l1 as [| a l1' IH]; intros l2 Hs1 Hs2 Hperm Huniq.
  - apply Permutation_nil in Hperm. symmetry. exact Hperm.
  - destruct l2 as [| b l2'].
    + apply Permutation_sym in Hperm. apply Permutation_nil in Hperm. discriminate.
    + assert (In a (b :: l2')) as Ha
        by (eapply Permutation_in; [exact Hperm | left; reflexivity]).
      assert (In b (a :: l1')) as Hb
        by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
      assert (tx_leb a b = true) as Hab.
      { destruct Hb as [Heq | Hin].
        - subst. apply tx_leb_refl.
        - exact (sorted_head_le a b l1' Hs1 Hin). }
      assert (tx_leb b a = true) as Hba.
      { destruct Ha as [Heq | Hin].
        - subst. apply tx_leb_refl.
        - exact (sorted_head_le b a l2' Hs2 Hin). }
      assert (a = b) as Heq.
      { apply Huniq; [left; reflexivity | |exact Hab | exact Hba].
        destruct Hb; [left; exact H | right; exact H]. }
      subst b. f_equal.
      apply IH.
      * inversion Hs1; exact H2.
      * inversion Hs2; exact H2.
      * exact (Permutation_cons_inv Hperm).
      * intros t1 t2 Ht1 Ht2.
        apply Huniq; right; assumption.
Qed.

Theorem replay_deterministic : forall txs1 txs2 F,
  sort_txs txs1 = sort_txs txs2 ->
  replay txs1 F = replay txs2 F.
Proof.
  intros txs1 txs2 F Heq. unfold replay. rewrite Heq. reflexivity.
Qed.

Lemma eval_tx_deterministic : forall ops F,
  eval_tx ops F = eval_tx ops F.
Proof. reflexivity. Qed.

Theorem replay_convergence : forall txs1 txs2 F,
  Permutation txs1 txs2 ->
  (forall t1 t2, In t1 txs1 -> In t2 txs1 ->
    tx_leb t1 t2 = true -> tx_leb t2 t1 = true -> t1 = t2) ->
  replay txs1 F = replay txs2 F.
Proof.
  intros txs1 txs2 F Hperm Huniq.
  apply replay_deterministic.
  apply sorted_perm_unique.
  - apply sort_txs_sorted.
  - apply sort_txs_sorted.
  - apply Permutation_trans with txs1.
    + apply Permutation_sym. apply sort_txs_perm.
    + apply Permutation_trans with txs2.
      * exact Hperm.
      * apply sort_txs_perm.
  - intros t1 t2 Ht1 Ht2.
    apply Huniq.
    + eapply Permutation_in; [apply Permutation_sym; apply sort_txs_perm | exact Ht1].
    + eapply Permutation_in; [apply Permutation_sym; apply sort_txs_perm | exact Ht2].
Qed.
