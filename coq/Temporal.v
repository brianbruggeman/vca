(* VCA Kernel - Temporal.v

   Temporal logic operators and SLA verification.
   Theorems 13-16: □ Coinductive, ◇ Inductive, SLA Decidable, Tower Satisfies SLA.
*)

Require Import VCA.Core.
Require Import VCA.Admissibility.
Require Import VCA.Towers.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Lia.
Import ListNotations.

Definition StatePredicate := SlotSystem -> bool.

Definition always (phi : StatePredicate) (T : Tower) : Prop :=
  forall n, phi (T n) = true.

Definition eventually (phi : StatePredicate) (T : Tower) : Prop :=
  exists n, phi (T n) = true.

Definition always_prefix (phi : StatePredicate) (T : Tower) (k : nat) : bool :=
  forallb (fun n => phi (T n)) (seq 0 (S k)).

Definition eventually_prefix (phi : StatePredicate) (T : Tower) (k : nat) : bool :=
  existsb (fun n => phi (T n)) (seq 0 (S k)).

(* Theorem 13: □ is Coinductive
   T ⊨ □φ iff we never find a level where φ fails. *)
Theorem box_coinductive : forall phi T,
  always phi T <-> (forall k, always_prefix phi T k = true).
Proof.
  intros phi T. split.
  - intro H. intro k. unfold always_prefix.
    apply forallb_forall. intros n Hn.
    apply in_seq in Hn. destruct Hn as [_ Hn].
    apply H.
  - intro H. intro n. unfold always.
    specialize (H n). unfold always_prefix in H.
    apply forallb_forall with (x := n) in H.
    + exact H.
    + apply in_seq. lia.
Qed.

(* Theorem 13 Decidability: □φ on prefix is decidable *)
Theorem box_prefix_decidable : forall phi T k,
  {always_prefix phi T k = true} + {always_prefix phi T k = false}.
Proof.
  intros phi T k. destruct (always_prefix phi T k) eqn:E.
  - left. reflexivity.
  - right. reflexivity.
Qed.

(* Theorem 14: ◇ is Inductive
   T ⊨ ◇φ iff we find some level where φ holds. *)
Theorem diamond_inductive : forall phi T,
  eventually phi T <-> (exists k, eventually_prefix phi T k = true).
Proof.
  intros phi T. split.
  - intro H. destruct H as [n Hn]. exists n.
    unfold eventually_prefix. apply existsb_exists.
    exists n. split.
    + apply in_seq. lia.
    + exact Hn.
  - intro H. destruct H as [k Hk].
    unfold eventually_prefix in Hk. apply existsb_exists in Hk.
    destruct Hk as [n [Hn Hphi]].
    exists n. exact Hphi.
Qed.

(* Theorem 14 Decidability: ◇φ on prefix is decidable *)
Theorem diamond_prefix_decidable : forall phi T k,
  {eventually_prefix phi T k = true} + {eventually_prefix phi T k = false}.
Proof.
  intros phi T k. destruct (eventually_prefix phi T k) eqn:E.
  - left. reflexivity.
  - right. reflexivity.
Qed.

Lemma forallb_false_existsb_negb : forall {A : Type} (f : A -> bool) (l : list A),
  forallb f l = false <-> existsb (fun x => negb (f x)) l = true.
Proof.
  intros A f l. induction l as [|x xs IH]; simpl.
  - split; discriminate.
  - destruct (f x) eqn:Hfx; simpl.
    + exact IH.
    + split; intro H; reflexivity.
Qed.

(* Duality: ¬□φ ↔ ◇¬φ *)
Lemma box_diamond_duality_prefix : forall phi T k,
  always_prefix phi T k = false <->
  eventually_prefix (fun F => negb (phi F)) T k = true.
Proof.
  intros phi T k. split.
  - intro H. unfold always_prefix, eventually_prefix in *.
    rewrite forallb_false_existsb_negb in H.
    apply existsb_exists in H. destruct H as [n [Hn Hphi]].
    apply existsb_exists. exists n. split.
    + exact Hn.
    + simpl. exact Hphi.
  - intro H. unfold always_prefix, eventually_prefix in *.
    apply existsb_exists in H. destruct H as [n [Hn Hphi]].
    simpl in Hphi.
    apply forallb_false_existsb_negb. apply existsb_exists.
    exists n. split.
    + exact Hn.
    + exact Hphi.
Qed.

(* SLA: Service Level Agreement as conjunction of □-properties *)
Definition SLA := list StatePredicate.

Definition sla_satisfied_at (sla : SLA) (F : SlotSystem) : bool :=
  forallb (fun phi => phi F) sla.

Definition sla_satisfied (sla : SLA) (T : Tower) : Prop :=
  forall n, sla_satisfied_at sla (T n) = true.

Definition sla_prefix (sla : SLA) (T : Tower) (k : nat) : bool :=
  forallb (fun n => sla_satisfied_at sla (T n)) (seq 0 (S k)).

(* Theorem 15: SLA Finite Prefix Decidable *)
Theorem sla_finite_prefix_decidable : forall sla T k,
  {sla_prefix sla T k = true} + {sla_prefix sla T k = false}.
Proof.
  intros sla T k. destruct (sla_prefix sla T k) eqn:E.
  - left. reflexivity.
  - right. reflexivity.
Qed.

(* Theorem 16: Tower Satisfies SLA iff □(sla_satisfied_at) *)
Theorem tower_satisfies_sla : forall sla T,
  sla_satisfied sla T <-> always (sla_satisfied_at sla) T.
Proof.
  intros sla T. split.
  - intro H. exact H.
  - intro H. exact H.
Qed.

(* Theorem 16 Corollary: SLA verification via prefix checking *)
Theorem sla_verification_coinductive : forall sla T,
  sla_satisfied sla T <-> (forall k, sla_prefix sla T k = true).
Proof.
  intros sla T.
  rewrite tower_satisfies_sla.
  rewrite box_coinductive.
  split.
  - intro H. intro k. exact (H k).
  - intro H. intro k. exact (H k).
Qed.

