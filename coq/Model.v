(* VCA Kernel - Model.v

   Concrete instantiation of VCA slot systems.
   Demonstrates the 4-tuple in action with example systems.
*)

Require Import VCA.Core.
Require Import VCA.Admissibility.
Require Import VCA.Transitions.
Require Import VCA.Towers.
Require Import VCA.Commutativity.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

(* Concrete slot type: natural numbers *)
Axiom slot_nat : nat -> Slot.
Axiom slot_nat_injective : forall n m, slot_nat n = slot_nat m -> n = m.
Axiom slot_nat_inv : forall s, {n : nat | s = slot_nat n}.

Definition slot_to_nat (s : Slot) : nat := proj1_sig (slot_nat_inv s).

Lemma slot_to_nat_spec : forall s, s = slot_nat (slot_to_nat s).
Proof.
  intro s. unfold slot_to_nat. destruct (slot_nat_inv s) as [n Hn]. exact Hn.
Qed.

Lemma slot_to_nat_nat : forall n, slot_to_nat (slot_nat n) = n.
Proof.
  intro n. unfold slot_to_nat. destruct (slot_nat_inv (slot_nat n)) as [m Hm].
  simpl. symmetry. apply slot_nat_injective. exact Hm.
Qed.

(* Default slot type *)
Definition default_type : SlotType :=
  mkSlotType FamData KindAny 0 AffLax 0 Infinite 0.

(* Rule slot type with Kind = Any *)
Definition rule_type_any (id : nat) : SlotType :=
  mkSlotType FamRule KindAny 1 AffLax 0 Infinite id.

(* Data slot type with upper bound *)
Definition data_type (upper : nat) (id : nat) : SlotType :=
  mkSlotType FamData KindAny 0 AffLax 0 (Finite upper) id.

(* Empty system - minimal valid system *)
Definition empty_system (v0 : Slot) : SlotSystem :=
  mkSlotSystem
    [v0]
    []
    (fun _ => default_type)
    RuleSelfRef.

(* Self-referential system with one rule slot *)
Definition self_ref_system (r0 : Slot) : SlotSystem :=
  mkSlotSystem
    [r0]
    []
    (fun _ => rule_type_any 0)
    RuleSelfRef.

(* Example: Two slots with one relation *)
Definition two_slot_system (v0 v1 : Slot) : SlotSystem :=
  mkSlotSystem
    [v0; v1]
    [mkRelation v0 v1 0]
    (fun s => if Slot_eq_dec s v0 then rule_type_any 0 else data_type 10 1)
    RuleSelfRef.

(* Verify empty system is structurally valid *)
Lemma empty_system_struct : forall v0,
  FS_struct (empty_system v0).
Proof.
  intro v0. unfold FS_struct, FS_struct_b, empty_system. simpl.
  reflexivity.
Qed.

(* Verify self-referential system is coherent *)
Lemma self_ref_system_coh : forall r0,
  FS_coh (self_ref_system r0).
Proof.
  intro r0. unfold FS_coh, FS_coh_b, self_ref_system. simpl.
  reflexivity.
Qed.

(* Verify two-slot system is structurally valid *)
Lemma two_slot_struct : forall v0 v1,
  v0 <> v1 ->
  FS_struct (two_slot_system v0 v1).
Proof.
  intros v0 v1 Hneq. unfold FS_struct, FS_struct_b, two_slot_system. simpl.
  unfold position_unique, position_unique_at, upper_bounds_ok. simpl.
  unfold Slot_eqb. destruct (Slot_eq_dec v1 v1) as [_|Hne]; [|contradiction].
  simpl.
  unfold upper_satisfied, src_count, data_type, rule_type_any. simpl.
  destruct (Slot_eq_dec v0 v0) as [_|Hne]; [|contradiction].
  simpl. unfold Slot_eqb.
  destruct (Slot_eq_dec v1 v0) as [Heq|_]; [symmetry in Heq; contradiction|].
  destruct (Slot_eq_dec v0 v1) as [Heq|_]; [contradiction|].
  destruct (Slot_eq_dec v1 v1) as [_|Hne]; [|contradiction].
  simpl. reflexivity.
Qed.

(* Transition example: Insert a new slot *)
Definition insert_example (F : SlotSystem) (v_new : Slot) : option SlotSystem :=
  apply_transition (InsertSlot v_new default_type) F.

(* Transition example: Attach a relation *)
Definition attach_example (F : SlotSystem) (u v : Slot) : option SlotSystem :=
  apply_transition (Attach u v 0) F.

(* Build a system incrementally *)
Definition build_three_slot (v0 v1 v2 : Slot) : option SlotSystem :=
  let F0 := self_ref_system v0 in
  match apply_transition (InsertSlot v1 (data_type 5 1)) F0 with
  | None => None
  | Some F1 =>
      match apply_transition (InsertSlot v2 (data_type 5 2)) F1 with
      | None => None
      | Some F2 =>
          match apply_transition (Attach v0 v1 0) F2 with
          | None => None
          | Some F3 => apply_transition (Attach v1 v2 0) F3
          end
      end
  end.

