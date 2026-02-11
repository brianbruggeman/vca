(* VCA Kernel - Core.v

   The 4-tuple slot system from VCA spec §2.
   Axioms Σ.1-Σ.4: Slots, Relations, Types, Rule System.
*)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Lia.
Import ListNotations.

(* Axiom Σ.1: Slots *)
Parameter Slot : Type.
Parameter Slot_eq_dec : forall (x y : Slot), {x = y} + {x <> y}.

Definition Slot_eqb (x y : Slot) : bool :=
  if Slot_eq_dec x y then true else false.

(* Position index *)
Definition PosIndex := nat.

(* Axiom Σ.2: Relations *)
Record Relation : Type := mkRelation {
  rel_source : Slot;
  rel_target : Slot;
  rel_position : PosIndex;
}.

Definition Relation_eqb (r1 r2 : Relation) : bool :=
  andb (Slot_eqb (rel_source r1) (rel_source r2))
       (andb (Slot_eqb (rel_target r1) (rel_target r2))
             (Nat.eqb (rel_position r1) (rel_position r2))).

(* Axiom Σ.3: Type Space *)
Inductive Family : Type :=
  | FamTop | FamBot | FamRule | FamData | FamLambda | FamTemporal.

Inductive Kind : Type :=
  | KindTop | KindBot | KindAny | KindNone | KindPatternMatch | KindEq | KindInvalid.

Inductive Affinity : Type :=
  | AffTop | AffBot | AffStrict | AffLax.

Inductive UpperBound : Type :=
  | Finite (n : nat)
  | Infinite.

Record SlotType : Type := mkSlotType {
  ty_family : Family;
  ty_kind : Kind;
  ty_layer : nat;
  ty_affinity : Affinity;
  ty_lower : nat;
  ty_upper : UpperBound;
  ty_id : nat;
}.

Definition Family_eqb (f1 f2 : Family) : bool :=
  match f1, f2 with
  | FamTop, FamTop | FamBot, FamBot | FamRule, FamRule
  | FamData, FamData | FamLambda, FamLambda | FamTemporal, FamTemporal => true
  | _, _ => false
  end.

Definition Kind_eqb (k1 k2 : Kind) : bool :=
  match k1, k2 with
  | KindTop, KindTop | KindBot, KindBot | KindAny, KindAny
  | KindNone, KindNone | KindPatternMatch, KindPatternMatch | KindEq, KindEq
  | KindInvalid, KindInvalid => true
  | _, _ => false
  end.

(* Axiom Σ.4: Slot System (4-tuple) *)
Inductive RuleRef : Type :=
  | RuleEmpty
  | RuleSelfRef
  | RuleExternal (id : nat).

Record SlotSystem : Type := mkSlotSystem {
  slots : list Slot;
  relations : list Relation;
  type_of : Slot -> SlotType;
  rule_ref : RuleRef;
}.

(* Definition 2.1: Slot System Class membership *)
Definition in_slots (v : Slot) (F : SlotSystem) : bool :=
  existsb (Slot_eqb v) (slots F).

Definition src_count (v : Slot) (F : SlotSystem) : nat :=
  length (filter (fun r => Slot_eqb (rel_target r) v) (relations F)).

Definition position_unique_at (v : Slot) (i : PosIndex) (F : SlotSystem) : bool :=
  let rels := filter (fun r =>
    andb (Slot_eqb (rel_target r) v) (Nat.eqb (rel_position r) i)) (relations F) in
  Nat.leb (length rels) 1.

Definition position_unique (F : SlotSystem) : bool :=
  forallb (fun r => position_unique_at (rel_target r) (rel_position r) F) (relations F).

Definition upper_satisfied (t : SlotType) (count : nat) : bool :=
  match ty_upper t with
  | Finite n => Nat.leb count n
  | Infinite => true
  end.

Definition upper_bounds_ok (F : SlotSystem) : bool :=
  forallb (fun v => upper_satisfied (type_of F v) (src_count v F)) (slots F).

(* Definition 4.1: Structural Validity *)
Definition FS_struct_b (F : SlotSystem) : bool :=
  andb (negb (Nat.eqb (length (slots F)) 0))
       (andb (position_unique F)
             (upper_bounds_ok F)).

Definition FS_struct (F : SlotSystem) : Prop :=
  FS_struct_b F = true.

(* Lemmas for structural validity *)
Lemma FS_struct_nonempty : forall F,
  FS_struct F -> slots F <> [].
Proof.
  intros F H. unfold FS_struct, FS_struct_b in H.
  apply andb_prop in H. destruct H as [Hne _].
  apply negb_true_iff in Hne. apply Nat.eqb_neq in Hne.
  intro Heq. rewrite Heq in Hne. simpl in Hne. lia.
Qed.

Lemma FS_struct_position_unique : forall F,
  FS_struct F -> position_unique F = true.
Proof.
  intros F H. unfold FS_struct, FS_struct_b in H.
  apply andb_prop in H. destruct H as [_ H].
  apply andb_prop in H. destruct H as [Hpos _].
  exact Hpos.
Qed.

Lemma FS_struct_upper_bounds : forall F,
  FS_struct F -> upper_bounds_ok F = true.
Proof.
  intros F H. unfold FS_struct, FS_struct_b in H.
  apply andb_prop in H. destruct H as [_ H].
  apply andb_prop in H. destruct H as [_ Hupper].
  exact Hupper.
Qed.
