(* VCA Kernel - Admissibility.v

   Interpretation and admissibility from VCA spec §3.
   Axioms Σ.5-Σ.7: Interpretation, Base Kinds, Kind Registry.
*)

Require Import VCA.Core.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition interpret (K : Kind) (r_type : SlotType) (t_src t_tgt : SlotType) (i : PosIndex) : bool :=
  match K with
  | KindAny => Nat.leb (ty_layer t_tgt) (ty_layer r_type)
  | KindNone => false
  | KindPatternMatch => Family_eqb (ty_family t_src) (ty_family t_tgt)
                         && Nat.leb (ty_layer t_tgt) (ty_layer r_type)
  | KindEq => Nat.eqb (ty_id t_src) (ty_id t_tgt)
               && Nat.leb (ty_layer t_tgt) (ty_layer r_type)
  | KindTop => true
  | KindBot => false
  | KindInvalid => false
  end.

Definition base_registry : list Kind :=
  [KindAny; KindNone; KindPatternMatch; KindEq; KindTop; KindBot].

Definition kind_in_registry (K : Kind) : bool :=
  existsb (Kind_eqb K) base_registry.

Lemma kind_in_registry_valid : forall K, K <> KindInvalid -> kind_in_registry K = true.
Proof.
  intro K. destruct K; intro H; try reflexivity. contradiction.
Qed.

Lemma kind_in_registry_invalid : kind_in_registry KindInvalid = false.
Proof. reflexivity. Qed.

(* Rule slot validity *)
Definition valid_rule_slot (F : SlotSystem) (r : Slot) : bool :=
  match ty_family (type_of F r) with
  | FamRule => kind_in_registry (ty_kind (type_of F r))
  | _ => true
  end.

(* Admissibility check: exists a rule that admits the relation *)
Definition relation_admissible (F : SlotSystem) (rel : Relation) : bool :=
  match rule_ref F with
  | RuleEmpty => false
  | RuleSelfRef =>
      existsb (fun r =>
        andb (Family_eqb (ty_family (type_of F r)) FamRule)
             (interpret (ty_kind (type_of F r)) (type_of F r)
                        (type_of F (rel_source rel))
                        (type_of F (rel_target rel))
                        (rel_position rel)))
        (slots F)
  | RuleExternal _ => true
  end.

Definition all_admissible (F : SlotSystem) : bool :=
  forallb (relation_admissible F) (relations F).

(* Definition 4.2: Coherence *)
Definition FS_coh_b (F : SlotSystem) : bool :=
  andb (FS_struct_b F)
       (all_admissible F).

Definition FS_coh (F : SlotSystem) : Prop :=
  FS_coh_b F = true.

Lemma existsb_ext : forall {A : Type} (f g : A -> bool) (l : list A),
  (forall x, f x = g x) -> existsb f l = existsb g l.
Proof.
  intros A f g l Hext. induction l as [|x xs IH]; [reflexivity|].
  simpl. rewrite Hext, IH. reflexivity.
Qed.

Theorem shallow_access : forall F1 F2 rel,
  slots F1 = slots F2 ->
  (forall v, type_of F1 v = type_of F2 v) ->
  rule_ref F1 = rule_ref F2 ->
  relation_admissible F1 rel = relation_admissible F2 rel.
Proof.
  intros F1 F2 rel Hslots Htypes Hrr.
  unfold relation_admissible. rewrite Hrr. rewrite Hslots.
  destruct (rule_ref F2); try reflexivity.
  apply existsb_ext. intro r.
  repeat rewrite Htypes. reflexivity.
Qed.

(* Theorem 2: Self-Reference Coherence *)
Theorem self_reference_coherence :
  forall F,
    rule_ref F = RuleSelfRef ->
    (FS_coh F <-> FS_struct F /\ all_admissible F = true).
Proof.
  intros F Hself. split.
  - intro H. unfold FS_coh, FS_coh_b in H.
    apply andb_prop in H. destruct H as [Hstruct Hadm].
    split; [exact Hstruct | exact Hadm].
  - intros [Hstruct Hadm]. unfold FS_coh, FS_coh_b.
    apply andb_true_intro. split; [exact Hstruct | exact Hadm].
Qed.

(* Theorem 3: Structural Validity Decidable *)
Theorem structural_validity_decidable :
  forall F, {FS_struct F} + {~ FS_struct F}.
Proof.
  intro F. unfold FS_struct, FS_struct_b.
  destruct (negb (length (slots F) =? 0)) eqn:Ene;
  destruct (position_unique F) eqn:Epos;
  destruct (upper_bounds_ok F) eqn:Eupper; simpl.
  all: try (left; reflexivity).
  all: right; discriminate.
Qed.

(* Theorem 4: Admissibility Decidable *)
Theorem admissibility_decidable :
  forall F rel, {relation_admissible F rel = true} + {relation_admissible F rel = false}.
Proof.
  intros F rel. unfold relation_admissible.
  destruct (rule_ref F) as [|  | ext_id].
  - right. reflexivity.
  - destruct (existsb (fun r =>
      andb (Family_eqb (ty_family (type_of F r)) FamRule)
           (interpret (ty_kind (type_of F r)) (type_of F r)
                      (type_of F (rel_source rel))
                      (type_of F (rel_target rel))
                      (rel_position rel))) (slots F)) eqn:E.
    + left. reflexivity.
    + right. reflexivity.
  - left. reflexivity.
Qed.
