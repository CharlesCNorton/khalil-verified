(******************************************************************************)
(*                                                                            *)
(*                    Khalil's Aruz: The Science of Prosody                   *)
(*                                                                            *)
(*     The original Arabic quantitative meter system devised by Khalil ibn    *)
(*     Ahmad al-Farahidi (c. 718-786 CE). Formalizes the 15 canonical         *)
(*     meters, syllable weight, and the tent-pole terminology.                *)
(*                                                                            *)
(*     "The origin of 'aruz is the tent-pole; the verse is a tent."           *)
(*     - Khalil ibn Ahmad al-Farahidi, c. 760 CE                              *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: February 6, 2026                                                 *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

Require Import List.
Import ListNotations.

(** * Section 1: Foundations *)

(** ** Syllable Weight *)

(** In Khalil's system, syllables are classified by weight:
    - Short (khafif): CV (consonant + short vowel)
    - Long (thaqil): CVV (consonant + long vowel) or CVC (closed syllable) *)

Inductive weight : Type :=
  | Short : weight
  | Long : weight.

(** ** Weight Pattern *)

(** A pattern is a sequence of syllable weights. *)

Definition pattern := list weight.

(** ** Decidable Equality for Weight *)

Definition weight_eq_dec (w1 w2 : weight) : {w1 = w2} + {w1 <> w2}.
Proof.
  destruct w1, w2.
  - left. reflexivity.
  - right. discriminate.
  - right. discriminate.
  - left. reflexivity.
Defined.

(** Witness: weight_eq_dec Short Short = left eq_refl *)
Example weight_eq_dec_witness : exists pf, weight_eq_dec Short Short = left pf.
Proof.
  exists eq_refl. reflexivity.
Qed.

(** Example: Short = Short *)
Example weight_eq_example : Short = Short.
Proof.
  reflexivity.
Qed.

(** Counterexample: weight_eq_dec correctly returns right for unequal inputs.
    A buggy implementation might return left for all inputs. *)
Example weight_eq_dec_counterexample :
  exists pf, weight_eq_dec Short Long = right pf.
Proof.
  eexists. reflexivity.
Qed.

(** ** Boolean Equality for Weight *)

Definition weight_eqb (w1 w2 : weight) : bool :=
  match w1, w2 with
  | Short, Short => true
  | Long, Long => true
  | _, _ => false
  end.

(** Correctness of boolean equality *)
Lemma weight_eqb_eq : forall w1 w2, weight_eqb w1 w2 = true <-> w1 = w2.
Proof.
  intros w1 w2. split.
  - destruct w1, w2; simpl; intros H; try reflexivity; discriminate.
  - intros H. rewrite H. destruct w2; reflexivity.
Qed.

(** Witness: weight_eqb Long Long = true *)
Example weight_eqb_witness : weight_eqb Long Long = true.
Proof.
  reflexivity.
Qed.

(** Example: weight_eqb Short Short = true *)
Example weight_eqb_example : weight_eqb Short Short = true.
Proof.
  reflexivity.
Qed.

(** Counterexample: weight_eqb returns false for unequal inputs in both directions.
    A buggy implementation might only check one direction. *)
Example weight_eqb_counterexample_1 : weight_eqb Short Long = false.
Proof. reflexivity. Qed.

Example weight_eqb_counterexample_2 : weight_eqb Long Short = false.
Proof. reflexivity. Qed.

(** ** Decidable Equality for Patterns *)

Fixpoint pattern_eq_dec (p1 p2 : pattern) : {p1 = p2} + {p1 <> p2}.
Proof.
  destruct p1 as [|w1 p1'], p2 as [|w2 p2'].
  - left. reflexivity.
  - right. discriminate.
  - right. discriminate.
  - destruct (weight_eq_dec w1 w2) as [Hw | Hw].
    + destruct (pattern_eq_dec p1' p2') as [Hp | Hp].
      * left. rewrite Hw, Hp. reflexivity.
      * right. intros H. injection H as H1 H2. contradiction.
    + right. intros H. injection H as H1 H2. contradiction.
Defined.

(** Witness: pattern_eq_dec [] [] = left eq_refl *)
Example pattern_eq_dec_witness : exists pf, pattern_eq_dec [] [] = left pf.
Proof.
  exists eq_refl. reflexivity.
Qed.

(** Example: [Short; Long] = [Short; Long] *)
Example pattern_eq_example : [Short; Long] = [Short; Long].
Proof.
  reflexivity.
Qed.

(** Counterexamples for pattern_eq_dec: test failure modes.
    - Different lengths: a buggy impl might not check length
    - Same length, differ at head: tests head comparison
    - Same length, differ at tail: tests recursive case *)
Example pattern_eq_dec_counterexample_length :
  exists pf, pattern_eq_dec [] [Short] = right pf.
Proof. eexists. reflexivity. Qed.

Example pattern_eq_dec_counterexample_head :
  exists pf, pattern_eq_dec [Short] [Long] = right pf.
Proof. eexists. reflexivity. Qed.

Example pattern_eq_dec_counterexample_tail :
  exists pf, pattern_eq_dec [Short; Short] [Short; Long] = right pf.
Proof. eexists. reflexivity. Qed.

(** ** Boolean Equality for Patterns *)

Fixpoint pattern_eqb (p1 p2 : pattern) : bool :=
  match p1, p2 with
  | [], [] => true
  | w1 :: p1', w2 :: p2' => weight_eqb w1 w2 && pattern_eqb p1' p2'
  | _, _ => false
  end.

(** Correctness of boolean pattern equality *)
Lemma pattern_eqb_eq : forall p1 p2, pattern_eqb p1 p2 = true <-> p1 = p2.
Proof.
  induction p1 as [|w1 p1' IH]; destruct p2 as [|w2 p2']; simpl.
  - split; reflexivity.
  - split; discriminate.
  - split; discriminate.
  - rewrite Bool.andb_true_iff. rewrite IH. rewrite weight_eqb_eq.
    split.
    + intros [H1 H2]. rewrite H1, H2. reflexivity.
    + intros H. injection H as H1 H2. split; assumption.
Qed.

(** Witness: pattern_eqb [Long] [Long] = true *)
Example pattern_eqb_witness : pattern_eqb [Long] [Long] = true.
Proof.
  reflexivity.
Qed.

(** Example: pattern_eqb [Short; Long; Long] [Short; Long; Long] = true *)
Example pattern_eqb_example : pattern_eqb [Short; Long; Long] [Short; Long; Long] = true.
Proof.
  reflexivity.
Qed.

(** Counterexamples for pattern_eqb: same failure modes as pattern_eq_dec *)
Example pattern_eqb_counterexample_length : pattern_eqb [] [Short] = false.
Proof. reflexivity. Qed.

Example pattern_eqb_counterexample_head : pattern_eqb [Short] [Long] = false.
Proof. reflexivity. Qed.

Example pattern_eqb_counterexample_tail : pattern_eqb [Short; Short] [Short; Long] = false.
Proof. reflexivity. Qed.

(** ** Pattern Length *)

Definition pattern_length (p : pattern) : nat := length p.

(** Witness: pattern_length [Short; Long; Long] = 3 *)
Example pattern_length_witness : pattern_length [Short; Long; Long] = 3.
Proof.
  reflexivity.
Qed.

(** Example: pattern_length [] = 0 *)
Example pattern_length_example : pattern_length [] = 0.
Proof.
  reflexivity.
Qed.

(** Counterexample: pattern_length increments correctly.
    A buggy implementation might return constant 0 or skip elements. *)
Example pattern_length_counterexample :
  pattern_length [Short] = 1 /\
  pattern_length [Short; Long] = 2 /\
  pattern_length [Short; Long; Short] = 3.
Proof.
  repeat split; reflexivity.
Qed.

(** ** Weight Enumeration *)

(** The type weight has exactly two inhabitants. *)

Definition all_weights : list weight := [Short; Long].

Lemma all_weights_complete : forall w : weight, In w all_weights.
Proof.
  intros w. destruct w.
  - left. reflexivity.
  - right. left. reflexivity.
Qed.

(** Witness: In Short all_weights *)
Example all_weights_witness : In Short all_weights.
Proof.
  left. reflexivity.
Qed.

(** Example: In Long all_weights *)
Example all_weights_example : In Long all_weights.
Proof.
  right. left. reflexivity.
Qed.

(** Counterexample: an incomplete enumeration fails completeness.
    This shows the property would fail if we forgot an element. *)
Example all_weights_counterexample : ~ (forall w : weight, In w [Short]).
Proof.
  intros H. specialize (H Long). simpl in H. destruct H as [H | H].
  - discriminate.
  - contradiction.
Qed.

(** ** No Duplicate Weights *)

Lemma all_weights_nodup : NoDup all_weights.
Proof.
  constructor.
  - simpl. intros [H | H].
    + discriminate.
    + contradiction.
  - constructor.
    + simpl. intros H. contradiction.
    + constructor.
Qed.

(** Witness: NoDup [Short; Long] *)
Example all_weights_nodup_witness : NoDup [Short; Long].
Proof.
  exact all_weights_nodup.
Qed.

(** Example: NoDup [] *)
Example nodup_example : NoDup ([] : list weight).
Proof.
  constructor.
Qed.

(** Counterexample: ~ NoDup [Short; Short] *)
Example nodup_counterexample : ~ NoDup [Short; Short].
Proof.
  intros H. inversion H as [| x xs Hnotin Hnodup].
  apply Hnotin. left. reflexivity.
Qed.

(** End of Section 1: Foundations *)

(** * Section 2: Building Blocks *)

(** In Khalil's terminology, syllable sequences are built from two primitives:
    - Sabab (سبب, "cord" or "guy-rope"): short sequences
    - Watad (وتد, "peg" or "tent-pole"): the structural core *)

(** ** Sabab Types *)

(** Sabab khafīf (light cord): a single short syllable *)
Definition sabab_khafif : pattern := [Short].

(** Sabab thaqīl (heavy cord): two short syllables *)
Definition sabab_thaqil : pattern := [Short; Short].

(** Sabab recognition *)
Definition is_sabab_khafif (p : pattern) : bool :=
  pattern_eqb p sabab_khafif.

Definition is_sabab_thaqil (p : pattern) : bool :=
  pattern_eqb p sabab_thaqil.

Definition is_sabab (p : pattern) : bool :=
  is_sabab_khafif p || is_sabab_thaqil p.

(** Witness: sabab_khafif is [Short] *)
Example sabab_khafif_witness : sabab_khafif = [Short].
Proof. reflexivity. Qed.

(** Example: is_sabab_khafif recognizes [Short] *)
Example is_sabab_khafif_example : is_sabab_khafif [Short] = true.
Proof. reflexivity. Qed.

(** Counterexample: is_sabab_khafif rejects other patterns *)
Example is_sabab_khafif_counterexample_long : is_sabab_khafif [Long] = false.
Proof. reflexivity. Qed.

Example is_sabab_khafif_counterexample_empty : is_sabab_khafif [] = false.
Proof. reflexivity. Qed.

Example is_sabab_khafif_counterexample_toolong : is_sabab_khafif [Short; Short] = false.
Proof. reflexivity. Qed.

(** Witness: sabab_thaqil is [Short; Short] *)
Example sabab_thaqil_witness : sabab_thaqil = [Short; Short].
Proof. reflexivity. Qed.

(** Example: is_sabab_thaqil recognizes [Short; Short] *)
Example is_sabab_thaqil_example : is_sabab_thaqil [Short; Short] = true.
Proof. reflexivity. Qed.

(** Counterexample: is_sabab_thaqil rejects other patterns *)
Example is_sabab_thaqil_counterexample_single : is_sabab_thaqil [Short] = false.
Proof. reflexivity. Qed.

Example is_sabab_thaqil_counterexample_mixed : is_sabab_thaqil [Short; Long] = false.
Proof. reflexivity. Qed.

(** ** Watad Types *)

(** Watad majmūʿ (joined peg): short followed by long *)
Definition watad_majmu : pattern := [Short; Long].

(** Watad mafrūq (split peg): long followed by short *)
Definition watad_mafruq : pattern := [Long; Short].

(** Watad recognition *)
Definition is_watad_majmu (p : pattern) : bool :=
  pattern_eqb p watad_majmu.

Definition is_watad_mafruq (p : pattern) : bool :=
  pattern_eqb p watad_mafruq.

Definition is_watad (p : pattern) : bool :=
  is_watad_majmu p || is_watad_mafruq p.

(** Witness: watad_majmu is [Short; Long] *)
Example watad_majmu_witness : watad_majmu = [Short; Long].
Proof. reflexivity. Qed.

(** Example: is_watad_majmu recognizes [Short; Long] *)
Example is_watad_majmu_example : is_watad_majmu [Short; Long] = true.
Proof. reflexivity. Qed.

(** Counterexample: is_watad_majmu rejects reversed and other patterns *)
Example is_watad_majmu_counterexample_reversed : is_watad_majmu [Long; Short] = false.
Proof. reflexivity. Qed.

Example is_watad_majmu_counterexample_same : is_watad_majmu [Short; Short] = false.
Proof. reflexivity. Qed.

Example is_watad_majmu_counterexample_single : is_watad_majmu [Short] = false.
Proof. reflexivity. Qed.

(** Witness: watad_mafruq is [Long; Short] *)
Example watad_mafruq_witness : watad_mafruq = [Long; Short].
Proof. reflexivity. Qed.

(** Example: is_watad_mafruq recognizes [Long; Short] *)
Example is_watad_mafruq_example : is_watad_mafruq [Long; Short] = true.
Proof. reflexivity. Qed.

(** Counterexample: is_watad_mafruq rejects reversed and other patterns *)
Example is_watad_mafruq_counterexample_reversed : is_watad_mafruq [Short; Long] = false.
Proof. reflexivity. Qed.

Example is_watad_mafruq_counterexample_same : is_watad_mafruq [Long; Long] = false.
Proof. reflexivity. Qed.

(** ** Mutual Exclusion *)

(** Sabab and watad are disjoint categories *)
Lemma sabab_not_watad : forall p, is_sabab p = true -> is_watad p = false.
Proof.
  intros p H. unfold is_sabab, is_watad in *.
  unfold is_sabab_khafif, is_sabab_thaqil, is_watad_majmu, is_watad_mafruq in *.
  apply Bool.orb_true_iff in H. destruct H as [H | H].
  - apply pattern_eqb_eq in H. rewrite H. reflexivity.
  - apply pattern_eqb_eq in H. rewrite H. reflexivity.
Qed.

(** Witness: [Short] is sabab, not watad *)
Example sabab_not_watad_witness : is_sabab [Short] = true /\ is_watad [Short] = false.
Proof. split; reflexivity. Qed.

(** Example: [Short; Short] is sabab, not watad *)
Example sabab_not_watad_example : is_sabab [Short; Short] = true /\ is_watad [Short; Short] = false.
Proof. split; reflexivity. Qed.

(** Counterexample: [Short; Long] is watad, not sabab *)
Example watad_not_sabab_counterexample : is_watad [Short; Long] = true /\ is_sabab [Short; Long] = false.
Proof. split; reflexivity. Qed.

(** ** Building Block Enumeration *)

Definition all_sabab : list pattern := [sabab_khafif; sabab_thaqil].
Definition all_watad : list pattern := [watad_majmu; watad_mafruq].
Definition all_building_blocks : list pattern := all_sabab ++ all_watad.

Lemma all_sabab_complete : forall p, is_sabab p = true -> In p all_sabab.
Proof.
  intros p H. unfold is_sabab in H.
  apply Bool.orb_true_iff in H. destruct H as [H | H].
  - apply pattern_eqb_eq in H. rewrite H. left. reflexivity.
  - apply pattern_eqb_eq in H. rewrite H. right. left. reflexivity.
Qed.

Lemma all_watad_complete : forall p, is_watad p = true -> In p all_watad.
Proof.
  intros p H. unfold is_watad in H.
  apply Bool.orb_true_iff in H. destruct H as [H | H].
  - apply pattern_eqb_eq in H. rewrite H. left. reflexivity.
  - apply pattern_eqb_eq in H. rewrite H. right. left. reflexivity.
Qed.

(** Witness: all_sabab contains sabab_khafif *)
Example all_sabab_witness : In sabab_khafif all_sabab.
Proof. left. reflexivity. Qed.

(** Example: all_watad contains watad_mafruq *)
Example all_watad_example : In watad_mafruq all_watad.
Proof. right. left. reflexivity. Qed.

(** Counterexample: incomplete list fails completeness *)
Example all_sabab_counterexample : ~ (forall p, is_sabab p = true -> In p [sabab_khafif]).
Proof.
  intros H. specialize (H sabab_thaqil).
  assert (Hs : is_sabab sabab_thaqil = true) by reflexivity.
  specialize (H Hs). simpl in H. destruct H as [H | H].
  - unfold sabab_thaqil, sabab_khafif in H. discriminate.
  - contradiction.
Qed.

(** ** No Duplicates *)

Lemma all_sabab_nodup : NoDup all_sabab.
Proof.
  constructor.
  - simpl. intros [H | H].
    + unfold sabab_khafif, sabab_thaqil in H. discriminate.
    + contradiction.
  - constructor.
    + simpl. intros H. contradiction.
    + constructor.
Qed.

Lemma all_watad_nodup : NoDup all_watad.
Proof.
  constructor.
  - simpl. intros [H | H].
    + unfold watad_majmu, watad_mafruq in H. discriminate.
    + contradiction.
  - constructor.
    + simpl. intros H. contradiction.
    + constructor.
Qed.

(** Witness: NoDup all_sabab *)
Example all_sabab_nodup_witness : NoDup all_sabab.
Proof. exact all_sabab_nodup. Qed.

(** Example: NoDup all_watad *)
Example all_watad_nodup_example : NoDup all_watad.
Proof. exact all_watad_nodup. Qed.

(** Counterexample: list with duplicates fails NoDup *)
Example building_blocks_nodup_counterexample : ~ NoDup [sabab_khafif; sabab_khafif].
Proof.
  intros H. inversion H as [| x xs Hnotin Hnodup].
  apply Hnotin. left. reflexivity.
Qed.

(** End of Section 2: Building Blocks *)
