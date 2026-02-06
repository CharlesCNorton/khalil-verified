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
