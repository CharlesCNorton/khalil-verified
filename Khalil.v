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

(** * Section 3: The Eight Feet (Tafāʿīl) *)

(** The tafāʿīl (تفاعيل) are mnemonic words representing the canonical
    metrical feet. Each encodes a specific weight pattern. Khalil identified
    eight core feet from which all meters are built. *)

(** ** Foot Definitions *)

(** Trisyllabic feet *)
Definition faulun : pattern := [Short; Long; Long].        (* faʿūlun: u - - *)
Definition failun : pattern := [Long; Short; Long].        (* fāʿilun: - u - *)

(** Quadrisyllabic feet *)
Definition mafailun : pattern := [Short; Long; Long; Long].     (* mafāʿīlun: u - - - *)
Definition mustafilun : pattern := [Long; Long; Short; Long].   (* mustafʿilun: - - u - *)
Definition failatun : pattern := [Long; Short; Long; Long].     (* fāʿilātun: - u - - *)
Definition mafulatu : pattern := [Long; Long; Long; Short].     (* mafʿūlātu: - - - u *)

(** Pentasyllabic feet *)
Definition mutafailun : pattern := [Short; Short; Long; Short; Long].  (* mutafāʿilun: u u - u - *)
Definition mufaalatun : pattern := [Short; Long; Short; Short; Long].  (* mufāʿalatun: u - u u - *)

(** ** Foot Type *)

Inductive foot : Type :=
  | Faulun | Failun
  | Mafailun | Mustafilun | Failatun | Mafulatu
  | Mutafailun | Mufaalatun.

(** Map foot to its pattern *)
Definition foot_pattern (f : foot) : pattern :=
  match f with
  | Faulun => faulun
  | Failun => failun
  | Mafailun => mafailun
  | Mustafilun => mustafilun
  | Failatun => failatun
  | Mafulatu => mafulatu
  | Mutafailun => mutafailun
  | Mufaalatun => mufaalatun
  end.

(** ** Foot Recognition *)

Definition is_foot (p : pattern) : bool :=
  pattern_eqb p faulun ||
  pattern_eqb p failun ||
  pattern_eqb p mafailun ||
  pattern_eqb p mustafilun ||
  pattern_eqb p failatun ||
  pattern_eqb p mafulatu ||
  pattern_eqb p mutafailun ||
  pattern_eqb p mufaalatun.

(** Witness: faulun pattern *)
Example faulun_witness : faulun = [Short; Long; Long].
Proof. reflexivity. Qed.

(** Example: is_foot recognizes mafailun *)
Example is_foot_example : is_foot mafailun = true.
Proof. reflexivity. Qed.

(** Counterexamples: is_foot rejects non-foot patterns *)
Example is_foot_counterexample_empty : is_foot [] = false.
Proof. reflexivity. Qed.

Example is_foot_counterexample_sabab : is_foot sabab_khafif = false.
Proof. reflexivity. Qed.

Example is_foot_counterexample_watad : is_foot watad_majmu = false.
Proof. reflexivity. Qed.

Example is_foot_counterexample_arbitrary : is_foot [Long; Long; Long; Long; Long] = false.
Proof. reflexivity. Qed.

(** ** Decidable Equality for Foot *)

Definition foot_eq_dec (f1 f2 : foot) : {f1 = f2} + {f1 <> f2}.
Proof.
  destruct f1, f2; try (left; reflexivity); right; discriminate.
Defined.

(** Witness: foot_eq_dec Faulun Faulun *)
Example foot_eq_dec_witness : exists pf, foot_eq_dec Faulun Faulun = left pf.
Proof. eexists. reflexivity. Qed.

(** Example: foot_eq_dec Mafailun Mafailun *)
Example foot_eq_dec_example : exists pf, foot_eq_dec Mafailun Mafailun = left pf.
Proof. eexists. reflexivity. Qed.

(** Counterexample: foot_eq_dec returns right for different feet *)
Example foot_eq_dec_counterexample : exists pf, foot_eq_dec Faulun Failun = right pf.
Proof. eexists. reflexivity. Qed.

(** ** All Feet Are Distinct *)

Lemma foot_patterns_distinct : forall f1 f2 : foot,
  f1 <> f2 -> foot_pattern f1 <> foot_pattern f2.
Proof.
  intros f1 f2 Hneq.
  destruct f1, f2; try contradiction; simpl; discriminate.
Qed.

(** Witness: faulun <> failun patterns *)
Example foot_distinct_witness : foot_pattern Faulun <> foot_pattern Failun.
Proof. simpl. discriminate. Qed.

(** Example: mustafilun <> failatun patterns (same length, different content) *)
Example foot_distinct_example : foot_pattern Mustafilun <> foot_pattern Failatun.
Proof. simpl. discriminate. Qed.

(** Counterexample: same foot has same pattern *)
Example foot_same_pattern : foot_pattern Faulun = foot_pattern Faulun.
Proof. reflexivity. Qed.

(** ** Foot Enumeration *)

Definition all_feet : list foot :=
  [Faulun; Failun; Mafailun; Mustafilun; Failatun; Mafulatu; Mutafailun; Mufaalatun].

Lemma all_feet_complete : forall f : foot, In f all_feet.
Proof.
  intros f. destruct f; simpl.
  - left. reflexivity.
  - right. left. reflexivity.
  - right. right. left. reflexivity.
  - right. right. right. left. reflexivity.
  - right. right. right. right. left. reflexivity.
  - right. right. right. right. right. left. reflexivity.
  - right. right. right. right. right. right. left. reflexivity.
  - right. right. right. right. right. right. right. left. reflexivity.
Qed.

(** Witness: Faulun is in all_feet *)
Example all_feet_witness : In Faulun all_feet.
Proof. left. reflexivity. Qed.

(** Example: Mufaalatun (last) is in all_feet *)
Example all_feet_example : In Mufaalatun all_feet.
Proof.
  right. right. right. right. right. right. right. left. reflexivity.
Qed.

(** Counterexample: incomplete list fails completeness *)
Example all_feet_counterexample : ~ (forall f : foot, In f [Faulun; Failun]).
Proof.
  intros H. specialize (H Mafailun). simpl in H.
  destruct H as [H | [H | H]].
  - discriminate.
  - discriminate.
  - contradiction.
Qed.

(** ** Foot Count *)

Lemma all_feet_length : length all_feet = 8.
Proof. reflexivity. Qed.

(** Witness: 8 feet *)
Example all_feet_count_witness : length all_feet = 8.
Proof. reflexivity. Qed.

(** Example: not 7, not 9 *)
Example all_feet_count_example : length all_feet <> 7 /\ length all_feet <> 9.
Proof. split; discriminate. Qed.

(** Counterexample: a 7-element list has wrong count *)
Example all_feet_count_counterexample :
  length [Faulun; Failun; Mafailun; Mustafilun; Failatun; Mafulatu; Mutafailun] <> 8.
Proof. discriminate. Qed.

(** ** No Duplicate Feet *)

Lemma all_feet_nodup : NoDup all_feet.
Proof.
  unfold all_feet.
  constructor. { simpl. intros [H|[H|[H|[H|[H|[H|[H|H]]]]]]]; discriminate || contradiction. }
  constructor. { simpl. intros [H|[H|[H|[H|[H|[H|H]]]]]]; discriminate || contradiction. }
  constructor. { simpl. intros [H|[H|[H|[H|[H|H]]]]]; discriminate || contradiction. }
  constructor. { simpl. intros [H|[H|[H|[H|H]]]]; discriminate || contradiction. }
  constructor. { simpl. intros [H|[H|[H|H]]]; discriminate || contradiction. }
  constructor. { simpl. intros [H|[H|H]]; discriminate || contradiction. }
  constructor. { simpl. intros [H|H]; discriminate || contradiction. }
  constructor. { simpl. intros H; contradiction. }
  constructor.
Qed.

(** Witness: NoDup all_feet *)
Example all_feet_nodup_witness : NoDup all_feet.
Proof. exact all_feet_nodup. Qed.

(** Example: NoDup for partial list *)
Example all_feet_nodup_example : NoDup [Faulun; Failun; Mafailun].
Proof.
  constructor. { simpl. intros [H|[H|H]]; discriminate || contradiction. }
  constructor. { simpl. intros [H|H]; discriminate || contradiction. }
  constructor. { simpl. intros H; contradiction. }
  constructor.
Qed.

(** Counterexample: duplicates fail NoDup *)
Example all_feet_nodup_counterexample : ~ NoDup [Faulun; Faulun].
Proof.
  intros H. inversion H as [| x xs Hnotin Hnodup].
  apply Hnotin. left. reflexivity.
Qed.

(** ** Foot Pattern Injectivity *)

Lemma foot_pattern_injective : forall f1 f2 : foot,
  foot_pattern f1 = foot_pattern f2 -> f1 = f2.
Proof.
  intros f1 f2 H.
  destruct f1, f2; simpl in H; try reflexivity; discriminate.
Qed.

(** Witness: same pattern implies same foot *)
Example foot_pattern_injective_witness :
  foot_pattern Faulun = foot_pattern Faulun -> Faulun = Faulun.
Proof. intros _. reflexivity. Qed.

(** Example: injectivity for quadrisyllabic feet *)
Example foot_pattern_injective_example :
  foot_pattern Mafailun = foot_pattern Mafailun -> Mafailun = Mafailun.
Proof. intros _. reflexivity. Qed.

(** Counterexample: different patterns imply different feet *)
Example foot_pattern_injective_counterexample :
  foot_pattern Faulun <> foot_pattern Failun.
Proof. discriminate. Qed.

(** ** Foot Decomposition into Building Blocks *)

(** Khalil's system analyzes each foot as combinations of sabab and watad.
    To complete this decomposition, we need a primitive for a single long
    syllable. *)

Definition lone_long : pattern := [Long].

(** Extended block type for decomposition *)
Inductive block : Type :=
  | BlkSababKhafif    (* [Short] *)
  | BlkSababThaqil    (* [Short; Short] *)
  | BlkWatadMajmu     (* [Short; Long] *)
  | BlkWatadMafruq    (* [Long; Short] *)
  | BlkLong.          (* [Long] *)

Definition block_pattern (b : block) : pattern :=
  match b with
  | BlkSababKhafif => sabab_khafif
  | BlkSababThaqil => sabab_thaqil
  | BlkWatadMajmu => watad_majmu
  | BlkWatadMafruq => watad_mafruq
  | BlkLong => lone_long
  end.

(** Concatenate block patterns *)
Definition blocks_to_pattern (bs : list block) : pattern :=
  concat (map block_pattern bs).

(** Foot decompositions into building blocks *)

(** faʿūlun (u - -) = watad majmūʿ + long *)
Definition faulun_blocks : list block := [BlkWatadMajmu; BlkLong].

(** fāʿilun (- u -) = watad mafrūq + long *)
Definition failun_blocks : list block := [BlkWatadMafruq; BlkLong].

(** mafāʿīlun (u - - -) = watad majmūʿ + long + long *)
Definition mafailun_blocks : list block := [BlkWatadMajmu; BlkLong; BlkLong].

(** mustafʿilun (- - u -) = long + long + watad majmūʿ *)
Definition mustafilun_blocks : list block := [BlkLong; BlkLong; BlkWatadMajmu].

(** fāʿilātun (- u - -) = watad mafrūq + long + long *)
Definition failatun_blocks : list block := [BlkWatadMafruq; BlkLong; BlkLong].

(** mafʿūlātu (- - - u) = long + long + watad mafrūq *)
Definition mafulatu_blocks : list block := [BlkLong; BlkLong; BlkWatadMafruq].

(** mutafāʿilun (u u - u -) = sabab thaqīl + watad mafrūq + long *)
Definition mutafailun_blocks : list block := [BlkSababThaqil; BlkWatadMafruq; BlkLong].

(** mufāʿalatun (u - u u -) = watad majmūʿ + sabab thaqīl + long *)
Definition mufaalatun_blocks : list block := [BlkWatadMajmu; BlkSababThaqil; BlkLong].

(** Map foot to its block decomposition *)
Definition foot_blocks (f : foot) : list block :=
  match f with
  | Faulun => faulun_blocks
  | Failun => failun_blocks
  | Mafailun => mafailun_blocks
  | Mustafilun => mustafilun_blocks
  | Failatun => failatun_blocks
  | Mafulatu => mafulatu_blocks
  | Mutafailun => mutafailun_blocks
  | Mufaalatun => mufaalatun_blocks
  end.

(** Decomposition correctness: blocks reconstruct the pattern *)
Lemma foot_blocks_correct : forall f : foot,
  blocks_to_pattern (foot_blocks f) = foot_pattern f.
Proof.
  intros f. destruct f; reflexivity.
Qed.

(** Witness: faulun decomposes correctly *)
Example foot_blocks_witness :
  blocks_to_pattern faulun_blocks = faulun.
Proof. reflexivity. Qed.

(** Example: pentasyllabic mutafailun decomposes correctly *)
Example foot_blocks_example :
  blocks_to_pattern mutafailun_blocks = mutafailun.
Proof. reflexivity. Qed.

(** Counterexample: wrong block order gives wrong pattern *)
Example foot_blocks_counterexample :
  blocks_to_pattern [BlkLong; BlkWatadMajmu] <> faulun.
Proof. discriminate. Qed.

(** ** Foot Classification by Syllable Count *)

Definition foot_length (f : foot) : nat :=
  length (foot_pattern f).

(** Trisyllabic feet (3 syllables) *)
Definition is_trisyllabic (f : foot) : bool :=
  Nat.eqb (foot_length f) 3.

(** Quadrisyllabic feet (4 syllables) *)
Definition is_quadrisyllabic (f : foot) : bool :=
  Nat.eqb (foot_length f) 4.

(** Pentasyllabic feet (5 syllables) *)
Definition is_pentasyllabic (f : foot) : bool :=
  Nat.eqb (foot_length f) 5.

(** Foot length lemmas *)
Lemma faulun_length : foot_length Faulun = 3.
Proof. reflexivity. Qed.

Lemma failun_length : foot_length Failun = 3.
Proof. reflexivity. Qed.

Lemma mafailun_length : foot_length Mafailun = 4.
Proof. reflexivity. Qed.

Lemma mustafilun_length : foot_length Mustafilun = 4.
Proof. reflexivity. Qed.

Lemma failatun_length : foot_length Failatun = 4.
Proof. reflexivity. Qed.

Lemma mafulatu_length : foot_length Mafulatu = 4.
Proof. reflexivity. Qed.

Lemma mutafailun_length : foot_length Mutafailun = 5.
Proof. reflexivity. Qed.

Lemma mufaalatun_length : foot_length Mufaalatun = 5.
Proof. reflexivity. Qed.

(** Classification lemmas *)
Lemma trisyllabic_feet : forall f,
  is_trisyllabic f = true <-> f = Faulun \/ f = Failun.
Proof.
  intros f. unfold is_trisyllabic, foot_length. split.
  - destruct f; simpl; intros H; try discriminate.
    + left. reflexivity.
    + right. reflexivity.
  - intros [H | H]; rewrite H; reflexivity.
Qed.

Lemma quadrisyllabic_feet : forall f,
  is_quadrisyllabic f = true <-> f = Mafailun \/ f = Mustafilun \/ f = Failatun \/ f = Mafulatu.
Proof.
  intros f. unfold is_quadrisyllabic, foot_length. split.
  - destruct f; simpl; intros H; try discriminate.
    + left. reflexivity.
    + right. left. reflexivity.
    + right. right. left. reflexivity.
    + right. right. right. reflexivity.
  - intros [H | [H | [H | H]]]; rewrite H; reflexivity.
Qed.

Lemma pentasyllabic_feet : forall f,
  is_pentasyllabic f = true <-> f = Mutafailun \/ f = Mufaalatun.
Proof.
  intros f. unfold is_pentasyllabic, foot_length. split.
  - destruct f; simpl; intros H; try discriminate.
    + left. reflexivity.
    + right. reflexivity.
  - intros [H | H]; rewrite H; reflexivity.
Qed.

(** Classification counts *)
Lemma trisyllabic_count : length (filter is_trisyllabic all_feet) = 2.
Proof. reflexivity. Qed.

Lemma quadrisyllabic_count : length (filter is_quadrisyllabic all_feet) = 4.
Proof. reflexivity. Qed.

Lemma pentasyllabic_count : length (filter is_pentasyllabic all_feet) = 2.
Proof. reflexivity. Qed.

(** Witness: Faulun is trisyllabic *)
Example trisyllabic_witness : is_trisyllabic Faulun = true.
Proof. reflexivity. Qed.

(** Example: Mafailun is quadrisyllabic *)
Example quadrisyllabic_example : is_quadrisyllabic Mafailun = true.
Proof. reflexivity. Qed.

(** Counterexample: Mutafailun is not quadrisyllabic *)
Example quadrisyllabic_counterexample : is_quadrisyllabic Mutafailun = false.
Proof. reflexivity. Qed.

(** ** Pattern to Foot Function *)

(** Computable inverse of foot_pattern *)
Definition pattern_to_foot (p : pattern) : option foot :=
  if pattern_eqb p faulun then Some Faulun
  else if pattern_eqb p failun then Some Failun
  else if pattern_eqb p mafailun then Some Mafailun
  else if pattern_eqb p mustafilun then Some Mustafilun
  else if pattern_eqb p failatun then Some Failatun
  else if pattern_eqb p mafulatu then Some Mafulatu
  else if pattern_eqb p mutafailun then Some Mutafailun
  else if pattern_eqb p mufaalatun then Some Mufaalatun
  else None.

(** Correctness: pattern_to_foot is left inverse of foot_pattern *)
Lemma pattern_to_foot_correct : forall f : foot,
  pattern_to_foot (foot_pattern f) = Some f.
Proof.
  intros f. destruct f; reflexivity.
Qed.

(** Correctness: pattern_to_foot returns the unique foot *)
Lemma pattern_to_foot_unique : forall p f,
  pattern_to_foot p = Some f -> foot_pattern f = p.
Proof.
  intros p f H.
  unfold pattern_to_foot in H.
  destruct (pattern_eqb p faulun) eqn:E1.
  { injection H as Hf. subst f. simpl. symmetry. apply pattern_eqb_eq. exact E1. }
  destruct (pattern_eqb p failun) eqn:E2.
  { injection H as Hf. subst f. simpl. symmetry. apply pattern_eqb_eq. exact E2. }
  destruct (pattern_eqb p mafailun) eqn:E3.
  { injection H as Hf. subst f. simpl. symmetry. apply pattern_eqb_eq. exact E3. }
  destruct (pattern_eqb p mustafilun) eqn:E4.
  { injection H as Hf. subst f. simpl. symmetry. apply pattern_eqb_eq. exact E4. }
  destruct (pattern_eqb p failatun) eqn:E5.
  { injection H as Hf. subst f. simpl. symmetry. apply pattern_eqb_eq. exact E5. }
  destruct (pattern_eqb p mafulatu) eqn:E6.
  { injection H as Hf. subst f. simpl. symmetry. apply pattern_eqb_eq. exact E6. }
  destruct (pattern_eqb p mutafailun) eqn:E7.
  { injection H as Hf. subst f. simpl. symmetry. apply pattern_eqb_eq. exact E7. }
  destruct (pattern_eqb p mufaalatun) eqn:E8.
  { injection H as Hf. subst f. simpl. symmetry. apply pattern_eqb_eq. exact E8. }
  discriminate.
Qed.

(** None for non-foot patterns *)
Lemma pattern_to_foot_none : forall p,
  pattern_to_foot p = None <-> (forall f, foot_pattern f <> p).
Proof.
  intros p. split.
  - intros H f Hcontra.
    rewrite <- Hcontra in H. rewrite pattern_to_foot_correct in H. discriminate.
  - intros H. unfold pattern_to_foot.
    destruct (pattern_eqb p faulun) eqn:E1.
    { apply pattern_eqb_eq in E1. exfalso. apply (H Faulun). symmetry. exact E1. }
    destruct (pattern_eqb p failun) eqn:E2.
    { apply pattern_eqb_eq in E2. exfalso. apply (H Failun). symmetry. exact E2. }
    destruct (pattern_eqb p mafailun) eqn:E3.
    { apply pattern_eqb_eq in E3. exfalso. apply (H Mafailun). symmetry. exact E3. }
    destruct (pattern_eqb p mustafilun) eqn:E4.
    { apply pattern_eqb_eq in E4. exfalso. apply (H Mustafilun). symmetry. exact E4. }
    destruct (pattern_eqb p failatun) eqn:E5.
    { apply pattern_eqb_eq in E5. exfalso. apply (H Failatun). symmetry. exact E5. }
    destruct (pattern_eqb p mafulatu) eqn:E6.
    { apply pattern_eqb_eq in E6. exfalso. apply (H Mafulatu). symmetry. exact E6. }
    destruct (pattern_eqb p mutafailun) eqn:E7.
    { apply pattern_eqb_eq in E7. exfalso. apply (H Mutafailun). symmetry. exact E7. }
    destruct (pattern_eqb p mufaalatun) eqn:E8.
    { apply pattern_eqb_eq in E8. exfalso. apply (H Mufaalatun). symmetry. exact E8. }
    reflexivity.
Qed.

(** Witness: pattern_to_foot recovers Faulun *)
Example pattern_to_foot_witness : pattern_to_foot faulun = Some Faulun.
Proof. reflexivity. Qed.

(** Example: pattern_to_foot recovers Mufaalatun (last in chain) *)
Example pattern_to_foot_example : pattern_to_foot mufaalatun = Some Mufaalatun.
Proof. reflexivity. Qed.

(** Counterexample: non-foot patterns return None *)
Example pattern_to_foot_counterexample_empty : pattern_to_foot [] = None.
Proof. reflexivity. Qed.

Example pattern_to_foot_counterexample_sabab : pattern_to_foot sabab_khafif = None.
Proof. reflexivity. Qed.

Example pattern_to_foot_counterexample_arbitrary :
  pattern_to_foot [Long; Long; Long; Long; Long] = None.
Proof. reflexivity. Qed.

(** End of Section 3: The Eight Feet *)

(** * Section 4: The Sixteen Meters (Buḥūr) *)

(** The buḥūr (بحور, "seas") are the sixteen canonical meters of Arabic poetry.
    Each meter is defined by a specific sequence of feet. Khalil identified
    fifteen; the sixteenth (mutadārik) was added by his student al-Akhfash. *)

(** ** Meter Type *)

Inductive meter : Type :=
  | Tawil      (* الطويل - the long *)
  | Madid      (* المديد - the extended *)
  | Basit      (* البسيط - the simple *)
  | Wafir      (* الوافر - the abundant *)
  | Kamil      (* الكامل - the complete *)
  | Hazaj      (* الهزج - the trembling *)
  | Rajaz      (* الرجز - the tremor *)
  | Ramal      (* الرمل - the trotting *)
  | Sari       (* السريع - the swift *)
  | Munsarih   (* المنسرح - the flowing *)
  | Khafif     (* الخفيف - the light *)
  | Mudari     (* المضارع - the similar *)
  | Muqtadab   (* المقتضب - the curtailed *)
  | Mujtathth  (* المجتث - the cut off *)
  | Mutaqarib  (* المتقارب - the approaching *)
  | Mutadarik. (* المتدارك - the overtaking *)

(** ** Meter Foot Sequences *)

(** Each meter is defined by its sequence of feet in a single hemistich.
    A full line (bayt) consists of two hemistichs. *)

Definition meter_feet (m : meter) : list foot :=
  match m with
  | Tawil      => [Faulun; Mafailun; Faulun; Mafailun]
  | Madid      => [Failatun; Failun; Failatun]
  | Basit      => [Mustafilun; Failun; Mustafilun; Failun]
  | Wafir      => [Mufaalatun; Mufaalatun; Faulun]
  | Kamil      => [Mutafailun; Mutafailun; Mutafailun]
  | Hazaj      => [Mafailun; Mafailun]
  | Rajaz      => [Mustafilun; Mustafilun; Mustafilun]
  | Ramal      => [Failatun; Failatun; Failatun]
  | Sari       => [Mustafilun; Mustafilun; Mafulatu]
  | Munsarih   => [Mustafilun; Mafulatu; Mustafilun]
  | Khafif     => [Failatun; Mustafilun; Failatun]
  | Mudari     => [Mafailun; Failatun]
  | Muqtadab   => [Mafulatu; Mustafilun]
  | Mujtathth  => [Mustafilun; Failatun]
  | Mutaqarib  => [Faulun; Faulun; Faulun; Faulun]
  | Mutadarik  => [Failun; Failun; Failun; Failun]
  end.

(** ** Meter Pattern *)

(** Flatten feet to get the meter's weight pattern *)
Definition meter_pattern (m : meter) : pattern :=
  concat (map foot_pattern (meter_feet m)).

(** ** Decidable Equality for Meter *)

Definition meter_eq_dec (m1 m2 : meter) : {m1 = m2} + {m1 <> m2}.
Proof.
  destruct m1, m2; try (left; reflexivity); right; discriminate.
Defined.

(** Witness: meter_eq_dec Tawil Tawil *)
Example meter_eq_dec_witness : exists pf, meter_eq_dec Tawil Tawil = left pf.
Proof. eexists. reflexivity. Qed.

(** Example: meter_eq_dec Kamil Kamil *)
Example meter_eq_dec_example : exists pf, meter_eq_dec Kamil Kamil = left pf.
Proof. eexists. reflexivity. Qed.

(** Counterexample: meter_eq_dec returns right for different meters *)
Example meter_eq_dec_counterexample : exists pf, meter_eq_dec Tawil Basit = right pf.
Proof. eexists. reflexivity. Qed.

(** ** Meter Enumeration *)

Definition all_meters : list meter :=
  [Tawil; Madid; Basit; Wafir; Kamil; Hazaj; Rajaz; Ramal;
   Sari; Munsarih; Khafif; Mudari; Muqtadab; Mujtathth;
   Mutaqarib; Mutadarik].

Lemma all_meters_complete : forall m : meter, In m all_meters.
Proof.
  intros m. destruct m; simpl;
  repeat (try (left; reflexivity); right).
Qed.

Lemma all_meters_length : length all_meters = 16.
Proof. reflexivity. Qed.

(** Witness: Tawil in all_meters *)
Example all_meters_witness : In Tawil all_meters.
Proof. left. reflexivity. Qed.

(** Example: Mutadarik (last) in all_meters *)
Example all_meters_example : In Mutadarik all_meters.
Proof.
  unfold all_meters. simpl.
  repeat (try (left; reflexivity); right).
Qed.

(** Counterexample: incomplete list fails *)
Example all_meters_counterexample : ~ (forall m : meter, In m [Tawil; Madid]).
Proof.
  intros H. specialize (H Basit). simpl in H.
  destruct H as [H | [H | H]]; try discriminate; contradiction.
Qed.

(** ** No Duplicate Meters *)

Lemma all_meters_nodup : NoDup all_meters.
Proof.
  unfold all_meters.
  repeat (constructor; [simpl; intros H; repeat destruct H as [H | H]; try discriminate; try contradiction | ]).
  constructor.
Qed.

(** Witness: NoDup all_meters *)
Example all_meters_nodup_witness : NoDup all_meters.
Proof. exact all_meters_nodup. Qed.

(** ** Meter Pattern Lengths *)

Definition meter_syllable_count (m : meter) : nat :=
  length (meter_pattern m).

(** Syllable counts for each meter *)
Lemma tawil_syllables : meter_syllable_count Tawil = 14.
Proof. reflexivity. Qed.

Lemma madid_syllables : meter_syllable_count Madid = 11.
Proof. reflexivity. Qed.

Lemma basit_syllables : meter_syllable_count Basit = 14.
Proof. reflexivity. Qed.

Lemma wafir_syllables : meter_syllable_count Wafir = 13.
Proof. reflexivity. Qed.

Lemma kamil_syllables : meter_syllable_count Kamil = 15.
Proof. reflexivity. Qed.

Lemma hazaj_syllables : meter_syllable_count Hazaj = 8.
Proof. reflexivity. Qed.

Lemma rajaz_syllables : meter_syllable_count Rajaz = 12.
Proof. reflexivity. Qed.

Lemma ramal_syllables : meter_syllable_count Ramal = 12.
Proof. reflexivity. Qed.

Lemma sari_syllables : meter_syllable_count Sari = 12.
Proof. reflexivity. Qed.

Lemma munsarih_syllables : meter_syllable_count Munsarih = 12.
Proof. reflexivity. Qed.

Lemma khafif_syllables : meter_syllable_count Khafif = 12.
Proof. reflexivity. Qed.

Lemma mudari_syllables : meter_syllable_count Mudari = 8.
Proof. reflexivity. Qed.

Lemma muqtadab_syllables : meter_syllable_count Muqtadab = 8.
Proof. reflexivity. Qed.

Lemma mujtathth_syllables : meter_syllable_count Mujtathth = 8.
Proof. reflexivity. Qed.

Lemma mutaqarib_syllables : meter_syllable_count Mutaqarib = 12.
Proof. reflexivity. Qed.

Lemma mutadarik_syllables : meter_syllable_count Mutadarik = 12.
Proof. reflexivity. Qed.

(** ** Meter Foot Count *)

Definition meter_foot_count (m : meter) : nat :=
  length (meter_feet m).

(** Classification by foot count *)
Definition is_dimeter (m : meter) : bool :=
  Nat.eqb (meter_foot_count m) 2.

Definition is_trimeter (m : meter) : bool :=
  Nat.eqb (meter_foot_count m) 3.

Definition is_tetrameter (m : meter) : bool :=
  Nat.eqb (meter_foot_count m) 4.

Lemma dimeter_meters : forall m,
  is_dimeter m = true <-> m = Hazaj \/ m = Mudari \/ m = Muqtadab \/ m = Mujtathth.
Proof.
  intros m. unfold is_dimeter, meter_foot_count. split.
  - destruct m; simpl; intros H; try discriminate.
    + left. reflexivity.
    + right. left. reflexivity.
    + right. right. left. reflexivity.
    + right. right. right. reflexivity.
  - intros [H|[H|[H|H]]]; rewrite H; reflexivity.
Qed.

Lemma trimeter_meters : forall m,
  is_trimeter m = true <->
    m = Madid \/ m = Wafir \/ m = Kamil \/ m = Rajaz \/ m = Ramal \/
    m = Sari \/ m = Munsarih \/ m = Khafif.
Proof.
  intros m. unfold is_trimeter, meter_foot_count. split.
  - destruct m; simpl; intros H; try discriminate.
    + left. reflexivity.
    + right. left. reflexivity.
    + right. right. left. reflexivity.
    + right. right. right. left. reflexivity.
    + right. right. right. right. left. reflexivity.
    + right. right. right. right. right. left. reflexivity.
    + right. right. right. right. right. right. left. reflexivity.
    + right. right. right. right. right. right. right. reflexivity.
  - intros [H|[H|[H|[H|[H|[H|[H|H]]]]]]]; rewrite H; reflexivity.
Qed.

Lemma tetrameter_meters : forall m,
  is_tetrameter m = true <-> m = Tawil \/ m = Basit \/ m = Mutaqarib \/ m = Mutadarik.
Proof.
  intros m. unfold is_tetrameter, meter_foot_count. split.
  - destruct m; simpl; intros H; try discriminate.
    + left. reflexivity.
    + right. left. reflexivity.
    + right. right. left. reflexivity.
    + right. right. right. reflexivity.
  - intros [H|[H|[H|H]]]; rewrite H; reflexivity.
Qed.

(** Witness: Hazaj is dimeter *)
Example dimeter_witness : is_dimeter Hazaj = true.
Proof. reflexivity. Qed.

(** Example: Kamil is trimeter *)
Example trimeter_example : is_trimeter Kamil = true.
Proof. reflexivity. Qed.

(** Counterexample: Tawil is not trimeter *)
Example trimeter_counterexample : is_trimeter Tawil = false.
Proof. reflexivity. Qed.

(** ** Meter Pattern Distinctness *)

Lemma meter_patterns_distinct : forall m1 m2 : meter,
  m1 <> m2 -> meter_pattern m1 <> meter_pattern m2.
Proof.
  intros m1 m2 Hneq.
  destruct m1, m2; try contradiction; simpl; discriminate.
Qed.

(** Witness: Tawil and Basit have different patterns *)
Example meter_distinct_witness : meter_pattern Tawil <> meter_pattern Basit.
Proof. simpl. discriminate. Qed.

(** Example: Rajaz and Ramal differ (same length, different content) *)
Example meter_distinct_example : meter_pattern Rajaz <> meter_pattern Ramal.
Proof. simpl. discriminate. Qed.

(** Counterexample: same meter has same pattern *)
Example meter_same_pattern : meter_pattern Kamil = meter_pattern Kamil.
Proof. reflexivity. Qed.

(** ** Meter Recognition *)

Definition pattern_to_meter (p : pattern) : option meter :=
  if pattern_eqb p (meter_pattern Tawil) then Some Tawil
  else if pattern_eqb p (meter_pattern Madid) then Some Madid
  else if pattern_eqb p (meter_pattern Basit) then Some Basit
  else if pattern_eqb p (meter_pattern Wafir) then Some Wafir
  else if pattern_eqb p (meter_pattern Kamil) then Some Kamil
  else if pattern_eqb p (meter_pattern Hazaj) then Some Hazaj
  else if pattern_eqb p (meter_pattern Rajaz) then Some Rajaz
  else if pattern_eqb p (meter_pattern Ramal) then Some Ramal
  else if pattern_eqb p (meter_pattern Sari) then Some Sari
  else if pattern_eqb p (meter_pattern Munsarih) then Some Munsarih
  else if pattern_eqb p (meter_pattern Khafif) then Some Khafif
  else if pattern_eqb p (meter_pattern Mudari) then Some Mudari
  else if pattern_eqb p (meter_pattern Muqtadab) then Some Muqtadab
  else if pattern_eqb p (meter_pattern Mujtathth) then Some Mujtathth
  else if pattern_eqb p (meter_pattern Mutaqarib) then Some Mutaqarib
  else if pattern_eqb p (meter_pattern Mutadarik) then Some Mutadarik
  else None.

Lemma pattern_to_meter_correct : forall m : meter,
  pattern_to_meter (meter_pattern m) = Some m.
Proof.
  intros m. destruct m; reflexivity.
Qed.

(** Witness: pattern_to_meter recovers Tawil *)
Example pattern_to_meter_witness : pattern_to_meter (meter_pattern Tawil) = Some Tawil.
Proof. reflexivity. Qed.

(** Example: pattern_to_meter recovers Mutadarik (last) *)
Example pattern_to_meter_example : pattern_to_meter (meter_pattern Mutadarik) = Some Mutadarik.
Proof. reflexivity. Qed.

(** Counterexample: non-meter patterns return None *)
Example pattern_to_meter_counterexample : pattern_to_meter [] = None.
Proof. reflexivity. Qed.

(** ** Khalil's Fifteen vs. Sixteen *)

(** Khalil identified 15 meters; Mutadarik was added later *)
Definition khalil_original : list meter :=
  [Tawil; Madid; Basit; Wafir; Kamil; Hazaj; Rajaz; Ramal;
   Sari; Munsarih; Khafif; Mudari; Muqtadab; Mujtathth; Mutaqarib].

Definition is_khalil_original (m : meter) : bool :=
  match m with
  | Mutadarik => false
  | _ => true
  end.

Lemma khalil_original_length : length khalil_original = 15.
Proof. reflexivity. Qed.

Lemma mutadarik_not_khalil : is_khalil_original Mutadarik = false.
Proof. reflexivity. Qed.

Lemma others_khalil_original : forall m,
  m <> Mutadarik -> is_khalil_original m = true.
Proof.
  intros m Hneq. destruct m; try reflexivity; contradiction.
Qed.

(** Witness: Tawil is Khalil original *)
Example khalil_original_witness : is_khalil_original Tawil = true.
Proof. reflexivity. Qed.

(** Example: Mutaqarib (last Khalil original) *)
Example khalil_original_example : is_khalil_original Mutaqarib = true.
Proof. reflexivity. Qed.

(** Counterexample: Mutadarik is not Khalil original *)
Example khalil_original_counterexample : is_khalil_original Mutadarik = false.
Proof. reflexivity. Qed.

(** End of Section 4: The Sixteen Meters *)

(** * Section 5: The Five Circles (Dawāʾir) *)

(** Khalil organized the meters into five circles (dawāʾir, دوائر), each
    grouping meters by their derivational relationships. Meters in the same
    circle share a common underlying pattern that can be rotated to produce
    the different meters. *)

(** ** Circle Type *)

Inductive circle : Type :=
  | Mukhtalifa   (* المختلفة - the mixed/different *)
  | Mualifa      (* المؤتلفة - the harmonious *)
  | Mujtallaba   (* المجتلبة - the attracted *)
  | Mushtabaha   (* المشتبهة - the similar *)
  | Muttafiqa.   (* المتفقة - the agreeing *)

(** ** Circle Membership *)

Definition meter_circle (m : meter) : circle :=
  match m with
  | Tawil | Madid | Basit => Mukhtalifa
  | Wafir | Kamil => Mualifa
  | Hazaj | Rajaz | Ramal => Mujtallaba
  | Sari | Munsarih | Khafif | Mudari | Muqtadab | Mujtathth => Mushtabaha
  | Mutaqarib | Mutadarik => Muttafiqa
  end.

(** ** Circle Meters *)

Definition circle_meters (c : circle) : list meter :=
  match c with
  | Mukhtalifa => [Tawil; Madid; Basit]
  | Mualifa => [Wafir; Kamil]
  | Mujtallaba => [Hazaj; Rajaz; Ramal]
  | Mushtabaha => [Sari; Munsarih; Khafif; Mudari; Muqtadab; Mujtathth]
  | Muttafiqa => [Mutaqarib; Mutadarik]
  end.

(** ** Decidable Equality for Circle *)

Definition circle_eq_dec (c1 c2 : circle) : {c1 = c2} + {c1 <> c2}.
Proof.
  destruct c1, c2; try (left; reflexivity); right; discriminate.
Defined.

(** Witness: circle_eq_dec Mukhtalifa Mukhtalifa *)
Example circle_eq_dec_witness : exists pf, circle_eq_dec Mukhtalifa Mukhtalifa = left pf.
Proof. eexists. reflexivity. Qed.

(** Example: circle_eq_dec Muttafiqa Muttafiqa *)
Example circle_eq_dec_example : exists pf, circle_eq_dec Muttafiqa Muttafiqa = left pf.
Proof. eexists. reflexivity. Qed.

(** Counterexample: different circles *)
Example circle_eq_dec_counterexample : exists pf, circle_eq_dec Mukhtalifa Mualifa = right pf.
Proof. eexists. reflexivity. Qed.

(** ** Circle Enumeration *)

Definition all_circles : list circle :=
  [Mukhtalifa; Mualifa; Mujtallaba; Mushtabaha; Muttafiqa].

Lemma all_circles_complete : forall c : circle, In c all_circles.
Proof.
  intros c. destruct c; simpl.
  - left. reflexivity.
  - right. left. reflexivity.
  - right. right. left. reflexivity.
  - right. right. right. left. reflexivity.
  - right. right. right. right. left. reflexivity.
Qed.

Lemma all_circles_length : length all_circles = 5.
Proof. reflexivity. Qed.

(** Witness: Mukhtalifa in all_circles *)
Example all_circles_witness : In Mukhtalifa all_circles.
Proof. left. reflexivity. Qed.

(** Example: Muttafiqa (last) in all_circles *)
Example all_circles_example : In Muttafiqa all_circles.
Proof. right. right. right. right. left. reflexivity. Qed.

(** Counterexample: incomplete list fails *)
Example all_circles_counterexample : ~ (forall c : circle, In c [Mukhtalifa; Mualifa]).
Proof.
  intros H. specialize (H Mujtallaba). simpl in H.
  destruct H as [H | [H | H]]; try discriminate; contradiction.
Qed.

(** ** No Duplicate Circles *)

Lemma all_circles_nodup : NoDup all_circles.
Proof.
  unfold all_circles.
  constructor. { simpl. intros [H|[H|[H|[H|H]]]]; discriminate || contradiction. }
  constructor. { simpl. intros [H|[H|[H|H]]]; discriminate || contradiction. }
  constructor. { simpl. intros [H|[H|H]]; discriminate || contradiction. }
  constructor. { simpl. intros [H|H]; discriminate || contradiction. }
  constructor. { simpl. intros H; contradiction. }
  constructor.
Qed.

(** Witness: NoDup all_circles *)
Example all_circles_nodup_witness : NoDup all_circles.
Proof. exact all_circles_nodup. Qed.

(** ** Membership Consistency *)

Lemma meter_in_circle : forall m : meter,
  In m (circle_meters (meter_circle m)).
Proof.
  intros m. destruct m; simpl.
  - left. reflexivity.
  - right. left. reflexivity.
  - right. right. left. reflexivity.
  - left. reflexivity.
  - right. left. reflexivity.
  - left. reflexivity.
  - right. left. reflexivity.
  - right. right. left. reflexivity.
  - left. reflexivity.
  - right. left. reflexivity.
  - right. right. left. reflexivity.
  - right. right. right. left. reflexivity.
  - right. right. right. right. left. reflexivity.
  - right. right. right. right. right. left. reflexivity.
  - left. reflexivity.
  - right. left. reflexivity.
Qed.

(** Witness: Tawil in Mukhtalifa *)
Example meter_in_circle_witness : In Tawil (circle_meters Mukhtalifa).
Proof. left. reflexivity. Qed.

(** Example: Mujtathth in Mushtabaha *)
Example meter_in_circle_example : In Mujtathth (circle_meters Mushtabaha).
Proof. right. right. right. right. right. left. reflexivity. Qed.

(** Counterexample: Tawil not in Muttafiqa *)
Example meter_not_in_circle_counterexample : ~ In Tawil (circle_meters Muttafiqa).
Proof.
  simpl. intros [H | [H | H]]; try discriminate; contradiction.
Qed.

(** ** Circle Sizes *)

Lemma mukhtalifa_size : length (circle_meters Mukhtalifa) = 3.
Proof. reflexivity. Qed.

Lemma mualifa_size : length (circle_meters Mualifa) = 2.
Proof. reflexivity. Qed.

Lemma mujtallaba_size : length (circle_meters Mujtallaba) = 3.
Proof. reflexivity. Qed.

Lemma mushtabaha_size : length (circle_meters Mushtabaha) = 6.
Proof. reflexivity. Qed.

Lemma muttafiqa_size : length (circle_meters Muttafiqa) = 2.
Proof. reflexivity. Qed.

(** ** Circle Coverage *)

(** All meters belong to exactly one circle *)
Lemma circles_partition_meters :
  length (concat (map circle_meters all_circles)) = 16.
Proof. reflexivity. Qed.

(** ** Circle Recognition from Meter *)

Definition is_in_circle (m : meter) (c : circle) : bool :=
  existsb (fun m' => match meter_eq_dec m m' with left _ => true | right _ => false end)
          (circle_meters c).

Lemma is_in_circle_iff_meter_circle : forall m c,
  is_in_circle m c = true <-> meter_circle m = c.
Proof.
  intros m c. unfold is_in_circle. split.
  - destruct m, c; simpl; intros H; try reflexivity; discriminate.
  - intros H. subst c. destruct m; reflexivity.
Qed.

(** Witness: is_in_circle Tawil Mukhtalifa *)
Example is_in_circle_witness : is_in_circle Tawil Mukhtalifa = true.
Proof. reflexivity. Qed.

(** Example: is_in_circle Kamil Mualifa *)
Example is_in_circle_example : is_in_circle Kamil Mualifa = true.
Proof. reflexivity. Qed.

(** Counterexample: is_in_circle Tawil Muttafiqa *)
Example is_in_circle_counterexample : is_in_circle Tawil Muttafiqa = false.
Proof. reflexivity. Qed.

(** ** Circle Uniqueness *)

Lemma meter_circle_unique : forall m,
  forall c, In m (circle_meters c) -> c = meter_circle m.
Proof.
  intros m c H. destruct m, c; simpl in H;
  repeat (destruct H as [H|H]; try discriminate; try contradiction);
  reflexivity.
Qed.

(** Witness: uniqueness for Tawil *)
Example circle_unique_witness : forall c,
  In Tawil (circle_meters c) -> c = Mukhtalifa.
Proof.
  intros c H. rewrite (meter_circle_unique Tawil c H). reflexivity.
Qed.

(** End of Section 5: The Five Circles *)

(** * Section 6: Variation Rules (Zihāf and ʿIlla) *)

(** Arabic meters allow systematic modifications to the basic foot patterns.
    - Zihāf (زحاف): optional modifications that may occur in non-final feet
    - ʿIlla (علة): obligatory modifications at line endings *)

(** ** Variation Types *)

Inductive zihaf : Type :=
  | Khabn    (* خبن - drop second quiescent: mustafʿilun → mutafʿilun *)
  | Tayy     (* طي - drop fourth quiescent: mustafʿilun → mustaʿlun *)
  | Qabḍ     (* قبض - drop fifth quiescent: mafāʿīlun → mafāʿlun *)
  | Kaff     (* كف - drop seventh quiescent: mafāʿīlun → mafāʿīlu *)
  | Waqṣ     (* وقص - drop second: mutafāʿilun → mufāʿilun *)
  | ʿAṣb.    (* عصب - make fifth quiescent: mufāʿalatun → mufāʿaltun *)

Inductive ʿilla : Type :=
  | Qaṭʿ     (* قطع - drop final consonant of watad *)
  | Qaṣr     (* قصر - shorten final long vowel *)
  | Ḥadhf    (* حذف - drop final sabab *)
  | Tasbīgh  (* تسبيغ - add consonant to final sabab *)
  | Batr.    (* بتر - combine Ḥadhf and Qaṭʿ *)

(** ** Effect on Patterns *)

(** Khabn: Long at position 2 becomes Short *)
Definition apply_khabn (p : pattern) : option pattern :=
  match p with
  | w1 :: Long :: rest => Some (w1 :: Short :: rest)
  | _ => None
  end.

(** Qabḍ: Long at position 5 becomes Short (0-indexed: position 4) *)
Definition apply_qabḍ (p : pattern) : option pattern :=
  match p with
  | w1 :: w2 :: w3 :: w4 :: Long :: rest => Some (w1 :: w2 :: w3 :: w4 :: Short :: rest)
  | _ => None
  end.

(** Qaṣr: Final Long becomes Short *)
Fixpoint apply_qaṣr (p : pattern) : option pattern :=
  match p with
  | [] => None
  | [Long] => Some [Short]
  | [Short] => None
  | w :: rest =>
      match apply_qaṣr rest with
      | Some rest' => Some (w :: rest')
      | None => None
      end
  end.

(** Ḥadhf: Drop final sabab (last syllable) *)
Fixpoint apply_ḥadhf (p : pattern) : option pattern :=
  match p with
  | [] => None
  | [_] => Some []
  | w :: rest =>
      match apply_ḥadhf rest with
      | Some rest' => Some (w :: rest')
      | None => None
      end
  end.

(** ** Variation Validity *)

Definition is_valid_khabn_target (p : pattern) : bool :=
  match p with
  | _ :: Long :: _ => true
  | _ => false
  end.

Definition is_valid_qaṣr_target (p : pattern) : bool :=
  match p with
  | [] => false
  | _ => match last p Short with Long => true | Short => false end
  end.

(** ** Example: Khabn on Mustafilun *)

(** mustafilun = [Long; Long; Short; Long]
    After khabn: [Long; Short; Short; Long] *)
Example khabn_mustafilun :
  apply_khabn mustafilun = Some [Long; Short; Short; Long].
Proof. reflexivity. Qed.

(** Witness: khabn applies to mustafilun *)
Example khabn_witness : is_valid_khabn_target mustafilun = true.
Proof. reflexivity. Qed.

(** Example: khabn on rajaz meter's mustafilun *)
Example khabn_on_rajaz :
  apply_khabn [Long; Long; Short; Long] = Some [Long; Short; Short; Long].
Proof. reflexivity. Qed.

(** Counterexample: khabn fails when second position is Short *)
Example khabn_counterexample :
  apply_khabn failatun = None.
Proof. reflexivity. Qed.

(** ** Example: Qabḍ *)

(** Qabḍ changes position 5 (0-indexed: 4) from Long to Short *)
Example qabḍ_example :
  apply_qabḍ [Short; Long; Long; Long; Long] = Some [Short; Long; Long; Long; Short].
Proof. reflexivity. Qed.

(** Counterexample: qabḍ fails on 4-element pattern *)
Example qabḍ_counterexample : apply_qabḍ mafailun = None.
Proof. reflexivity. Qed.

(** ** Example: Qaṣr *)

(** Convert final Long to Short *)
Example qaṣr_example :
  apply_qaṣr [Short; Long; Long] = Some [Short; Long; Short].
Proof. reflexivity. Qed.

(** Counterexample: qaṣr fails when final is Short *)
Example qaṣr_counterexample :
  apply_qaṣr [Long; Short] = None.
Proof. reflexivity. Qed.

(** ** Example: Ḥadhf *)

(** Drop final syllable *)
Example ḥadhf_example :
  apply_ḥadhf [Short; Long; Long] = Some [Short; Long].
Proof. reflexivity. Qed.

Example ḥadhf_faulun :
  apply_ḥadhf faulun = Some [Short; Long].
Proof. reflexivity. Qed.

(** Counterexample: ḥadhf fails on empty *)
Example ḥadhf_counterexample : apply_ḥadhf [] = None.
Proof. reflexivity. Qed.

(** ** Variation Enumeration *)

Definition all_zihaf : list zihaf := [Khabn; Tayy; Qabḍ; Kaff; Waqṣ; ʿAṣb].
Definition all_ʿilla : list ʿilla := [Qaṭʿ; Qaṣr; Ḥadhf; Tasbīgh; Batr].

Lemma all_zihaf_complete : forall z : zihaf, In z all_zihaf.
Proof.
  intros z. destruct z; simpl.
  - left. reflexivity.
  - right. left. reflexivity.
  - right. right. left. reflexivity.
  - right. right. right. left. reflexivity.
  - right. right. right. right. left. reflexivity.
  - right. right. right. right. right. left. reflexivity.
Qed.

Lemma all_ʿilla_complete : forall i : ʿilla, In i all_ʿilla.
Proof.
  intros i. destruct i; simpl.
  - left. reflexivity.
  - right. left. reflexivity.
  - right. right. left. reflexivity.
  - right. right. right. left. reflexivity.
  - right. right. right. right. left. reflexivity.
Qed.

Lemma all_zihaf_length : length all_zihaf = 6.
Proof. reflexivity. Qed.

Lemma all_ʿilla_length : length all_ʿilla = 5.
Proof. reflexivity. Qed.

(** Witness: Khabn in all_zihaf *)
Example all_zihaf_witness : In Khabn all_zihaf.
Proof. left. reflexivity. Qed.

(** Example: Qaṣr in all_ʿilla *)
Example all_ʿilla_example : In Qaṣr all_ʿilla.
Proof. right. left. reflexivity. Qed.

(** End of Section 6: Variation Rules *)

(** * Section 7: Scansion *)

(** Scansion is the process of analyzing a verse to determine its metrical pattern.
    In a full implementation, this would involve:
    1. Phonological analysis of Arabic text
    2. Syllable boundary detection
    3. Weight assignment (open/closed syllables)
    4. Pattern matching against known meters

    Here we formalize the abstract scansion process, assuming syllable weights
    are already determined. *)

(** ** Scansion Result *)

Inductive scan_result : Type :=
  | ScanSuccess : meter -> scan_result
  | ScanVariant : meter -> scan_result  (* matches with variations *)
  | ScanFailed : scan_result.

(** ** Direct Meter Matching *)

Definition scan_exact (p : pattern) : scan_result :=
  match pattern_to_meter p with
  | Some m => ScanSuccess m
  | None => ScanFailed
  end.

(** Witness: exact match for Tawil *)
Example scan_exact_witness :
  scan_exact (meter_pattern Tawil) = ScanSuccess Tawil.
Proof. reflexivity. Qed.

(** Example: exact match for Kamil *)
Example scan_exact_example :
  scan_exact (meter_pattern Kamil) = ScanSuccess Kamil.
Proof. reflexivity. Qed.

(** Counterexample: non-meter pattern fails *)
Example scan_exact_counterexample :
  scan_exact [] = ScanFailed.
Proof. reflexivity. Qed.

(** ** Hemistich Repetition *)

(** A full line (bayt) consists of two hemistichs (shaṭr).
    This checks if a pattern is exactly two repetitions of a meter. *)

Definition is_full_line (p : pattern) (m : meter) : bool :=
  pattern_eqb p (meter_pattern m ++ meter_pattern m).

(** Witness: double Tawil is full line *)
Example full_line_witness :
  is_full_line (meter_pattern Tawil ++ meter_pattern Tawil) Tawil = true.
Proof. reflexivity. Qed.

(** Example: double Hazaj *)
Example full_line_example :
  is_full_line (meter_pattern Hazaj ++ meter_pattern Hazaj) Hazaj = true.
Proof. reflexivity. Qed.

(** Counterexample: single hemistich is not full line *)
Example full_line_counterexample :
  is_full_line (meter_pattern Tawil) Tawil = false.
Proof. reflexivity. Qed.

(** ** Pattern Prefix Matching *)

(** Check if a pattern is a prefix of a meter pattern *)
Fixpoint is_prefix (p1 p2 : pattern) : bool :=
  match p1, p2 with
  | [], _ => true
  | _, [] => false
  | w1 :: p1', w2 :: p2' =>
      weight_eqb w1 w2 && is_prefix p1' p2'
  end.

Lemma is_prefix_refl : forall p, is_prefix p p = true.
Proof.
  induction p as [|w p' IH]; simpl.
  - reflexivity.
  - rewrite IH. destruct w; reflexivity.
Qed.

Lemma is_prefix_nil : forall p, is_prefix [] p = true.
Proof. reflexivity. Qed.

(** Witness: prefix check *)
Example is_prefix_witness : is_prefix [Short; Long] [Short; Long; Long] = true.
Proof. reflexivity. Qed.

(** Example: full pattern is prefix of itself *)
Example is_prefix_example : is_prefix faulun faulun = true.
Proof. reflexivity. Qed.

(** Counterexample: longer pattern is not prefix *)
Example is_prefix_counterexample : is_prefix [Short; Long; Long] [Short; Long] = false.
Proof. reflexivity. Qed.

(** ** Candidate Meter Detection *)

(** Find all meters whose pattern starts with the given prefix *)
Definition candidate_meters (p : pattern) : list meter :=
  filter (fun m => is_prefix p (meter_pattern m)) all_meters.

(** Witness: Short-Long-Long prefix matches Tawil, Wafir, Mutaqarib *)
Example candidate_meters_witness :
  In Tawil (candidate_meters [Short; Long]).
Proof.
  unfold candidate_meters. simpl.
  left. reflexivity.
Qed.

(** Example: Long-Long prefix matches Basit, Rajaz, etc. *)
Example candidate_meters_example :
  In Basit (candidate_meters [Long; Long]).
Proof.
  unfold candidate_meters. simpl.
  left. reflexivity.
Qed.

(** Counterexample: impossible prefix has no candidates *)
Example candidate_meters_counterexample :
  candidate_meters [Short; Short; Short; Short; Short; Short; Short; Short; Short] = [].
Proof. reflexivity. Qed.

(** ** Scansion Summary *)

(** Successful scansion requires:
    1. A weight pattern derived from phonological analysis
    2. Exact or variant match against known meters
    3. Optional: identification of zihāf/ʿilla modifications *)

Definition scan_summary (p : pattern) : option meter :=
  pattern_to_meter p.

Lemma scan_summary_correct : forall m,
  scan_summary (meter_pattern m) = Some m.
Proof.
  intros m. unfold scan_summary. apply pattern_to_meter_correct.
Qed.

(** Witness: scan_summary *)
Example scan_summary_witness :
  scan_summary (meter_pattern Mutaqarib) = Some Mutaqarib.
Proof. reflexivity. Qed.

(** End of Section 7: Scansion *)

(** * Conclusion *)

(** This formalization covers Khalil ibn Ahmad al-Farahidi's aruz system:
    - Section 1: Weight foundations (Short/Long syllables)
    - Section 2: Building blocks (sabab, watad)
    - Section 3: The eight tafāʿīl (feet) with decomposition
    - Section 4: The sixteen buḥūr (meters)
    - Section 5: The five dawāʾir (circles)
    - Section 6: Variation rules (zihāf, ʿilla)
    - Section 7: Scansion framework

    The original system dates to c. 760 CE and forms the foundation of
    Arabic, Persian, Turkish, Kurdish, and Urdu prosody. *)
