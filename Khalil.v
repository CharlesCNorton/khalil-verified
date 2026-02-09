(******************************************************************************)
(*                                                                            *)
(*                    Khalil's Aruz: The Science of Prosody                   *)
(*                                                                            *)
(*     The original Arabic quantitative meter system devised by Khalil ibn    *)
(*     Ahmad al-Farahidi (c. 718-786 CE). Formalizes Khalil's 15 meters      *)
(*     (plus al-Akhfash's 16th), syllable weight, and the tent-pole          *)
(*     terminology.                                                           *)
(*                                                                            *)
(*     "The origin of 'aruz is the tent-pole; the verse is a tent."           *)
(*     - Khalil ibn Ahmad al-Farahidi, c. 760 CE                              *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: February 6, 2026                                                 *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

(** Table of Contents:
    - Section  1: Foundations (Short/Long syllables)
    - Section  2: Letter-level structure (mutaḥarrik/sākin)
    - Section  3: Building blocks (sabab, watad)
    - Section  4: The eight tafāʿīl (feet) with decomposition
    - Section  5: The sixteen buḥūr (meters)
    - Section  6: The five dawāʾir (circles) with rotation
    - Section  7: Variation rules (zihāf, ʿilla)
    - Section  8: Foot positions and variation scope
    - Section  9: Legal variation rules per meter
    - Section 10: Scansion framework with variant detection
    - Section 11: Rhyme (qāfiya) structure
    - Section 12: Poem (qaṣīda) structure *)

Require Import List Lia Bool Arith.
Require Import Coq.Classes.DecidableClass.
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

(** Reflection: weight_eqb decides equality *)
Lemma weight_eqb_reflect : forall w1 w2, Bool.reflect (w1 = w2) (weight_eqb w1 w2).
Proof.
  intros w1 w2. destruct (weight_eqb w1 w2) eqn:E.
  - apply ReflectT. apply weight_eqb_eq. exact E.
  - apply ReflectF. intros H. subst. destruct w2; discriminate.
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

(** Reflection: pattern_eqb decides equality *)
Lemma pattern_eqb_reflect : forall p1 p2, Bool.reflect (p1 = p2) (pattern_eqb p1 p2).
Proof.
  intros p1 p2. destruct (pattern_eqb p1 p2) eqn:E.
  - apply ReflectT. apply pattern_eqb_eq. exact E.
  - apply ReflectF. intros H. subst.
    rewrite (proj2 (pattern_eqb_eq p2 p2) eq_refl) in E. discriminate.
Qed.

(** ** Standard-library decidable equality instances *)

#[export] Instance weight_eq_decidable (w1 w2 : weight) : Decidable (w1 = w2) := {
  Decidable_witness := weight_eqb w1 w2 ;
  Decidable_spec := weight_eqb_eq w1 w2
}.

#[export] Instance pattern_eq_decidable (p1 p2 : pattern) : Decidable (p1 = p2) := {
  Decidable_witness := pattern_eqb p1 p2 ;
  Decidable_spec := pattern_eqb_eq p1 p2
}.

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

(** ** Mora Count *)

(** In Khalil's system, Short = 1 mora (light), Long = 2 morae (heavy). *)

Definition weight_morae (w : weight) : nat :=
  match w with
  | Short => 1
  | Long => 2
  end.

Fixpoint pattern_morae (p : pattern) : nat :=
  match p with
  | [] => 0
  | w :: rest => weight_morae w + pattern_morae rest
  end.

Example pattern_morae_example : pattern_morae [Short; Long; Long] = 5.
Proof. reflexivity. Qed.

Example pattern_morae_empty : pattern_morae [] = 0.
Proof. reflexivity. Qed.

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

(** * Section 2: Letter-Level Structure *)

(** In Khalil's system, variation rules (zihāf) operate on individual
    letters (ḥurūf) within a foot's mnemonic word, not on syllables
    directly. Each letter is either:
    - Mutaḥarrik (moving): a consonant bearing a short vowel
    - Sākin (quiescent): a consonant with no vowel, or a long vowel
      extension (alif, wāw, yāʾ of madd)

    A Short syllable = one mutaḥarrik (Cv)
    A Long syllable = one mutaḥarrik + one sākin (CvC or CvV)

    Khalil's variation rules reference letter positions by number.
    For example, khabn "drops the second quiescent" — meaning the
    second sākin letter in the foot's mnemonic. *)

(** ** Letter Type *)

Inductive letter : Type :=
  | Mutaharrik : letter   (* moving: consonant + short vowel *)
  | Sakin : letter.       (* quiescent: no vowel / long vowel extension *)

(** ** Decidable Equality for Letter *)

Definition letter_eq_dec (l1 l2 : letter) : {l1 = l2} + {l1 <> l2}.
Proof.
  destruct l1, l2.
  - left. reflexivity.
  - right. discriminate.
  - right. discriminate.
  - left. reflexivity.
Defined.

(** ** Letter Sequence *)

Definition letter_seq := list letter.

(** ** Syllable to Letters *)

(** A Short syllable is one mutaḥarrik letter (Cv).
    A Long syllable is one mutaḥarrik followed by one sākin (CvC or CvV). *)

Definition syllable_to_letters (w : weight) : letter_seq :=
  match w with
  | Short => [Mutaharrik]
  | Long => [Mutaharrik; Sakin]
  end.

(** ** Pattern to Letters *)

Fixpoint pattern_to_letters (p : pattern) : letter_seq :=
  match p with
  | [] => []
  | w :: rest => syllable_to_letters w ++ pattern_to_letters rest
  end.

(** ** Letters to Pattern *)

(** Recover syllable weights from a letter sequence: each mutaḥarrik
    followed by sākin is Long; a mutaḥarrik followed by another
    mutaḥarrik (or at end) is Short. Returns None on orphan sākin. *)

Fixpoint letters_to_pattern (ls : letter_seq) : option pattern :=
  match ls with
  | [] => Some []
  | Mutaharrik :: Sakin :: rest =>
      match letters_to_pattern rest with
      | Some p => Some (Long :: p)
      | None => None
      end
  | Mutaharrik :: rest =>
      match letters_to_pattern rest with
      | Some p => Some (Short :: p)
      | None => None
      end
  | Sakin :: _ => None
  end.

(** ** Round-trip correctness *)

Lemma pattern_to_letters_hd : forall p l ls,
  pattern_to_letters p = l :: ls -> l = Mutaharrik.
Proof.
  intros p l ls H. destruct p as [|w p'].
  - simpl in H. discriminate.
  - destruct w; simpl in H; injection H as H1 _; symmetry; exact H1.
Qed.

(** ** Well-Formed Letter Sequences *)

(** A well-formed letter sequence has no orphan sākin: every sākin is
    immediately preceded by a mutaḥarrik. Equivalently, no sākin appears
    at the start or immediately after another sākin. *)

Fixpoint wf_letter_seq (ls : letter_seq) : bool :=
  match ls with
  | [] => true
  | Sakin :: _ => false
  | Mutaharrik :: Sakin :: rest => wf_letter_seq rest
  | Mutaharrik :: rest => wf_letter_seq rest
  end.

(** pattern_to_letters always produces well-formed letter sequences. *)
Lemma pattern_to_letters_wf : forall p : pattern,
  wf_letter_seq (pattern_to_letters p) = true.
Proof.
  induction p as [|w p' IH].
  - reflexivity.
  - destruct w; simpl.
    + (* Short: emits [Mutaharrik] ++ rest *)
      destruct (pattern_to_letters p') as [|l ls] eqn:E.
      * simpl. reflexivity.
      * assert (Hl : l = Mutaharrik).
        { exact (pattern_to_letters_hd _ _ _ E). }
        subst l. simpl. exact IH.
    + (* Long: emits [Mutaharrik; Sakin] ++ rest *)
      exact IH.
Qed.

Lemma pattern_letters_roundtrip : forall p : pattern,
  letters_to_pattern (pattern_to_letters p) = Some p.
Proof.
  induction p as [|w p' IH].
  - reflexivity.
  - destruct w.
    + (* Short *)
      change (pattern_to_letters (Short :: p'))
        with (Mutaharrik :: pattern_to_letters p').
      destruct (pattern_to_letters p') as [|l ls] eqn:E.
      * (* pattern_to_letters p' = [] → IH: Some [] = Some p' *)
        simpl. simpl in IH. injection IH as IH'. subst p'. reflexivity.
      * (* pattern_to_letters p' = l :: ls → IH: letters_to_pattern (l :: ls) = Some p' *)
        assert (Hl : l = Mutaharrik) by (exact (pattern_to_letters_hd _ _ _ E)).
        subst l.
        change (letters_to_pattern (Mutaharrik :: Mutaharrik :: ls))
          with (match letters_to_pattern (Mutaharrik :: ls) with
                | Some p => Some (Short :: p)
                | None => None
                end).
        rewrite IH. reflexivity.
    + (* Long *)
      change (pattern_to_letters (Long :: p'))
        with (Mutaharrik :: Sakin :: pattern_to_letters p').
      simpl. rewrite IH. reflexivity.
Qed.

(** ** Well-formedness characterizes convertibility *)

(** One-step unfolding lemmas for letters_to_pattern. *)

Lemma letters_to_pattern_cons_M_M : forall ls,
  letters_to_pattern (Mutaharrik :: Mutaharrik :: ls) =
  match letters_to_pattern (Mutaharrik :: ls) with
  | Some p => Some (Short :: p) | None => None end.
Proof. reflexivity. Qed.

Lemma letters_to_pattern_cons_M_S : forall ls,
  letters_to_pattern (Mutaharrik :: Sakin :: ls) =
  match letters_to_pattern ls with
  | Some p => Some (Long :: p) | None => None end.
Proof. reflexivity. Qed.

(** Forward: well-formed letter sequences convert successfully.
    Uses strong induction on length because the M::S::rest case
    decreases by 2, beyond standard structural induction. *)

Lemma wf_letter_seq_implies_some_aux : forall n ls,
  length ls <= n ->
  wf_letter_seq ls = true -> exists p, letters_to_pattern ls = Some p.
Proof.
  induction n as [|n IH]; intros ls Hlen H.
  - destruct ls; [exists []; reflexivity | simpl in Hlen; lia].
  - destruct ls as [|[] ls'].
    + exists []. reflexivity.
    + destruct ls' as [|[] ls''].
      * exists [Short]. reflexivity.
      * (* Mutaharrik :: Mutaharrik :: ls'' *)
        rewrite letters_to_pattern_cons_M_M. simpl in H.
        assert (Hlen' : length (Mutaharrik :: ls'') <= n) by (simpl in Hlen |- *; lia).
        destruct (IH _ Hlen' H) as [p Hp]. rewrite Hp. eexists. reflexivity.
      * (* Mutaharrik :: Sakin :: ls'' *)
        rewrite letters_to_pattern_cons_M_S. simpl in H.
        assert (Hlen' : length ls'' <= n) by (simpl in Hlen; lia).
        destruct (IH _ Hlen' H) as [p Hp]. rewrite Hp. eexists. reflexivity.
    + simpl in H. discriminate.
Qed.

Lemma wf_letter_seq_implies_some : forall ls,
  wf_letter_seq ls = true -> exists p, letters_to_pattern ls = Some p.
Proof.
  intros ls. apply (wf_letter_seq_implies_some_aux (length ls)). lia.
Qed.

(** Backward: successful conversion implies well-formedness. *)

Lemma some_implies_wf_letter_seq_aux : forall n ls p,
  length ls <= n ->
  letters_to_pattern ls = Some p -> wf_letter_seq ls = true.
Proof.
  induction n as [|n IH]; intros ls p Hlen H.
  - destruct ls; [reflexivity | simpl in Hlen; lia].
  - destruct ls as [|[] ls'].
    + reflexivity.
    + destruct ls' as [|[] ls''].
      * reflexivity.
      * (* Mutaharrik :: Mutaharrik :: ls'' *)
        rewrite letters_to_pattern_cons_M_M in H. simpl.
        destruct (letters_to_pattern (Mutaharrik :: ls'')) as [q|] eqn:E; [|discriminate].
        assert (Hlen' : length (Mutaharrik :: ls'') <= n) by (simpl in Hlen |- *; lia).
        exact (IH _ q Hlen' E).
      * (* Mutaharrik :: Sakin :: ls'' *)
        rewrite letters_to_pattern_cons_M_S in H. simpl.
        destruct (letters_to_pattern ls'') as [q|] eqn:E; [|discriminate].
        assert (Hlen' : length ls'' <= n) by (simpl in Hlen; lia).
        exact (IH _ q Hlen' E).
    + simpl in H. discriminate.
Qed.

Lemma some_implies_wf_letter_seq : forall ls p,
  letters_to_pattern ls = Some p -> wf_letter_seq ls = true.
Proof.
  intros ls p. apply (some_implies_wf_letter_seq_aux (length ls)). lia.
Qed.

(** wf_letter_seq decides exactly which letter sequences are
    convertible to syllable patterns. Checking wf_letter_seq before
    letters_to_pattern guarantees success; failure of letters_to_pattern
    after a wf_letter_seq=true check is impossible. *)

Theorem wf_letter_seq_iff_convertible : forall ls,
  wf_letter_seq ls = true <-> exists p, letters_to_pattern ls = Some p.
Proof.
  intros ls. split.
  - apply wf_letter_seq_implies_some.
  - intros [p Hp]. exact (some_implies_wf_letter_seq ls p Hp).
Qed.

(** ** Hardened Letter-to-Pattern Conversion *)

(** A richer error type distinguishes "variation precondition not met"
    (the operation is inapplicable) from "variation produced a malformed
    letter sequence" (a bug in the variation function). *)

Inductive conversion_result : Type :=
  | ConvOk : pattern -> conversion_result
  | ConvPreconditionFailed : conversion_result
  | ConvMalformedOutput : conversion_result.

(** Guarded conversion: checks wf_letter_seq before attempting
    letters_to_pattern, so a malformed output is reported distinctly. *)

Definition letters_to_pattern_guarded (ls : letter_seq) : conversion_result :=
  if wf_letter_seq ls then
    match letters_to_pattern ls with
    | Some p => ConvOk p
    | None => ConvMalformedOutput  (* should be impossible by wf_letter_seq_iff_convertible *)
    end
  else
    ConvMalformedOutput.

(** A well-formed input always succeeds via guarded conversion. *)
Lemma letters_to_pattern_guarded_wf : forall ls p,
  wf_letter_seq ls = true ->
  letters_to_pattern ls = Some p ->
  letters_to_pattern_guarded ls = ConvOk p.
Proof.
  intros ls p Hwf Hconv. unfold letters_to_pattern_guarded.
  rewrite Hwf, Hconv. reflexivity.
Qed.

(** Safe variation wrapper: given a variation function that operates on
    letters, checks that the input is well-formed (precondition), applies
    the variation, then checks that the output is well-formed (postcondition).
    Returns ConvPreconditionFailed if the operation returns None,
    ConvMalformedOutput if the result is ill-formed. *)

Definition safe_apply_variation
  (vary : letter_seq -> option letter_seq)
  (p : pattern) : conversion_result :=
  let ls := pattern_to_letters p in
  match vary ls with
  | None => ConvPreconditionFailed
  | Some ls' =>
      if wf_letter_seq ls' then
        match letters_to_pattern ls' with
        | Some p' => ConvOk p'
        | None => ConvMalformedOutput
        end
      else
        ConvMalformedOutput
  end.

(** The input to safe_apply_variation is always well-formed. *)
Lemma safe_apply_input_wf : forall p,
  wf_letter_seq (pattern_to_letters p) = true.
Proof.
  exact pattern_to_letters_wf.
Qed.

(** If safe_apply_variation returns ConvOk, the result round-trips. *)
Lemma safe_apply_ok_sound : forall vary p p',
  safe_apply_variation vary p = ConvOk p' ->
  exists ls', vary (pattern_to_letters p) = Some ls' /\
              letters_to_pattern ls' = Some p'.
Proof.
  intros vary p p' H. unfold safe_apply_variation in H.
  destruct (vary (pattern_to_letters p)) as [ls'|] eqn:Ev;
    [|discriminate].
  destruct (wf_letter_seq ls') eqn:Ewf; [|discriminate].
  destruct (letters_to_pattern ls') as [q|] eqn:Ec; [|discriminate].
  exists ls'. inversion H. subst q. auto.
Qed.

(** ** Letter-level position helpers *)

(** Find the nth sākin letter's index in a letter sequence (0-indexed). *)

Fixpoint nth_sakin_pos (n : nat) (ls : letter_seq) (idx : nat) : option nat :=
  match ls with
  | [] => None
  | Sakin :: rest =>
      match n with
      | 0 => Some idx
      | S n' => nth_sakin_pos n' rest (S idx)
      end
  | _ :: rest => nth_sakin_pos n rest (S idx)
  end.

(** Find the nth mutaḥarrik letter's index in a letter sequence (0-indexed). *)

Fixpoint nth_mutaharrik_pos (n : nat) (ls : letter_seq) (idx : nat) : option nat :=
  match ls with
  | [] => None
  | Mutaharrik :: rest =>
      match n with
      | 0 => Some idx
      | S n' => nth_mutaharrik_pos n' rest (S idx)
      end
  | _ :: rest => nth_mutaharrik_pos n rest (S idx)
  end.

(** Delete letter at a given index *)

Fixpoint delete_at (n : nat) (ls : letter_seq) : letter_seq :=
  match ls, n with
  | [], _ => []
  | _ :: rest, 0 => rest
  | l :: rest, S n' => l :: delete_at n' rest
  end.

(** Replace letter at a given index *)

Fixpoint replace_at (n : nat) (new_l : letter) (ls : letter_seq) : letter_seq :=
  match ls, n with
  | [], _ => []
  | _ :: rest, 0 => new_l :: rest
  | l :: rest, S n' => l :: replace_at n' new_l rest
  end.

(** Insert letter at a given index *)

Fixpoint insert_at (n : nat) (new_l : letter) (ls : letter_seq) : letter_seq :=
  match ls, n with
  | _, 0 => new_l :: ls
  | [], _ => [new_l]
  | l :: rest, S n' => l :: insert_at n' new_l rest
  end.

(** ** General sākin-deletion preserves syllable count *)

(** Prepending a mutaḥarrik to a non-empty well-formed letter sequence
    whose letters_to_pattern gives Some q yields Some (Short :: q). *)
Lemma prepend_M_short : forall ls q,
  wf_letter_seq ls = true ->
  letters_to_pattern ls = Some q ->
  ls <> [] ->
  letters_to_pattern (Mutaharrik :: ls) = Some (Short :: q).
Proof.
  intros ls q Hwf Hconv Hne.
  destruct ls as [|l ls']; [contradiction|].
  destruct l.
  - rewrite letters_to_pattern_cons_M_M. rewrite Hconv. reflexivity.
  - simpl in Hwf. discriminate.
Qed.

(** Deleting a sākin from the letter representation of any pattern
    produces a pattern of the same length. Every sākin in a well-formed
    letter sequence is preceded by a mutaḥarrik (forming a Long syllable);
    deleting the sākin turns that Long into Short, preserving count. *)
Lemma delete_sakin_preserves_count : forall p i,
  nth_error (pattern_to_letters p) i = Some Sakin ->
  exists p', letters_to_pattern (delete_at i (pattern_to_letters p)) = Some p' /\
             length p' = length p.
Proof.
  induction p as [|w p_tail IH]; intros i Hi.
  - simpl in Hi. destruct i; discriminate.
  - destruct w.
    + (* Short: pattern_to_letters = M :: pattern_to_letters p_tail *)
      change (pattern_to_letters (Short :: p_tail))
        with (Mutaharrik :: pattern_to_letters p_tail) in *.
      destruct i as [|i'].
      * simpl in Hi. discriminate.
      * simpl in Hi.
        destruct (IH i' Hi) as [q [Hq Hqlen]].
        assert (Hwf : wf_letter_seq (delete_at i' (pattern_to_letters p_tail)) = true).
        { exact (some_implies_wf_letter_seq _ q Hq). }
        assert (Hne : delete_at i' (pattern_to_letters p_tail) <> []).
        { intro Hempty. rewrite Hempty in Hq. simpl in Hq. injection Hq as <-.
          simpl in Hqlen. symmetry in Hqlen.
          apply length_zero_iff_nil in Hqlen. subst p_tail.
          simpl in Hi. destruct i'; discriminate. }
        assert (Hpre : letters_to_pattern
          (Mutaharrik :: delete_at i' (pattern_to_letters p_tail)) = Some (Short :: q)).
        { exact (prepend_M_short _ q Hwf Hq Hne). }
        change (delete_at (S i') (Mutaharrik :: pattern_to_letters p_tail))
          with (Mutaharrik :: delete_at i' (pattern_to_letters p_tail)).
        exists (Short :: q). split. exact Hpre. simpl. lia.
    + (* Long: pattern_to_letters = M :: S :: pattern_to_letters p_tail *)
      change (pattern_to_letters (Long :: p_tail))
        with (Mutaharrik :: Sakin :: pattern_to_letters p_tail) in *.
      destruct i as [|i'].
      * simpl in Hi. discriminate.
      * destruct i' as [|i''].
        -- (* i = 1: deleting the S in this Long syllable *)
           change (delete_at 1 (Mutaharrik :: Sakin :: pattern_to_letters p_tail))
             with (Mutaharrik :: pattern_to_letters p_tail).
           assert (Hwf_pt : wf_letter_seq (pattern_to_letters p_tail) = true)
             by (apply pattern_to_letters_wf).
           assert (Hrt : letters_to_pattern (pattern_to_letters p_tail) = Some p_tail)
             by (apply pattern_letters_roundtrip).
           destruct (pattern_to_letters p_tail) as [|l ls'] eqn:Ept.
           ++ simpl. exists [Short]. split. reflexivity.
              destruct p_tail; [reflexivity | simpl in Ept; destruct w; discriminate].
           ++ assert (Hl : l = Mutaharrik) by (exact (pattern_to_letters_hd _ _ _ Ept)).
              subst l.
              rewrite letters_to_pattern_cons_M_M. rewrite Hrt.
              exists (Short :: p_tail). split. reflexivity. reflexivity.
        -- (* i >= 2: sākin is in p_tail's letters *)
           change (nth_error (Mutaharrik :: Sakin :: pattern_to_letters p_tail) (S (S i'')))
             with (nth_error (pattern_to_letters p_tail) i'') in Hi.
           destruct (IH i'' Hi) as [q [Hq Hqlen]].
           change (delete_at (S (S i'')) (Mutaharrik :: Sakin :: pattern_to_letters p_tail))
             with (Mutaharrik :: Sakin :: delete_at i'' (pattern_to_letters p_tail)).
           rewrite letters_to_pattern_cons_M_S. rewrite Hq.
           exists (Long :: q). split. reflexivity. simpl. lia.
Qed.

(** Deleting a sākin reduces mora count by exactly 1 (Long → Short = -1 mora). *)
Lemma delete_sakin_reduces_morae : forall p i,
  nth_error (pattern_to_letters p) i = Some Sakin ->
  exists p', letters_to_pattern (delete_at i (pattern_to_letters p)) = Some p' /\
             S (pattern_morae p') = pattern_morae p.
Proof.
  induction p as [|w p_tail IH]; intros i Hi.
  - simpl in Hi. destruct i; discriminate.
  - destruct w.
    + (* Short *)
      change (pattern_to_letters (Short :: p_tail))
        with (Mutaharrik :: pattern_to_letters p_tail) in *.
      destruct i as [|i'].
      * simpl in Hi. discriminate.
      * simpl in Hi.
        destruct (IH i' Hi) as [q [Hq Hqmor]].
        assert (Hwf : wf_letter_seq (delete_at i' (pattern_to_letters p_tail)) = true).
        { exact (some_implies_wf_letter_seq _ q Hq). }
        assert (Hne : delete_at i' (pattern_to_letters p_tail) <> []).
        { intro Hempty. rewrite Hempty in Hq. simpl in Hq. injection Hq as Hq'.
          subst q.
          destruct (delete_sakin_preserves_count p_tail i' Hi) as [q2 [Hq2 Hq2len]].
          rewrite Hempty in Hq2. simpl in Hq2. injection Hq2 as <-.
          simpl in Hq2len. symmetry in Hq2len.
          apply length_zero_iff_nil in Hq2len. subst p_tail.
          simpl in Hi. destruct i'; discriminate. }
        assert (Hpre : letters_to_pattern
          (Mutaharrik :: delete_at i' (pattern_to_letters p_tail)) = Some (Short :: q)).
        { exact (prepend_M_short _ q Hwf Hq Hne). }
        change (delete_at (S i') (Mutaharrik :: pattern_to_letters p_tail))
          with (Mutaharrik :: delete_at i' (pattern_to_letters p_tail)).
        exists (Short :: q). split. exact Hpre. simpl. lia.
    + (* Long *)
      change (pattern_to_letters (Long :: p_tail))
        with (Mutaharrik :: Sakin :: pattern_to_letters p_tail) in *.
      destruct i as [|i'].
      * simpl in Hi. discriminate.
      * destruct i' as [|i''].
        -- (* i = 1: deleting the S in this Long syllable *)
           change (delete_at 1 (Mutaharrik :: Sakin :: pattern_to_letters p_tail))
             with (Mutaharrik :: pattern_to_letters p_tail).
           assert (Hrt : letters_to_pattern (pattern_to_letters p_tail) = Some p_tail)
             by (apply pattern_letters_roundtrip).
           destruct (pattern_to_letters p_tail) as [|l ls'] eqn:Ept.
           ++ simpl. exists [Short]. split. reflexivity.
              destruct p_tail; [simpl; reflexivity | simpl in Ept; destruct w; discriminate].
           ++ assert (Hl : l = Mutaharrik) by (exact (pattern_to_letters_hd _ _ _ Ept)).
              subst l.
              rewrite letters_to_pattern_cons_M_M. rewrite Hrt.
              exists (Short :: p_tail). split. reflexivity. simpl. lia.
        -- (* i >= 2 *)
           change (nth_error (Mutaharrik :: Sakin :: pattern_to_letters p_tail) (S (S i'')))
             with (nth_error (pattern_to_letters p_tail) i'') in Hi.
           destruct (IH i'' Hi) as [q [Hq Hqmor]].
           change (delete_at (S (S i'')) (Mutaharrik :: Sakin :: pattern_to_letters p_tail))
             with (Mutaharrik :: Sakin :: delete_at i'' (pattern_to_letters p_tail)).
           rewrite letters_to_pattern_cons_M_S. rewrite Hq.
           exists (Long :: q). split. reflexivity. simpl. lia.
Qed.

(** End of Section 2: Letter-Level Structure *)

(** * Section 3: Building Blocks *)

(** In Khalil's terminology, syllable sequences are built from two primitives:
    - Sabab (سبب, "cord" or "guy-rope"): short sequences
    - Watad (وتد, "peg" or "tent-pole"): the structural core *)

(** ** Sabab Types *)

(** Sabab khafīf (light cord): a single long syllable *)
Definition sabab_khafif : pattern := [Long].

(** Sabab thaqīl (heavy cord): two short syllables *)
Definition sabab_thaqil : pattern := [Short; Short].

(** Sabab recognition *)
Definition is_sabab_khafif (p : pattern) : bool :=
  pattern_eqb p sabab_khafif.

Definition is_sabab_thaqil (p : pattern) : bool :=
  pattern_eqb p sabab_thaqil.

Definition is_sabab (p : pattern) : bool :=
  is_sabab_khafif p || is_sabab_thaqil p.

(** Witness: sabab_khafif is [Long] *)
Example sabab_khafif_witness : sabab_khafif = [Long].
Proof. reflexivity. Qed.

(** Example: is_sabab_khafif recognizes [Long] *)
Example is_sabab_khafif_example : is_sabab_khafif [Long] = true.
Proof. reflexivity. Qed.

(** Counterexample: is_sabab_khafif rejects other patterns *)
Example is_sabab_khafif_counterexample_short : is_sabab_khafif [Short] = false.
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

(** Witness: [Long] is sabab, not watad *)
Example sabab_not_watad_witness : is_sabab [Long] = true /\ is_watad [Long] = false.
Proof. split; reflexivity. Qed.

(** Example: [Short; Short] is sabab, not watad *)
Example sabab_not_watad_example : is_sabab [Short; Short] = true /\ is_watad [Short; Short] = false.
Proof. split; reflexivity. Qed.

(** Counterexample: [Short; Long] is watad, not sabab *)
Example watad_not_sabab_counterexample : is_watad [Short; Long] = true /\ is_sabab [Short; Long] = false.
Proof. split; reflexivity. Qed.

(** Converse: watad implies not sabab *)
Lemma watad_not_sabab : forall p, is_watad p = true -> is_sabab p = false.
Proof.
  intros p H. unfold is_sabab, is_watad in *.
  unfold is_sabab_khafif, is_sabab_thaqil, is_watad_majmu, is_watad_mafruq in *.
  apply Bool.orb_true_iff in H. destruct H as [H | H].
  - apply pattern_eqb_eq in H. rewrite H. reflexivity.
  - apply pattern_eqb_eq in H. rewrite H. reflexivity.
Qed.

(** Witness: [Short; Long] is watad, not sabab *)
Example watad_not_sabab_witness : is_watad [Short; Long] = true /\ is_sabab [Short; Long] = false.
Proof. split; reflexivity. Qed.

(** Example: [Long; Short] is watad, not sabab *)
Example watad_not_sabab_example : is_watad [Long; Short] = true /\ is_sabab [Long; Short] = false.
Proof. split; reflexivity. Qed.

(** Counterexample: [Long] is sabab, not watad *)
Example sabab_not_watad_counterexample2 : is_sabab [Long] = true /\ is_watad [Long] = false.
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

(** Witness: all_watad contains watad_majmu *)
Example all_watad_witness : In watad_majmu all_watad.
Proof. left. reflexivity. Qed.

(** Example: all_watad contains watad_mafruq *)
Example all_watad_example : In watad_mafruq all_watad.
Proof. right. left. reflexivity. Qed.

(** Counterexample: incomplete watad list fails completeness *)
Example all_watad_counterexample : ~ (forall p, is_watad p = true -> In p [watad_majmu]).
Proof.
  intros H. specialize (H watad_mafruq).
  assert (Hw : is_watad watad_mafruq = true) by reflexivity.
  specialize (H Hw). simpl in H. destruct H as [H | H].
  - unfold watad_mafruq, watad_majmu in H. discriminate.
  - contradiction.
Qed.

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

(** Witness: NoDup all_watad *)
Example all_watad_nodup_witness : NoDup all_watad.
Proof. exact all_watad_nodup. Qed.

(** Example: NoDup all_watad *)
Example all_watad_nodup_example : NoDup all_watad.
Proof. exact all_watad_nodup. Qed.

(** Counterexample: duplicate watad list fails NoDup *)
Example all_watad_nodup_counterexample : ~ NoDup [watad_majmu; watad_majmu].
Proof.
  intros H. inversion H as [| x xs Hnotin Hnodup].
  apply Hnotin. left. reflexivity.
Qed.

(** Counterexample: list with duplicates fails NoDup *)
Example building_blocks_nodup_counterexample : ~ NoDup [sabab_khafif; sabab_khafif].
Proof.
  intros H. inversion H as [| x xs Hnotin Hnodup].
  apply Hnotin. left. reflexivity.
Qed.

(** End of Section 3: Building Blocks *)

(** * Section 4: The Eight Feet (Tafāʿīl) *)

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

(** Khalil's system analyzes each foot as combinations of sabab and watad. *)

(** Block type for decomposition *)
Inductive block : Type :=
  | BlkSababKhafif    (* [Long] *)
  | BlkSababThaqil    (* [Short; Short] *)
  | BlkWatadMajmu     (* [Short; Long] *)
  | BlkWatadMafruq.   (* [Long; Short] *)

(** ** Decidable Equality for Block *)

Definition block_eq_dec (b1 b2 : block) : {b1 = b2} + {b1 <> b2}.
Proof.
  destruct b1, b2; try (left; reflexivity); right; discriminate.
Defined.

(** Witness: block_eq_dec BlkSababKhafif BlkSababKhafif *)
Example block_eq_dec_witness : exists pf, block_eq_dec BlkSababKhafif BlkSababKhafif = left pf.
Proof. eexists. reflexivity. Qed.

(** Example: block_eq_dec BlkWatadMajmu BlkWatadMajmu *)
Example block_eq_dec_example : exists pf, block_eq_dec BlkWatadMajmu BlkWatadMajmu = left pf.
Proof. eexists. reflexivity. Qed.

(** Counterexample: block_eq_dec returns right for different blocks *)
Example block_eq_dec_counterexample : exists pf, block_eq_dec BlkSababKhafif BlkWatadMajmu = right pf.
Proof. eexists. reflexivity. Qed.

Definition block_pattern (b : block) : pattern :=
  match b with
  | BlkSababKhafif => sabab_khafif
  | BlkSababThaqil => sabab_thaqil
  | BlkWatadMajmu => watad_majmu
  | BlkWatadMafruq => watad_mafruq
  end.

(** Concatenate block patterns *)
Definition blocks_to_pattern (bs : list block) : pattern :=
  concat (map block_pattern bs).

(** Foot decompositions into building blocks *)

(** faʿūlun (u - -) = watad majmūʿ + sabab khafīf *)
Definition faulun_blocks : list block := [BlkWatadMajmu; BlkSababKhafif].

(** fāʿilun (- u -) = watad mafrūq + sabab khafīf *)
Definition failun_blocks : list block := [BlkWatadMafruq; BlkSababKhafif].

(** mafāʿīlun (u - - -) = watad majmūʿ + sabab khafīf + sabab khafīf *)
Definition mafailun_blocks : list block := [BlkWatadMajmu; BlkSababKhafif; BlkSababKhafif].

(** mustafʿilun (- - u -) = sabab khafīf + sabab khafīf + watad majmūʿ *)
Definition mustafilun_blocks : list block := [BlkSababKhafif; BlkSababKhafif; BlkWatadMajmu].

(** fāʿilātun (- u - -) = watad mafrūq + sabab khafīf + sabab khafīf *)
Definition failatun_blocks : list block := [BlkWatadMafruq; BlkSababKhafif; BlkSababKhafif].

(** mafʿūlātu (- - - u) = sabab khafīf + sabab khafīf + watad mafrūq *)
Definition mafulatu_blocks : list block := [BlkSababKhafif; BlkSababKhafif; BlkWatadMafruq].

(** mutafāʿilun (u u - u -) = sabab thaqīl + sabab khafīf + watad majmūʿ *)
Definition mutafailun_blocks : list block := [BlkSababThaqil; BlkSababKhafif; BlkWatadMajmu].

(** mufāʿalatun (u - u u -) = watad majmūʿ + sabab thaqīl + sabab khafīf *)
Definition mufaalatun_blocks : list block := [BlkWatadMajmu; BlkSababThaqil; BlkSababKhafif].

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
  blocks_to_pattern [BlkSababKhafif; BlkWatadMajmu] <> faulun.
Proof. discriminate. Qed.

(** ** Non-Uniqueness of Foot Block Decomposition *)

(** Block decomposition is NOT unique: two distinct block lists can
    reconstruct the same foot pattern. The traditional decomposition
    is fixed by convention (sabab/watad boundary placement), not by
    mathematical uniqueness. *)

Example foot_blocks_not_unique :
  let alt := [BlkSababKhafif; BlkWatadMafruq; BlkSababKhafif] in
  blocks_to_pattern alt = mustafilun /\
  alt <> mustafilun_blocks.
Proof.
  split.
  - reflexivity.
  - discriminate.
Qed.

(** Witness: the standard decomposition reconstructs correctly *)
Example foot_blocks_unique_witness :
  blocks_to_pattern mustafilun_blocks = mustafilun.
Proof. reflexivity. Qed.

(** Example: the alternative also reconstructs correctly *)
Example foot_blocks_unique_example :
  blocks_to_pattern [BlkSababKhafif; BlkWatadMafruq; BlkSababKhafif] = mustafilun.
Proof. reflexivity. Qed.

(** Counterexample: the two decompositions are distinct *)
Example foot_blocks_unique_counterexample :
  [BlkSababKhafif; BlkWatadMafruq; BlkSababKhafif] <> mustafilun_blocks.
Proof. discriminate. Qed.

(** ** Canonical Decomposition *)

(** Khalil's convention: the canonical decomposition of each foot is the
    one given by foot_blocks. The watad placement follows the traditional
    analysis of each foot's mnemonic word.
    We define block-list boolean equality and use it to check canonicity. *)

Fixpoint block_list_eqb (l1 l2 : list block) : bool :=
  match l1, l2 with
  | [], [] => true
  | b1 :: r1, b2 :: r2 =>
      match block_eq_dec b1 b2 with
      | left _ => block_list_eqb r1 r2
      | right _ => false
      end
  | _, _ => false
  end.

Lemma block_list_eqb_eq : forall l1 l2,
  block_list_eqb l1 l2 = true <-> l1 = l2.
Proof.
  induction l1 as [|b1 r1 IH]; destruct l2 as [|b2 r2]; simpl.
  - split; reflexivity.
  - split; discriminate.
  - split; discriminate.
  - destruct (block_eq_dec b1 b2) as [->|Hneq].
    + rewrite IH. split.
      * intros H. rewrite H. reflexivity.
      * intros H. injection H as H2. exact H2.
    + split.
      * discriminate.
      * intros H. injection H as H1. contradiction.
Qed.

Definition is_canonical_decomposition (f : foot) (bs : list block) : bool :=
  block_list_eqb bs (foot_blocks f).

(** The canonical decomposition is always canonical. *)
Lemma canonical_is_canonical : forall f,
  is_canonical_decomposition f (foot_blocks f) = true.
Proof.
  intros f. unfold is_canonical_decomposition.
  apply block_list_eqb_eq. reflexivity.
Qed.

(** The canonical decomposition is unique: it equals foot_blocks. *)
Lemma canonical_decomposition_unique : forall f bs,
  is_canonical_decomposition f bs = true -> bs = foot_blocks f.
Proof.
  intros f bs H. unfold is_canonical_decomposition in H.
  apply block_list_eqb_eq. exact H.
Qed.

(** Witness: faulun canonical decomposition *)
Example canonical_witness :
  is_canonical_decomposition Faulun faulun_blocks = true.
Proof. reflexivity. Qed.

(** Example: mustafilun canonical decomposition *)
Example canonical_example :
  is_canonical_decomposition Mustafilun mustafilun_blocks = true.
Proof. reflexivity. Qed.

(** Counterexample: alternative mustafilun decomposition is not canonical *)
Example canonical_counterexample :
  is_canonical_decomposition Mustafilun
    [BlkSababKhafif; BlkWatadMafruq; BlkSababKhafif] = false.
Proof. reflexivity. Qed.

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

(** Witness: trisyllabic foot length *)
Example foot_length_witness_tri : foot_length Faulun = 3.
Proof. reflexivity. Qed.

(** Witness: quadrisyllabic foot length *)
Example foot_length_witness_quad : foot_length Mafailun = 4.
Proof. reflexivity. Qed.

(** Witness: pentasyllabic foot length *)
Example foot_length_witness_penta : foot_length Mutafailun = 5.
Proof. reflexivity. Qed.

(** Example: all feet in the same class have the same length *)
Example foot_length_example_tri : foot_length Faulun = foot_length Failun.
Proof. reflexivity. Qed.

Example foot_length_example_quad :
  foot_length Mafailun = foot_length Mustafilun /\
  foot_length Mustafilun = foot_length Failatun /\
  foot_length Failatun = foot_length Mafulatu.
Proof. repeat split; reflexivity. Qed.

Example foot_length_example_penta : foot_length Mutafailun = foot_length Mufaalatun.
Proof. reflexivity. Qed.

(** Counterexample: feet of different classes have different lengths *)
Example foot_length_counterexample_tri_quad : foot_length Faulun <> foot_length Mafailun.
Proof. discriminate. Qed.

Example foot_length_counterexample_quad_penta : foot_length Mafailun <> foot_length Mutafailun.
Proof. discriminate. Qed.

Example foot_length_counterexample_tri_penta : foot_length Faulun <> foot_length Mutafailun.
Proof. discriminate. Qed.

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

(** Example: Failun is also trisyllabic *)
Example trisyllabic_example : is_trisyllabic Failun = true.
Proof. reflexivity. Qed.

(** Counterexample: Mafailun is not trisyllabic *)
Example trisyllabic_counterexample : is_trisyllabic Mafailun = false.
Proof. reflexivity. Qed.

(** Witness: Mafailun is quadrisyllabic *)
Example quadrisyllabic_witness : is_quadrisyllabic Mafailun = true.
Proof. reflexivity. Qed.

(** Example: Mafulatu is also quadrisyllabic *)
Example quadrisyllabic_example : is_quadrisyllabic Mafulatu = true.
Proof. reflexivity. Qed.

(** Counterexample: Mutafailun is not quadrisyllabic *)
Example quadrisyllabic_counterexample : is_quadrisyllabic Mutafailun = false.
Proof. reflexivity. Qed.

(** Witness: Mutafailun is pentasyllabic *)
Example pentasyllabic_witness : is_pentasyllabic Mutafailun = true.
Proof. reflexivity. Qed.

(** Example: Mufaalatun is also pentasyllabic *)
Example pentasyllabic_example : is_pentasyllabic Mufaalatun = true.
Proof. reflexivity. Qed.

(** Counterexample: Faulun is not pentasyllabic *)
Example pentasyllabic_counterexample : is_pentasyllabic Faulun = false.
Proof. reflexivity. Qed.

(** Witness: 2 trisyllabic feet *)
Example trisyllabic_count_witness : length (filter is_trisyllabic all_feet) = 2.
Proof. reflexivity. Qed.

(** Example: 4 quadrisyllabic feet *)
Example quadrisyllabic_count_example : length (filter is_quadrisyllabic all_feet) = 4.
Proof. reflexivity. Qed.

(** Counterexample: count is not 3 for any class *)
Example classification_count_counterexample :
  length (filter is_trisyllabic all_feet) <> 3 /\
  length (filter is_quadrisyllabic all_feet) <> 3 /\
  length (filter is_pentasyllabic all_feet) <> 3.
Proof. repeat split; discriminate. Qed.

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

(** Witness: pattern_to_foot_unique — faulun maps back *)
Example pattern_to_foot_unique_witness :
  foot_pattern Faulun = faulun.
Proof. reflexivity. Qed.

(** Example: pattern_to_foot_unique — mufaalatun maps back *)
Example pattern_to_foot_unique_example :
  foot_pattern Mufaalatun = mufaalatun.
Proof. reflexivity. Qed.

(** Counterexample: pattern_to_foot_unique — wrong foot gives wrong pattern *)
Example pattern_to_foot_unique_counterexample :
  foot_pattern Failun <> faulun.
Proof. discriminate. Qed.

(** Witness: pattern_to_foot_none — empty pattern has no foot *)
Example pattern_to_foot_none_witness :
  pattern_to_foot [] = None /\ (forall f, foot_pattern f <> []).
Proof.
  split.
  - reflexivity.
  - intros f. destruct f; discriminate.
Qed.

(** Example: pattern_to_foot_none — sabab has no foot *)
Example pattern_to_foot_none_example :
  pattern_to_foot sabab_thaqil = None.
Proof. reflexivity. Qed.

(** Counterexample: a foot pattern is NOT None *)
Example pattern_to_foot_none_counterexample :
  pattern_to_foot faulun <> None.
Proof. discriminate. Qed.

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

(** ** Foot Letter Sequences *)

(** Letter-level representations of the eight feet. *)

(** faʿūlun = fa + ʿū + lun = Cv + CvV + CvC = M + M S + M S *)
Definition faulun_letters : letter_seq :=
  pattern_to_letters faulun.

(** fāʿilun = fā + ʿi + lun = CvV + Cv + CvC = M S + M + M S *)
Definition failun_letters : letter_seq :=
  pattern_to_letters failun.

(** mafāʿīlun = ma + fā + ʿī + lun = Cv + CvV + CvV + CvC *)
Definition mafailun_letters : letter_seq :=
  pattern_to_letters mafailun.

(** mustafʿilun = mus + taf + ʿi + lun = CvC + CvC + Cv + CvC *)
Definition mustafilun_letters : letter_seq :=
  pattern_to_letters mustafilun.

(** fāʿilātun = fā + ʿi + lā + tun = CvV + Cv + CvV + CvC *)
Definition failatun_letters : letter_seq :=
  pattern_to_letters failatun.

(** mafʿūlātu = maf + ʿū + lā + tu = CvC + CvV + CvV + Cv *)
Definition mafulatu_letters : letter_seq :=
  pattern_to_letters mafulatu.

(** mutafāʿilun = mu + ta + fā + ʿi + lun = Cv + Cv + CvV + Cv + CvC *)
Definition mutafailun_letters : letter_seq :=
  pattern_to_letters mutafailun.

(** mufāʿalatun = mu + fā + ʿa + la + tun = Cv + CvV + Cv + Cv + CvC *)
Definition mufaalatun_letters : letter_seq :=
  pattern_to_letters mufaalatun.

(** Witness: faulun has 5 letters *)
Example faulun_letters_witness : length faulun_letters = 5.
Proof. reflexivity. Qed.

(** Example: mustafilun has 7 letters *)
Example mustafilun_letters_example : length mustafilun_letters = 7.
Proof. reflexivity. Qed.

(** Counterexample: mutafailun has 7 letters, not 5 (syllables != letters) *)
Example mutafailun_letters_counterexample : length mutafailun_letters <> 5.
Proof. discriminate. Qed.

(** Witness: round-trip on faulun *)
Example faulun_roundtrip_witness :
  letters_to_pattern faulun_letters = Some faulun.
Proof. reflexivity. Qed.

(** Example: round-trip on mutafailun *)
Example mutafailun_roundtrip_example :
  letters_to_pattern mutafailun_letters = Some mutafailun.
Proof. reflexivity. Qed.

(** Counterexample: orphan sākin returns None *)
Example letters_roundtrip_counterexample :
  letters_to_pattern [Sakin; Sakin] = None.
Proof. reflexivity. Qed.

(** ** Sākin Position Witnesses *)

(** In mustafilun (M S M S M M S), the 2nd sākin (0-indexed: 1) is at index 3. *)
Example mustafilun_sakin_pos_witness :
  nth_sakin_pos 1 mustafilun_letters 0 = Some 3.
Proof. reflexivity. Qed.

(** In mafailun (M M S M S M S), the 1st sākin (0-indexed: 0) is at index 2. *)
Example mafailun_sakin_pos_example :
  nth_sakin_pos 0 mafailun_letters 0 = Some 2.
Proof. reflexivity. Qed.

(** Counterexample: asking for 10th sākin in a short foot returns None *)
Example sakin_pos_counterexample :
  nth_sakin_pos 10 faulun_letters 0 = None.
Proof. reflexivity. Qed.

(** ** Full Pattern Space *)

(** Generate all weight patterns of a given length. *)

Fixpoint all_patterns (n : nat) : list pattern :=
  match n with
  | 0 => [[]]
  | S n' =>
      let ps := all_patterns n' in
      map (cons Short) ps ++ map (cons Long) ps
  end.

(** Total pattern space for foot-length patterns (3, 4, or 5 syllables). *)
Definition foot_length_patterns : list pattern :=
  all_patterns 3 ++ all_patterns 4 ++ all_patterns 5.

(** The space has exactly 56 = 8 + 16 + 32 patterns. *)
Lemma all_patterns_3_length : length (all_patterns 3) = 8.
Proof. reflexivity. Qed.

Lemma all_patterns_4_length : length (all_patterns 4) = 16.
Proof. reflexivity. Qed.

Lemma all_patterns_5_length : length (all_patterns 5) = 32.
Proof. reflexivity. Qed.

Lemma foot_length_patterns_count : length foot_length_patterns = 56.
Proof. reflexivity. Qed.

(** All 8 canonical feet are in this space. *)
Lemma feet_in_pattern_space : forall f : foot,
  In (foot_pattern f) foot_length_patterns.
Proof.
  intros f. destruct f; simpl;
  unfold foot_length_patterns, all_patterns;
  simpl; repeat (try (left; reflexivity); right).
Qed.

(** Khalil selected 8 of the 56 possible patterns. *)
Lemma khalil_selection_ratio :
  length (map foot_pattern all_feet) = 8 /\
  length foot_length_patterns = 56.
Proof. split; reflexivity. Qed.

(** Exactly 8 of the 56 foot-length patterns are recognized as feet. *)
Lemma foot_recognition_count :
  length (filter is_foot foot_length_patterns) = 8.
Proof. reflexivity. Qed.

(** End of Section 4: The Eight Feet *)

(** * Section 5: The Sixteen Meters (Buḥūr) *)

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

(** Witness: 16 meters *)
Example all_meters_length_witness : length all_meters = 16.
Proof. reflexivity. Qed.

(** Example: not 15 (Khalil's original count) *)
Example all_meters_length_example : length all_meters <> 15.
Proof. discriminate. Qed.

(** Counterexample: a 15-element list has wrong count *)
Example all_meters_length_counterexample :
  length [Tawil; Madid; Basit; Wafir; Kamil; Hazaj; Rajaz; Ramal;
          Sari; Munsarih; Khafif; Mudari; Muqtadab; Mujtathth; Mutaqarib] <> 16.
Proof. discriminate. Qed.

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

(** Example: NoDup for partial meter list *)
Example all_meters_nodup_example : NoDup [Tawil; Madid; Basit].
Proof.
  constructor. { simpl. intros [H|[H|H]]; discriminate || contradiction. }
  constructor. { simpl. intros [H|H]; discriminate || contradiction. }
  constructor. { simpl. intros H; contradiction. }
  constructor.
Qed.

(** Counterexample: duplicates fail NoDup *)
Example all_meters_nodup_counterexample : ~ NoDup [Tawil; Tawil].
Proof.
  intros H. inversion H as [| x xs Hnotin Hnodup].
  apply Hnotin. left. reflexivity.
Qed.

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

(** Witness: shortest meter (Hazaj, 8 syllables) *)
Example meter_syllable_witness : meter_syllable_count Hazaj = 8.
Proof. reflexivity. Qed.

(** Example: longest meter (Kamil, 15 syllables) *)
Example meter_syllable_example : meter_syllable_count Kamil = 15.
Proof. reflexivity. Qed.

(** Counterexample: same syllable count does not imply same meter *)
Example meter_syllable_counterexample :
  meter_syllable_count Rajaz = meter_syllable_count Ramal /\
  Rajaz <> Ramal.
Proof. split. reflexivity. discriminate. Qed.

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

(** Example: Mujtathth is also dimeter *)
Example dimeter_example : is_dimeter Mujtathth = true.
Proof. reflexivity. Qed.

(** Counterexample: Kamil is not dimeter *)
Example dimeter_counterexample : is_dimeter Kamil = false.
Proof. reflexivity. Qed.

(** Witness: Madid is trimeter *)
Example trimeter_witness : is_trimeter Madid = true.
Proof. reflexivity. Qed.

(** Example: Kamil is trimeter *)
Example trimeter_example : is_trimeter Kamil = true.
Proof. reflexivity. Qed.

(** Counterexample: Tawil is not trimeter *)
Example trimeter_counterexample : is_trimeter Tawil = false.
Proof. reflexivity. Qed.

(** Witness: Tawil is tetrameter *)
Example tetrameter_witness : is_tetrameter Tawil = true.
Proof. reflexivity. Qed.

(** Example: Mutadarik is also tetrameter *)
Example tetrameter_example : is_tetrameter Mutadarik = true.
Proof. reflexivity. Qed.

(** Counterexample: Hazaj is not tetrameter *)
Example tetrameter_counterexample : is_tetrameter Hazaj = false.
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

(** Witness: 15 original meters *)
Example khalil_original_length_witness : length khalil_original = 15.
Proof. reflexivity. Qed.

(** Example: not 16 (the total including al-Akhfash's addition) *)
Example khalil_original_length_example : length khalil_original <> 16.
Proof. discriminate. Qed.

(** Counterexample: the full list has 16, not 15 *)
Example khalil_original_length_counterexample : length all_meters <> 15.
Proof. discriminate. Qed.

Lemma mutadarik_not_khalil : is_khalil_original Mutadarik = false.
Proof. reflexivity. Qed.

(** Witness: Mutadarik is the only non-Khalil meter *)
Example mutadarik_not_khalil_witness : is_khalil_original Mutadarik = false.
Proof. reflexivity. Qed.

(** Example: Tawil IS Khalil original *)
Example mutadarik_not_khalil_example : is_khalil_original Tawil = true.
Proof. reflexivity. Qed.

(** Counterexample: Mutaqarib (close in name) IS Khalil original *)
Example mutadarik_not_khalil_counterexample : is_khalil_original Mutaqarib = true.
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

(** End of Section 5: The Sixteen Meters *)

(** * Section 6: The Five Circles (Dawāʾir) *)

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

(** Example: NoDup for partial circle list *)
Example all_circles_nodup_example : NoDup [Mukhtalifa; Mualifa].
Proof.
  constructor. { simpl. intros [H|H]; discriminate || contradiction. }
  constructor. { simpl. intros H; contradiction. }
  constructor.
Qed.

(** Counterexample: duplicate circles fail NoDup *)
Example all_circles_nodup_counterexample : ~ NoDup [Mukhtalifa; Mukhtalifa].
Proof.
  intros H. inversion H as [| x xs Hnotin Hnodup].
  apply Hnotin. left. reflexivity.
Qed.

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

(** Witness: Mushtabaha is the largest circle (6 meters) *)
Example circle_size_witness : length (circle_meters Mushtabaha) = 6.
Proof. reflexivity. Qed.

(** Example: Mualifa and Muttafiqa are the smallest (2 meters each) *)
Example circle_size_example :
  length (circle_meters Mualifa) = 2 /\
  length (circle_meters Muttafiqa) = 2.
Proof. split; reflexivity. Qed.

(** Counterexample: no circle has exactly 5 meters *)
Example circle_size_counterexample :
  length (circle_meters Mukhtalifa) <> 5 /\
  length (circle_meters Mualifa) <> 5 /\
  length (circle_meters Mujtallaba) <> 5 /\
  length (circle_meters Mushtabaha) <> 5 /\
  length (circle_meters Muttafiqa) <> 5.
Proof. repeat split; discriminate. Qed.

(** ** Circle Coverage *)

(** All meters belong to exactly one circle *)
Lemma circles_partition_meters :
  length (concat (map circle_meters all_circles)) = 16.
Proof. reflexivity. Qed.

(** Witness: partition totals to 16 *)
Example circles_partition_witness :
  length (concat (map circle_meters all_circles)) = 16.
Proof. reflexivity. Qed.

(** Example: circle sizes sum to 16 *)
Example circles_partition_example :
  length (circle_meters Mukhtalifa) +
  length (circle_meters Mualifa) +
  length (circle_meters Mujtallaba) +
  length (circle_meters Mushtabaha) +
  length (circle_meters Muttafiqa) = 16.
Proof. reflexivity. Qed.

(** Counterexample: partition does not total to 15 *)
Example circles_partition_counterexample :
  length (concat (map circle_meters all_circles)) <> 15.
Proof. discriminate. Qed.

(** No meter appears in two circles' lists *)
Lemma circles_partition_nodup :
  NoDup (concat (map circle_meters all_circles)).
Proof.
  unfold all_circles. simpl.
  repeat (constructor;
    [simpl; intros H;
     repeat destruct H as [H | H]; try discriminate; try contradiction
    | ]).
  constructor.
Qed.

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

(** Example: uniqueness for Mutadarik *)
Example circle_unique_example : forall c,
  In Mutadarik (circle_meters c) -> c = Muttafiqa.
Proof.
  intros c H. rewrite (meter_circle_unique Mutadarik c H). reflexivity.
Qed.

(** Counterexample: Tawil is not in Muttafiqa *)
Example circle_unique_counterexample : ~ In Tawil (circle_meters Muttafiqa).
Proof.
  simpl. intros [H | [H | H]]; try discriminate; contradiction.
Qed.

(** ** Circle Rotation Property *)

(** Khalil's key insight: meters in the same circle arise from cyclic
    rotation of a common underlying pattern. He literally drew the meters
    as circles and read them off at different starting points. *)

Definition rotate (n : nat) (p : pattern) : pattern :=
  skipn n p ++ firstn n p.

(** *** Rotation Algebra *)

(** Rotation by 0 is the identity. *)
Lemma rotate_0 : forall p, rotate 0 p = p.
Proof.
  intros p. unfold rotate. simpl. apply app_nil_r.
Qed.

(** Rotation by the length of the list is the identity. *)
Lemma rotate_length : forall p, rotate (length p) p = p.
Proof.
  intros p. unfold rotate.
  rewrite skipn_all, firstn_all. reflexivity.
Qed.

(** Rotation preserves length. *)
Lemma rotate_length_preserved : forall n p,
  length (rotate n p) = length p.
Proof.
  intros n p. unfold rotate.
  rewrite app_length, skipn_length, firstn_length.
  lia.
Qed.

(** Witness: rotate 0 on faulun *)
Example rotate_0_witness : rotate 0 faulun = faulun.
Proof. reflexivity. Qed.

(** Example: rotate by length on mafailun *)
Example rotate_length_example : rotate 4 mafailun = mafailun.
Proof. reflexivity. Qed.

(** Counterexample: rotate 1 is not identity on faulun *)
Example rotate_not_identity : rotate 1 faulun <> faulun.
Proof. discriminate. Qed.

(** Rotation composition: rotate m after rotate n = rotate (n + m),
    when (n + m) <= length p. *)
Lemma skipn_skipn : forall {A : Type} (n m : nat) (l : list A),
  skipn m (skipn n l) = skipn (n + m) l.
Proof.
  intros A n. induction n as [|n' IH]; intros m l.
  - reflexivity.
  - destruct l as [|a l'].
    + simpl. rewrite skipn_nil. destruct (n' + m); reflexivity.
    + simpl. exact (IH m l').
Qed.

Lemma firstn_skipn_comm : forall {A : Type} (n m : nat) (l : list A),
  n + m <= length l ->
  firstn n l ++ firstn m (skipn n l) = firstn (n + m) l.
Proof.
  intros A n. induction n as [|n' IH]; intros m l Hle.
  - reflexivity.
  - destruct l as [|a l']; simpl in Hle; try lia.
    simpl. f_equal. apply IH. lia.
Qed.

Lemma skipn_app_le : forall {A : Type} (n : nat) (l1 l2 : list A),
  n <= length l1 ->
  skipn n (l1 ++ l2) = skipn n l1 ++ l2.
Proof.
  intros A n. induction n as [|n' IH]; intros l1 l2 Hle.
  - reflexivity.
  - destruct l1 as [|a l1']; simpl in Hle; try lia.
    simpl. apply IH. lia.
Qed.

Lemma firstn_app_le : forall {A : Type} (n : nat) (l1 l2 : list A),
  n <= length l1 ->
  firstn n (l1 ++ l2) = firstn n l1.
Proof.
  intros A n. induction n as [|n' IH]; intros l1 l2 Hle.
  - reflexivity.
  - destruct l1 as [|a l1']; simpl in Hle; try lia.
    simpl. f_equal. apply IH. lia.
Qed.

Lemma rotate_add : forall (n m : nat) (p : pattern),
  n <= length p -> n + m <= length p ->
  rotate m (rotate n p) = rotate (n + m) p.
Proof.
  intros n m p Hn Hnm. unfold rotate.
  rewrite skipn_app_le by (rewrite skipn_length; lia).
  rewrite firstn_app_le by (rewrite skipn_length; lia).
  rewrite skipn_skipn.
  rewrite <- app_assoc.
  f_equal.
  apply firstn_skipn_comm. exact Hnm.
Qed.

(** Rotation by complement restores the original. *)
Lemma rotate_complement : forall n p,
  n <= length p ->
  rotate (length p - n) (rotate n p) = p.
Proof.
  intros n p Hn.
  rewrite rotate_add by lia.
  replace (n + (length p - n)) with (length p) by lia.
  apply rotate_length.
Qed.

(** Mod helper: when a < b and c > 0, (a + 1 * c) mod c = a. *)
Lemma mod_add_once : forall a c,
  c > 0 -> a < c -> (a + c) mod c = a.
Proof.
  intros a c Hc Ha.
  replace (a + c) with (a + 1 * c) by lia.
  rewrite Nat.Div0.mod_add.
  apply Nat.mod_small. lia.
Qed.

(** Full mod composition: rotate m after rotate n equals rotate ((n+m) mod length p). *)
Lemma rotate_add_mod : forall n m p,
  length p > 0 -> n <= length p -> m <= length p ->
  rotate m (rotate n p) = rotate ((n + m) mod length p) p.
Proof.
  intros n m p Hpos Hn Hm.
  destruct (Nat.le_gt_cases (n + m) (length p)) as [Hle|Hgt].
  - (* n + m <= length p: use rotate_add *)
    rewrite rotate_add by assumption.
    destruct (Nat.eq_dec (n + m) (length p)) as [Heq|Hneq].
    + rewrite Heq, Nat.mod_same by lia.
      rewrite rotate_length. symmetry. apply rotate_0.
    + rewrite Nat.mod_small by lia. reflexivity.
  - (* n + m > length p: factor through complement *)
    destruct (Nat.eq_dec (n + m) (2 * length p)) as [He2|Hne2].
    + (* n = m = length p: both sides are p *)
      assert (n = length p) by lia.
      assert (m = length p) by lia.
      subst n m.
      rewrite rotate_length.
      rewrite rotate_length.
      replace (length p + length p) with (2 * length p) by lia.
      rewrite Nat.Div0.mod_mul.
      symmetry. apply rotate_0.
    + set (k := n + m - length p).
      assert (Hk: k < length p) by (unfold k; lia).
      assert (Hm_split: m = (length p - n) + k) by (unfold k; lia).
      assert (Hmod: (n + m) mod length p = k).
      { assert (Hnm_eq: n + m = k + length p) by (unfold k; lia).
        rewrite Hnm_eq. apply mod_add_once; lia. }
      rewrite Hmod. rewrite Hm_split.
      (* rotate (length p - n + k) (rotate n p) = rotate k p *)
      rewrite <- (rotate_add (length p - n) k (rotate n p))
        by (rewrite rotate_length_preserved; unfold k; lia).
      rewrite rotate_complement by assumption.
      reflexivity.
Qed.

(** Witness: rotation preserves length *)
Example rotate_length_witness :
  length (rotate 2 mafailun) = length mafailun.
Proof. reflexivity. Qed.

(** *** Muttafiqa Circle: Full Meter Rotation *)

(** Mutadarik is Mutaqarib rotated by 2 syllables. *)
Lemma muttafiqa_rotation :
  rotate 2 (meter_pattern Mutaqarib) = meter_pattern Mutadarik.
Proof. reflexivity. Qed.

(** *** Foot-Level Rotations *)

(** The feet used in each circle are cyclic rotations of a base foot. *)

(** Mujtallaba circle: mafailun rotated gives all four quadrisyllabic feet. *)
Lemma mujtallaba_rotation_mafulatu :
  rotate 1 mafailun = mafulatu.
Proof. reflexivity. Qed.

Lemma mujtallaba_rotation_mustafilun :
  rotate 2 mafailun = mustafilun.
Proof. reflexivity. Qed.

Lemma mujtallaba_rotation_failatun :
  rotate 3 mafailun = failatun.
Proof. reflexivity. Qed.

(** Mualifa circle: mufaalatun rotated gives mutafailun. *)
Lemma mualifa_rotation :
  rotate 2 mufaalatun = mutafailun.
Proof. reflexivity. Qed.

(** Mukhtalifa circle: faulun rotated gives failun. *)
Lemma mukhtalifa_rotation_tri :
  rotate 2 faulun = failun.
Proof. reflexivity. Qed.

(** Mukhtalifa circle: mafailun rotated gives the other quadrisyllabic feet. *)
Lemma mukhtalifa_rotation_mustafilun :
  rotate 2 mafailun = mustafilun.
Proof. reflexivity. Qed.

Lemma mukhtalifa_rotation_failatun :
  rotate 3 mafailun = failatun.
Proof. reflexivity. Qed.

(** Witness: Mutadarik is Mutaqarib rotated by 2 *)
Example rotation_witness :
  rotate 2 (meter_pattern Mutaqarib) = meter_pattern Mutadarik.
Proof. reflexivity. Qed.

(** Example: all Mujtallaba feet are rotations of mafailun *)
Example rotation_example :
  rotate 1 mafailun = mafulatu /\
  rotate 2 mafailun = mustafilun /\
  rotate 3 mafailun = failatun.
Proof. repeat split; reflexivity. Qed.

(** Counterexample: rotation by wrong amount does not give a valid foot *)
Example rotation_counterexample :
  rotate 1 faulun <> failun.
Proof. discriminate. Qed.

(** *** Circle Closure: Rotation Generates Exactly the Circle's Feet *)

(** For each circle, we define a generator foot and prove that rotating it
    by all valid offsets yields exactly the circle's foot set. *)

(** Muttafiqa: faulun generates {faulun, failun} *)
Lemma muttafiqa_foot_closure :
  rotate 0 faulun = faulun /\
  rotate 2 faulun = failun /\
  rotate 1 faulun <> faulun /\
  rotate 1 faulun <> failun.
Proof. repeat split; try reflexivity; discriminate. Qed.

(** Mujtallaba: mafailun generates {mafailun, mafulatu, mustafilun, failatun} *)
Lemma mujtallaba_foot_closure :
  rotate 0 mafailun = mafailun /\
  rotate 1 mafailun = mafulatu /\
  rotate 2 mafailun = mustafilun /\
  rotate 3 mafailun = failatun.
Proof. repeat split; reflexivity. Qed.

(** Mualifa: mufaalatun generates {mufaalatun, mutafailun} *)
Lemma mualifa_foot_closure :
  rotate 0 mufaalatun = mufaalatun /\
  rotate 2 mufaalatun = mutafailun.
Proof. repeat split; reflexivity. Qed.

(** *** Rotation Exhaustion: No Other Offsets Produce Feet *)

(** For each generator, every rotation offset either produces one of the
    circle's feet or produces a non-foot pattern. Since rotation by n and
    by n + length give the same result, we only check 0..length-1. *)

(** Trisyllabic generator faulun: only offsets 0 and 2 give feet. *)
Lemma faulun_rotation_exhaustive :
  is_foot (rotate 0 faulun) = true /\
  is_foot (rotate 1 faulun) = false /\
  is_foot (rotate 2 faulun) = true.
Proof. repeat split; reflexivity. Qed.

(** Quadrisyllabic generator mafailun: all 4 offsets give feet. *)
Lemma mafailun_rotation_exhaustive :
  is_foot (rotate 0 mafailun) = true /\
  is_foot (rotate 1 mafailun) = true /\
  is_foot (rotate 2 mafailun) = true /\
  is_foot (rotate 3 mafailun) = true.
Proof. repeat split; reflexivity. Qed.

(** Pentasyllabic generator mufaalatun: only offsets 0 and 2 give feet. *)
Lemma mufaalatun_rotation_exhaustive :
  is_foot (rotate 0 mufaalatun) = true /\
  is_foot (rotate 1 mufaalatun) = false /\
  is_foot (rotate 2 mufaalatun) = true /\
  is_foot (rotate 3 mufaalatun) = false /\
  is_foot (rotate 4 mufaalatun) = false.
Proof. repeat split; reflexivity. Qed.

(** *** Cross-Circle Non-Relation *)

(** Feet in different circles are NOT related by rotation. *)

(** Trisyllabic feet (faulun, failun) cannot produce quadrisyllabic feet
    by rotation, because rotation preserves length. *)
Lemma cross_circle_length_barrier : forall n,
  rotate n faulun <> mafailun.
Proof.
  intros n Hcontra.
  assert (Hlen : length (rotate n faulun) = length mafailun) by (rewrite Hcontra; reflexivity).
  rewrite rotate_length_preserved in Hlen. simpl in Hlen. discriminate.
Qed.

(** Mujtallaba (quadrisyllabic, e.g., mafailun) cannot produce
    pentasyllabic feet (mutafailun, mufaalatun) by rotation. *)
Lemma cross_circle_quad_penta : forall n,
  rotate n mafailun <> mutafailun.
Proof.
  intros n Hcontra.
  assert (Hlen : length (rotate n mafailun) = length mutafailun) by (rewrite Hcontra; reflexivity).
  rewrite rotate_length_preserved in Hlen. simpl in Hlen. discriminate.
Qed.

(** Witness: faulun and mafailun are in different circles *)
Example cross_circle_witness :
  meter_circle Mutaqarib <> meter_circle Hazaj.
Proof. discriminate. Qed.

(** Example: rotation of mafailun never yields faulun (length mismatch) *)
Example cross_circle_example : forall n,
  rotate n mafailun <> faulun.
Proof.
  intros n Hcontra.
  assert (Hlen : length (rotate n mafailun) = length faulun) by (rewrite Hcontra; reflexivity).
  rewrite rotate_length_preserved in Hlen. simpl in Hlen. discriminate.
Qed.

(** Counterexample: within-circle rotation DOES relate feet *)
Example within_circle_counterexample :
  rotate 2 mafailun = mustafilun.
Proof. reflexivity. Qed.

(** ** Orbit Representative Theorem *)

(** The 8 canonical feet are exactly the foot-patterns obtainable by
    rotating three generators — faulun (trisyllabic), mafailun
    (quadrisyllabic), mufaalatun (pentasyllabic) — within the full
    pattern space {S,L}^3 ∪ {S,L}^4 ∪ {S,L}^5. *)

(** Every canonical foot is a rotation of its size-class generator. *)
Theorem foot_in_generator_orbit : forall f : foot,
  exists (g : pattern) (n : nat),
    In g [faulun; mafailun; mufaalatun] /\
    n < length g /\
    rotate n g = foot_pattern f.
Proof.
  intros f; destruct f.
  - exists faulun, 0. split. left. reflexivity. split. simpl. lia. reflexivity.
  - exists faulun, 2. split. left. reflexivity. split. simpl. lia. reflexivity.
  - exists mafailun, 0. split. right. left. reflexivity. split. simpl. lia. reflexivity.
  - exists mafailun, 2. split. right. left. reflexivity. split. simpl. lia. reflexivity.
  - exists mafailun, 3. split. right. left. reflexivity. split. simpl. lia. reflexivity.
  - exists mafailun, 1. split. right. left. reflexivity. split. simpl. lia. reflexivity.
  - exists mufaalatun, 2. split. right. right. left. reflexivity. split. simpl. lia. reflexivity.
  - exists mufaalatun, 0. split. right. right. left. reflexivity. split. simpl. lia. reflexivity.
Defined.

(** Converse: every foot-producing rotation of a generator is a
    canonical foot pattern. Together with the forward direction and the
    exhaustion lemmas, this shows the 8 feet are exactly the
    rotation-orbit representatives. *)
Theorem generator_orbit_yields_foot : forall g n,
  In g [faulun; mafailun; mufaalatun] ->
  n < length g ->
  is_foot (rotate n g) = true ->
  exists f : foot, foot_pattern f = rotate n g.
Proof.
  intros g n Hg Hn Hfoot.
  destruct Hg as [Hg | [Hg | [Hg | []]]]; subst g; simpl in Hn.
  - destruct n as [|[|[|n]]]; try lia; simpl in Hfoot |- *.
    + exists Faulun. reflexivity.
    + discriminate.
    + exists Failun. reflexivity.
  - destruct n as [|[|[|[|n]]]]; try lia; simpl in Hfoot |- *.
    + exists Mafailun. reflexivity.
    + exists Mafulatu. reflexivity.
    + exists Mustafilun. reflexivity.
    + exists Failatun. reflexivity.
  - destruct n as [|[|[|[|[|n]]]]]; try lia; simpl in Hfoot |- *.
    + exists Mufaalatun. reflexivity.
    + discriminate.
    + exists Mutafailun. reflexivity.
    + discriminate.
    + discriminate.
Defined.

(** The three generator orbits are pairwise disjoint
    (rotation preserves length, and 3 ≠ 4 ≠ 5). *)

Lemma orbit_disjoint_tri_quad : forall n m,
  rotate n faulun <> rotate m mafailun.
Proof.
  intros n m Hcontra.
  assert (Hlen : length (rotate n faulun) = length (rotate m mafailun)).
  { rewrite Hcontra. reflexivity. }
  repeat rewrite rotate_length_preserved in Hlen.
  simpl in Hlen. discriminate.
Qed.

Lemma orbit_disjoint_tri_penta : forall n m,
  rotate n faulun <> rotate m mufaalatun.
Proof.
  intros n m Hcontra.
  assert (Hlen : length (rotate n faulun) = length (rotate m mufaalatun)).
  { rewrite Hcontra. reflexivity. }
  repeat rewrite rotate_length_preserved in Hlen.
  simpl in Hlen. discriminate.
Qed.

Lemma orbit_disjoint_quad_penta : forall n m,
  rotate n mafailun <> rotate m mufaalatun.
Proof.
  intros n m Hcontra.
  assert (Hlen : length (rotate n mafailun) = length (rotate m mufaalatun)).
  { rewrite Hcontra. reflexivity. }
  repeat rewrite rotate_length_preserved in Hlen.
  simpl in Hlen. discriminate.
Qed.

(** End of Section 6: The Five Circles *)

(** * Section 7: Variation Rules (Zihāf and ʿIlla) *)

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
  | ʿAṣb    (* عصب - make fifth quiescent: mufāʿalatun → mufāʿaltun *)
  | Iḍmār   (* إضمار - make second quiescent: mutafāʿilun → mustafʿilun *)
  | ʿAql    (* عقل - drop fifth mutaḥarrik: mufāʿalatun → mufāʿlatun *)
  | Shamm.  (* شمّ - partial quiescence of second mutaḥarrik: metrically = iḍmār *)

(** ** Decidable Equality for Zihaf *)

Definition zihaf_eq_dec (z1 z2 : zihaf) : {z1 = z2} + {z1 <> z2}.
Proof.
  destruct z1, z2; try (left; reflexivity); right; discriminate.
Defined.

(** Witness: zihaf_eq_dec Khabn Khabn *)
Example zihaf_eq_dec_witness : exists pf, zihaf_eq_dec Khabn Khabn = left pf.
Proof. eexists. reflexivity. Qed.

(** Example: zihaf_eq_dec ʿAṣb ʿAṣb *)
Example zihaf_eq_dec_example : exists pf, zihaf_eq_dec ʿAṣb ʿAṣb = left pf.
Proof. eexists. reflexivity. Qed.

(** Counterexample: zihaf_eq_dec returns right for different zihaf *)
Example zihaf_eq_dec_counterexample : exists pf, zihaf_eq_dec Khabn Tayy = right pf.
Proof. eexists. reflexivity. Qed.

Inductive ʿilla : Type :=
  | Qaṭʿ     (* قطع - drop final consonant of watad majmūʿ, still preceding *)
  | Qaṣr     (* قصر - shorten final long vowel *)
  | Ḥadhf    (* حذف - drop final sabab khafīf *)
  | Tasbīgh  (* تسبيغ - add sākin after final sabab khafīf *)
  | Batr     (* بتر - combine Ḥadhf and Qaṭʿ *)
  | Qaṭf     (* قطف - combine ʿaṣb and Ḥadhf: mufāʿalatun → faʿūlun *)
  | Tarfīl   (* ترفيل - add sabab khafīf after final watad majmūʿ *)
  | Tadhyīl  (* تذييل - add one sākin after final watad majmūʿ *)
  | Ḥadhādh  (* حذذ - drop entire final watad majmūʿ (3 letters) *)
  | Ṣalm     (* صلم - drop entire final watad mafrūq (3 letters) *)
  | Kashf    (* كسف - drop last letter of final watad mafrūq *)
  | Waqf     (* وقف - still (make sākin) the last letter of watad mafrūq *)
  | Tashʿīth. (* تشعيث - drop a mutaḥarrik from watad majmūʿ in fāʿilātun *)

(** ** Decidable Equality for ʿIlla *)

Definition ʿilla_eq_dec (i1 i2 : ʿilla) : {i1 = i2} + {i1 <> i2}.
Proof.
  destruct i1, i2; try (left; reflexivity); right; discriminate.
Defined.

(** Witness: ʿilla_eq_dec Qaṭʿ Qaṭʿ *)
Example ʿilla_eq_dec_witness : exists pf, ʿilla_eq_dec Qaṭʿ Qaṭʿ = left pf.
Proof. eexists. reflexivity. Qed.

(** Example: ʿilla_eq_dec Batr Batr *)
Example ʿilla_eq_dec_example : exists pf, ʿilla_eq_dec Batr Batr = left pf.
Proof. eexists. reflexivity. Qed.

(** Counterexample: ʿilla_eq_dec returns right for different ʿilla *)
Example ʿilla_eq_dec_counterexample : exists pf, ʿilla_eq_dec Qaṣr Ḥadhf = right pf.
Proof. eexists. reflexivity. Qed.

(** ** Effect on Patterns — Letter-Level Operations *)

(** Zihāf operations are defined at the letter level, as in Khalil's
    original system. Each operation targets a specific letter position
    (1-indexed in the tradition, 0-indexed here) within the foot's
    mnemonic word. The pattern is converted to letters, the operation
    is performed, and the result is converted back to syllable weights. *)

(** Khabn: delete 2nd letter (index 1), which must be sākin *)
Definition apply_khabn (p : pattern) : option pattern :=
  let ls := pattern_to_letters p in
  match nth_error ls 1 with
  | Some Sakin => letters_to_pattern (delete_at 1 ls)
  | _ => None
  end.

(** Tayy: delete 4th letter (index 3), which must be sākin *)
Definition apply_tayy (p : pattern) : option pattern :=
  let ls := pattern_to_letters p in
  match nth_error ls 3 with
  | Some Sakin => letters_to_pattern (delete_at 3 ls)
  | _ => None
  end.

(** Qabḍ: delete 5th letter (index 4), which must be sākin *)
Definition apply_qabḍ (p : pattern) : option pattern :=
  let ls := pattern_to_letters p in
  match nth_error ls 4 with
  | Some Sakin => letters_to_pattern (delete_at 4 ls)
  | _ => None
  end.

(** Kaff: delete 7th letter (index 6), which must be sākin *)
Definition apply_kaff (p : pattern) : option pattern :=
  let ls := pattern_to_letters p in
  match nth_error ls 6 with
  | Some Sakin => letters_to_pattern (delete_at 6 ls)
  | _ => None
  end.

(** Waqṣ: delete 2nd letter (index 1), which must be mutaḥarrik *)
Definition apply_waqṣ (p : pattern) : option pattern :=
  let ls := pattern_to_letters p in
  match nth_error ls 1 with
  | Some Mutaharrik => letters_to_pattern (delete_at 1 ls)
  | _ => None
  end.

(** ʿAṣb: make 5th letter (index 4) quiescent (Mutaharrik → Sakin) *)
Definition apply_ʿaṣb (p : pattern) : option pattern :=
  let ls := pattern_to_letters p in
  match nth_error ls 4 with
  | Some Mutaharrik => letters_to_pattern (replace_at 4 Sakin ls)
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

(** Ḥadhf raw: Drop final syllable (used internally by drop_last_n). *)
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

(** Qaṭʿ: drop final syllable and make penultimate Long *)
Fixpoint apply_qaṭʿ (p : pattern) : option pattern :=
  match p with
  | [] => None
  | [_] => None
  | [_; _] => Some [Long]
  | w :: rest =>
      match apply_qaṭʿ rest with
      | Some rest' => Some (w :: rest')
      | None => None
      end
  end.

(** Tasbīgh: change final Short to Long *)
Fixpoint apply_tasbīgh (p : pattern) : option pattern :=
  match p with
  | [] => None
  | [Short] => Some [Long]
  | [Long] => None
  | w :: rest =>
      match apply_tasbīgh rest with
      | Some rest' => Some (w :: rest')
      | None => None
      end
  end.

(** Batr: compose Ḥadhf then Qaṭʿ *)
Definition apply_batr (p : pattern) : option pattern :=
  match apply_ḥadhf p with
  | Some p' => apply_qaṭʿ p'
  | None => None
  end.

(** Qaṭf: compose ʿAṣb then Ḥadhf *)
Definition apply_qaṭf (p : pattern) : option pattern :=
  match apply_ʿaṣb p with
  | Some p' => apply_ḥadhf p'
  | None => None
  end.

(** ** Watad-ending predicates *)

(** Extract the last two syllables of a pattern, if it has at least two. *)
Fixpoint last_two (p : pattern) : option (weight * weight) :=
  match p with
  | [] | [_] => None
  | [a; b] => Some (a, b)
  | _ :: rest => last_two rest
  end.

Definition ends_with_watad_majmu (p : pattern) : bool :=
  match last_two p with Some (Short, Long) => true | _ => false end.

Definition ends_with_watad_mafruq (p : pattern) : bool :=
  match last_two p with Some (Long, Short) => true | _ => false end.

(** Tarfīl: append sabab khafīf after final watad majmūʿ.
    Requires the pattern to end in watad majmūʿ (Short; Long). *)
Definition apply_tarfīl (p : pattern) : option pattern :=
  if ends_with_watad_majmu p then Some (p ++ [Long])
  else None.

(** Qaṭf on mufaalatun: ʿaṣb gives [Short;Long;Long;Long],
    then ḥadhf drops final: [Short;Long;Long] = faulun. *)
Example qaṭf_mufaalatun :
  apply_qaṭf mufaalatun = Some [Short; Long; Long].
Proof. reflexivity. Qed.

(** Counterexample: qaṭf fails when ʿaṣb fails *)
Example qaṭf_counterexample :
  apply_qaṭf mafailun = None.
Proof. reflexivity. Qed.

(** Tarfīl on failun: append Long → [Long; Short; Long; Long] = failatun. *)
Example tarfīl_failun :
  apply_tarfīl failun = Some [Long; Short; Long; Long].
Proof. reflexivity. Qed.

(** Counterexample: tarfīl fails on empty *)
Example tarfīl_counterexample :
  apply_tarfīl [] = None.
Proof. reflexivity. Qed.

(** Tadhyīl: add one sākin letter after the final watad majmūʿ.
    At the syllable level, this extends the final Long by one mora,
    which in practice means the final syllable becomes super-heavy.
    We model this as appending a Long syllable (the extra sākin
    merges with the preceding watad's final sākin to form CvCC).
    Requires the pattern to end in watad majmūʿ (Short; Long).
    NOTE: at the syllable-weight level, tadhyīl and tarfīl are
    identical operations. The distinction is sub-syllabic and would
    require a richer weight type (e.g., SuperLong) to capture. *)
Definition apply_tadhyīl (p : pattern) : option pattern :=
  if ends_with_watad_majmu p then Some (p ++ [Long])
  else None.

(** Tadhyīl on failun: append Long → [Long; Short; Long; Long]. *)
Example tadhyīl_failun :
  apply_tadhyīl failun = Some [Long; Short; Long; Long].
Proof. reflexivity. Qed.

(** Counterexample: tadhyīl fails on empty *)
Example tadhyīl_counterexample :
  apply_tadhyīl [] = None.
Proof. reflexivity. Qed.

(** Ḥadhādh: drop the entire final watad majmūʿ (last two syllables
    of a watad: Short + Long → remove both). We model this as
    removing the last two syllables. *)
Fixpoint drop_last_n (n : nat) (p : pattern) : option pattern :=
  match n with
  | 0 => Some p
  | S n' =>
      match apply_ḥadhf p with
      | Some p' => drop_last_n n' p'
      | None => None
      end
  end.

(** Requires the pattern to end in watad majmūʿ (Short; Long). *)
Definition apply_ḥadhādh (p : pattern) : option pattern :=
  if ends_with_watad_majmu p then drop_last_n 2 p
  else None.

(** Ḥadhādh on mutafailun: drop last 2 syllables.
    mutafailun = [Short; Short; Long; Short; Long] →
    [Short; Short; Long]. *)
Example ḥadhādh_mutafailun :
  apply_ḥadhādh mutafailun = Some [Short; Short; Long].
Proof. reflexivity. Qed.

(** Counterexample: ḥadhādh fails on single-syllable pattern *)
Example ḥadhādh_counterexample :
  apply_ḥadhādh [Long] = None.
Proof. reflexivity. Qed.

(** Ṣalm: drop the entire final watad mafrūq (last two syllables:
    Long + Short → remove both). Requires the pattern to end in
    watad mafrūq (Long; Short). *)
Definition apply_ṣalm (p : pattern) : option pattern :=
  if ends_with_watad_mafruq p then drop_last_n 2 p
  else None.

(** Ṣalm on mafulatu: drop last 2.
    mafulatu = [Long; Long; Long; Short] → [Long; Long]. *)
Example ṣalm_mafulatu :
  apply_ṣalm mafulatu = Some [Long; Long].
Proof. reflexivity. Qed.

(** Counterexample: ṣalm fails on single-syllable pattern *)
Example ṣalm_counterexample :
  apply_ṣalm [Short] = None.
Proof. reflexivity. Qed.

(** Ṣalm rejects watad majmūʿ endings (only ḥadhādh accepts those). *)
Example ṣalm_rejects_majmu :
  apply_ṣalm mutafailun = None.
Proof. reflexivity. Qed.

(** Ḥadhādh rejects watad mafrūq endings (only ṣalm accepts those). *)
Example ḥadhādh_rejects_mafruq :
  apply_ḥadhādh mafulatu = None.
Proof. reflexivity. Qed.

(** Tarfīl and tadhyīl are extensionally equal at the syllable-weight
    level. The traditional distinction (tarfīl adds a full sabab,
    tadhyīl adds a single sākin letter) is sub-syllabic and would
    require a richer weight type (e.g., SuperLong) to capture. *)
Lemma tarfīl_eq_tadhyīl : forall p,
  apply_tarfīl p = apply_tadhyīl p.
Proof.
  intros p. unfold apply_tarfīl, apply_tadhyīl. reflexivity.
Qed.

(** Kashf: drop the last letter of the final watad mafrūq.
    At the syllable level, the final Short of watad mafrūq
    (Long; Short) is dropped. We model as dropping the last syllable. *)
Definition apply_kashf (p : pattern) : option pattern :=
  apply_ḥadhf p.

(** Kashf on mafulatu: drop last.
    mafulatu = [Long; Long; Long; Short] → [Long; Long; Long]. *)
Example kashf_mafulatu :
  apply_kashf mafulatu = Some [Long; Long; Long].
Proof. reflexivity. Qed.

(** Counterexample: kashf fails on empty *)
Example kashf_counterexample :
  apply_kashf [] = None.
Proof. reflexivity. Qed.

(** ** Guarded ʿilla operations with traditional preconditions *)

(** Helper: check if a pattern ends with a specific syllable. *)
Fixpoint ends_with (p : pattern) (w : weight) : bool :=
  match p with
  | [] => false
  | [x] => weight_eqb x w
  | _ :: rest => ends_with rest w
  end.

(** Ḥadhf (guarded): drop the final sabab khafīf.
    Traditionally, ḥadhf only removes a final Long syllable. *)
Definition apply_ḥadhf_guarded (p : pattern) : option pattern :=
  if ends_with p Long then apply_ḥadhf p
  else None.

(** Qaṭʿ (guarded): operates on a final watad majmūʿ (Short; Long).
    Drops the final syllable and makes the penultimate Long. *)
Definition apply_qaṭʿ_guarded (p : pattern) : option pattern :=
  if ends_with_watad_majmu p then apply_qaṭʿ p
  else None.

(** Kashf (guarded): drops the last letter of a final watad mafrūq.
    Only applies when the pattern ends in watad mafrūq (Long; Short). *)
Definition apply_kashf_guarded (p : pattern) : option pattern :=
  if ends_with_watad_mafruq p then apply_ḥadhf p
  else None.

(** Guarded ḥadhf on faulun: faulun = [Short;Long;Long], ends with Long. *)
Example ḥadhf_guarded_faulun :
  apply_ḥadhf_guarded faulun = Some [Short; Long].
Proof. reflexivity. Qed.

(** Guarded ḥadhf rejects patterns ending in Short. *)
Example ḥadhf_guarded_rejects_short :
  apply_ḥadhf_guarded [Long; Short] = None.
Proof. reflexivity. Qed.

(** Guarded qaṭʿ on failun: failun = [Long;Short;Long], ends with watad majmūʿ. *)
Example qaṭʿ_guarded_failun :
  apply_qaṭʿ_guarded failun = Some [Long; Long].
Proof. reflexivity. Qed.

(** Guarded qaṭʿ rejects patterns not ending in watad majmūʿ. *)
Example qaṭʿ_guarded_rejects :
  apply_qaṭʿ_guarded [Long; Long; Long] = None.
Proof. reflexivity. Qed.

(** Guarded kashf on mafulatu: mafulatu = [Long;Long;Long;Short], ends with watad mafrūq. *)
Example kashf_guarded_mafulatu :
  apply_kashf_guarded mafulatu = Some [Long; Long; Long].
Proof. reflexivity. Qed.

(** Guarded kashf rejects patterns not ending in watad mafrūq. *)
Example kashf_guarded_rejects :
  apply_kashf_guarded [Long; Long; Long] = None.
Proof. reflexivity. Qed.

(** Waqf: make the last mutaḥarrik of watad mafrūq quiescent.
    At the syllable level, the final Short becomes Long
    (the vowel is suppressed, making it a closed syllable). *)
Fixpoint apply_waqf (p : pattern) : option pattern :=
  match p with
  | [] => None
  | [Short] => Some [Long]
  | [Long] => None  (* already quiescent *)
  | w :: rest =>
      match apply_waqf rest with
      | Some rest' => Some (w :: rest')
      | None => None
      end
  end.

(** Waqf on mafulatu: final Short → Long.
    mafulatu = [Long; Long; Long; Short] → [Long; Long; Long; Long]. *)
Example waqf_mafulatu :
  apply_waqf mafulatu = Some [Long; Long; Long; Long].
Proof. reflexivity. Qed.

(** Counterexample: waqf fails when last is already Long *)
Example waqf_counterexample :
  apply_waqf [Long; Long] = None.
Proof. reflexivity. Qed.

(** Tashʿīth: drop a mutaḥarrik from the watad majmūʿ within
    fāʿilātun, effectively turning Short;Long into Long.
    At the syllable level: delete the Short that precedes a Long
    in the second position. We model as deleting the 2nd syllable
    when it is Short and the 3rd is Long. *)
Definition apply_tashʿīth (p : pattern) : option pattern :=
  match p with
  | w1 :: Short :: Long :: rest => Some (w1 :: Long :: rest)
  | _ => None
  end.

(** Tashʿīth on failatun: delete 2nd (Short) syllable.
    failatun = [Long; Short; Long; Long] → [Long; Long; Long]. *)
Example tashʿīth_failatun :
  apply_tashʿīth failatun = Some [Long; Long; Long].
Proof. reflexivity. Qed.

(** Counterexample: tashʿīth fails on faulun (2nd is Long, not Short) *)
Example tashʿīth_counterexample :
  apply_tashʿīth faulun = None.
Proof. reflexivity. Qed.

(** ** Example: Khabn on Mustafilun *)

(** mustafilun = [Long; Long; Short; Long], letters = [M;S;M;S;M;M;S].
    Khabn deletes 2nd letter (S at index 1): [M;M;S;M;M;S].
    Re-syllabified: mutafʿilun = [Short; Long; Short; Long]. *)
Example khabn_mustafilun :
  apply_khabn mustafilun = Some [Short; Long; Short; Long].
Proof. reflexivity. Qed.

(** Witness: khabn applies to mustafilun *)
Example khabn_witness :
  exists p, apply_khabn mustafilun = Some p.
Proof. eexists. reflexivity. Qed.

(** Example: khabn on failatun — now correctly applies.
    failatun = [Long; Short; Long; Long], letters = [M;S;M;M;S;M;S].
    2nd letter is S: khabn applies. Delete it: [M;M;M;S;M;S].
    Re-syllabified: [Short; Short; Long; Long]. *)
Example khabn_on_failatun :
  apply_khabn failatun = Some [Short; Short; Long; Long].
Proof. reflexivity. Qed.

(** Counterexample: khabn fails when 2nd letter is not sākin.
    faulun = [Short; Long; Long], letters = [M;M;S;M;S].
    2nd letter (index 1) is M, not S. *)
Example khabn_counterexample :
  apply_khabn faulun = None.
Proof. reflexivity. Qed.

(** ** Example: Qabḍ *)

(** Qabḍ on mafāʿīlun: delete 5th letter (index 4).
    mafailun letters = [M;M;S;M;S;M;S]. 5th letter (index 4) is S.
    Delete it: [M;M;S;M;M;S]. Re-syllabified: [Short; Long; Short; Long]. *)
Example qabḍ_mafailun :
  apply_qabḍ mafailun = Some [Short; Long; Short; Long].
Proof. reflexivity. Qed.

(** Witness: qabḍ applies to mafailun *)
Example qabḍ_witness :
  exists p, apply_qabḍ mafailun = Some p.
Proof. eexists. reflexivity. Qed.

(** Counterexample: qabḍ fails when 5th letter is not sākin.
    mustafilun letters = [M;S;M;S;M;M;S]. 5th letter (index 4) is M. *)
Example qabḍ_counterexample :
  apply_qabḍ mustafilun = None.
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

(** Iḍmār (إضمار): make 2nd letter (index 1) quiescent (Mutaharrik → Sakin).
    Applies when the 2nd letter is mutaḥarrik. *)

Definition apply_iḍmār (p : pattern) : option pattern :=
  let ls := pattern_to_letters p in
  match nth_error ls 1 with
  | Some Mutaharrik => letters_to_pattern (replace_at 1 Sakin ls)
  | _ => None
  end.

(** Iḍmār on mutafailun: make 2nd letter quiescent.
    mutafailun letters = [M;M;M;S;M;M;S]. Index 1 is M.
    Replace with S: [M;S;M;S;M;M;S].
    Re-syllabified: [Long; Long; Short; Long] = mustafilun. *)
Example iḍmār_mutafailun :
  apply_iḍmār mutafailun = Some [Long; Long; Short; Long].
Proof. reflexivity. Qed.

(** Counterexample: iḍmār fails when 2nd letter is sākin *)
Example iḍmār_counterexample :
  apply_iḍmār mustafilun = None.
Proof. reflexivity. Qed.

(** Shamm (شمّ): partially quiesce the 2nd letter (index 1).
    Traditionally a phonetic distinction from iḍmār — the vowel is
    "tasted" (mushamma) rather than fully suppressed. At the syllable-weight
    level the effect is identical to iḍmār: Mutaharrik → Sakin at index 1. *)

Definition apply_shamm (p : pattern) : option pattern :=
  let ls := pattern_to_letters p in
  match nth_error ls 1 with
  | Some Mutaharrik => letters_to_pattern (replace_at 1 Sakin ls)
  | _ => None
  end.

(** Shamm on mutafailun: same metrical result as iḍmār. *)
Example shamm_mutafailun :
  apply_shamm mutafailun = Some [Long; Long; Short; Long].
Proof. reflexivity. Qed.

(** Counterexample: shamm fails when 2nd letter is sākin *)
Example shamm_counterexample :
  apply_shamm mustafilun = None.
Proof. reflexivity. Qed.

(** ʿAql (عقل): delete 5th letter (index 4), which must be mutaḥarrik.
    Applies to mufāʿalatun where the 5th letter is mutaḥarrik. *)

Definition apply_ʿaql (p : pattern) : option pattern :=
  let ls := pattern_to_letters p in
  match nth_error ls 4 with
  | Some Mutaharrik => letters_to_pattern (delete_at 4 ls)
  | _ => None
  end.

(** ʿAql on mufaalatun: delete 5th letter (mutaḥarrik at index 4).
    mufaalatun letters = [M;M;S;M;M;M;S]. Delete index 4 (M):
    [M;M;S;M;M;S]. Re-syllabified: [Short; Long; Short; Long]. *)
Example ʿaql_mufaalatun :
  apply_ʿaql mufaalatun = Some [Short; Long; Short; Long].
Proof. reflexivity. Qed.

(** Counterexample: ʿaql fails when 5th letter is sākin *)
Example ʿaql_counterexample :
  apply_ʿaql mafailun = None.
Proof. reflexivity. Qed.

(** ** Compound Zihāf (Zihāf Murakkab) *)

(** Compound zihāf types combine two simple operations on different
    letter positions within the same foot. *)

Inductive compound_zihaf : Type :=
  | Khazl    (* خزل - iḍmār + tayy *)
  | Khabl    (* خبل - khabn + tayy *)
  | Shakl    (* شكل - khabn + kaff *)
  | Naqs.    (* نقص - ʿaṣb + kaff *)

(** Decidable equality for compound_zihaf *)
Definition compound_zihaf_eq_dec (z1 z2 : compound_zihaf)
  : {z1 = z2} + {z1 <> z2}.
Proof.
  destruct z1, z2; try (left; reflexivity); right; discriminate.
Defined.

(** Compound zihāf application.
    Khazl and naqs use sequential composition because their first
    operation is a replacement (iḍmār, ʿaṣb), which preserves indices.
    Khabl and shakl use simultaneous deletion because their first
    operation (khabn) is a deletion that shifts subsequent indices. *)

Definition apply_khazl (p : pattern) : option pattern :=
  match apply_iḍmār p with
  | Some p' => apply_tayy p'
  | None => None
  end.

(** Khabl: khabn (delete index 1) + tayy (delete index 3).
    Both target the original letter sequence simultaneously. *)
Definition apply_khabl (p : pattern) : option pattern :=
  let ls := pattern_to_letters p in
  match nth_error ls 1, nth_error ls 3 with
  | Some Sakin, Some Sakin =>
      letters_to_pattern (delete_at 1 (delete_at 3 ls))
  | _, _ => None
  end.

(** Shakl: khabn (delete index 1) + kaff (delete index 6).
    Both target the original letter sequence simultaneously. *)
Definition apply_shakl (p : pattern) : option pattern :=
  let ls := pattern_to_letters p in
  match nth_error ls 1, nth_error ls 6 with
  | Some Sakin, Some Sakin =>
      letters_to_pattern (delete_at 1 (delete_at 6 ls))
  | _, _ => None
  end.

Definition apply_naqs (p : pattern) : option pattern :=
  match apply_ʿaṣb p with
  | Some p' => apply_kaff p'
  | None => None
  end.

(** Compound zihāf enumeration *)

Definition all_compound_zihaf : list compound_zihaf :=
  [Khazl; Khabl; Shakl; Naqs].

Lemma all_compound_zihaf_complete : forall z : compound_zihaf,
  In z all_compound_zihaf.
Proof.
  intros z. destruct z; simpl.
  - left. reflexivity.
  - right. left. reflexivity.
  - right. right. left. reflexivity.
  - right. right. right. left. reflexivity.
Qed.

Lemma all_compound_zihaf_length : length all_compound_zihaf = 4.
Proof. reflexivity. Qed.

(** Witness: khazl on mutafailun (iḍmār then tayy).
    iḍmār: [M;M;M;S;M;M;S] → [M;S;M;S;M;M;S] = [Long;Long;Short;Long].
    tayy on [Long;Long;Short;Long]: letters [M;S;M;S;M;M;S],
    index 3 is S, delete: [M;S;M;M;M;S] = [Long;Short;Short;Long]. *)
Example khazl_witness :
  apply_khazl mutafailun = Some [Long; Short; Short; Long].
Proof. reflexivity. Qed.

(** Example: khabl on mustafilun (simultaneous delete indices 1 and 3).
    mustafilun letters = [M;S;M;S;M;M;S].
    Delete index 3 first: [M;S;M;M;M;S].
    Delete index 1: [M;M;M;M;S].
    Re-syllabified: maftaʿlun = [Short;Short;Short;Long]. *)
Example khabl_mustafilun :
  apply_khabl mustafilun = Some [Short; Short; Short; Long].
Proof. reflexivity. Qed.

(** Example: shakl on failatun (simultaneous delete indices 1 and 6).
    failatun letters = [M;S;M;M;S;M;S].
    Delete index 6 first: [M;S;M;M;S;M].
    Delete index 1: [M;M;M;S;M].
    Re-syllabified: [Short;Short;Long;Short]. *)
Example shakl_failatun :
  apply_shakl failatun = Some [Short; Short; Long; Short].
Proof. reflexivity. Qed.

(** Counterexample: shakl fails when khabn precondition not met *)
Example shakl_on_faulun :
  apply_shakl faulun = None.
Proof. reflexivity. Qed.

(** Witness: naqs on mufaalatun (ʿaṣb then kaff).
    ʿaṣb: [M;M;S;M;M;M;S] → replace index 4 M→S → [M;M;S;M;S;M;S]
    = [Short;Long;Long;Long].
    kaff on [Short;Long;Long;Long]: letters [M;M;S;M;S;M;S],
    index 6 is S, delete: [M;M;S;M;S;M] = [Short;Long;Long;Short]. *)
Example naqs_witness :
  apply_naqs mufaalatun = Some [Short; Long; Long; Short].
Proof. reflexivity. Qed.

(** ** Variation Enumeration *)

Definition all_zihaf : list zihaf := [Khabn; Tayy; Qabḍ; Kaff; Waqṣ; ʿAṣb; Iḍmār; ʿAql; Shamm].
Definition all_ʿilla : list ʿilla := [Qaṭʿ; Qaṣr; Ḥadhf; Tasbīgh; Batr; Qaṭf; Tarfīl; Tadhyīl; Ḥadhādh; Ṣalm; Kashf; Waqf; Tashʿīth].

Lemma all_zihaf_complete : forall z : zihaf, In z all_zihaf.
Proof.
  intros z. destruct z; simpl.
  - left. reflexivity.
  - right. left. reflexivity.
  - right. right. left. reflexivity.
  - right. right. right. left. reflexivity.
  - right. right. right. right. left. reflexivity.
  - right. right. right. right. right. left. reflexivity.
  - right. right. right. right. right. right. left. reflexivity.
  - right. right. right. right. right. right. right. left. reflexivity.
  - right. right. right. right. right. right. right. right. left. reflexivity.
Qed.

Lemma all_ʿilla_complete : forall i : ʿilla, In i all_ʿilla.
Proof.
  intros i. destruct i; simpl;
  repeat (try (left; reflexivity); right).
Qed.

Lemma all_zihaf_length : length all_zihaf = 9.
Proof. reflexivity. Qed.

Lemma all_ʿilla_length : length all_ʿilla = 13.
Proof. reflexivity. Qed.

(** Witness: Khabn in all_zihaf *)
Example all_zihaf_witness : In Khabn all_zihaf.
Proof. left. reflexivity. Qed.

(** Example: ʿAql (last) in all_zihaf *)
Example all_zihaf_example : In ʿAql all_zihaf.
Proof. right. right. right. right. right. right. right. left. reflexivity. Qed.

(** Counterexample: incomplete zihaf list fails completeness *)
Example all_zihaf_counterexample : ~ (forall z : zihaf, In z [Khabn; Tayy]).
Proof.
  intros H. specialize (H Qabḍ). simpl in H.
  destruct H as [H | [H | H]]; try discriminate; contradiction.
Qed.

(** Witness: Qaṭʿ in all_ʿilla *)
Example all_ʿilla_witness : In Qaṭʿ all_ʿilla.
Proof. left. reflexivity. Qed.

(** Example: Qaṣr in all_ʿilla *)
Example all_ʿilla_example : In Qaṣr all_ʿilla.
Proof. right. left. reflexivity. Qed.

(** Counterexample: incomplete ʿilla list fails completeness *)
Example all_ʿilla_counterexample : ~ (forall i : ʿilla, In i [Qaṭʿ; Qaṣr]).
Proof.
  intros H. specialize (H Ḥadhf). simpl in H.
  destruct H as [H | [H | H]]; try discriminate; contradiction.
Qed.

(** Witness: 9 zihaf types *)
Example all_zihaf_length_witness : length all_zihaf = 9.
Proof. reflexivity. Qed.

(** Example: not 8 *)
Example all_zihaf_length_example : length all_zihaf <> 8.
Proof. discriminate. Qed.

(** Counterexample: 5 ʿilla types, not 8 *)
Example all_zihaf_length_counterexample : length all_ʿilla <> 9.
Proof. discriminate. Qed.

(** Witness: 13 ʿilla types *)
Example all_ʿilla_length_witness : length all_ʿilla = 13.
Proof. reflexivity. Qed.

(** Example: not 7 (old count) *)
Example all_ʿilla_length_example : length all_ʿilla <> 7.
Proof. discriminate. Qed.

(** Counterexample: 9 zihaf types, not 13 *)
Example all_ʿilla_length_counterexample : length all_zihaf <> 13.
Proof. discriminate. Qed.

(** ** Variation Applicability *)

(** Each zihāf applies to feet where the target letter position has
    the required type (sākin or mutaḥarrik). *)

(** Khabn applies to mustafilun (2nd letter is sākin) *)
Example khabn_applies_mustafilun :
  apply_khabn mustafilun = Some [Short; Long; Short; Long].
Proof. reflexivity. Qed.

(** Khabn applies to failatun (2nd letter is sākin) *)
Example khabn_applies_failatun :
  apply_khabn failatun = Some [Short; Short; Long; Long].
Proof. reflexivity. Qed.

(** Khabn does not apply to faulun (2nd letter is mutaḥarrik) *)
Example khabn_not_applies_faulun :
  apply_khabn faulun = None.
Proof. reflexivity. Qed.

(** Tayy applies to mustafilun (4th letter is sākin).
    mustafilun letters = [M;S;M;S;M;M;S]. Delete index 3 (S):
    [M;S;M;M;M;S]. Re-syllabified: [Long; Short; Short; Long]. *)
Example tayy_applies_mustafilun :
  apply_tayy mustafilun = Some [Long; Short; Short; Long].
Proof. reflexivity. Qed.

(** Tayy does not apply to faulun (only 5 letters, 4th is M) *)
Example tayy_not_applies_faulun :
  apply_tayy faulun = None.
Proof. reflexivity. Qed.

(** Qabḍ applies to mafailun (5th letter is sākin) *)
Example qabḍ_applies_mafailun :
  apply_qabḍ mafailun = Some [Short; Long; Short; Long].
Proof. reflexivity. Qed.

(** Qabḍ does not apply to mustafilun (5th letter is mutaḥarrik) *)
Example qabḍ_not_applies_mustafilun :
  apply_qabḍ mustafilun = None.
Proof. reflexivity. Qed.

(** Kaff applies to mafailun (7th letter is sākin).
    mafailun letters = [M;M;S;M;S;M;S]. Delete index 6 (S):
    [M;M;S;M;S;M]. Re-syllabified: [Short; Long; Long; Short]. *)
Example kaff_applies_mafailun :
  apply_kaff mafailun = Some [Short; Long; Long; Short].
Proof. reflexivity. Qed.

(** Kaff does not apply to faulun (only 5 letters, no index 6) *)
Example kaff_not_applies_faulun :
  apply_kaff faulun = None.
Proof. reflexivity. Qed.

(** Waqṣ applies to mutafailun (2nd letter is mutaḥarrik).
    mutafailun letters = [M;M;M;S;M;M;S]. Delete index 1 (M):
    [M;M;S;M;M;S]. Re-syllabified: [Short; Long; Short; Long]. *)
Example waqṣ_applies_mutafailun :
  apply_waqṣ mutafailun = Some [Short; Long; Short; Long].
Proof. reflexivity. Qed.

(** Waqṣ does not apply to mustafilun (2nd letter is sākin, not mutaḥarrik) *)
Example waqṣ_not_applies_mustafilun :
  apply_waqṣ mustafilun = None.
Proof. reflexivity. Qed.

(** ʿAṣb applies to mufaalatun (5th letter is mutaḥarrik).
    mufaalatun letters = [M;M;S;M;M;M;S]. Replace index 4 M→S:
    [M;M;S;M;S;M;S]. Re-syllabified: [Short; Long; Long; Long]. *)
Example ʿaṣb_applies_mufaalatun :
  apply_ʿaṣb mufaalatun = Some [Short; Long; Long; Long].
Proof. reflexivity. Qed.

(** ʿAṣb does not apply to mustafilun (5th letter is mutaḥarrik but
    let's check — mustafilun letters = [M;S;M;S;M;M;S], index 4 is M).
    Actually ʿaṣb DOES apply here. Test on mafailun where index 4 is S. *)
Example ʿaṣb_not_applies_mafailun :
  apply_ʿaṣb mafailun = None.
Proof. reflexivity. Qed.

(** Qaṭʿ applies to failun *)
Example qaṭʿ_applies_failun :
  apply_qaṭʿ failun = Some [Long; Long].
Proof. reflexivity. Qed.

(** Batr applies to faulun *)
Example batr_applies_faulun :
  apply_batr faulun = Some [Long].
Proof. reflexivity. Qed.

(** Witness: khabn on mustafilun produces a 4-syllable variant *)
Example variation_applicability_witness :
  exists p, apply_khabn mustafilun = Some p /\ length p = 4.
Proof. eexists. split. reflexivity. reflexivity. Qed.

(** Example: qabḍ on mafailun produces a 4-syllable variant *)
Example variation_applicability_example :
  exists p, apply_qabḍ mafailun = Some p /\ length p = 4.
Proof. eexists. split. reflexivity. reflexivity. Qed.

(** Counterexample: waqṣ on mustafilun fails (2nd letter is sākin) *)
Example variation_applicability_counterexample :
  apply_waqṣ mustafilun = None.
Proof. reflexivity. Qed.

(** ** Zihāf-Foot Applicability Predicates *)

(** A computable predicate: does the given simple zihāf apply to the
    given foot? This is determined by whether the apply function
    succeeds (returns Some). *)

Definition zihaf_applies_to (z : zihaf) (f : foot) : bool :=
  match (match z with
         | Khabn => apply_khabn
         | Tayy => apply_tayy
         | Qabḍ => apply_qabḍ
         | Kaff => apply_kaff
         | Waqṣ => apply_waqṣ
         | ʿAṣb => apply_ʿaṣb
         | Iḍmār => apply_iḍmār
         | ʿAql => apply_ʿaql
         | Shamm => apply_shamm
         end) (foot_pattern f) with
  | Some _ => true
  | None => false
  end.

(** Applicability table: which simple zihāf apply to which feet. *)

(** Khabn applies to feet whose 2nd letter is sākin. *)
Example khabn_applicability :
  filter (zihaf_applies_to Khabn) all_feet =
    [Failun; Mustafilun; Failatun; Mafulatu].
Proof. reflexivity. Qed.

(** Tayy applies to feet whose 4th letter is sākin. *)
Example tayy_applicability :
  filter (zihaf_applies_to Tayy) all_feet =
    [Mustafilun; Mafulatu; Mutafailun].
Proof. reflexivity. Qed.

(** Qabḍ applies to feet whose 5th letter is sākin. *)
Example qabḍ_applicability :
  filter (zihaf_applies_to Qabḍ) all_feet =
    [Faulun; Failun; Mafailun; Failatun].
Proof. reflexivity. Qed.

(** Kaff applies to feet whose 7th letter is sākin. *)
Example kaff_applicability :
  filter (zihaf_applies_to Kaff) all_feet =
    [Mafailun; Mustafilun; Failatun; Mutafailun; Mufaalatun].
Proof. reflexivity. Qed.

(** Waqṣ applies to feet whose 2nd letter is mutaḥarrik. *)
Example waqṣ_applicability :
  filter (zihaf_applies_to Waqṣ) all_feet =
    [Faulun; Mafailun; Mutafailun; Mufaalatun].
Proof. reflexivity. Qed.

(** ʿAṣb applies to feet whose 5th letter is mutaḥarrik AND where
    the M→S replacement yields a well-formed letter sequence.
    Only mufāʿalatun survives: in other feet, the replacement
    creates adjacent sākin letters that letters_to_pattern rejects. *)
Example ʿaṣb_applicability :
  filter (zihaf_applies_to ʿAṣb) all_feet =
    [Mufaalatun].
Proof. reflexivity. Qed.

(** Iḍmār applies to feet whose 2nd letter is mutaḥarrik AND where
    the M→S replacement yields a well-formed letter sequence.
    Only mutafāʿilun survives. *)
Example iḍmār_applicability :
  filter (zihaf_applies_to Iḍmār) all_feet =
    [Mutafailun].
Proof. reflexivity. Qed.

(** ʿAql applies to feet whose 5th letter is mutaḥarrik AND where
    deleting it yields a well-formed letter sequence. *)
Example ʿaql_applicability :
  filter (zihaf_applies_to ʿAql) all_feet =
    [Mustafilun; Mutafailun; Mufaalatun].
Proof. reflexivity. Qed.

(** Shamm applies to feet whose 2nd letter is mutaḥarrik AND where
    the M→S replacement yields a well-formed letter sequence
    (same as iḍmār). *)
Example shamm_applicability :
  filter (zihaf_applies_to Shamm) all_feet =
    [Mutafailun].
Proof. reflexivity. Qed.

(** Witness: every simple zihāf applies to at least one foot. *)
Lemma every_zihaf_has_target : forall z : zihaf,
  exists f, zihaf_applies_to z f = true.
Proof.
  intros z. destruct z.
  - exists Mustafilun. reflexivity.
  - exists Mustafilun. reflexivity.
  - exists Mafailun. reflexivity.
  - exists Mafailun. reflexivity.
  - exists Mutafailun. reflexivity.
  - exists Mufaalatun. reflexivity.
  - exists Mutafailun. reflexivity.
  - exists Mufaalatun. reflexivity.
  - exists Mutafailun. reflexivity.
Qed.

(** Counterexample: no zihāf applies to all 8 feet. *)
Example no_universal_zihaf : forall z : zihaf,
  length (filter (zihaf_applies_to z) all_feet) < 8.
Proof. intros z. destruct z; simpl; repeat constructor. Qed.

(** ** Variation Syllable Count Properties *)

(** *** ʿIlla syllable count properties (general) *)

(** One-step unfolding lemmas for recursive ʿilla functions. *)

Lemma apply_qaṣr_cons2 : forall w w' p'',
  apply_qaṣr (w :: w' :: p'') =
  match apply_qaṣr (w' :: p'') with
  | Some rest' => Some (w :: rest')
  | None => None
  end.
Proof. destruct w; reflexivity. Qed.

Lemma apply_tasbīgh_cons2 : forall w w' p'',
  apply_tasbīgh (w :: w' :: p'') =
  match apply_tasbīgh (w' :: p'') with
  | Some rest' => Some (w :: rest')
  | None => None
  end.
Proof. destruct w; reflexivity. Qed.

Lemma apply_ḥadhf_cons2 : forall w w' p'',
  apply_ḥadhf (w :: w' :: p'') =
  match apply_ḥadhf (w' :: p'') with
  | Some rest' => Some (w :: rest')
  | None => None
  end.
Proof. destruct w; reflexivity. Qed.

Lemma apply_qaṭʿ_cons3 : forall w w' w'' p''',
  apply_qaṭʿ (w :: w' :: w'' :: p''') =
  match apply_qaṭʿ (w' :: w'' :: p''') with
  | Some rest' => Some (w :: rest')
  | None => None
  end.
Proof. destruct w; reflexivity. Qed.

(** Qaṣr preserves syllable count. *)
Lemma qaṣr_preserves_count : forall p p',
  apply_qaṣr p = Some p' -> length p' = length p.
Proof.
  induction p as [|w p' IH]; intros q H.
  - discriminate.
  - destruct p' as [|w' p''].
    + simpl in H. destruct w; inversion H; reflexivity.
    + rewrite apply_qaṣr_cons2 in H.
      destruct (apply_qaṣr (w' :: p'')) as [r|] eqn:E; try discriminate.
      inversion H; subst. simpl. f_equal. exact (IH r eq_refl).
Qed.

(** Tasbīgh preserves syllable count. *)
Lemma tasbīgh_preserves_count : forall p p',
  apply_tasbīgh p = Some p' -> length p' = length p.
Proof.
  induction p as [|w p' IH]; intros q H.
  - discriminate.
  - destruct p' as [|w' p''].
    + simpl in H. destruct w; inversion H; reflexivity.
    + rewrite apply_tasbīgh_cons2 in H.
      destruct (apply_tasbīgh (w' :: p'')) as [r|] eqn:E; try discriminate.
      inversion H; subst. simpl. f_equal. exact (IH r eq_refl).
Qed.

(** Ḥadhf reduces syllable count by 1. *)
Lemma ḥadhf_reduces_by_one : forall p p',
  apply_ḥadhf p = Some p' -> S (length p') = length p.
Proof.
  induction p as [|w p' IH]; intros q H.
  - discriminate.
  - destruct p' as [|w' p''].
    + simpl in H. destruct w; inversion H; subst; reflexivity.
    + rewrite apply_ḥadhf_cons2 in H.
      destruct (apply_ḥadhf (w' :: p'')) as [r|] eqn:E; try discriminate.
      inversion H; subst. simpl. f_equal. exact (IH r eq_refl).
Qed.

(** Qaṭʿ reduces syllable count by 1. *)
Lemma qaṭʿ_reduces_by_one : forall p p',
  apply_qaṭʿ p = Some p' -> S (length p') = length p.
Proof.
  induction p as [|w p' IH]; intros q H.
  - discriminate.
  - destruct p' as [|w' p''].
    + discriminate.
    + destruct p'' as [|w'' p'''].
      * simpl in H. destruct w; inversion H; subst; reflexivity.
      * rewrite apply_qaṭʿ_cons3 in H.
        destruct (apply_qaṭʿ (w' :: w'' :: p''')) as [r|] eqn:E; try discriminate.
        inversion H; subst. simpl. f_equal. exact (IH r eq_refl).
Qed.

(** Batr reduces syllable count by 2. *)
Lemma batr_reduces_by_two : forall p p',
  apply_batr p = Some p' -> S (S (length p')) = length p.
Proof.
  intros p q H. unfold apply_batr in H.
  destruct (apply_ḥadhf p) as [p1|] eqn:E1; try discriminate.
  apply qaṭʿ_reduces_by_one in H.
  apply ḥadhf_reduces_by_one in E1.
  lia.
Qed.

(** Qaṭf reduces syllable count by 2 on all applicable feet. *)
Lemma qaṭf_reduces_by_two : forall f p,
  apply_qaṭf (foot_pattern f) = Some p -> S (S (length p)) = foot_length f.
Proof.
  intros f p H. destruct f; simpl in H; try discriminate;
  injection H as Hp; subst p; reflexivity.
Qed.

(** Tarfīl increases syllable count by 1. *)
Lemma tarfīl_increases_by_one : forall p p',
  apply_tarfīl p = Some p' -> length p' = S (length p).
Proof.
  intros p p' H. unfold apply_tarfīl in H.
  destruct (ends_with_watad_majmu p); [|discriminate].
  injection H as Hp. subst p'. rewrite app_length. simpl. lia.
Qed.

(** Deleting a sākin letter preserves syllable count for any pattern.
    These general lemmas replace the former per-foot destruct-f proofs. *)

(** Helper: extract the sākin-deletion core from any apply function that
    deletes a sākin at a fixed index. *)
Lemma sākin_delete_preserves_count : forall p idx p',
  nth_error (pattern_to_letters p) idx = Some Sakin ->
  letters_to_pattern (delete_at idx (pattern_to_letters p)) = Some p' ->
  length p' = length p.
Proof.
  intros p idx p' Hnth Hconv.
  destruct (delete_sakin_preserves_count p idx Hnth) as [q [Hq Hqlen]].
  rewrite Hq in Hconv. injection Hconv as <-. exact Hqlen.
Qed.

Lemma khabn_preserves_count : forall p p',
  apply_khabn p = Some p' -> length p' = length p.
Proof.
  intros p p' H. unfold apply_khabn in H.
  set (ls := pattern_to_letters p) in *.
  destruct (nth_error ls 1) as [[|]|] eqn:E; try discriminate.
  exact (sākin_delete_preserves_count p 1 p' E H).
Qed.

Lemma tayy_preserves_count : forall p p',
  apply_tayy p = Some p' -> length p' = length p.
Proof.
  intros p p' H. unfold apply_tayy in H.
  set (ls := pattern_to_letters p) in *.
  destruct (nth_error ls 3) as [[|]|] eqn:E; try discriminate.
  exact (sākin_delete_preserves_count p 3 p' E H).
Qed.

Lemma qabḍ_preserves_count : forall p p',
  apply_qabḍ p = Some p' -> length p' = length p.
Proof.
  intros p p' H. unfold apply_qabḍ in H.
  set (ls := pattern_to_letters p) in *.
  destruct (nth_error ls 4) as [[|]|] eqn:E; try discriminate.
  exact (sākin_delete_preserves_count p 4 p' E H).
Qed.

Lemma kaff_preserves_count : forall p p',
  apply_kaff p = Some p' -> length p' = length p.
Proof.
  intros p p' H. unfold apply_kaff in H.
  set (ls := pattern_to_letters p) in *.
  destruct (nth_error ls 6) as [[|]|] eqn:E; try discriminate.
  exact (sākin_delete_preserves_count p 6 p' E H).
Qed.

(** ** Mora-count properties of sākin-deleting zihāf *)

(** Helper: extract the sākin-deletion mora core. *)
Lemma sākin_delete_reduces_morae : forall p idx p',
  nth_error (pattern_to_letters p) idx = Some Sakin ->
  letters_to_pattern (delete_at idx (pattern_to_letters p)) = Some p' ->
  S (pattern_morae p') = pattern_morae p.
Proof.
  intros p idx p' Hnth Hconv.
  destruct (delete_sakin_reduces_morae p idx Hnth) as [q [Hq Hqmor]].
  rewrite Hq in Hconv. injection Hconv as <-. exact Hqmor.
Qed.

Lemma khabn_reduces_morae : forall p p',
  apply_khabn p = Some p' -> S (pattern_morae p') = pattern_morae p.
Proof.
  intros p p' H. unfold apply_khabn in H.
  set (ls := pattern_to_letters p) in *.
  destruct (nth_error ls 1) as [[|]|] eqn:E; try discriminate.
  exact (sākin_delete_reduces_morae p 1 p' E H).
Qed.

Lemma tayy_reduces_morae : forall p p',
  apply_tayy p = Some p' -> S (pattern_morae p') = pattern_morae p.
Proof.
  intros p p' H. unfold apply_tayy in H.
  set (ls := pattern_to_letters p) in *.
  destruct (nth_error ls 3) as [[|]|] eqn:E; try discriminate.
  exact (sākin_delete_reduces_morae p 3 p' E H).
Qed.

Lemma qabḍ_reduces_morae : forall p p',
  apply_qabḍ p = Some p' -> S (pattern_morae p') = pattern_morae p.
Proof.
  intros p p' H. unfold apply_qabḍ in H.
  set (ls := pattern_to_letters p) in *.
  destruct (nth_error ls 4) as [[|]|] eqn:E; try discriminate.
  exact (sākin_delete_reduces_morae p 4 p' E H).
Qed.

Lemma kaff_reduces_morae : forall p p',
  apply_kaff p = Some p' -> S (pattern_morae p') = pattern_morae p.
Proof.
  intros p p' H. unfold apply_kaff in H.
  set (ls := pattern_to_letters p) in *.
  destruct (nth_error ls 6) as [[|]|] eqn:E; try discriminate.
  exact (sākin_delete_reduces_morae p 6 p' E H).
Qed.

(** ** Mora-count properties of mutaḥarrik-modifying zihāf *)

(** Iḍmār, shamm, and ʿaṣb preserve morae: they make a mutaḥarrik
    quiescent, merging two Shorts into one Long (1+1 = 2). *)
Lemma iḍmār_preserves_morae : forall f p,
  apply_iḍmār (foot_pattern f) = Some p -> pattern_morae p = pattern_morae (foot_pattern f).
Proof.
  intros f p H. destruct f; simpl in H; try discriminate;
  injection H as Hp; subst p; reflexivity.
Qed.

Lemma shamm_preserves_morae : forall f p,
  apply_shamm (foot_pattern f) = Some p -> pattern_morae p = pattern_morae (foot_pattern f).
Proof.
  intros f p H. destruct f; simpl in H; try discriminate;
  injection H as Hp; subst p; reflexivity.
Qed.

Lemma ʿaṣb_preserves_morae : forall f p,
  apply_ʿaṣb (foot_pattern f) = Some p -> pattern_morae p = pattern_morae (foot_pattern f).
Proof.
  intros f p H. destruct f; simpl in H; try discriminate;
  injection H as Hp; subst p; reflexivity.
Qed.

(** Waqṣ and ʿaql delete a mutaḥarrik (Short syllable), reducing morae by 1. *)
Lemma waqṣ_reduces_morae : forall f p,
  apply_waqṣ (foot_pattern f) = Some p -> S (pattern_morae p) = pattern_morae (foot_pattern f).
Proof.
  intros f p H. destruct f; simpl in H; try discriminate;
  injection H as Hp; subst p; reflexivity.
Qed.

Lemma ʿaql_reduces_morae : forall f p,
  apply_ʿaql (foot_pattern f) = Some p -> S (pattern_morae p) = pattern_morae (foot_pattern f).
Proof.
  intros f p H. destruct f; simpl in H; try discriminate;
  injection H as Hp; subst p; reflexivity.
Qed.

(** Waqṣ reduces syllable count by 1 on all applicable feet. *)
Lemma waqṣ_reduces_count : forall f p,
  apply_waqṣ (foot_pattern f) = Some p -> S (length p) = foot_length f.
Proof.
  intros f p H. destruct f; simpl in H; try discriminate;
  injection H as Hp; subst p; reflexivity.
Qed.

(** ʿAṣb reduces syllable count by 1 on all applicable feet. *)
Lemma ʿaṣb_reduces_count : forall f p,
  apply_ʿaṣb (foot_pattern f) = Some p -> S (length p) = foot_length f.
Proof.
  intros f p H. destruct f; simpl in H; try discriminate;
  injection H as Hp; subst p; reflexivity.
Qed.

(** Iḍmār reduces syllable count by 1 on all applicable feet. *)
Lemma iḍmār_reduces_count : forall f p,
  apply_iḍmār (foot_pattern f) = Some p -> S (length p) = foot_length f.
Proof.
  intros f p H. destruct f; simpl in H; try discriminate;
  injection H as Hp; subst p; reflexivity.
Qed.

(** ʿAql reduces syllable count by 1 on all applicable feet. *)
Lemma ʿaql_reduces_count : forall f p,
  apply_ʿaql (foot_pattern f) = Some p -> S (length p) = foot_length f.
Proof.
  intros f p H. destruct f; simpl in H; try discriminate;
  injection H as Hp; subst p; reflexivity.
Qed.

(** Shamm reduces syllable count by 1 on all applicable feet (same as iḍmār). *)
Lemma shamm_reduces_count : forall f p,
  apply_shamm (foot_pattern f) = Some p -> S (length p) = foot_length f.
Proof.
  intros f p H. destruct f; simpl in H; try discriminate;
  injection H as Hp; subst p; reflexivity.
Qed.

(** Witness: khabn on mustafilun preserves 4-syllable count *)
Example khabn_count_witness :
  exists p, apply_khabn mustafilun = Some p /\ length p = 4.
Proof. eexists. split; reflexivity. Qed.

(** Example: waqṣ on mutafailun reduces count from 5 to 4 *)
Example waqṣ_count_example :
  exists p, apply_waqṣ mutafailun = Some p /\ length p = 4 /\ foot_length Mutafailun = 5.
Proof. eexists. repeat split; reflexivity. Qed.

(** Counterexample: ḥadhf on faulun reduces from 3 to 2, not 3 *)
Example ḥadhf_count_counterexample :
  exists p, apply_ḥadhf faulun = Some p /\ length p = 2 /\ length p <> 3.
Proof. eexists. repeat split; try reflexivity. discriminate. Qed.

(** ** No Variation Maps a Canonical Foot to Another Canonical Foot *)

(** A simple zihāf applied to any canonical foot never produces another
    canonical foot pattern. This is verified exhaustively: for each
    (zihāf, foot) pair where the zihāf applies, the result is not in
    the set of canonical foot patterns. *)

Definition apply_zihaf (z : zihaf) : pattern -> option pattern :=
  match z with
  | Khabn => apply_khabn
  | Tayy => apply_tayy
  | Qabḍ => apply_qabḍ
  | Kaff => apply_kaff
  | Waqṣ => apply_waqṣ
  | ʿAṣb => apply_ʿaṣb
  | Iḍmār => apply_iḍmār
  | ʿAql => apply_ʿaql
  | Shamm => apply_shamm
  end.

(** Compound zihāf dispatch function. *)
Definition apply_compound_zihaf (z : compound_zihaf) : pattern -> option pattern :=
  match z with
  | Khazl => apply_khazl
  | Khabl => apply_khabl
  | Shakl => apply_shakl
  | Naqs => apply_naqs
  end.

(** ʿIlla dispatch function. Uses guarded variants of qaṭʿ, ḥadhf,
    and kashf to enforce traditional preconditions (watad/sabab ending)
    at the pattern level. *)
Definition apply_ʿilla (i : ʿilla) : pattern -> option pattern :=
  match i with
  | Qaṭʿ => apply_qaṭʿ_guarded
  | Qaṣr => apply_qaṣr
  | Ḥadhf => apply_ḥadhf_guarded
  | Tasbīgh => apply_tasbīgh
  | Batr => apply_batr
  | Qaṭf => apply_qaṭf
  | Tarfīl => apply_tarfīl
  | Tadhyīl => apply_tadhyīl
  | Ḥadhādh => apply_ḥadhādh
  | Ṣalm => apply_ṣalm
  | Kashf => apply_kashf_guarded
  | Waqf => apply_waqf
  | Tashʿīth => apply_tashʿīth
  end.

(** The claim "no variation produces a canonical foot" is ALMOST true.
    There are exactly three exceptions:
    - ʿaṣb on mufāʿalatun produces mafāʿīlun. This is well-known in the
      tradition — it is why ʿaṣb on Wāfir yields a Hazaj-like pattern.
    - iḍmār on mutafāʿilun produces mustafʿilun. This is the classical
      relationship between Kāmil and Rajaz.
    - shamm on mutafāʿilun produces mustafʿilun. Metrically identical
      to iḍmār; the distinction is phonetic only.

    We prove the claim for all other (zihāf, foot) pairs exhaustively. *)

(** Exception 1: ʿaṣb on mufaalatun yields mafailun's pattern. *)
Example ʿaṣb_mufaalatun_is_mafailun :
  apply_ʿaṣb mufaalatun = Some mafailun.
Proof. reflexivity. Qed.

(** Exception 2: iḍmār on mutafailun yields mustafilun's pattern. *)
Example iḍmār_mutafailun_is_mustafilun :
  apply_iḍmār mutafailun = Some mustafilun.
Proof. reflexivity. Qed.

(** Exception 3: shamm on mutafailun yields mustafilun's pattern. *)
Example shamm_mutafailun_is_mustafilun :
  apply_shamm mutafailun = Some mustafilun.
Proof. reflexivity. Qed.

(** For all other applicable (zihāf, foot) pairs, the result is not a foot. *)
Lemma zihaf_no_foot_except_known : forall z f p,
  apply_zihaf z (foot_pattern f) = Some p ->
  (z = ʿAṣb /\ f = Mufaalatun) \/ (z = Iḍmār /\ f = Mutafailun) \/
  (z = Shamm /\ f = Mutafailun) \/ is_foot p = false.
Proof.
  intros z f p H.
  destruct z, f; simpl in H; try discriminate;
  injection H as Hp; subst p;
  first [ left; split; reflexivity
        | right; left; split; reflexivity
        | right; right; left; split; reflexivity
        | right; right; right; reflexivity ].
Qed.

(** Witness: khabn on mustafilun gives [Short;Long;Short;Long], not a foot *)
Example zihaf_no_foot_witness :
  apply_khabn mustafilun = Some [Short; Long; Short; Long] /\
  is_foot [Short; Long; Short; Long] = false.
Proof. split; reflexivity. Qed.

(** Example: qabḍ on mafailun gives [Short;Long;Short;Long], not a foot *)
Example zihaf_no_foot_example :
  apply_qabḍ mafailun = Some [Short; Long; Short; Long] /\
  is_foot [Short; Long; Short; Long] = false.
Proof. split; reflexivity. Qed.

(** Counterexample: ʿaṣb on mufaalatun IS a foot *)
Example zihaf_foot_counterexample :
  exists p, apply_ʿaṣb mufaalatun = Some p /\ is_foot p = true.
Proof. exists mafailun. split; reflexivity. Qed.

(** Counterexample: iḍmār on mutafailun IS a foot *)
Example zihaf_foot_counterexample_iḍmār :
  exists p, apply_iḍmār mutafailun = Some p /\ is_foot p = true.
Proof. exists mustafilun. split; reflexivity. Qed.

(** Counterexample: shamm on mutafailun IS a foot *)
Example zihaf_foot_counterexample_shamm :
  exists p, apply_shamm mutafailun = Some p /\ is_foot p = true.
Proof. exists mustafilun. split; reflexivity. Qed.

(** End of Section 7: Variation Rules *)

(** * Section 8: Foot Positions and Variation Scope *)

(** In a hemistich, feet occupy three positional roles:
    - Ḥashw (حشو, "stuffing"): all interior feet (not the last)
    - ʿArūḍ (عروض): the last foot of the first hemistich (ṣadr)
    - Ḍarb (ضرب): the last foot of the second hemistich (ʿajuz)

    The traditional rule: zihāf applies only in ḥashw positions;
    ʿilla applies only in ʿarūḍ and ḍarb. *)

(** ** Foot Position Type *)

Inductive foot_position : Type :=
  | Hashw     (* interior foot *)
  | Arud      (* last foot of first hemistich *)
  | Darb.     (* last foot of second hemistich *)

(** ** Decidable Equality for Foot Position *)

Definition foot_position_eq_dec (p1 p2 : foot_position)
  : {p1 = p2} + {p1 <> p2}.
Proof.
  destruct p1, p2; try (left; reflexivity); right; discriminate.
Defined.

(** ** Position Assignment *)

(** Given a list of feet (a hemistich), assign positions:
    all but the last are Hashw, the last is the given terminal position. *)

Fixpoint assign_positions_aux (fs : list foot) (terminal : foot_position)
  : list (foot * foot_position) :=
  match fs with
  | [] => []
  | [f] => [(f, terminal)]
  | f :: rest => (f, Hashw) :: assign_positions_aux rest terminal
  end.

Definition assign_sadr_positions (m : meter) : list (foot * foot_position) :=
  assign_positions_aux (meter_feet m) Arud.

Definition assign_ajuz_positions (m : meter) : list (foot * foot_position) :=
  assign_positions_aux (meter_feet m) Darb.

(** ** Variation Scope *)

(** Zihāf is permitted only at Hashw positions. *)
Definition zihaf_permitted (pos : foot_position) : bool :=
  match pos with
  | Hashw => true
  | _ => false
  end.

(** ʿIlla is permitted only at ʿArūḍ and Ḍarb positions. *)
Definition ʿilla_permitted (pos : foot_position) : bool :=
  match pos with
  | Arud => true
  | Darb => true
  | Hashw => false
  end.

(** ** Position Assignment Witnesses *)

(** Witness: Tawil ṣadr = [Faulun:Hashw; Mafailun:Hashw; Faulun:Hashw; Mafailun:ʿArūḍ] *)
Example tawil_sadr_positions :
  assign_sadr_positions Tawil =
    [(Faulun, Hashw); (Mafailun, Hashw); (Faulun, Hashw); (Mafailun, Arud)].
Proof. reflexivity. Qed.

(** Example: Hazaj ṣadr = [Mafailun:Hashw; Mafailun:ʿArūḍ] *)
Example hazaj_sadr_positions :
  assign_sadr_positions Hazaj =
    [(Mafailun, Hashw); (Mafailun, Arud)].
Proof. reflexivity. Qed.

(** Counterexample: Kamil ʿajuz last foot is Ḍarb, not ʿArūḍ *)
Example kamil_ajuz_positions :
  assign_ajuz_positions Kamil =
    [(Mutafailun, Hashw); (Mutafailun, Hashw); (Mutafailun, Darb)].
Proof. reflexivity. Qed.

(** ** Scope Verification *)

(** Witness: zihāf permitted at Hashw *)
Example zihaf_scope_witness : zihaf_permitted Hashw = true.
Proof. reflexivity. Qed.

(** Example: zihāf NOT permitted at ʿArūḍ *)
Example zihaf_scope_example : zihaf_permitted Arud = false.
Proof. reflexivity. Qed.

(** Counterexample: ʿilla NOT permitted at Hashw *)
Example ʿilla_scope_counterexample : ʿilla_permitted Hashw = false.
Proof. reflexivity. Qed.

(** Witness: ʿilla permitted at Ḍarb *)
Example ʿilla_scope_witness : ʿilla_permitted Darb = true.
Proof. reflexivity. Qed.

(** Example: ʿilla permitted at ʿArūḍ *)
Example ʿilla_scope_example : ʿilla_permitted Arud = true.
Proof. reflexivity. Qed.

(** ** Mutual Exclusion of Scope *)

Lemma zihaf_ʿilla_exclusive : forall pos,
  zihaf_permitted pos = true -> ʿilla_permitted pos = false.
Proof.
  intros pos H. destruct pos; simpl in *; try discriminate; reflexivity.
Qed.

Lemma ʿilla_zihaf_exclusive : forall pos,
  ʿilla_permitted pos = true -> zihaf_permitted pos = false.
Proof.
  intros pos H. destruct pos; simpl in *; try discriminate; reflexivity.
Qed.

(** Witness: Hashw is zihāf-only *)
Example scope_exclusive_witness :
  zihaf_permitted Hashw = true /\ ʿilla_permitted Hashw = false.
Proof. split; reflexivity. Qed.

(** Example: Darb is ʿilla-only *)
Example scope_exclusive_example :
  ʿilla_permitted Darb = true /\ zihaf_permitted Darb = false.
Proof. split; reflexivity. Qed.

(** Counterexample: no position permits both *)
Example scope_exclusive_counterexample : forall pos,
  ~ (zihaf_permitted pos = true /\ ʿilla_permitted pos = true).
Proof.
  intros pos [H1 H2]. destruct pos; simpl in *; discriminate.
Qed.

(** End of Section 8: Foot Positions and Variation Scope *)

(** * Section 9: Legal Variation Rules Per Meter *)

(** The tradition restricts which zihāf are considered legal for each
    foot type, beyond the structural preconditions (which letter positions
    have the right type). These rules reflect centuries of scholarly
    consensus on which variations produce acceptable verse. *)

(** ** Boolean Equality for Variation Types *)

Definition zihaf_eqb (z1 z2 : zihaf) : bool :=
  match zihaf_eq_dec z1 z2 with left _ => true | right _ => false end.

Definition compound_zihaf_eqb (z1 z2 : compound_zihaf) : bool :=
  match compound_zihaf_eq_dec z1 z2 with left _ => true | right _ => false end.

Definition ʿilla_eqb (i1 i2 : ʿilla) : bool :=
  match ʿilla_eq_dec i1 i2 with left _ => true | right _ => false end.

(** ** Permitted Simple Zihāf by Foot Type *)

(** Standard rules for ḥashw (interior) positions. Meter-specific
    refinements (e.g., kaff on mafāʿīlun is rare in Ṭawīl) are
    not yet modeled — these are the consensus per-foot-type rules. *)

Definition foot_permitted_zihaf (f : foot) : list zihaf :=
  match f with
  | Faulun => [Qabḍ]
  | Failun => [Khabn; Qabḍ]
  | Mafailun => [Qabḍ; Kaff]
  | Mustafilun => [Khabn; Tayy]
  | Failatun => [Khabn; Kaff]
  | Mafulatu => [Khabn; Tayy]
  | Mutafailun => [Iḍmār; Waqṣ; Shamm]
  | Mufaalatun => [ʿAṣb; ʿAql]
  end.

(** ** Permitted Compound Zihāf by Foot Type *)

Definition foot_permitted_compound (f : foot) : list compound_zihaf :=
  match f with
  | Mustafilun => [Khabl]
  | Failatun => [Shakl]
  | Mutafailun => [Khazl]
  | Mufaalatun => [Naqs]
  | _ => []
  end.

(** ** Legality Predicates *)

Definition is_legal_zihaf_for_foot (z : zihaf) (f : foot) : bool :=
  existsb (zihaf_eqb z) (foot_permitted_zihaf f).

Definition is_legal_compound_for_foot (z : compound_zihaf) (f : foot) : bool :=
  existsb (compound_zihaf_eqb z) (foot_permitted_compound f).

Definition is_legal_zihaf_at (m : meter) (pos : nat) (z : zihaf) : bool :=
  match nth_error (meter_feet m) pos with
  | Some f => is_legal_zihaf_for_foot z f
  | None => false
  end.

Definition is_legal_compound_at (m : meter) (pos : nat) (z : compound_zihaf) : bool :=
  match nth_error (meter_feet m) pos with
  | Some f => is_legal_compound_for_foot z f
  | None => false
  end.

(** ** Compound Zihāf Applicability *)

Definition compound_zihaf_applies_to (z : compound_zihaf) (f : foot) : bool :=
  match apply_compound_zihaf z (foot_pattern f) with
  | Some _ => true
  | None => false
  end.

(** ** Soundness: Every Permitted Zihāf Is Structurally Applicable *)

(** No permitted zihāf is a dead letter — each one actually applies
    to its designated foot. *)

Lemma permitted_zihaf_applicable : forall f z,
  is_legal_zihaf_for_foot z f = true ->
  zihaf_applies_to z f = true.
Proof.
  intros f z H.
  destruct f, z; simpl in *; try discriminate; reflexivity.
Qed.

Lemma permitted_compound_applicable : forall f z,
  is_legal_compound_for_foot z f = true ->
  compound_zihaf_applies_to z f = true.
Proof.
  intros f z H.
  destruct f, z; simpl in *; try discriminate; reflexivity.
Qed.

(** The converse does not hold: structural applicability does not imply
    traditional legality. Kaff applies to mustafilun (7th letter is sākin)
    but is not traditionally permitted. *)
Example applicable_not_legal :
  zihaf_applies_to Kaff Mustafilun = true /\
  is_legal_zihaf_for_foot Kaff Mustafilun = false.
Proof. split; reflexivity. Qed.

(** ** Permitted ʿIlla at Terminal Positions *)

(** ʿIlla at ʿarūḍ (last foot of first hemistich) for each meter.
    These follow the standard classical sources; some meters have no
    ʿilla at ʿarūḍ (the foot appears in its canonical form). *)

Definition permitted_arud_illa (m : meter) : list ʿilla :=
  match m with
  | Tawil => [Ḥadhf; Qaṣr]
  | Madid => [Ḥadhf]
  | Basit => []
  | Wafir => [Qaṭf]
  | Kamil => []
  | Hazaj => [Ḥadhf]
  | Rajaz => []
  | Ramal => [Ḥadhf]
  | Sari => [Kashf]
  | Munsarih => []
  | Khafif => []
  | Mudari => []
  | Muqtadab => []
  | Mujtathth => []
  | Mutaqarib => [Ḥadhf]
  | Mutadarik => []
  end.

(** ʿIlla at ḍarb (last foot of second hemistich) for each meter.
    The ḍarb admits more variation than the ʿarūḍ in most meters. *)

Definition permitted_darb_illa (m : meter) : list ʿilla :=
  match m with
  | Tawil => [Ḥadhf; Qaṣr; Qaṭʿ]
  | Madid => [Ḥadhf; Qaṣr; Qaṭʿ; Batr]
  | Basit => [Qaṭʿ]
  | Wafir => [Qaṭf; Ḥadhf]
  | Kamil => [Qaṭʿ; Ḥadhādh]
  | Hazaj => [Ḥadhf; Qaṣr]
  | Rajaz => [Qaṭʿ]
  | Ramal => [Ḥadhf; Qaṣr; Qaṭʿ; Tasbīgh]
  | Sari => [Kashf; Waqf; Ṣalm]
  | Munsarih => [Qaṭʿ]
  | Khafif => [Qaṣr; Qaṭʿ; Tasbīgh]
  | Mudari => [Qaṣr]
  | Muqtadab => [Qaṭʿ]
  | Mujtathth => [Qaṣr; Qaṭʿ]
  | Mutaqarib => [Ḥadhf; Qaṣr; Qaṭʿ; Batr]
  | Mutadarik => [Qaṭʿ; Tashʿīth]
  end.

Definition is_legal_arud_illa (m : meter) (i : ʿilla) : bool :=
  existsb (ʿilla_eqb i) (permitted_arud_illa m).

Definition is_legal_darb_illa (m : meter) (i : ʿilla) : bool :=
  existsb (ʿilla_eqb i) (permitted_darb_illa m).

(** ** Witnesses *)

(** Khabn is legal for mustafilun. *)
Example legal_khabn_mustafilun :
  is_legal_zihaf_for_foot Khabn Mustafilun = true.
Proof. reflexivity. Qed.

(** Qabḍ is legal for faulun. *)
Example legal_qabḍ_faulun :
  is_legal_zihaf_for_foot Qabḍ Faulun = true.
Proof. reflexivity. Qed.

(** Khabn is NOT legal for faulun (2nd letter is mutaḥarrik, and the
    tradition does not list khabn for faʿūlun). *)
Example illegal_khabn_faulun :
  is_legal_zihaf_for_foot Khabn Faulun = false.
Proof. reflexivity. Qed.

(** Khabl (compound) is legal for mustafilun. *)
Example legal_khabl_mustafilun :
  is_legal_compound_for_foot Khabl Mustafilun = true.
Proof. reflexivity. Qed.

(** Khabn at position 0 of Rajaz (mustafilun) is legal. *)
Example legal_khabn_rajaz_pos0 :
  is_legal_zihaf_at Rajaz 0 Khabn = true.
Proof. reflexivity. Qed.

(** Qabḍ at position 0 of Rajaz (mustafilun) is NOT legal. *)
Example illegal_qabḍ_rajaz_pos0 :
  is_legal_zihaf_at Rajaz 0 Qabḍ = false.
Proof. reflexivity. Qed.

(** Ḥadhf is legal at ʿarūḍ of Ṭawīl. *)
Example legal_ḥadhf_tawil_arud :
  is_legal_arud_illa Tawil Ḥadhf = true.
Proof. reflexivity. Qed.

(** Qaṭʿ is legal at ḍarb of Kāmil. *)
Example legal_qaṭʿ_kamil_darb :
  is_legal_darb_illa Kamil Qaṭʿ = true.
Proof. reflexivity. Qed.

(** Ḍarb admits more ʿilla than ʿarūḍ in most meters. *)
Example darb_richer_than_arud :
  length (permitted_darb_illa Ramal) > length (permitted_arud_illa Ramal).
Proof. simpl. lia. Qed.

(** Every foot has at least one permitted simple zihāf. *)
Lemma every_foot_has_zihaf : forall f : foot,
  foot_permitted_zihaf f <> [].
Proof.
  intros f. destruct f; discriminate.
Qed.

(** The number of permitted simple zihāf per foot is between 1 and 3. *)
Lemma foot_zihaf_count_bounds : forall f : foot,
  1 <= length (foot_permitted_zihaf f) <= 3.
Proof.
  intros f. destruct f; simpl; lia.
Qed.

(** End of Section 9: Legal Variation Rules Per Meter *)

(** * Section 10: Scansion *)

(** Scansion is the process of analyzing a verse to determine its metrical pattern.
    In a full implementation, this would involve:
    1. Phonological analysis of Arabic text
    2. Syllable boundary detection
    3. Weight assignment (open/closed syllables)
    4. Pattern matching against known meters

    Here we formalize the abstract scansion process, assuming syllable weights
    are already determined. *)

(** ** Foot Annotation *)

(** Records what variation (if any) was applied at each foot position
    during scansion. *)

Inductive foot_annotation : Type :=
  | Canonical                            (* no variation *)
  | SimpleZihaf   : zihaf -> foot_annotation
  | CompoundZihaf : compound_zihaf -> foot_annotation
  | Illa          : ʿilla -> foot_annotation.

(** ** Scansion Result *)

Inductive scan_result : Type :=
  | ScanSuccess : meter -> scan_result
  | ScanVariant : meter -> list foot_annotation -> scan_result
  | ScanFailed : scan_result.

(** ** Decidable Equality for Foot Annotation *)

Definition foot_annotation_eq_dec (a1 a2 : foot_annotation)
  : {a1 = a2} + {a1 <> a2}.
Proof.
  destruct a1 as [|z1|c1|i1], a2 as [|z2|c2|i2];
    try (left; reflexivity); try (right; discriminate).
  - destruct (zihaf_eq_dec z1 z2) as [->|H].
    + left. reflexivity.
    + right. intros Heq. injection Heq. exact H.
  - destruct (compound_zihaf_eq_dec c1 c2) as [->|H].
    + left. reflexivity.
    + right. intros Heq. injection Heq. exact H.
  - destruct (ʿilla_eq_dec i1 i2) as [->|H].
    + left. reflexivity.
    + right. intros Heq. injection Heq. exact H.
Defined.

(** ** Decidable Equality for Scan Result *)

Fixpoint foot_annotation_list_eq_dec (l1 l2 : list foot_annotation)
  : {l1 = l2} + {l1 <> l2}.
Proof.
  destruct l1 as [|a1 l1'], l2 as [|a2 l2'];
    try (left; reflexivity); try (right; discriminate).
  destruct (foot_annotation_eq_dec a1 a2) as [->|Ha].
  - destruct (foot_annotation_list_eq_dec l1' l2') as [->|Hl].
    + left. reflexivity.
    + right. intros Heq. apply Hl. congruence.
  - right. congruence.
Defined.

Definition scan_result_eq_dec (s1 s2 : scan_result) : {s1 = s2} + {s1 <> s2}.
Proof.
  destruct s1 as [m1|m1 a1|], s2 as [m2|m2 a2|];
    try (right; discriminate); try (left; reflexivity).
  - destruct (meter_eq_dec m1 m2) as [->|Hm].
    + left. reflexivity.
    + right. congruence.
  - destruct (meter_eq_dec m1 m2) as [->|Hm].
    + destruct (foot_annotation_list_eq_dec a1 a2) as [->|Ha].
      * left. reflexivity.
      * right. congruence.
    + right. congruence.
Defined.

(** Witness: scan_result_eq_dec ScanFailed ScanFailed *)
Example scan_result_eq_dec_witness :
  exists pf, scan_result_eq_dec ScanFailed ScanFailed = left pf.
Proof. eexists. reflexivity. Qed.

(** Example: scan_result_eq_dec (ScanSuccess Tawil) (ScanSuccess Tawil) *)
Example scan_result_eq_dec_example :
  exists pf, scan_result_eq_dec (ScanSuccess Tawil) (ScanSuccess Tawil) = left pf.
Proof. eexists. reflexivity. Qed.

(** Counterexample: scan_result_eq_dec returns right for different results *)
Example scan_result_eq_dec_counterexample :
  exists pf, scan_result_eq_dec (ScanSuccess Tawil) ScanFailed = right pf.
Proof. eexists. reflexivity. Qed.

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

(** ** Combinatorial Scansion *)

(** Annotated variant: a pattern paired with the variation that
    produced it, enabling the scanner to report what happened. *)

Definition annotated_variant := (pattern * foot_annotation)%type.

(** For each foot, compute all legal annotated variants at a ḥashw
    (interior) position: canonical pattern plus results of applying
    legal simple and compound zihāf. *)

Definition foot_hashw_variants (f : foot) : list annotated_variant :=
  (foot_pattern f, Canonical) ::
  flat_map (fun z =>
    match apply_zihaf z (foot_pattern f) with
    | Some p => [(p, SimpleZihaf z)]
    | None => []
    end) (foot_permitted_zihaf f) ++
  flat_map (fun z =>
    match apply_compound_zihaf z (foot_pattern f) with
    | Some p => [(p, CompoundZihaf z)]
    | None => []
    end) (foot_permitted_compound f).

(** For the terminal foot, compute all legal annotated variants:
    canonical pattern, legal zihāf (simple and compound), and legal
    ʿilla from both ʿarūḍ and ḍarb lists. *)

Definition foot_terminal_variants (m : meter) : list annotated_variant :=
  let f := last (meter_feet m) Faulun in
  (foot_pattern f, Canonical) ::
  flat_map (fun z =>
    match apply_zihaf z (foot_pattern f) with
    | Some p => [(p, SimpleZihaf z)]
    | None => []
    end) (foot_permitted_zihaf f) ++
  flat_map (fun z =>
    match apply_compound_zihaf z (foot_pattern f) with
    | Some p => [(p, CompoundZihaf z)]
    | None => []
    end) (foot_permitted_compound f) ++
  flat_map (fun i =>
    match apply_ʿilla i (foot_pattern f) with
    | Some p => [(p, Illa i)]
    | None => []
    end) (permitted_arud_illa m ++ permitted_darb_illa m).

(** Assemble the per-foot annotated variant lists for a meter. *)

Definition meter_foot_variants (m : meter) : list (list annotated_variant) :=
  let feet := meter_feet m in
  let init := removelast feet in
  map foot_hashw_variants init ++ [foot_terminal_variants m].

(** Recursive foot-by-foot matching with annotation collection.
    Returns the first matching annotation list, or None. *)

Fixpoint match_variant_pattern
  (p : pattern) (foot_vars : list (list annotated_variant))
  : option (list foot_annotation) :=
  match foot_vars with
  | [] => match p with [] => Some [] | _ => None end
  | vs :: rest =>
      (fix try_variants (candidates : list annotated_variant)
        : option (list foot_annotation) :=
        match candidates with
        | [] => None
        | (v, ann) :: cs =>
            if pattern_eqb (firstn (length v) p) v then
              match match_variant_pattern (skipn (length v) p) rest with
              | Some anns => Some (ann :: anns)
              | None => try_variants cs
              end
            else try_variants cs
        end) vs
  end.

(** Full scansion: try exact match first, then combinatorial variant
    matching across all meters using foot-by-foot decomposition.
    ScanVariant now carries the per-foot annotation list. *)

Definition scan (p : pattern) : scan_result :=
  match pattern_to_meter p with
  | Some m => ScanSuccess m
  | None =>
      (fix try_meters (ms : list meter) : scan_result :=
        match ms with
        | [] => ScanFailed
        | m :: ms' =>
            match match_variant_pattern p (meter_foot_variants m) with
            | Some anns => ScanVariant m anns
            | None => try_meters ms'
            end
        end) all_meters
  end.

(** Witness: exact match still works through scan. *)
Example scan_witness :
  scan (meter_pattern Tawil) = ScanSuccess Tawil.
Proof. vm_compute. reflexivity. Qed.

(** Example: khabl on the first foot of Rajaz — the annotation
    reports CompoundZihaf Khabl at foot 1, Canonical at feet 2-3. *)
Example scan_variant_example :
  scan [Short; Short; Short; Long;
        Long; Long; Short; Long;
        Long; Long; Short; Long]
    = ScanVariant Rajaz [CompoundZihaf Khabl; Canonical; Canonical].
Proof. vm_compute. reflexivity. Qed.

(** Example: khabl on the third (terminal) foot of Rajaz. *)
Example scan_perfoot_example :
  scan [Long; Long; Short; Long;
        Long; Long; Short; Long;
        Short; Short; Short; Long]
    = ScanVariant Rajaz [Canonical; Canonical; CompoundZihaf Khabl].
Proof. vm_compute. reflexivity. Qed.

(** Example: this 12-syllable pattern matches Kāmil with waqṣ
    on foot 1 and iḍmār on feet 2-3 (mutafāʿilun → mustafʿilun). *)
Example scan_ambiguity_example :
  scan [Short; Long; Short; Long;
        Long; Long; Short; Long;
        Long; Long; Short; Long]
    = ScanVariant Kamil [SimpleZihaf Waqṣ; SimpleZihaf Iḍmār; SimpleZihaf Iḍmār].
Proof. vm_compute. reflexivity. Qed.

(** Example: multi-foot simultaneous variation — khabl on foot 1
    and tayy on foot 2 of Rajaz, both reported in annotations. *)
Example scan_multi_foot_example :
  scan [Short; Short; Short; Long;
        Long; Short; Short; Long;
        Long; Long; Short; Long]
    = ScanVariant Rajaz [CompoundZihaf Khabl; SimpleZihaf Tayy; Canonical].
Proof. vm_compute. reflexivity. Qed.

(** Example: ʿilla at the terminal position — qaṭʿ on the last
    foot of Rajaz, reported as Illa Qaṭʿ. *)
Example scan_illa_example :
  scan [Long; Long; Short; Long;
        Long; Long; Short; Long;
        Long; Long; Long]
    = ScanVariant Rajaz [Canonical; Canonical; Illa Qaṭʿ].
Proof. vm_compute. reflexivity. Qed.

(** Counterexample: gibberish still fails. *)
Example scan_counterexample :
  scan [Short; Short; Short] = ScanFailed.
Proof. vm_compute. reflexivity. Qed.

(** ** Scansion Soundness *)

(** A pattern is a valid variant decomposition of a list of per-foot
    variant sets if it can be split into consecutive segments, where
    each segment is drawn from the corresponding variant set. *)

Fixpoint is_variant_decomposition
  (p : pattern) (foot_vars : list (list annotated_variant))
  : Prop :=
  match foot_vars with
  | [] => p = []
  | vs :: rest =>
      exists v ann,
        In (v, ann) vs /\
        firstn (length v) p = v /\
        is_variant_decomposition (skipn (length v) p) rest
  end.

(** The inner try_variants loop: if it returns Some, one of the
    candidates matched and the rest decomposed. *)

Lemma try_variants_sound : forall candidates p rest anns,
  (fix try_variants (cs : list annotated_variant)
    : option (list foot_annotation) :=
    match cs with
    | [] => None
    | (v, ann) :: cs' =>
        if pattern_eqb (firstn (length v) p) v then
          match match_variant_pattern (skipn (length v) p) rest with
          | Some anns => Some (ann :: anns)
          | None => try_variants cs'
          end
        else try_variants cs'
    end) candidates = Some anns ->
  (forall p' anns',
    match_variant_pattern p' rest = Some anns' ->
    is_variant_decomposition p' rest) ->
  exists v ann,
    In (v, ann) candidates /\
    firstn (length v) p = v /\
    is_variant_decomposition (skipn (length v) p) rest.
Proof.
  induction candidates as [|[v ann] cs IH]; intros p rest anns H IHmvp.
  - discriminate.
  - simpl in H.
    destruct (pattern_eqb (firstn (length v) p) v) eqn:Epfx.
    + apply pattern_eqb_eq in Epfx.
      destruct (match_variant_pattern (skipn (length v) p) rest) as [anns'|] eqn:Emvp.
      * injection H as Hanns.
        exists v, ann. split.
        -- left. reflexivity.
        -- split. exact Epfx. exact (IHmvp _ _ Emvp).
      * destruct (IH p rest anns H IHmvp) as [v' [ann' [Hin [Hpfx Hdecomp]]]].
        exists v', ann'. split.
        -- right. exact Hin.
        -- split; assumption.
    + destruct (IH p rest anns H IHmvp) as [v' [ann' [Hin [Hpfx Hdecomp]]]].
      exists v', ann'. split.
      -- right. exact Hin.
      -- split; assumption.
Qed.

(** Main structural lemma: match_variant_pattern returning Some
    implies the pattern decomposes into segments from the variant sets. *)

Lemma match_variant_pattern_sound : forall p foot_vars anns,
  match_variant_pattern p foot_vars = Some anns ->
  is_variant_decomposition p foot_vars.
Proof.
  intros p foot_vars. revert p.
  induction foot_vars as [|vs rest IH]; intros p anns H.
  - simpl in H. destruct p; [injection H as _; reflexivity | discriminate].
  - simpl in H. simpl.
    exact (try_variants_sound vs p rest anns H IH).
Qed.

(** Annotation length equals the number of foot positions. *)

Lemma match_variant_anns_length : forall p foot_vars anns,
  match_variant_pattern p foot_vars = Some anns ->
  length anns = length foot_vars.
Proof.
  intros p foot_vars. revert p.
  induction foot_vars as [|vs rest IH]; intros p anns H.
  - simpl in H. destruct p; [injection H as <-; reflexivity | discriminate].
  - simpl in H.
    revert H.
    induction vs as [|[v0 ann0] cs0 IHcs]; intros H.
    + discriminate.
    + simpl in H.
      destruct (pattern_eqb (firstn (length v0) p) v0) eqn:Epfx.
      * destruct (match_variant_pattern (skipn (length v0) p) rest) as [anns'|] eqn:Emvp.
        -- injection H as <-. simpl. f_equal. exact (IH _ _ Emvp).
        -- exact (IHcs H).
      * exact (IHcs H).
Qed.

(** Helper: the try_meters loop in scan. If it returns ScanVariant,
    then match_variant_pattern succeeded for that meter. *)

Lemma try_meters_sound : forall ms p m anns,
  (fix try_meters (ms : list meter) : scan_result :=
    match ms with
    | [] => ScanFailed
    | m :: ms' =>
        match match_variant_pattern p (meter_foot_variants m) with
        | Some anns => ScanVariant m anns
        | None => try_meters ms'
        end
    end) ms = ScanVariant m anns ->
  In m ms /\
  match_variant_pattern p (meter_foot_variants m) = Some anns.
Proof.
  induction ms as [|m0 ms' IH]; intros p m anns H.
  - discriminate.
  - simpl in H.
    destruct (match_variant_pattern p (meter_foot_variants m0)) as [anns0|] eqn:Emvp.
    + injection H as <- <-.
      split. left. reflexivity. exact Emvp.
    + destruct (IH p m anns H) as [Hin Hmvp].
      split. right. exact Hin. exact Hmvp.
Qed.

(** ** Scansion Soundness Theorem *)

(** If scan returns ScanVariant m anns, then:
    1. m is a valid meter (In m all_meters).
    2. The pattern decomposes foot-by-foot into legal variants of m.
    3. The annotations have the same length as the number of feet. *)

Theorem scan_sound : forall p m anns,
  scan p = ScanVariant m anns ->
  In m all_meters /\
  match_variant_pattern p (meter_foot_variants m) = Some anns /\
  is_variant_decomposition p (meter_foot_variants m) /\
  length anns = length (meter_foot_variants m).
Proof.
  intros p m anns H.
  unfold scan in H.
  destruct (pattern_to_meter p) as [m0|] eqn:Eptm.
  - discriminate.
  - destruct (try_meters_sound all_meters p m anns H) as [Hin Hmvp].
    split. exact Hin.
    split. exact Hmvp.
    split.
    + exact (match_variant_pattern_sound p _ anns Hmvp).
    + exact (match_variant_anns_length p _ anns Hmvp).
Qed.

(** Corollary: ScanSuccess implies exact meter match. *)

Theorem scan_exact_sound : forall p m,
  scan p = ScanSuccess m ->
  pattern_to_meter p = Some m.
Proof.
  intros p m H. unfold scan in H.
  destruct (pattern_to_meter p) as [m0|] eqn:Eptm.
  - inversion H as [Hm]. subst m0. reflexivity.
  - (* The try_meters loop only returns ScanVariant or ScanFailed, never ScanSuccess. *)
    exfalso.
    assert (Hloop :
      forall ms, (fix try_meters (ms0 : list meter) : scan_result :=
        match ms0 with
        | [] => ScanFailed
        | m1 :: ms' =>
            match match_variant_pattern p (meter_foot_variants m1) with
            | Some anns => ScanVariant m1 anns
            | None => try_meters ms'
            end
        end) ms <> ScanSuccess m).
    { induction ms as [|m1 ms' IHms]; intros Habs.
      - discriminate.
      - simpl in Habs.
        destruct (match_variant_pattern p (meter_foot_variants m1));
          [discriminate | exact (IHms Habs)]. }
    exact (Hloop all_meters H).
Qed.

(** ** Scansion Completeness *)

(** A pattern is a legal variant of meter m if it decomposes into
    one variant from each foot's variant list (as computed by
    meter_foot_variants). *)

Definition is_legal_meter_variant (p : pattern) (m : meter) : Prop :=
  is_variant_decomposition p (meter_foot_variants m).

(** The inner try_variants loop is complete: if some candidate in the
    list has a matching prefix and the recursive call on the remainder
    succeeds, the loop returns Some. *)

Lemma try_variants_complete : forall candidates p rest v_w ann_w,
  In (v_w, ann_w) candidates ->
  pattern_eqb (firstn (length v_w) p) v_w = true ->
  (exists anns_rest, match_variant_pattern (skipn (length v_w) p) rest = Some anns_rest) ->
  exists anns,
    (fix try_variants (cs : list annotated_variant)
      : option (list foot_annotation) :=
      match cs with
      | [] => None
      | (v, ann) :: cs' =>
          if pattern_eqb (firstn (length v) p) v then
            match match_variant_pattern (skipn (length v) p) rest with
            | Some anns => Some (ann :: anns)
            | None => try_variants cs'
            end
          else try_variants cs'
      end) candidates = Some anns.
Proof.
  induction candidates as [|[v0 ann0] cs0 IH];
    intros p rest v_w ann_w Hin Hpfx Hmvp.
  - destruct Hin.
  - simpl.
    destruct (pattern_eqb (firstn (length v0) p) v0) eqn:Epfx0.
    + destruct (match_variant_pattern (skipn (length v0) p) rest) as [anns0|] eqn:Emvp0.
      * eexists. reflexivity.
      * destruct Hin as [Heq | Hin].
        -- inversion Heq; subst.
           destruct Hmvp as [ar Har]. rewrite Har in Emvp0. discriminate.
        -- exact (IH p rest v_w ann_w Hin Hpfx Hmvp).
    + destruct Hin as [Heq | Hin].
      * inversion Heq; subst. rewrite Hpfx in Epfx0. discriminate.
      * exact (IH p rest v_w ann_w Hin Hpfx Hmvp).
Qed.

(** Main structural lemma: if a pattern admits a variant decomposition
    with respect to a list of per-foot variant sets, then
    match_variant_pattern succeeds. *)

Lemma match_variant_pattern_complete : forall p foot_vars,
  is_variant_decomposition p foot_vars ->
  exists anns, match_variant_pattern p foot_vars = Some anns.
Proof.
  intros p foot_vars. revert p.
  induction foot_vars as [|vs rest IH]; intros p Hdecomp.
  - simpl in Hdecomp. subst p. exists []. reflexivity.
  - simpl in Hdecomp.
    destruct Hdecomp as [v [ann [Hin [Hpfx Hrest]]]].
    destruct (IH _ Hrest) as [anns_rest Hmvp].
    simpl.
    exact (try_variants_complete vs p rest v ann Hin
      (proj2 (pattern_eqb_eq _ _) Hpfx)
      (ex_intro _ anns_rest Hmvp)).
Qed.

(** The try_meters loop is complete: if some meter in the list has a
    successful match_variant_pattern, the loop does not return ScanFailed. *)

Lemma try_meters_complete : forall ms p m anns,
  In m ms ->
  match_variant_pattern p (meter_foot_variants m) = Some anns ->
  (fix try_meters (ms : list meter) : scan_result :=
    match ms with
    | [] => ScanFailed
    | m :: ms' =>
        match match_variant_pattern p (meter_foot_variants m) with
        | Some anns => ScanVariant m anns
        | None => try_meters ms'
        end
    end) ms <> ScanFailed.
Proof.
  induction ms as [|m0 ms' IH]; intros p m anns Hin Hmvp.
  - destruct Hin.
  - simpl.
    destruct (match_variant_pattern p (meter_foot_variants m0)) as [anns0|] eqn:Emvp0.
    + discriminate.
    + destruct Hin as [Heq | Hin].
      * subst m0. rewrite Hmvp in Emvp0. discriminate.
      * exact (IH p m anns Hin Hmvp).
Qed.

(** Scansion completeness theorem: if a pattern is a legal variant
    of any meter (each foot contributes either its canonical pattern
    or the result of a legal variation), then scan does not fail. *)

Theorem scan_complete : forall p m,
  is_legal_meter_variant p m ->
  scan p <> ScanFailed.
Proof.
  intros p m Hvar.
  unfold is_legal_meter_variant in Hvar.
  destruct (match_variant_pattern_complete p _ Hvar) as [anns Hmvp].
  unfold scan.
  destruct (pattern_to_meter p) eqn:Eptm.
  - discriminate.
  - exact (try_meters_complete all_meters p m anns (all_meters_complete m) Hmvp).
Qed.

(** Canonical foot patterns are always in the hashw variant list. *)
Lemma canonical_in_hashw : forall f,
  In (foot_pattern f, Canonical) (foot_hashw_variants f).
Proof.
  intros f. unfold foot_hashw_variants. left. reflexivity.
Qed.

(** Canonical foot patterns are always in the terminal variant list. *)
Lemma canonical_in_terminal : forall m,
  In (foot_pattern (last (meter_feet m) Faulun), Canonical)
    (foot_terminal_variants m).
Proof.
  intros m. unfold foot_terminal_variants. left. reflexivity.
Qed.

(** The exact meter pattern admits a variant decomposition via
    match_variant_pattern (each foot matches canonically). *)
Lemma exact_meter_matches : forall m,
  exists anns, match_variant_pattern (meter_pattern m) (meter_foot_variants m) = Some anns.
Proof.
  intros m. destruct m; vm_compute; eexists; reflexivity.
Qed.

(** The exact meter pattern is a legal variant (by soundness of
    match_variant_pattern). *)
Lemma exact_is_legal_variant : forall m,
  is_legal_meter_variant (meter_pattern m) m.
Proof.
  intros m.
  unfold is_legal_meter_variant.
  destruct (exact_meter_matches m) as [anns Hmvp].
  exact (match_variant_pattern_sound _ _ _ Hmvp).
Qed.

(** Witness: scan_complete applied to exact Tawil. *)
Example scan_complete_witness_exact :
  scan (meter_pattern Tawil) <> ScanFailed.
Proof.
  exact (scan_complete _ _ (exact_is_legal_variant Tawil)).
Qed.

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

(** Transitivity of is_prefix *)
Lemma is_prefix_trans : forall p1 p2 p3,
  is_prefix p1 p2 = true -> is_prefix p2 p3 = true -> is_prefix p1 p3 = true.
Proof.
  induction p1 as [|w1 p1' IH]; intros p2 p3 H12 H23.
  - reflexivity.
  - destruct p2 as [|w2 p2']; simpl in H12; try discriminate.
    destruct p3 as [|w3 p3']; simpl in H23; try discriminate.
    apply Bool.andb_true_iff in H12. destruct H12 as [Hw12 Hp12].
    apply Bool.andb_true_iff in H23. destruct H23 as [Hw23 Hp23].
    simpl. apply Bool.andb_true_iff. split.
    + apply weight_eqb_eq in Hw12. apply weight_eqb_eq in Hw23.
      apply weight_eqb_eq. rewrite Hw12. exact Hw23.
    + exact (IH _ _ Hp12 Hp23).
Qed.

(** Witness: is_prefix_refl on faulun *)
Example is_prefix_refl_witness : is_prefix faulun faulun = true.
Proof. reflexivity. Qed.

(** Example: is_prefix_refl on a long pattern *)
Example is_prefix_refl_example : is_prefix (meter_pattern Tawil) (meter_pattern Tawil) = true.
Proof. reflexivity. Qed.

(** Counterexample: a different pattern is not always a prefix *)
Example is_prefix_refl_counterexample : is_prefix faulun failun = false.
Proof. reflexivity. Qed.

(** Witness: is_prefix_nil — empty is prefix of non-empty *)
Example is_prefix_nil_witness : is_prefix [] faulun = true.
Proof. reflexivity. Qed.

(** Example: is_prefix_nil — empty is prefix of empty *)
Example is_prefix_nil_example : is_prefix [] [] = true.
Proof. reflexivity. Qed.

(** Counterexample: non-empty may not be prefix of empty *)
Example is_prefix_nil_counterexample : is_prefix [Short] [] = false.
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

(** Example: scan_summary on Hazaj (shortest meter) *)
Example scan_summary_example :
  scan_summary (meter_pattern Hazaj) = Some Hazaj.
Proof. reflexivity. Qed.

(** Counterexample: non-meter pattern returns None *)
Example scan_summary_counterexample :
  scan_summary [Short; Short; Short] = None.
Proof. reflexivity. Qed.

(** End of Section 10: Scansion *)

(** * Section 11: Rhyme (Qāfiya) *)

(** The qāfiya (قافية) is the rhyme at the end of each line. In Khalil's
    system, the rhyme is defined by the pattern of syllable weights at the
    end of a hemistich, starting from the last moving letter before the
    final quiescent. We formalize the abstract rhyme structure. *)

(** ** Rhyme Letter Types *)

(** The rawīy (روي) is the primary rhyme consonant — the letter on which
    the poem is said to rhyme. *)

Inductive rhyme_element : Type :=
  | Rawiy     (* روي - the rhyme consonant *)
  | Wasl      (* وصل - the connecting letter after rawīy *)
  | Ridf      (* ردف - a long vowel before rawīy *)
  | Tasis     (* تأسيس - an alif separated from rawīy by one letter *)
  | Dakhil.   (* دخيل - the letter between tāsīs and rawīy *)

(** ** Rhyme Pattern *)

(** A rhyme pattern is the sequence of rhyme elements at the end of a line. *)

Definition rhyme_pattern := list rhyme_element.

(** Minimal rhyme: just the rawīy *)
Definition minimal_rhyme : rhyme_pattern := [Rawiy].

(** Common rhyme: ridf + rawīy (e.g., long vowel then rhyme consonant) *)
Definition ridf_rhyme : rhyme_pattern := [Ridf; Rawiy].

(** Extended rhyme: rawīy + waṣl *)
Definition wasl_rhyme : rhyme_pattern := [Rawiy; Wasl].

(** Full rhyme: tāsīs + dakhīl + rawīy *)
Definition tasis_rhyme : rhyme_pattern := [Tasis; Dakhil; Rawiy].

(** ** Decidable Equality for Rhyme Element *)

Definition rhyme_element_eq_dec (r1 r2 : rhyme_element) : {r1 = r2} + {r1 <> r2}.
Proof.
  destruct r1, r2; try (left; reflexivity); right; discriminate.
Defined.

(** ** Rhyme Element Enumeration *)

Definition all_rhyme_elements : list rhyme_element :=
  [Rawiy; Wasl; Ridf; Tasis; Dakhil].

Lemma all_rhyme_elements_complete : forall r : rhyme_element, In r all_rhyme_elements.
Proof.
  intros r. destruct r; simpl.
  - left. reflexivity.
  - right. left. reflexivity.
  - right. right. left. reflexivity.
  - right. right. right. left. reflexivity.
  - right. right. right. right. left. reflexivity.
Qed.

Lemma all_rhyme_elements_length : length all_rhyme_elements = 5.
Proof. reflexivity. Qed.

(** ** Rhyme Validity *)

(** A valid rhyme must contain exactly one rawīy *)
Fixpoint count_rawiy (rp : rhyme_pattern) : nat :=
  match rp with
  | [] => 0
  | Rawiy :: rest => S (count_rawiy rest)
  | _ :: rest => count_rawiy rest
  end.

Definition is_valid_rhyme (rp : rhyme_pattern) : bool :=
  Nat.eqb (count_rawiy rp) 1.

(** Witness: minimal rhyme is valid *)
Example rhyme_witness : is_valid_rhyme minimal_rhyme = true.
Proof. reflexivity. Qed.

(** Example: ridf rhyme is valid *)
Example rhyme_example : is_valid_rhyme ridf_rhyme = true.
Proof. reflexivity. Qed.

(** Counterexample: empty rhyme is invalid *)
Example rhyme_counterexample : is_valid_rhyme [] = false.
Proof. reflexivity. Qed.

(** Counterexample: double rawīy is invalid *)
Example rhyme_counterexample_double : is_valid_rhyme [Rawiy; Rawiy] = false.
Proof. reflexivity. Qed.

(** ** Rhyme Ordering Constraints *)

(** In a well-formed rhyme, elements must appear in a specific order:
    tāsīs (if present) must precede dakhīl, which precedes rawīy,
    which precedes waṣl. Ridf must immediately precede rawīy. *)

(** Boolean rhyme element equality *)
Definition rhyme_element_eqb (r1 r2 : rhyme_element) : bool :=
  match r1, r2 with
  | Rawiy, Rawiy => true
  | Wasl, Wasl => true
  | Ridf, Ridf => true
  | Tasis, Tasis => true
  | Dakhil, Dakhil => true
  | _, _ => false
  end.

(** Check if rawīy appears before waṣl (if both present) *)
Fixpoint rawiy_before_wasl (rp : rhyme_pattern) : bool :=
  match rp with
  | [] => true
  | Wasl :: _ => false  (* waṣl without preceding rawīy *)
  | Rawiy :: rest => true  (* rawīy found first: ok *)
  | _ :: rest => rawiy_before_wasl rest
  end.

(** Check if tāsīs appears before dakhīl (if both present) *)
Fixpoint tasis_before_dakhil (rp : rhyme_pattern) : bool :=
  match rp with
  | [] => true
  | Dakhil :: _ => false  (* dakhīl without preceding tāsīs *)
  | Tasis :: _ => true   (* tāsīs found first: ok *)
  | _ :: rest => tasis_before_dakhil rest
  end.

(** Full structural validity: exactly one rawīy + correct ordering *)
Definition is_well_formed_rhyme (rp : rhyme_pattern) : bool :=
  is_valid_rhyme rp &&
  rawiy_before_wasl rp &&
  tasis_before_dakhil rp.

(** Witness: tasis_rhyme is well-formed *)
Example well_formed_witness : is_well_formed_rhyme tasis_rhyme = true.
Proof. reflexivity. Qed.

(** Example: ridf_rhyme is well-formed *)
Example well_formed_example : is_well_formed_rhyme ridf_rhyme = true.
Proof. reflexivity. Qed.

(** Counterexample: waṣl before rawīy is malformed *)
Example well_formed_counterexample :
  is_well_formed_rhyme [Wasl; Rawiy] = false.
Proof. reflexivity. Qed.

(** Counterexample: dakhīl before tāsīs is malformed *)
Example well_formed_counterexample2 :
  is_well_formed_rhyme [Dakhil; Tasis; Rawiy] = false.
Proof. reflexivity. Qed.

(** End of Section 11: Rhyme *)

(** * Section 12: Poem Structure *)

(** A poem (qaṣīda) consists of lines (abyāt, singular bayt). Each line
    has two hemistichs (shaṭr). All lines share the same meter and rhyme. *)

(** ** Line Structure *)

(** A hemistich is a weight pattern. *)
Definition hemistich := pattern.

(** A line (bayt) is a pair of hemistichs. *)
Record bayt : Type := mk_bayt {
  sadr  : hemistich;   (* صدر - first hemistich *)
  ajuz  : hemistich    (* عجز - second hemistich *)
}.

(** A poem is a non-empty list of lines. *)
Definition poem := list bayt.

(** ** Line Validity *)

(** A line is metrically valid if both hemistichs match the meter. *)
Definition is_valid_bayt (b : bayt) (m : meter) : bool :=
  pattern_eqb (sadr b) (meter_pattern m) &&
  pattern_eqb (ajuz b) (meter_pattern m).

(** ** Poem Validity *)

(** A poem is valid if all lines match the same meter. *)
Definition is_valid_poem (p : poem) (m : meter) : bool :=
  forallb (fun b => is_valid_bayt b m) p.

(** ** Matlaʿ Detection *)

(** The matlaʿ (مطلع) is the opening line of a qaṣīda, where both
    hemistichs rhyme. *)
Definition is_matla (b : bayt) (m : meter) : bool :=
  is_valid_bayt b m.

(** Witness: a valid Mutaqarib bayt *)
Example bayt_witness :
  let h := meter_pattern Mutaqarib in
  is_valid_bayt (mk_bayt h h) Mutaqarib = true.
Proof. reflexivity. Qed.

(** Example: a valid two-line Hazaj poem *)
Example poem_example :
  let h := meter_pattern Hazaj in
  is_valid_poem [mk_bayt h h; mk_bayt h h] Hazaj = true.
Proof. reflexivity. Qed.

(** Counterexample: mismatched hemistichs fail *)
Example bayt_counterexample :
  is_valid_bayt (mk_bayt (meter_pattern Tawil) (meter_pattern Basit)) Tawil = false.
Proof. reflexivity. Qed.

(** Counterexample: empty poem is trivially valid (vacuous truth) *)
Example poem_counterexample_empty :
  is_valid_poem [] Tawil = true.
Proof. reflexivity. Qed.

(** ** Full Line as Concatenation *)

(** Relates the bayt structure to the flat is_full_line predicate *)
Lemma bayt_full_line : forall b m,
  is_valid_bayt b m = true ->
  is_full_line (sadr b ++ ajuz b) m = true.
Proof.
  intros b m H. unfold is_valid_bayt in H.
  apply Bool.andb_true_iff in H. destruct H as [Hs Ha].
  apply pattern_eqb_eq in Hs. apply pattern_eqb_eq in Ha.
  unfold is_full_line. apply pattern_eqb_eq.
  rewrite Hs, Ha. reflexivity.
Qed.

(** Witness: bayt_full_line for Hazaj *)
Example bayt_full_line_witness :
  let h := meter_pattern Hazaj in
  is_full_line (h ++ h) Hazaj = true.
Proof. reflexivity. Qed.

(** Example: bayt_full_line for Kamil *)
Example bayt_full_line_example :
  let h := meter_pattern Kamil in
  is_full_line (h ++ h) Kamil = true.
Proof. reflexivity. Qed.

(** Counterexample: mismatched hemistichs are not a full line *)
Example bayt_full_line_counterexample :
  is_full_line (meter_pattern Tawil ++ meter_pattern Basit) Tawil = false.
Proof. reflexivity. Qed.

(** ** Rhyme-Aware Poem Structure *)

(** A rhyme identifier — abstract, just needs decidable equality. *)
Definition rhyme_id := nat.

(** A line with rhyme annotation on the ʿajuz (second hemistich). *)
Record annotated_bayt : Type := mk_annotated_bayt {
  ab_sadr      : hemistich;
  ab_ajuz      : hemistich;
  ab_sadr_rhyme : rhyme_id;  (* rhyme of first hemistich *)
  ab_ajuz_rhyme : rhyme_id   (* rhyme of second hemistich *)
}.

(** ** Matlaʿ: Both Hemistichs Rhyme *)

(** In the matlaʿ (opening line), both hemistichs share the same rhyme.
    This distinguishes it from subsequent lines where only the ʿajuz rhymes. *)
Definition is_matla_proper (b : annotated_bayt) (m : meter) : bool :=
  pattern_eqb (ab_sadr b) (meter_pattern m) &&
  pattern_eqb (ab_ajuz b) (meter_pattern m) &&
  Nat.eqb (ab_sadr_rhyme b) (ab_ajuz_rhyme b).

(** Witness: matlaʿ with matching rhymes *)
Example matla_proper_witness :
  let h := meter_pattern Mutaqarib in
  is_matla_proper (mk_annotated_bayt h h 1 1) Mutaqarib = true.
Proof. reflexivity. Qed.

(** Counterexample: non-matlaʿ line (different rhymes) *)
Example matla_proper_counterexample :
  let h := meter_pattern Mutaqarib in
  is_matla_proper (mk_annotated_bayt h h 1 2) Mutaqarib = false.
Proof. reflexivity. Qed.

(** ** Rhyme Consistency Across Lines *)

(** In a qaṣīda, all ʿajuz hemistichs must share the same rhyme. *)
Definition is_rhyme_consistent (lines : list annotated_bayt) (r : rhyme_id) : bool :=
  forallb (fun b => Nat.eqb (ab_ajuz_rhyme b) r) lines.

(** Witness: consistent rhyme *)
Example rhyme_consistent_witness :
  let h := meter_pattern Hazaj in
  is_rhyme_consistent
    [mk_annotated_bayt h h 1 1; mk_annotated_bayt h h 2 1] 1 = true.
Proof. reflexivity. Qed.

(** Counterexample: inconsistent rhyme *)
Example rhyme_consistent_counterexample :
  let h := meter_pattern Hazaj in
  is_rhyme_consistent
    [mk_annotated_bayt h h 1 1; mk_annotated_bayt h h 2 2] 1 = false.
Proof. reflexivity. Qed.

(** ** Non-Empty Poem (Qaṣīda) *)

(** A qaṣīda must have at least one line. *)
Record qasida : Type := mk_qasida {
  qas_first : annotated_bayt;
  qas_rest  : list annotated_bayt;
  qas_meter : meter;
  qas_rhyme : rhyme_id
}.

Definition qasida_lines (q : qasida) : list annotated_bayt :=
  qas_first q :: qas_rest q.

Definition is_valid_qasida (q : qasida) : bool :=
  let m := qas_meter q in
  let r := qas_rhyme q in
  is_matla_proper (qas_first q) m &&
  forallb (fun b =>
    pattern_eqb (ab_sadr b) (meter_pattern m) &&
    pattern_eqb (ab_ajuz b) (meter_pattern m))
    (qas_rest q) &&
  is_rhyme_consistent (qasida_lines q) r.

(** Witness: valid single-line qasida *)
Example qasida_witness :
  let h := meter_pattern Hazaj in
  is_valid_qasida (mk_qasida (mk_annotated_bayt h h 1 1) [] Hazaj 1) = true.
Proof. reflexivity. Qed.

(** Example: valid two-line qasida *)
Example qasida_example :
  let h := meter_pattern Hazaj in
  is_valid_qasida
    (mk_qasida
      (mk_annotated_bayt h h 1 1)
      [mk_annotated_bayt h h 2 1]
      Hazaj 1) = true.
Proof. reflexivity. Qed.

(** Counterexample: matlaʿ rhyme mismatch invalidates qasida *)
Example qasida_counterexample :
  let h := meter_pattern Hazaj in
  is_valid_qasida (mk_qasida (mk_annotated_bayt h h 1 2) [] Hazaj 2) = false.
Proof. reflexivity. Qed.

(** ** Non-emptiness Guarantee *)

Lemma qasida_nonempty : forall q, length (qasida_lines q) >= 1.
Proof.
  intros q. unfold qasida_lines. simpl. lia.
Qed.

(** Witness: single-line qasida has 1 line *)
Example qasida_nonempty_witness :
  let h := meter_pattern Hazaj in
  length (qasida_lines (mk_qasida (mk_annotated_bayt h h 1 1) [] Hazaj 1)) = 1.
Proof. reflexivity. Qed.

(** End of Section 12: Poem Structure *)

(** * Conclusion *)

(** The original system dates to c. 760 CE and forms the foundation of
    Arabic, Persian, Turkish, Kurdish, and Urdu prosody. *)
