(******************************************************************************)
(*                                                                            *)
(*                    Khalil Extraction to OCaml                              *)
(*                                                                            *)
(*     Extracts core computable functions from Khalil.v to OCaml.             *)
(*                                                                            *)
(******************************************************************************)

Require Import Khalil.
Require Import Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.

(** * Extraction Configuration *)

(** Map Coq nat to OCaml int for efficiency. *)
Extract Inductive nat => "int" ["0" "succ"]
  "(fun fO fS n -> if n = 0 then fO () else fS (n - 1))".

(** Map Coq bool to OCaml bool. *)
Extract Inductive bool => "bool" ["true" "false"].

(** Map Coq list to OCaml list. *)
Extract Inductive list => "list" ["[]" "(::)"].

(** Map Coq option to OCaml option. *)
Extract Inductive option => "option" ["Some" "None"].

(** Map Coq prod to OCaml tuple. *)
Extract Inductive prod => "( * )" ["(,)"].

(** Map Coq sumbool to OCaml bool (drop proof content). *)
Extract Inductive sumbool => "bool" ["true" "false"].

(** * Core Type Extractions *)

(** Section 1: Foundations *)
Extract Inductive weight => "weight"
  ["Short" "Long" "SuperLong"].

(** Section 2: Letter-Level Structure *)
Extract Inductive letter => "letter"
  ["Mutaharrik" "Sakin"].

Extract Inductive conversion_result => "conversion_result"
  ["ConvOk" "ConvPreconditionFailed" "ConvMalformedOutput"].

(** Section 3: Building Blocks — no custom types *)

(** Section 4: Feet *)
Extract Inductive foot => "foot"
  ["Faulun" "Failun" "Mafailun" "Mustafilun"
   "Failatun" "Mafulatu" "Mutafailun" "Mufaalatun"].

Extract Inductive block => "block"
  ["BlkSababKhafif" "BlkSababThaqil"
   "BlkWatadMajmu" "BlkWatadMafruq"].

(** Section 5: Meters *)
Extract Inductive meter => "meter"
  ["Tawil" "Madid" "Basit" "Wafir" "Kamil"
   "Hazaj" "Rajaz" "Ramal" "Sari" "Munsarih"
   "Khafif" "Mudari" "Muqtadab" "Mujtathth"
   "Mutaqarib" "Mutadarik"].

(** Section 6: Circles *)
Extract Inductive circle => "circle"
  ["Mukhtalifa" "Mualifa" "Mujtallaba"
   "Mushtabaha" "Muttafiqa"].

(** Section 7: Variations *)
Extract Inductive zihaf => "zihaf"
  ["Khabn" "Tayy" "Qabd" "Kaff" "Waqs"
   "Asb" "Idmar" "Aql" "Shamm"].

Extract Inductive ʿilla => "illa"
  ["Qat" "Qasr" "Hadhf" "Tasbigh" "Batr"
   "Qatf" "Tarfil" "Tadhyil" "Hadhadh"
   "Salm" "Kashf" "Waqf" "Tashith"].

Extract Inductive compound_zihaf => "compound_zihaf"
  ["Khazl" "Khabl" "Shakl" "Naqs"].

(** Section 8: Foot Positions *)
Extract Inductive foot_position => "foot_position"
  ["Hashw" "Arud" "Darb"].

(** Section 10: Scansion *)
Extract Inductive foot_annotation => "foot_annotation"
  ["Canonical" "SimpleZihaf" "CompoundZihaf" "Illa"].

Extract Inductive scan_result => "scan_result"
  ["ScanSuccess" "ScanVariant" "ScanFailed"].

(** Section 11: Rhyme *)
Extract Inductive rhyme_element => "rhyme_element"
  ["Rawiy" "Wasl" "Ridf" "Tasis" "Dakhil"].

(** Section 12: Poem Structure *)
Extract Inductive haraka => "haraka"
  ["Damma" "Fatha" "Kasra"].

(** * Extracted Functions *)

Set Extraction Output Directory ".".

(** Section 1: Foundations *)
Extraction "khalil_extracted"

  (* Types *)
  weight
  letter
  foot
  block
  meter
  circle
  zihaf
  ʿilla
  compound_zihaf
  foot_position
  foot_annotation
  scan_result
  rhyme_element
  haraka

  (* Section 1 *)
  weight_eqb
  pattern_eqb
  weight_morae
  pattern_morae
  pattern_length
  all_weights

  (* Section 2 *)
  syllable_to_letters
  pattern_to_letters
  letters_to_pattern
  wf_letter_seq
  normalize_weight
  normalize_pattern
  no_superlong
  nth_sakin_pos
  nth_mutaharrik_pos
  delete_at
  replace_at
  insert_at
  letters_to_pattern_guarded
  safe_apply_variation

  (* Section 3 *)
  sabab_khafif
  sabab_thaqil
  watad_majmu
  watad_mafruq
  is_sabab_khafif
  is_sabab_thaqil
  is_sabab
  is_watad_majmu
  is_watad_mafruq
  is_watad
  all_sabab
  all_watad
  all_building_blocks

  (* Section 4 *)
  faulun failun mafailun mustafilun
  failatun mafulatu mutafailun mufaalatun
  foot_pattern
  is_foot
  foot_blocks
  blocks_to_pattern
  block_pattern
  is_canonical_decomposition
  foot_length
  is_trisyllabic
  is_quadrisyllabic
  is_pentasyllabic
  pattern_to_foot
  all_feet
  all_patterns
  foot_length_patterns

  (* Section 5 *)
  meter_feet
  meter_pattern
  all_meters
  meter_syllable_count
  meter_foot_count
  is_dimeter
  is_trimeter
  is_tetrameter
  pattern_to_meter
  khalil_original
  is_khalil_original

  (* Section 6 *)
  meter_circle
  circle_meters
  all_circles
  rotate
  is_in_circle

  (* Section 7 *)
  apply_khabn
  apply_tayy
  apply_qabḍ
  apply_kaff
  apply_waqṣ
  apply_ʿaṣb
  apply_iḍmār
  apply_shamm
  apply_ʿaql
  apply_qaṣr
  apply_ḥadhf
  apply_qaṭʿ
  apply_tasbīgh
  apply_batr
  apply_qaṭf
  apply_tarfīl
  apply_tadhyīl
  apply_ḥadhādh
  apply_ṣalm
  apply_kashf
  apply_waqf
  apply_tashʿīth
  apply_ḥadhf_guarded
  apply_qaṭʿ_guarded
  apply_kashf_guarded
  apply_khazl
  apply_khabl
  apply_shakl
  apply_naqs
  apply_zihaf
  apply_compound_zihaf
  apply_ʿilla
  zihaf_applies_to
  compound_zihaf_applies_to
  all_zihaf
  all_ʿilla
  all_compound_zihaf

  (* Section 8 *)
  assign_sadr_positions
  assign_ajuz_positions
  zihaf_permitted
  ʿilla_permitted

  (* Section 9 *)
  foot_permitted_zihaf
  foot_permitted_compound
  is_legal_zihaf_for_foot
  is_legal_compound_for_foot
  is_legal_zihaf_at
  is_legal_compound_at
  permitted_arud_illa
  permitted_darb_illa
  is_legal_arud_illa
  is_legal_darb_illa
  meter_hashw_zihaf
  is_legal_zihaf_at_strict

  (* Section 10 *)
  scan_exact
  scan
  scan_all
  is_ambiguous
  ambiguity_count
  foot_hashw_variants
  foot_terminal_variants
  meter_foot_variants
  match_variant_pattern
  is_full_line
  is_prefix
  candidate_meters
  scan_summary
  taqtii
  meter_variant_patterns
  meters_share_variant
  overlap_pairs
  is_known_overlap

  (* Section 11 *)
  minimal_rhyme
  ridf_rhyme
  wasl_rhyme
  tasis_rhyme
  count_rawiy
  is_valid_rhyme
  rawiy_before_wasl
  tasis_before_dakhil
  ridf_adjacent_rawiy
  is_well_formed_rhyme
  all_rhyme_elements

  (* Section 12 *)
  is_valid_hemistich
  is_valid_bayt
  is_valid_poem
  is_matla_proper
  is_rhyme_consistent
  is_valid_qasida
  qasida_lines
  is_valid_ghazal
  is_valid_rubai
  is_valid_maqtua
  rhyme_id_eqb.
