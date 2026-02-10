open Khalil_types

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

val add : int -> int -> int

module Nat :
 sig
  val sub : int -> int -> int

  val ltb : int -> int -> bool

  val divmod : int -> int -> int -> int -> int * int

  val modulo : int -> int -> int
 end

val nth_error : 'a1 list -> int -> 'a1 option

val last : 'a1 list -> 'a1 -> 'a1

val removelast : 'a1 list -> 'a1 list

val concat : 'a1 list list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list

val existsb : ('a1 -> bool) -> 'a1 list -> bool

val forallb : ('a1 -> bool) -> 'a1 list -> bool

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

val firstn : int -> 'a1 list -> 'a1 list

val skipn : int -> 'a1 list -> 'a1 list

type pattern = weight list

val weight_eqb : weight -> weight -> bool

val pattern_eqb : pattern -> pattern -> bool

val pattern_length : pattern -> int

val weight_morae : weight -> int

val pattern_morae : pattern -> int

val all_weights : weight list

type letter_seq = letter list

val syllable_to_letters : weight -> letter_seq

val pattern_to_letters : pattern -> letter_seq

val letters_to_pattern : letter_seq -> pattern option

val wf_letter_seq : letter_seq -> bool

val normalize_weight : weight -> weight

val normalize_pattern : pattern -> pattern

val no_superlong : pattern -> bool

val letters_to_pattern_guarded : letter_seq -> conversion_result

val safe_apply_variation :
  (letter_seq -> letter_seq option) -> pattern -> conversion_result

val nth_sakin_pos : int -> letter_seq -> int -> int option

val nth_mutaharrik_pos : int -> letter_seq -> int -> int option

val delete_at : int -> letter_seq -> letter_seq

val replace_at : int -> letter -> letter_seq -> letter_seq

val insert_at : int -> letter -> letter_seq -> letter_seq

val sabab_khafif : pattern

val sabab_thaqil : pattern

val is_sabab_khafif : pattern -> bool

val is_sabab_thaqil : pattern -> bool

val is_sabab : pattern -> bool

val watad_majmu : pattern

val watad_mafruq : pattern

val is_watad_majmu : pattern -> bool

val is_watad_mafruq : pattern -> bool

val is_watad : pattern -> bool

val all_sabab : pattern list

val all_watad : pattern list

val all_building_blocks : pattern list

val faulun : pattern

val failun : pattern

val mafailun : pattern

val mustafilun : pattern

val failatun : pattern

val mafulatu : pattern

val mutafailun : pattern

val mufaalatun : pattern

val foot_pattern : foot -> pattern

val is_foot : pattern -> bool

val all_feet : foot list

val block_eq_dec : block -> block -> bool

val block_pattern : block -> pattern

val blocks_to_pattern : block list -> pattern

val faulun_blocks : block list

val failun_blocks : block list

val mafailun_blocks : block list

val mustafilun_blocks : block list

val failatun_blocks : block list

val mafulatu_blocks : block list

val mutafailun_blocks : block list

val mufaalatun_blocks : block list

val foot_blocks : foot -> block list

val block_list_eqb : block list -> block list -> bool

val is_canonical_decomposition : foot -> block list -> bool

val foot_length : foot -> int

val is_trisyllabic : foot -> bool

val is_quadrisyllabic : foot -> bool

val is_pentasyllabic : foot -> bool

val pattern_to_foot : pattern -> foot option

val all_patterns : int -> pattern list

val foot_length_patterns : pattern list

val meter_feet : meter -> foot list

val meter_pattern : meter -> pattern

val meter_eq_dec : meter -> meter -> bool

val all_meters : meter list

val meter_syllable_count : meter -> int

val meter_foot_count : meter -> int

val is_dimeter : meter -> bool

val is_trimeter : meter -> bool

val is_tetrameter : meter -> bool

val pattern_to_meter : pattern -> meter option

val khalil_original : meter list

val is_khalil_original : meter -> bool

val meter_circle : meter -> circle

val circle_meters : circle -> meter list

val all_circles : circle list

val is_in_circle : meter -> circle -> bool

val rotate : int -> pattern -> pattern

val zihaf_eq_dec : zihaf -> zihaf -> bool

val _UU02bf_illa_eq_dec : illa -> illa -> bool

val apply_khabn : pattern -> pattern option

val apply_tayy : pattern -> pattern option

val apply_qab_UU1e0d_ : pattern -> pattern option

val apply_kaff : pattern -> pattern option

val apply_waq_UU1e63_ : pattern -> pattern option

val apply__UU02bf_a_UU1e63_b : pattern -> pattern option

val apply_qa_UU1e63_r : pattern -> pattern option

val apply__UU1e25_adhf : pattern -> pattern option

val apply_qa_UU1e6d__UU02bf_ : pattern -> pattern option

val apply_tasb_UU012b_gh : pattern -> pattern option

val apply_batr : pattern -> pattern option

val apply_qa_UU1e6d_f : pattern -> pattern option

val last_two : pattern -> (weight * weight) option

val ends_with_watad_majmu : pattern -> bool

val ends_with_watad_mafruq : pattern -> bool

val apply_tarf_UU012b_l : pattern -> pattern option

val apply_tadhy_UU012b_l : pattern -> pattern option

val drop_last_n : int -> pattern -> pattern option

val apply__UU1e25_adh_UU0101_dh : pattern -> pattern option

val apply__UU1e63_alm : pattern -> pattern option

val apply_kashf : pattern -> pattern option

val ends_with : pattern -> weight -> bool

val apply__UU1e25_adhf_guarded : pattern -> pattern option

val apply_qa_UU1e6d__UU02bf__guarded : pattern -> pattern option

val apply_kashf_guarded : pattern -> pattern option

val apply_waqf : pattern -> pattern option

val apply_tash_UU02bf__UU012b_th : pattern -> pattern option

val apply_i_UU1e0d_m_UU0101_r : pattern -> pattern option

val apply_shamm : pattern -> pattern option

val apply__UU02bf_aql : pattern -> pattern option

val compound_zihaf_eq_dec : compound_zihaf -> compound_zihaf -> bool

val apply_khazl : pattern -> pattern option

val apply_khabl : pattern -> pattern option

val apply_shakl : pattern -> pattern option

val apply_naqs : pattern -> pattern option

val all_compound_zihaf : compound_zihaf list

val all_zihaf : zihaf list

val all__UU02bf_illa : illa list

val zihaf_applies_to : zihaf -> foot -> bool

val apply_zihaf : zihaf -> pattern -> pattern option

val apply_compound_zihaf : compound_zihaf -> pattern -> pattern option

val apply__UU02bf_illa : illa -> pattern -> pattern option

val assign_positions_aux :
  foot list -> foot_position -> (foot * foot_position) list

val assign_sadr_positions : meter -> (foot * foot_position) list

val assign_ajuz_positions : meter -> (foot * foot_position) list

val zihaf_permitted : foot_position -> bool

val _UU02bf_illa_permitted : foot_position -> bool

val zihaf_eqb : zihaf -> zihaf -> bool

val compound_zihaf_eqb : compound_zihaf -> compound_zihaf -> bool

val _UU02bf_illa_eqb : illa -> illa -> bool

val foot_permitted_zihaf : foot -> zihaf list

val foot_permitted_compound : foot -> compound_zihaf list

val is_legal_zihaf_for_foot : zihaf -> foot -> bool

val is_legal_compound_for_foot : compound_zihaf -> foot -> bool

val is_legal_zihaf_at : meter -> int -> zihaf -> bool

val is_legal_compound_at : meter -> int -> compound_zihaf -> bool

val compound_zihaf_applies_to : compound_zihaf -> foot -> bool

val permitted_arud_illa : meter -> illa list

val permitted_darb_illa : meter -> illa list

val is_legal_arud_illa : meter -> illa -> bool

val is_legal_darb_illa : meter -> illa -> bool

val meter_hashw_zihaf : meter -> foot -> zihaf list

val is_legal_zihaf_at_strict : meter -> int -> zihaf -> bool

val scan_exact : pattern -> scan_result

type annotated_variant = pattern * foot_annotation

val foot_hashw_variants : foot -> annotated_variant list

val foot_terminal_variants : meter -> annotated_variant list

val meter_foot_variants : meter -> annotated_variant list list

val match_variant_pattern :
  pattern -> annotated_variant list list -> foot_annotation list option

val scan : pattern -> scan_result

val scan_all : pattern -> (meter * foot_annotation list) list

val is_ambiguous : pattern -> bool

val ambiguity_count : pattern -> int

val cart_concat : annotated_variant list list -> pattern list

val meter_variant_patterns : meter -> pattern list

val meters_share_variant : meter -> meter -> bool

val overlap_pairs : (meter * meter) list

val is_known_overlap : meter -> meter -> bool

val is_full_line : pattern -> meter -> bool

val is_prefix : pattern -> pattern -> bool

val candidate_meters : pattern -> meter list

val scan_summary : pattern -> meter option

type taqtii_segment = pattern * foot_annotation

type taqtii_result = taqtii_segment list

val segment_variant_pattern :
  pattern -> annotated_variant list list -> taqtii_result option

val taqtii : meter -> pattern -> taqtii_result option

type rhyme_pattern = rhyme_element list

val minimal_rhyme : rhyme_pattern

val ridf_rhyme : rhyme_pattern

val wasl_rhyme : rhyme_pattern

val tasis_rhyme : rhyme_pattern

val all_rhyme_elements : rhyme_element list

val count_rawiy : rhyme_pattern -> int

val is_valid_rhyme : rhyme_pattern -> bool

val rawiy_before_wasl : rhyme_pattern -> bool

val tasis_before_dakhil : rhyme_pattern -> bool

val ridf_adjacent_rawiy : rhyme_pattern -> bool

val is_well_formed_rhyme : rhyme_pattern -> bool

type hemistich = pattern

type bayt = { sadr : hemistich; ajuz : hemistich }

type poem = bayt list

val is_valid_hemistich : hemistich -> meter -> bool

val is_valid_bayt : bayt -> meter -> bool

val is_valid_poem : poem -> meter -> bool

val haraka_eqb : haraka -> haraka -> bool

type rhyme_id = { ri_rawiy : int; ri_majra : haraka }

val rhyme_id_eqb : rhyme_id -> rhyme_id -> bool

type annotated_bayt = { ab_sadr : hemistich; ab_ajuz : hemistich;
                        ab_sadr_rhyme : rhyme_id; ab_ajuz_rhyme : rhyme_id }

val is_matla_proper : annotated_bayt -> meter -> bool

val is_rhyme_consistent : annotated_bayt list -> rhyme_id -> bool

type qasida = { qas_first : annotated_bayt; qas_rest : annotated_bayt list;
                qas_meter : meter; qas_rhyme : rhyme_id }

val qasida_lines : qasida -> annotated_bayt list

val is_valid_qasida : qasida -> bool

val is_valid_ghazal : qasida -> bool

val is_valid_rubai : qasida -> bool

val is_valid_maqtua : qasida -> bool
