# Khalil-Verified: Outstanding Issues

1. Section 2 (Letter-Level Structure) examples: boundary cases for `letters_to_pattern` at syllable boundaries, `wf_letter_seq` on hand-crafted edge inputs, round-trip on patterns of length 0–6, `delete_at`/`replace_at`/`insert_at` at first/last/out-of-bounds indices, `nth_sakin_pos`/`nth_mutaharrik_pos` when target count exceeds available.
2. Section 3 (Building Blocks) examples: `is_sabab`/`is_watad` on all four building-block patterns plus near-miss patterns (e.g. [Long; Long]), `sabab_not_watad` and `watad_not_sabab` exercised on every block, `all_building_blocks` coverage cross-check.
3. Section 4 (Feet) examples: `is_foot` on all 8 canonical patterns and all 48 non-foot patterns from `foot_length_patterns`, `foot_blocks_correct` cross-verified against manual block concatenation for every foot, `pattern_to_foot` round-trip on all 8 feet plus None on representative non-feet.
4. Section 5 (Meters) examples: `meter_pattern` distinctness spot-checks on same-length pairs (Rajaz/Ramal, Hazaj/Mudari), `pattern_to_meter` round-trip on all 16 meters, `meter_foot_count` cross-checked against `meter_feet` length for every meter.
5. Section 6 (Circles) examples: `rotate` at 0, 1, length−1, length, length+1 on a representative pattern, `rotate_add_mod` concrete instances near the wrap boundary, every circle's generator exhaustively rotated to confirm exactly the expected feet appear and no others.
6. Section 7 (Variations — zihāf) examples: every simple zihāf applied to every foot (72 pairs), confirming Some/None matches `zihaf_applies_to`, result pattern verified for each applicable pair, mora-count change verified per pair.
7. Section 8 (Variations — ʿilla + compound) examples: every compound zihāf applied to every foot (32 pairs), every ʿilla applied to every foot (104 pairs), guarded vs unguarded ḥadhf/qaṭʿ/kashf divergence cases, `apply_batr` and `apply_qaṭf` intermediate-step verification.
8. Section 9 (Foot Positions & Variation Scope) examples: `assign_sadr_positions`/`assign_ajuz_positions` for every meter, all three positions tested against `zihaf_permitted`/`ʿilla_permitted`, `is_legal_zihaf_at` for boundary foot indices (first, last, out-of-range).
9. Section 10 (Legal Rules Per Meter) examples: `foot_permitted_zihaf` length bounds verified per foot, `permitted_arud_illa`/`permitted_darb_illa` non-emptiness or emptiness confirmed per meter, `is_legal_arud_illa`/`is_legal_darb_illa` full cross-product spot-checks.
10. Section 11 (Scansion) examples: `scan` on all 16 canonical meter patterns, `scan` on at least one variant per meter, `scan_all` on the Rajaz/Kamil ambiguous pattern plus 2–3 other known overlaps, `taqtii` concatenation verified on variant inputs, `taqtii` segment count verified on every meter.
11. Section 12 (Rhyme) examples: `is_valid_rhyme` on 0-rawiy, 1-rawiy, 2-rawiy patterns, `is_well_formed_rhyme` on all four named rhyme patterns plus malformed orderings, `ridf_adjacent_rawiy` on ridf-at-end and ridf-separated cases.
12. Section 13 (Poem Structure) examples: `is_valid_hemistich` on canonical + one variant + one gibberish per meter, `is_valid_qasida` on 1-line, 2-line, rhyme-mismatch, meter-mismatch, and variant-hemistich cases.
13. Generalize mutaḥarrik-modifying lemmas (`iḍmār_preserves_morae`, `waqṣ_reduces_morae`, `ʿaṣb_preserves_morae`, etc.) to pattern-general forms analogous to `delete_sakin_preserves_count`.
14. Prove compound zihāf simultaneous deletion equivalent to (or intentionally distinct from) sequential composition.
15. Generalize `rotate_add_mod` to arbitrary naturals, removing the `n ≤ length p` and `m ≤ length p` preconditions.
16. Add meter-specific ḥashw refinements to `foot_permitted_zihaf` (e.g. kaff rare in Ṭawīl).
17. Formalize poem sub-genres (ghazal, rubāʿī, maqṭūʿa) as structural predicates over `poem`.
18. Introduce `SuperLong` weight to distinguish tarfīl from tadhyīl. Do last — touches everything.
19. Add `Extraction` directives for core computable functions to OCaml or Haskell.
20. Build an extracted test harness against classical Arabic verse transcriptions.
