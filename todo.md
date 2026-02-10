# Khalil-Verified: Outstanding Issues

1. Generalize `waqṣ_reduces_morae` to pattern-general form (delete index 1 M always removes exactly 1 mora).
2. Generalize `iḍmār_preserves_morae` to pattern-general form (replace index 1 M→S: Short+Short→Long preserves morae).
3. Generalize `shamm_preserves_morae` to pattern-general form (identical to iḍmār).
4. Generalize `iḍmār_reduces_count` to pattern-general form (replace index 1 M→S always reduces count by 1).
5. Generalize `shamm_reduces_count` to pattern-general form (identical to iḍmār).
6. Document that `ʿaṣb_preserves_morae`, `ʿaṣb_reduces_count`, `ʿaql_reduces_morae`, and `ʿaql_reduces_count` cannot be generalized beyond per-foot form — false on arbitrary patterns (e.g. ʿaṣb on [S;S;S;S;S]: morae 5→4, count 5→3; ʿaql on [S;S;L;S;S]: morae 6→4, count 5→3).
7. Prove compound zihāf simultaneous deletion equivalent to (or intentionally distinct from) sequential composition.
8. Section 4 (Feet) examples: `is_foot` on all 8 canonical patterns and all 48 non-foot patterns from `foot_length_patterns`, `foot_blocks_correct` cross-verified against manual block concatenation for every foot, `pattern_to_foot` round-trip on all 8 feet plus None on representative non-feet.
9. Section 5 (Meters) examples: `meter_pattern` distinctness spot-checks on same-length pairs (Rajaz/Ramal, Hazaj/Mudari), `pattern_to_meter` round-trip on all 16 meters, `meter_foot_count` cross-checked against `meter_feet` length for every meter.
10. Section 6 (Circles) examples: `rotate` at 0, 1, length−1, length, length+1 on a representative pattern, `rotate_add_mod` concrete instances near the wrap boundary, every circle's generator exhaustively rotated to confirm exactly the expected feet appear and no others.
11. Section 7 (Variations — zihāf) examples: every simple zihāf applied to every foot (72 pairs), confirming Some/None matches `zihaf_applies_to`, result pattern verified for each applicable pair, mora-count change verified per pair.
12. Section 8 (Variations — ʿilla + compound) examples: every compound zihāf applied to every foot (32 pairs), every ʿilla applied to every foot (104 pairs), guarded vs unguarded ḥadhf/qaṭʿ/kashf divergence cases, `apply_batr` and `apply_qaṭf` intermediate-step verification.
13. Section 9 (Foot Positions & Variation Scope) examples: `assign_sadr_positions`/`assign_ajuz_positions` for every meter, all three positions tested against `zihaf_permitted`/`ʿilla_permitted`, `is_legal_zihaf_at` for boundary foot indices (first, last, out-of-range).
14. Section 10 (Legal Rules Per Meter) examples: `foot_permitted_zihaf` length bounds verified per foot, `permitted_arud_illa`/`permitted_darb_illa` non-emptiness or emptiness confirmed per meter, `is_legal_arud_illa`/`is_legal_darb_illa` full cross-product spot-checks.
15. Section 11 (Scansion) examples: `scan` on all 16 canonical meter patterns, `scan` on at least one variant per meter, `scan_all` on the Rajaz/Kamil ambiguous pattern plus 2–3 other known overlaps, `taqtii` concatenation verified on variant inputs, `taqtii` segment count verified on every meter.
16. Section 12 (Rhyme) examples: `is_valid_rhyme` on 0-rawiy, 1-rawiy, 2-rawiy patterns, `is_well_formed_rhyme` on all four named rhyme patterns plus malformed orderings, `ridf_adjacent_rawiy` on ridf-at-end and ridf-separated cases.
17. Section 13 (Poem Structure) examples: `is_valid_hemistich` on canonical + one variant + one gibberish per meter, `is_valid_qasida` on 1-line, 2-line, rhyme-mismatch, meter-mismatch, and variant-hemistich cases.
18. Add meter-specific ḥashw refinements to `foot_permitted_zihaf` (e.g. kaff rare in Ṭawīl).
19. Formalize poem sub-genres (ghazal, rubāʿī, maqṭūʿa) as structural predicates over `poem`.
20. Introduce `SuperLong` weight to distinguish tarfīl from tadhyīl.
21. Add `Extraction` directives for core computable functions to OCaml or Haskell.
22. Build an extracted test harness against classical Arabic verse transcriptions.
