# Khalil-Verified: Outstanding Issues

## Generalization Limits (Document)

1. Document that `ʿaṣb_reduces_count` cannot be generalized beyond per-foot form — false on arbitrary patterns (e.g. ʿaṣb on [S;S;S;S;S]: count 5→3).
2. Document that `ʿaql_reduces_morae` cannot be generalized beyond per-foot form — false on arbitrary patterns (e.g. ʿaql on [S;S;L;S;S]: morae 6→4).
3. Document that `ʿaql_reduces_count` cannot be generalized beyond per-foot form — false on arbitrary patterns (e.g. ʿaql on [S;S;L;S;S]: count 5→3).

## Exhaustive Example Suites

4. Section 4 (Feet) examples: `is_foot` on all 8 canonical patterns and all 48 non-foot patterns from `foot_length_patterns`, `foot_blocks_correct` cross-verified against manual block concatenation for every foot, `pattern_to_foot` round-trip on all 8 feet plus None on representative non-feet.
5. Section 5 (Meters) examples: `meter_pattern` distinctness spot-checks on same-length pairs (Rajaz/Ramal, Hazaj/Mudari), `pattern_to_meter` round-trip on all 16 meters, `meter_foot_count` cross-checked against `meter_feet` length for every meter.
6. Section 6 (Circles) examples: `rotate` at 0, 1, length−1, length, length+1 on a representative pattern, `rotate_add_mod` concrete instances near the wrap boundary, every circle's generator exhaustively rotated to confirm exactly the expected feet appear and no others.
7. Section 7 (Variations — zihāf) examples: every simple zihāf applied to every foot (72 pairs), confirming Some/None matches `zihaf_applies_to`, result pattern verified for each applicable pair, mora-count change verified per pair.
8. Section 8 (Variations — ʿilla + compound) examples: every compound zihāf applied to every foot (32 pairs), every ʿilla applied to every foot (104 pairs), guarded vs unguarded ḥadhf/qaṭʿ/kashf divergence cases, `apply_batr` and `apply_qaṭf` intermediate-step verification.
9. Section 9 (Foot Positions & Variation Scope) examples: `assign_sadr_positions`/`assign_ajuz_positions` for every meter, all three positions tested against `zihaf_permitted`/`ʿilla_permitted`, `is_legal_zihaf_at` for boundary foot indices (first, last, out-of-range).
10. Section 10 (Legal Rules Per Meter) examples: `foot_permitted_zihaf` length bounds verified per foot, `permitted_arud_illa`/`permitted_darb_illa` non-emptiness or emptiness confirmed per meter, `is_legal_arud_illa`/`is_legal_darb_illa` full cross-product spot-checks.
11. Section 11 (Scansion) examples: `scan` on all 16 canonical meter patterns, `scan` on at least one variant per meter, `scan_all` on the Rajaz/Kamil ambiguous pattern plus 2–3 other known overlaps, `taqtii` concatenation verified on variant inputs, `taqtii` segment count verified on every meter.
12. Section 12 (Rhyme) examples: `is_valid_rhyme` on 0-rawiy, 1-rawiy, 2-rawiy patterns, `is_well_formed_rhyme` on all four named rhyme patterns plus malformed orderings, `ridf_adjacent_rawiy` on ridf-at-end and ridf-separated cases.
13. Section 13 (Poem Structure) examples: `is_valid_hemistich` on canonical + one variant + one gibberish per meter, `is_valid_qasida` on 1-line, 2-line, rhyme-mismatch, meter-mismatch, and variant-hemistich cases.

## Dead Code

14. Remove or use `safe_apply_variation`, `conversion_result`, and `letters_to_pattern_guarded` — defined in Section 2 but never referenced downstream. Either integrate them into the zihāf implementations or delete them.
15. `apply_kashf` is defined as `apply_ḥadhf` verbatim. `apply_shamm` is character-for-character identical to `apply_iḍmār`. Define as aliases with a documenting comment rather than duplicated function bodies.

## Guarding Inconsistencies

16. `apply_waqf` does not check for a watad mafrūq ending, unlike `apply_kashf_guarded`. Add a guarded variant (`apply_waqf_guarded`) that enforces `ends_with_watad_mafruq`, or document why waqf is intentionally unguarded.

## Proof Fragility

17. `ʿaṣb_preserves_morae_general` is a 15-line nested destruct cascade over w1/w2/w3/w4/w5. Replace with a structured proof (e.g. induction on the prefix up to index 4, then a single case split on the target letter) that would survive the addition of a fourth weight constructor.

## Domain Modeling Gaps

18. The rubāʿī is hardcoded to Hazaj (Persian convention). Document that the Arabic rubāʿī tradition uses a different meter structure (hazaj al-akhrab), or parameterize the meter.
19. `meter_hashw_zihaf` refinements collapse the traditional distinction between "rare" (qalīl) and "ugly" (qabīḥ) into a single exclusion. Either model two tiers (permitted / rare / forbidden) or document the collapse.
20. Section 11 (Rhyme) is skeletal — `rhyme_id` uses `nat` for consonant identity with no connection to actual phonological content. Extend with a concrete consonant type or document the abstraction boundary.

## Verse Coverage

21. Section 13 covers only 4 poems across 4 meters (Kāmil, Ṭawīl, Wāfir, Ramal). Add at least one classical verse test for each of the remaining 12 meters: Madīd, Basīṭ, Hazaj, Rajaz, Sarīʿ, Munsariḥ, Khafīf, Muḍāriʿ, Muqtaḍab, Mujtathth, Mutaqārib, Mutadārik.

## Structure

22. Split monolithic Khalil.v (~8100 lines) into modules: Foundations (Sections 1–3), Feet (Section 4), Meters (Sections 5–6), Variations (Sections 7–9), Scansion (Section 10), Rhyme (Section 11), Poem (Section 12), Tests (Section 13). This would enable parallel compilation and reduce cognitive load.
