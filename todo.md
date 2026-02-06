# Khalil-Verified: Outstanding Issues

1. Implement per-foot variation matching — try each legal variation on each foot independently
2. Implement combinatorial scansion — match input against the Cartesian product of per-foot variant possibilities
3. Enrich `scan_result` to report *which* variation was applied at *which* foot position
4. Prove scansion soundness: if `scan` returns `ScanVariant m`, the input is a legal variant of meter `m`
5. Prove scansion completeness: if a pattern is any legal single-variation of a meter, `scan` finds it
6. Add ambiguity detection — flag when a pattern matches more than one meter (with or without variation)
7. Formalize taqṭīʿ: given a meter and a flat syllable pattern, recover the foot-boundary segmentation
8. Replace `Qed` with `Defined` on all variation-application functions so they remain transparent for computation and extraction
9. Prune witness/counterexample pairs that add no assurance beyond an already-proven universal lemma (e.g., drop `weight_eqb_counterexample_1` when `weight_eqb_eq` already covers it)
10. Add inductive lemmas over arbitrary-length patterns — e.g., prove `is_prefix` is transitive, `rotate` composes correctly for arbitrary `n` and `m`, `pattern_eqb` is decidable equality in the standard-library sense
11. Prove a negative characterization: every 3-to-5-element pattern over `{Short, Long}` that is *not* one of the 8 canonical feet is rejected by `is_foot`
12. Formalize the relationship between the 8 selected feet and the full space of `{S,L}^3 ∪ {S,L}^4 ∪ {S,L}^5` — how many total patterns exist vs. how many Khalil chose and why (rotation orbits)
13. Add `Require Export` or a `_CoqProject` file so the development can be used as a library by downstream files
14. Add `Extraction Language OCaml` and `Extraction` directives for all computable functions (`scan`, `pattern_to_meter`, `apply_*`, `is_valid_poem`)
15. Build an extracted test harness that runs the scanner against known syllable-weight transcriptions of classical Arabic verses (e.g., the opening of the Muʿallaqa of Imruʾ al-Qays in Ṭawīl)
16. Formalize poem sub-genres — qaṣīda (long, mono-rhyme), ghazal, rubāʿī, maqṭūʿa — as structural predicates over the `poem` type
