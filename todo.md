# Khalil-Verified: Outstanding Issues

1. Add missing simple zihāf (shamm and others from the classical inventory) to the type and enumeration.
2. Add missing compound zihāf (khazt and others) to `compound_zihaf` with application functions. (Qaṭf is implemented as ʿilla; khazt and others still missing.)
3. Add missing ʿilla operations (tathlīth, tadhyīl, ḥadhdhāʾ, and others) to the `ʿilla` type with application functions.
4. Make `letters_to_pattern` return `option pattern` or otherwise signal an error on orphan sākin instead of silently dropping them.
5. Wrap `pattern_eqb_eq` as a standard-library `DecidableEq` instance.
6. Prove `rotate` composes correctly for arbitrary `n` and `m` — `rotate m (rotate n p) = rotate ((m + n) mod length p) p`. (Restricted version `rotate_add` proved with preconditions; full mod version outstanding.)
7. Prove the 8 canonical feet are exactly the rotation-orbit representatives of `{S,L}^3 ∪ {S,L}^4 ∪ {S,L}^5`. (Enumeration and count done; orbit representative proof outstanding.)
8. Prove that rotation of a circle's generator foot produces exactly that circle's foot set and nothing beyond it — exhaustion, not just inclusion. (Per-generator exhaustion lemmas exist; general theorem outstanding.)
9. Replace the per-foot `destruct f` proofs for zihāf syllable-count properties with general lemmas over arbitrary patterns (e.g., deleting a sākin from a well-formed letter sequence preserves syllable count for any pattern).
10. Define a mora-counting function and prove that every applicable zihāf reduces total mora count.
11. Implement per-foot variation matching — try each legal variation on each foot independently rather than on the whole concatenated meter pattern.
12. Extend variant scanning to cover ṭayy, qabḍ, kaff, waqṣ, ʿaṣb, iḍmār, and all compound zihāf, not just khabn.
13. Implement combinatorial scansion — match input against the Cartesian product of per-foot variant possibilities.
14. Enrich `scan_result` to report which variation was applied at which foot position.
15. Prove scansion soundness: if `scan` returns `ScanVariant m`, the input is a legal variant of meter `m`.
16. Prove scansion completeness: if a pattern is any legal single-variation of a meter, `scan` finds it.
17. Add ambiguity detection — flag when a pattern matches more than one meter with or without variation.
18. Formalize taqṭīʿ: given a meter and a flat syllable pattern, recover the foot-boundary segmentation.
19. Build an extracted test harness that runs the scanner against known syllable-weight transcriptions of classical Arabic verses (e.g., the opening of the Muʿallaqa of Imruʾ al-Qays in Ṭawīl).
20. Revise `is_valid_bayt` to accept hemistichs with legal zihāf in ḥashw positions and ʿilla in ʿarūḍ/ḍarb, rather than demanding exact meter-pattern match.
21. Revise `is_valid_qasida` to use variation-aware bayt validity.
22. Make `is_well_formed_rhyme` check adjacency constraints (ridf must immediately precede rawīy), not just relative ordering.
23. Replace the abstract `rhyme_id = nat` with a type derived from actual rawīy consonant and vowel identity, connecting rhyme elements to rhyme identity.
24. Make `is_matla_proper` verify phonological rhyme content rather than abstract nat equality.
25. Enforce poem non-emptiness at the type level or make `is_valid_poem` reject empty lists. (`qasida` record enforces non-emptiness; `is_valid_poem` on plain `poem` type still accepts `[]`.)
26. Formalize poem sub-genres (ghazal, rubāʿī, maqṭūʿa) as structural predicates over the `poem` type.
27. Prune witnesses and counterexamples that add no assurance beyond an already-proven universal lemma.
