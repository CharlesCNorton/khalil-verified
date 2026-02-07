# Khalil-Verified: Outstanding Issues

1. Promote iḍmār into the `zihaf` inductive type and `all_zihaf` enumeration instead of treating it as a standalone function.
2. Add missing simple zihāf (shamm and others from the classical inventory) to the type and enumeration.
3. Add missing compound zihāf (qaṭf, khazt, and others) to `compound_zihaf` with application functions.
4. Add missing ʿilla operations (tathlīth, tadhyīl, ḥadhdhāʾ, and others) to the `ʿilla` type with application functions.
5. Correct `mutafailun_blocks` to the traditional decomposition (sabab thaqīl + sabab khafīf + watad majmūʿ) or explicitly document and justify the divergence from the dominant Khalilian analysis.
6. Make `letters_to_pattern` return `option pattern` or otherwise signal an error on orphan sākin instead of silently dropping them.
7. Wrap `pattern_eqb_eq` as a standard-library `DecidableEq` instance.
8. Prove `is_prefix` is transitive.
9. Prove `rotate` composes correctly for arbitrary `n` and `m` — `rotate m (rotate n p) = rotate ((m + n) mod length p) p`.
10. Prove `NoDup (concat (map circle_meters all_circles))` — that no meter appears in two circles' lists, completing the partition theorem beyond the count check.
11. Enumerate `{S,L}^3 ∪ {S,L}^4 ∪ {S,L}^5` (56 total patterns) and prove the 8 canonical feet are exactly the rotation-orbit representatives.
12. Prove that every 3-to-5-element pattern over `{Short, Long}` not among the 8 canonical feet is rejected by `is_foot`.
13. Prove that rotation of a circle's generator foot produces exactly that circle's foot set and nothing beyond it — exhaustion, not just inclusion.
14. Replace the per-foot `destruct f` proofs for zihāf syllable-count properties with general lemmas over arbitrary patterns (e.g., deleting a sākin from a well-formed letter sequence preserves syllable count for any pattern).
15. Define a mora-counting function and prove that every applicable zihāf reduces total mora count.
16. Implement per-foot variation matching — try each legal variation on each foot independently rather than on the whole concatenated meter pattern.
17. Extend variant scanning to cover ṭayy, qabḍ, kaff, waqṣ, ʿaṣb, iḍmār, and all compound zihāf, not just khabn.
18. Implement combinatorial scansion — match input against the Cartesian product of per-foot variant possibilities.
19. Enrich `scan_result` to report which variation was applied at which foot position.
20. Prove scansion soundness: if `scan` returns `ScanVariant m`, the input is a legal variant of meter `m`.
21. Prove scansion completeness: if a pattern is any legal single-variation of a meter, `scan` finds it.
22. Add ambiguity detection — flag when a pattern matches more than one meter with or without variation.
23. Formalize taqṭīʿ: given a meter and a flat syllable pattern, recover the foot-boundary segmentation.
24. Build an extracted test harness that runs the scanner against known syllable-weight transcriptions of classical Arabic verses (e.g., the opening of the Muʿallaqa of Imruʾ al-Qays in Ṭawīl).
25. Revise `is_valid_bayt` to accept hemistichs with legal zihāf in ḥashw positions and ʿilla in ʿarūḍ/ḍarb, rather than demanding exact meter-pattern match.
26. Revise `is_valid_qasida` to use variation-aware bayt validity.
27. Make `is_well_formed_rhyme` check adjacency constraints (ridf must immediately precede rawīy), not just relative ordering.
28. Replace the abstract `rhyme_id = nat` with a type derived from actual rawīy consonant and vowel identity, connecting rhyme elements to rhyme identity.
29. Make `is_matla_proper` verify phonological rhyme content rather than abstract nat equality.
30. Enforce poem non-emptiness at the type level or make `is_valid_poem` reject empty lists.
31. Formalize poem sub-genres (ghazal, rubāʿī, maqṭūʿa) as structural predicates over the `poem` type.
32. Prune witnesses and counterexamples that add no assurance beyond an already-proven universal lemma.
