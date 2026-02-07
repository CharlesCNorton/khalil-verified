# Khalil-Verified: Outstanding Issues

1. ~~Add missing compound zihāf (khazt and others)~~ **DONE** — all four traditional compound zihāf (khazl, khabl, shakl, naqs) are implemented. "Khazt" was a typo for khazl.
2. ~~Add missing ʿilla operations~~ **DONE** — added tadhyīl, ḥadhādh, ṣalm, kashf, waqf, tashʿīth (6 new types, 13 total). "Tathlīth" is not a standard ʿilla in any traditional source; "ḥadhdhāʾ" is the adjectival form — the operation is ḥadhādh.
3. Make `letters_to_pattern` return `option pattern` or otherwise signal an error on orphan sākin instead of silently dropping them. **This is a latent bug — silent data loss in a conversion function can mask errors in variation functions that produce malformed letter sequences. Fix before building more on top of it.**
4. Wrap `pattern_eqb_eq` as a standard-library `DecidableEq` instance.
5. Prove `rotate` composes correctly for arbitrary `n` and `m` — `rotate m (rotate n p) = rotate ((m + n) mod length p) p`. (Restricted version `rotate_add` proved with preconditions; full mod version outstanding.)
6. Prove the 8 canonical feet are exactly the rotation-orbit representatives of `{S,L}^3 ∪ {S,L}^4 ∪ {S,L}^5`. (Enumeration and count done; orbit representative proof outstanding.)
7. Prove that rotation of a circle's generator foot produces exactly that circle's foot set and nothing beyond it — exhaustion, not just inclusion. (Per-generator exhaustion lemmas exist; general theorem outstanding.)
8. Replace the per-foot `destruct f` proofs for zihāf syllable-count properties with general lemmas over arbitrary patterns (e.g., deleting a sākin from a well-formed letter sequence preserves syllable count for any pattern). **The contrast with the ʿilla count lemmas (which ARE general) makes this inconsistency conspicuous. The structural fact — "deleting a sākin never changes syllable count" — should be provable once over arbitrary well-formed letter sequences.**
9. Define a mora-counting function and prove that every applicable zihāf reduces total mora count.
10. Implement per-foot variation matching — try each legal variation on each foot independently rather than on the whole concatenated meter pattern.
11. Extend variant scanning to cover ṭayy, qabḍ, kaff, waqṣ, ʿaṣb, iḍmār, and all compound zihāf, not just khabn.
12. Implement combinatorial scansion — match input against the Cartesian product of per-foot variant possibilities.
13. Enrich `scan_result` to report which variation was applied at which foot position.
14. Prove scansion soundness: if `scan` returns `ScanVariant m`, the input is a legal variant of meter `m`.
15. Prove scansion completeness: if a pattern is any legal single-variation of a meter, `scan` finds it.
16. Add ambiguity detection — flag when a pattern matches more than one meter with or without variation.
17. Formalize taqṭīʿ: given a meter and a flat syllable pattern, recover the foot-boundary segmentation.
18. Build an extracted test harness that runs the scanner against known syllable-weight transcriptions of classical Arabic verses (e.g., the opening of the Muʿallaqa of Imruʾ al-Qays in Ṭawīl). **Without this, the formalization proves internal consistency but not correspondence to reality. The meter definitions themselves are unverified against real poetry — if a foot sequence is wrong, all proofs still pass. This is the single most important validation step.**
19. Revise `is_valid_bayt` to accept hemistichs with legal zihāf in ḥashw positions and ʿilla in ʿarūḍ/ḍarb, rather than demanding exact meter-pattern match. **As-is, `is_valid_bayt` rejects the vast majority of real classical Arabic poetry, since virtually every line uses at least one variation. This makes the poem-structure section (Section 9) largely decorative until fixed.**
20. Revise `is_valid_qasida` to use variation-aware bayt validity.
21. Make `is_well_formed_rhyme` check adjacency constraints (ridf must immediately precede rawīy), not just relative ordering.
22. Replace the abstract `rhyme_id = nat` with a type derived from actual rawīy consonant and vowel identity, connecting rhyme elements to rhyme identity.
23. Make `is_matla_proper` verify phonological rhyme content rather than abstract nat equality.
24. Enforce poem non-emptiness at the type level or make `is_valid_poem` reject empty lists. (`qasida` record enforces non-emptiness; `is_valid_poem` on plain `poem` type still accepts `[]`.)
25. Formalize poem sub-genres (ghazal, rubāʿī, maqṭūʿa) as structural predicates over the `poem` type.
26. Prune witnesses and counterexamples that add no assurance beyond an already-proven universal lemma. **The file is roughly 50% examples. Most witnesses immediately following a universal lemma or computable definition add zero proof strength — e.g., `weight_eq_dec_witness` after `weight_eq_dec` is already `Defined`. The counterexamples for trivial properties (NoDup failures on duplicated lists, etc.) are mechanical padding. Aggressive pruning would cut the file nearly in half with no loss of assurance.**
27. Add `Extraction` directives for the core computable functions (`scan`, `pattern_to_meter`, `apply_khabn`, etc.) to OCaml or Haskell, enabling use outside Coq. Without extraction, the formalization is a proof artifact only — it cannot be called from real software.
28. Formalize the legal zihāf/ʿilla combinations per meter — which variations are traditionally permitted at which positions in which meters. Currently the variation functions are generic (any zihāf on any foot), but the tradition restricts which variations are actually legal in each meter. Without this, combinatorial scansion (item 12) will over-generate false matches.
