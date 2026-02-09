# Khalil-Verified: Outstanding Issues

1. Prove scansion completeness: if a pattern is any legal single-variation of a meter, `scan` finds it.
3. Add ambiguity detection — flag when a pattern matches more than one meter with or without variation.
4. Formalize taqṭīʿ: given a meter and a flat syllable pattern, recover the foot-boundary segmentation.
5. Revise `is_valid_bayt` to accept hemistichs with legal zihāf in ḥashw positions and ʿilla in ʿarūḍ/ḍarb, rather than demanding exact meter-pattern match. **As-is, `is_valid_bayt` rejects the vast majority of real classical Arabic poetry, since virtually every line uses at least one variation. This makes Section 12 largely decorative until fixed.**
6. Revise `is_valid_qasida` to use variation-aware bayt validity.
7. Make `is_well_formed_rhyme` check adjacency constraints (ridf must immediately precede rawīy), not just relative ordering.
8. Replace the abstract `rhyme_id = nat` with a type derived from actual rawīy consonant and vowel identity, connecting rhyme elements to rhyme identity. **Currently rhyme is entirely abstract — `nat` equality says nothing about phonological content. The rhyme section proves structural properties of a type that doesn't model what rhyme actually is.**
9. Make `is_matla_proper` verify phonological rhyme content rather than abstract nat equality.
10. Enforce poem non-emptiness at the type level or make `is_valid_poem` reject empty lists. (`qasida` record enforces non-emptiness; `is_valid_poem` on plain `poem` type still accepts `[]`.)
11. Formalize poem sub-genres (ghazal, rubāʿī, maqṭūʿa) as structural predicates over the `poem` type.
12. Strengthen witnesses and counterexamples so that each one tests a property the universal lemma does NOT already guarantee — e.g., boundary cases, off-by-one positions, interaction between operations, or coverage of all constructors.
13. Add `Extraction` directives for the core computable functions (`scan`, `pattern_to_meter`, `apply_khabn`, etc.) to OCaml or Haskell, enabling use outside Coq.
14. Build an extracted test harness that runs the scanner against known syllable-weight transcriptions of classical Arabic verses (e.g., the opening of the Muʿallaqa of Imruʾ al-Qays in Ṭawīl). **This is the single most important validation step.**
15. Add meter-specific ḥashw refinements to `foot_permitted_zihaf` — e.g., kaff on mafāʿīlun is rare/ugly in Ṭawīl but acceptable in other meters. Currently the rules are per-foot-type only, with no meter-level overrides.
