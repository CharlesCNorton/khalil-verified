# Khalil-Verified: Outstanding Issues

1. Prove scansion completeness: if a pattern is any legal single-variation of a meter, `scan` finds it.
2. Add ambiguity detection — flag when a pattern matches more than one meter with or without variation.
3. Prove non-ambiguity/uniqueness theorems for the scanner — e.g., "no pattern matches two distinct meters under single-variation scansion," or "Tawil and Basit are never confused by `scan`." These are proof obligations about the system's discriminating power, distinct from the detection feature in #2.
4. Formalize taqṭīʿ: given a meter and a flat syllable pattern, recover the foot-boundary segmentation.
5. Revise `is_valid_bayt` to accept hemistichs with legal zihāf in ḥashw positions and ʿilla in ʿarūḍ/ḍarb, rather than demanding exact meter-pattern match. **As-is, `is_valid_bayt` rejects the vast majority of real classical Arabic poetry, since virtually every line uses at least one variation. This makes Section 12 largely decorative until fixed.**
6. Revise `is_valid_qasida` to use variation-aware bayt validity.
7. Make `is_well_formed_rhyme` check adjacency constraints (ridf must immediately precede rawīy), not just relative ordering.
8. Replace the abstract `rhyme_id = nat` with a type derived from actual rawīy consonant and vowel identity, connecting rhyme elements to rhyme identity. **Currently rhyme is entirely abstract — `nat` equality says nothing about phonological content. The rhyme section proves structural properties of a type that doesn't model what rhyme actually is.**
9. Make `is_matla_proper` verify phonological rhyme content rather than abstract nat equality.
10. Enforce poem non-emptiness at the type level or make `is_valid_poem` reject empty lists. (`qasida` record enforces non-emptiness; `is_valid_poem` on plain `poem` type still accepts `[]`.)
11. Formalize poem sub-genres (ghazal, rubāʿī, maqṭūʿa) as structural predicates over the `poem` type.
12. Generalize mutaḥarrik-modifying lemmas (`iḍmār_preserves_morae`, `shamm_preserves_morae`, `ʿaṣb_preserves_morae`, `waqṣ_reduces_morae`, `ʿaql_reduces_morae`, and corresponding count lemmas) to pattern-general lemmas analogous to `delete_sakin_preserves_count`, eliminating the per-foot `destruct f` proofs.
13. Introduce a `SuperLong` weight constructor to distinguish tarfīl from tadhyīl at the type level. Currently `tarfīl_eq_tadhyīl` proves them extensionally identical, meaning the formalization conflates two traditionally distinct operations. This propagates changes throughout the weight type and all downstream definitions.
14. Add Ltac automation for exhaustive case splits on `foot`, `meter`, `zihaf`, `ʿilla`, and `compound_zihaf` types. The current 8-way foot destructs and 16-way meter destructs are done manually every time; a `decide_by_exhaustion` tactic or similar would eliminate hundreds of repetitive proof lines.
15. Strengthen witnesses and counterexamples so that each one tests a property the universal lemma does NOT already guarantee — e.g., boundary cases, off-by-one positions, interaction between operations, or coverage of all constructors.
16. Add meter-specific ḥashw refinements to `foot_permitted_zihaf` — e.g., kaff on mafāʿīlun is rare/ugly in Ṭawīl but acceptable in other meters. Currently the rules are per-foot-type only, with no meter-level overrides.
17. Split monolithic `Khalil.v` (5,871 lines) into per-section modules (`Foundations.v`, `Letters.v`, `Blocks.v`, `Feet.v`, `Meters.v`, `Circles.v`, `Variations.v`, `Scansion.v`, `Rhyme.v`, `Poem.v`). Enables parallel `coqc` compilation, cleaner dependency tracking, and independent development of sections.
18. Add `Extraction` directives for the core computable functions (`scan`, `pattern_to_meter`, `apply_khabn`, etc.) to OCaml or Haskell, enabling use outside Coq.
19. Build an extracted test harness that runs the scanner against known syllable-weight transcriptions of classical Arabic verses (e.g., the opening of the Muʿallaqa of Imruʾ al-Qays in Ṭawīl). **This is the single most important validation step.**
