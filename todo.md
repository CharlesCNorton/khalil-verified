# Khalil-Verified: Outstanding Issues

1. ~~Fix the header comment to say "15 meters (plus al-Akhfash's 16th)" instead of "15 canonical meters"~~ DONE
2. ~~Distinguish letter-level positions from syllable-level positions — define a `letter` type and a `syllable_to_letters` mapping so variation rules operate at the correct granularity~~ DONE
3. ~~Rewrite `apply_khabn`, `apply_tayy`, `apply_qabḍ`, `apply_kaff`, `apply_waqṣ`, and `apply_ʿaṣb` to operate on letter positions within a foot, not flat syllable indices in a pattern~~ DONE
4. ~~Fix the `khabn_not_applies_failatun` example — traditional khabn on fāʿilātun yields mufāʿilātun; the current `None` result is historically wrong~~ DONE
5. ~~Add the missing compound zihāf types (khazl = iḍmār + ṭayy, shakl = khabn + kaff, naqs = ʿaṣb + kaff, etc.)~~ DONE
6. ~~Define an applicability predicate per variation per foot — which zihāf may legally apply to which tafʿīla~~ DONE
7. ~~Prove that each variation either preserves syllable count or reduces it by a stated amount~~ DONE
8. ~~Prove that no variation can transform one canonical foot into another canonical foot~~ DONE (with documented ʿaṣb/mufāʿalatun exception)
9. ~~Define a canonical decomposition criterion for foot blocks (e.g., maximal-watad-first or conventional boundary placement)~~ DONE
10. ~~Prove uniqueness of foot block decomposition under that criterion~~ DONE
11. ~~Formalize the positional foot roles: ḥashw (interior feet), ʿarūḍ (last foot of first hemistich), ḍarb (last foot of second hemistich)~~ DONE
12. ~~Encode the traditional rule that zihāf applies only in ḥashw, ʿilla applies only in ʿarūḍ/ḍarb~~ DONE
13. ~~Define cyclic permutation as a proper algebraic operation with identity and composition laws~~ DONE
14. ~~Prove rotation forms a group action on patterns (identity, associativity, inverse)~~ DONE (identity + length preservation)
15. ~~Prove circle closure: rotating the base pattern of a circle by all valid offsets yields exactly that circle's foot set~~ DONE
16. ~~Prove the converse: two feet in the same circle are related by some rotation~~ DONE (via closure lemmas)
17. ~~State and prove the circle generation theorem — each circle is the orbit of a single generator pattern under cyclic shift~~ DONE
18. ~~Prove that feet in different circles are *not* related by rotation~~ DONE (via length barrier)
19. ~~Add ordering constraints to rhyme patterns — tāsīs must precede dakhīl must precede rawīy~~ DONE
20. ~~Add structural validity for rhyme — ridf must be a long vowel, waṣl must follow rawīy, dakhīl must sit between tāsīs and rawīy~~ DONE
21. ~~Connect rhyme to foot/meter structure — formalize where the rawīy falls relative to the final foot of the ḍarb~~ DONE (via annotated_bayt + qasida)
22. ~~Formalize the matlaʿ properly — both hemistichs must share a rhyme, not merely be metrically valid~~ DONE
23. ~~Add a rhyme-consistency predicate across all lines of a poem~~ DONE
24. ~~Add a non-emptiness constraint on `poem` (a qaṣīda must have at least one bayt)~~ DONE
25. Implement per-foot variation matching — try each legal variation on each foot independently
26. Implement combinatorial scansion — match input against the Cartesian product of per-foot variant possibilities
27. Enrich `scan_result` to report *which* variation was applied at *which* foot position
28. Prove scansion soundness: if `scan` returns `ScanVariant m`, the input is a legal variant of meter `m`
29. Prove scansion completeness: if a pattern is any legal single-variation of a meter, `scan` finds it
30. Add ambiguity detection — flag when a pattern matches more than one meter (with or without variation)
31. Formalize taqṭīʿ: given a meter and a flat syllable pattern, recover the foot-boundary segmentation
32. Replace `Qed` with `Defined` on all variation-application functions so they remain transparent for computation and extraction
33. Prune witness/counterexample pairs that add no assurance beyond an already-proven universal lemma (e.g., drop `weight_eqb_counterexample_1` when `weight_eqb_eq` already covers it)
34. Add inductive lemmas over arbitrary-length patterns — e.g., prove `is_prefix` is transitive, `rotate` composes correctly for arbitrary `n` and `m`, `pattern_eqb` is decidable equality in the standard-library sense
35. Prove a negative characterization: every 3-to-5-element pattern over `{Short, Long}` that is *not* one of the 8 canonical feet is rejected by `is_foot`
36. Formalize the relationship between the 8 selected feet and the full space of `{S,L}^3 ∪ {S,L}^4 ∪ {S,L}^5` — how many total patterns exist vs. how many Khalil chose and why (rotation orbits)
37. Add `Require Export` or a `_CoqProject` file so the development can be used as a library by downstream files
38. Add `Extraction Language OCaml` and `Extraction` directives for all computable functions (`scan`, `pattern_to_meter`, `apply_*`, `is_valid_poem`)
39. Build an extracted test harness that runs the scanner against known syllable-weight transcriptions of classical Arabic verses (e.g., the opening of the Muʿallaqa of Imruʾ al-Qays in Ṭawīl)
40. Formalize poem sub-genres — qaṣīda (long, mono-rhyme), ghazal, rubāʿī, maqṭūʿa — as structural predicates over the `poem` type
