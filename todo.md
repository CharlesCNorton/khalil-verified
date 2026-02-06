# Khalil-Verified: Outstanding Issues

1. Fix `sabab_khafif` from `[Short]` to `[Long]` (line 297)
2. Eliminate `BlkLong` and replace all uses with `BlkSababKhafif` in foot decompositions (lines 746, 764–785)
3. Fix `apply_qabḍ` to target syllable position 2 (0-indexed), not position 4 (line 1605)
4. Add the converse lemma `watad_not_sabab` — currently only shown by example at line 417
5. Add decidable equality for `zihaf`
6. Add decidable equality for `ʿilla`
7. Add decidable equality for `block`
8. Add decidable equality for `scan_result`
9. Add witness and counterexample for `all_watad_complete` (line 434)
10. Add witness and counterexample for `all_watad_nodup` (line 473)
11. Add witness, example, and counterexample for each of `faulun_length` through `mufaalatun_length` (lines 840–863)
12. Add example and counterexample for `trisyllabic_feet` (line 865)
13. Add witness for `quadrisyllabic_feet` (line 875)
14. Add witness, example, and counterexample for `pentasyllabic_feet` (line 887)
15. Add witness, example, and counterexample for `trisyllabic_count` (line 898)
16. Add witness, example, and counterexample for `quadrisyllabic_count` (line 901)
17. Add witness, example, and counterexample for `pentasyllabic_count` (line 904)
18. Add witness, example, and counterexample for `pattern_to_foot_unique` (line 941)
19. Add witness, example, and counterexample for `pattern_to_foot_none` (line 966)
20. Add foot decomposition uniqueness proof — `foot_blocks_correct` proves reconstruction, not that the decomposition is the only valid one
21. Add witness, example, and counterexample for `all_meters_length` (line 1102)
22. Add example and counterexample for `all_meters_nodup` (line 1125)
23. Add witness, example, and counterexample for each of `tawil_syllables` through `mutadarik_syllables` (lines 1142–1188)
24. Add example and counterexample for `dimeter_meters` (line 1205)
25. Add witness for `trimeter_meters` (line 1217)
26. Add witness, example, and counterexample for `tetrameter_meters` (line 1235)
27. Add witness, example, and counterexample for `khalil_original_length` (line 1332)
28. Add witness, example, and counterexample for `mutadarik_not_khalil` (line 1335)
29. Add example and counterexample for `all_circles_nodup` (line 1450)
30. Add witness, example, and counterexample for each of `mukhtalifa_size` through `muttafiqa_size` (lines 1505–1518)
31. Add witness, example, and counterexample for `circles_partition_meters` (line 1523)
32. Add example and counterexample for `meter_circle_unique` (line 1555)
33. Formalize the circle rotation property — define cyclic permutation on patterns and prove meters within each circle are rotations of a common pattern
34. Implement `apply_` functions for the 7 missing variation types (Tayy, Kaff, Waqṣ, ʿAṣb, Qaṭʿ, Tasbīgh, Batr)
35. Add example and counterexample for `all_zihaf_complete` (line 1715)
36. Add witness and counterexample for `all_ʿilla_complete` (line 1726)
37. Add witness, example, and counterexample for `all_zihaf_length` (line 1736)
38. Add witness, example, and counterexample for `all_ʿilla_length` (line 1739)
39. Prove which variations apply to which feet/meters — the context-dependence rules
40. Add witness, example, and counterexample for `is_prefix_refl` (line 1828)
41. Add witness, example, and counterexample for `is_prefix_nil` (line 1835)
42. Make `ScanVariant` actually constructible — implement variant-aware scansion that uses it
43. Add example and counterexample for `scan_summary_correct` (line 1887)
44. Formalize rhyme (qāfiya)
45. Formalize poem/line structure beyond the `is_full_line` boolean
