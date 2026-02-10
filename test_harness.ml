open Khalil_types
open Khalil_extracted

(* ================================================================ *)
(*  Test infrastructure                                             *)
(* ================================================================ *)

let passed = ref 0
let failed = ref 0
let errors = ref []

let check name cond =
  if cond then incr passed
  else begin
    incr failed;
    errors := name :: !errors;
    Printf.printf "  FAIL: %s\n%!" name
  end

let s = Short
let l = Long

let string_of_weight = function Short -> "S" | Long -> "L" | SuperLong -> "X"

let string_of_pattern p =
  String.concat "" (List.map string_of_weight p)

let string_of_meter = function
  | Tawil -> "Tawil" | Madid -> "Madid" | Basit -> "Basit"
  | Wafir -> "Wafir" | Kamil -> "Kamil" | Hazaj -> "Hazaj"
  | Rajaz -> "Rajaz" | Ramal -> "Ramal" | Sari -> "Sari"
  | Munsarih -> "Munsarih" | Khafif -> "Khafif" | Mudari -> "Mudari"
  | Muqtadab -> "Muqtadab" | Mujtathth -> "Mujtathth"
  | Mutaqarib -> "Mutaqarib" | Mutadarik -> "Mutadarik"

let string_of_foot = function
  | Faulun -> "Faulun" | Failun -> "Failun" | Mafailun -> "Mafailun"
  | Mustafilun -> "Mustafilun" | Failatun -> "Failatun"
  | Mafulatu -> "Mafulatu" | Mutafailun -> "Mutafailun"
  | Mufaalatun -> "Mufaalatun"

let string_of_annotation = function
  | Canonical -> "canonical"
  | SimpleZihaf z ->
    (match z with Khabn -> "khabn" | Tayy -> "tayy" | Qabd -> "qabd"
     | Kaff -> "kaff" | Waqs -> "waqs" | Asb -> "asb" | Idmar -> "idmar"
     | Aql -> "aql" | Shamm -> "shamm")
  | CompoundZihaf z ->
    (match z with Khazl -> "khazl" | Khabl -> "khabl"
     | Shakl -> "shakl" | Naqs -> "naqs")
  | Illa i ->
    (match i with Qat -> "qat" | Qasr -> "qasr" | Hadhf -> "hadhf"
     | Tasbigh -> "tasbigh" | Batr -> "batr" | Qatf -> "qatf"
     | Tarfil -> "tarfil" | Tadhyil -> "tadhyil" | Hadhadh -> "hadhadh"
     | Salm -> "salm" | Kashf -> "kashf" | Waqf -> "waqf"
     | Tashith -> "tashith")

let string_of_scan_result = function
  | ScanSuccess m -> Printf.sprintf "ScanSuccess(%s)" (string_of_meter m)
  | ScanVariant (m, anns) ->
    Printf.sprintf "ScanVariant(%s, [%s])" (string_of_meter m)
      (String.concat "; " (List.map string_of_annotation anns))
  | ScanFailed -> "ScanFailed"

let section name =
  Printf.printf "\n=== %s ===\n%!" name

(* ================================================================ *)
(*  1. Canonical meter scan — all 16 meters                        *)
(* ================================================================ *)

let () = section "Canonical meter scan (all 16)"

let () =
  List.iter (fun m ->
    let p = meter_pattern m in
    let name = string_of_meter m in
    let result = scan p in
    check (Printf.sprintf "%s exact scan" name)
      (match result with ScanSuccess m' -> meter_eq_dec m m' | _ -> false);
    check (Printf.sprintf "%s pattern_to_meter round-trip" name)
      (match pattern_to_meter p with Some m' -> meter_eq_dec m m' | None -> false)
  ) all_meters

(* ================================================================ *)
(*  2. Foot pattern round-trip — all 8 feet                        *)
(* ================================================================ *)

let () = section "Foot pattern round-trip (all 8)"

let () =
  List.iter (fun f ->
    let p = foot_pattern f in
    let name = string_of_foot f in
    check (Printf.sprintf "%s pattern_to_foot" name)
      (match pattern_to_foot p with Some f' -> f = f' | None -> false);
    check (Printf.sprintf "%s is_foot" name)
      (is_foot p)
  ) all_feet

(* ================================================================ *)
(*  3. Meter pattern distinctness — all pairs                      *)
(* ================================================================ *)

let () = section "Meter pattern distinctness"

let () =
  let ms = all_meters in
  List.iter (fun m1 ->
    List.iter (fun m2 ->
      if not (meter_eq_dec m1 m2) then
        check (Printf.sprintf "%s != %s" (string_of_meter m1) (string_of_meter m2))
          (not (pattern_eqb (meter_pattern m1) (meter_pattern m2)))
    ) ms
  ) ms

(* ================================================================ *)
(*  4. Foot block decomposition — all 8 feet                       *)
(* ================================================================ *)

let () = section "Foot block decomposition (all 8)"

let () =
  List.iter (fun f ->
    let name = string_of_foot f in
    let blocks = foot_blocks f in
    check (Printf.sprintf "%s blocks reconstruct pattern" name)
      (pattern_eqb (blocks_to_pattern blocks) (foot_pattern f));
    check (Printf.sprintf "%s canonical decomposition" name)
      (is_canonical_decomposition f blocks)
  ) all_feet

(* ================================================================ *)
(*  5. Circle membership — all 16 meters                           *)
(* ================================================================ *)

let () = section "Circle membership (all 16 meters)"

let () =
  List.iter (fun m ->
    let c = meter_circle m in
    let name = string_of_meter m in
    check (Printf.sprintf "%s in its circle" name)
      (is_in_circle m c)
  ) all_meters

(* ================================================================ *)
(*  6. Rotation algebra                                            *)
(* ================================================================ *)

let () = section "Rotation algebra"

let () =
  check "rotate 0 = identity"
    (pattern_eqb (rotate 0 mafailun) mafailun);
  check "rotate length = identity"
    (pattern_eqb (rotate 4 mafailun) mafailun);
  check "mafailun rot 1 = mafulatu"
    (pattern_eqb (rotate 1 mafailun) mafulatu);
  check "mafailun rot 2 = mustafilun"
    (pattern_eqb (rotate 2 mafailun) mustafilun);
  check "mafailun rot 3 = failatun"
    (pattern_eqb (rotate 3 mafailun) failatun);
  check "faulun rot 2 = failun"
    (pattern_eqb (rotate 2 faulun) failun);
  check "mufaalatun rot 2 = mutafailun"
    (pattern_eqb (rotate 2 mufaalatun) mutafailun);
  check "Mutadarik = Mutaqarib rotated by 2"
    (pattern_eqb (rotate 2 (meter_pattern Mutaqarib)) (meter_pattern Mutadarik))

(* ================================================================ *)
(*  7. Simple zihaf on all feet (72 pairs)                         *)
(* ================================================================ *)

let () = section "Simple zihaf applicability (72 pairs)"

let () =
  let count = ref 0 in
  List.iter (fun z ->
    List.iter (fun f ->
      let applies = zihaf_applies_to z f in
      let result = apply_zihaf z (foot_pattern f) in
      check (Printf.sprintf "zihaf consistency z=%d f=%s"
        !count (string_of_foot f))
        (match result with
         | Some _ -> applies
         | None -> not applies);
      incr count
    ) all_feet
  ) all_zihaf

(* ================================================================ *)
(*  8. Canonical ambiguity — only Rajaz is ambiguous               *)
(* ================================================================ *)

let () = section "Canonical ambiguity counts"

let () =
  List.iter (fun m ->
    let cnt = ambiguity_count (meter_pattern m) in
    let name = string_of_meter m in
    let expected = if meter_eq_dec m Rajaz then 2 else 1 in
    check (Printf.sprintf "%s ambiguity=%d (expect %d)" name cnt expected)
      (cnt = expected)
  ) all_meters

(* ================================================================ *)
(*  9. Variant overlap pairs                                       *)
(* ================================================================ *)

let () = section "Variant overlap pairs"

let () =
  let pairs = overlap_pairs in
  check "overlap_pairs has 14 entries" (Khalil_extracted.length pairs = 14);
  check "Kamil-Rajaz overlap" (meters_share_variant Kamil Rajaz);
  check "Rajaz-Kamil overlap" (meters_share_variant Rajaz Kamil);
  check "Tawil-Basit no overlap" (not (meters_share_variant Tawil Basit));
  check "Hazaj-Muqtadab overlap" (meters_share_variant Hazaj Muqtadab);
  check "Mudari-Mujtathth overlap" (meters_share_variant Mudari Mujtathth)

(* ================================================================ *)
(*  10. Classical verse — Antara (Kamil)                           *)
(* ================================================================ *)

let () = section "Classical verse: Antara (Kamil)"

(* هل غادر الشعراء من متردم / أم هل عرفت الدار بعد توهم *)
(* First hemistich: idmar on foot 1, canonical feet 2-3 *)
let antara_sadr = [l;l;s;l; s;s;l;s;l; s;s;l;s;l]
(* Second hemistich: idmar on feet 1-2, canonical foot 3 *)
let antara_ajuz = [l;l;s;l; l;l;s;l; s;s;l;s;l]

let () =
  check "Antara sadr scans as Kamil"
    (match scan antara_sadr with
     | ScanVariant (Kamil, _) -> true | _ -> false);
  check "Antara sadr: idmar + canonical + canonical"
    (match scan antara_sadr with
     | ScanVariant (Kamil, [SimpleZihaf Idmar; Canonical; Canonical]) -> true
     | _ -> false);
  check "Antara ajuz scans as Kamil"
    (match scan antara_ajuz with
     | ScanVariant (Kamil, _) -> true | _ -> false);
  check "Antara ajuz: idmar + idmar + canonical"
    (match scan antara_ajuz with
     | ScanVariant (Kamil, [SimpleZihaf Idmar; SimpleZihaf Idmar; Canonical]) -> true
     | _ -> false);
  check "Antara sadr is valid Kamil hemistich"
    (is_valid_hemistich antara_sadr Kamil);
  check "Antara ajuz is valid Kamil hemistich"
    (is_valid_hemistich antara_ajuz Kamil);
  check "Antara bayt is valid"
    (is_valid_bayt { sadr = antara_sadr; ajuz = antara_ajuz } Kamil);
  check "Antara sadr unambiguous"
    (Khalil_extracted.length (scan_all antara_sadr) = 1);
  check "Antara sadr taqtii segments = 3"
    (match taqtii Kamil antara_sadr with
     | Some segs -> Khalil_extracted.length segs = 3
     | None -> false)

(* ================================================================ *)
(*  11. Classical verse — Imru' al-Qays (Tawil)                   *)
(* ================================================================ *)

let () = section "Classical verse: Imru' al-Qays (Tawil)"

(* قفا نبك من ذكرى حبيب ومنزل / بسقط اللوى بين الدخول فحومل *)
(* First hemistich: canonical feet 1-3, qabd on foot 4 *)
let imru_sadr = [s;l;l; s;l;l;l; s;l;l; s;l;s;l]
(* Second hemistich: canonical feet 1-2, qabd on feet 3-4 *)
let imru_ajuz = [s;l;l; s;l;l;l; s;l;s; s;l;s;l]

let () =
  check "Imru sadr scans as Tawil"
    (match scan imru_sadr with
     | ScanVariant (Tawil, _) -> true | _ -> false);
  check "Imru sadr: canonical + canonical + canonical + qabd"
    (match scan imru_sadr with
     | ScanVariant (Tawil, [Canonical; Canonical; Canonical; SimpleZihaf Qabd]) -> true
     | _ -> false);
  check "Imru ajuz scans as Tawil"
    (match scan imru_ajuz with
     | ScanVariant (Tawil, _) -> true | _ -> false);
  check "Imru ajuz: canonical + canonical + qabd + qabd"
    (match scan imru_ajuz with
     | ScanVariant (Tawil, [Canonical; Canonical; SimpleZihaf Qabd; SimpleZihaf Qabd]) -> true
     | _ -> false);
  check "Imru bayt is valid"
    (is_valid_bayt { sadr = imru_sadr; ajuz = imru_ajuz } Tawil);
  check "Imru sadr unambiguous"
    (Khalil_extracted.length (scan_all imru_sadr) = 1);
  check "Imru sadr taqtii segments = 4"
    (match taqtii Tawil imru_sadr with
     | Some segs -> Khalil_extracted.length segs = 4
     | None -> false)

(* ================================================================ *)
(*  12. Classical verse — Amr ibn Kulthum (Wafir)                  *)
(* ================================================================ *)

let () = section "Classical verse: Amr ibn Kulthum (Wafir)"

(* ألا هبي بصحنك فاصبحينا / ولا تبقي خمور الأندرينا *)
(* First hemistich: asb on foot 1, canonical feet 2-3 *)
let amr_sadr = [s;l;l;l; s;l;s;s;l; s;l;l]
(* Second hemistich: asb on feet 1-2, canonical foot 3 *)
let amr_ajuz = [s;l;l;l; s;l;l;l; s;l;l]

let () =
  check "Amr sadr scans as Wafir"
    (match scan amr_sadr with
     | ScanVariant (Wafir, _) -> true | _ -> false);
  check "Amr sadr: asb + canonical + canonical"
    (match scan amr_sadr with
     | ScanVariant (Wafir, [SimpleZihaf Asb; Canonical; Canonical]) -> true
     | _ -> false);
  check "Amr ajuz scans as Wafir"
    (match scan amr_ajuz with
     | ScanVariant (Wafir, _) -> true | _ -> false);
  check "Amr ajuz: asb + asb + canonical"
    (match scan amr_ajuz with
     | ScanVariant (Wafir, [SimpleZihaf Asb; SimpleZihaf Asb; Canonical]) -> true
     | _ -> false);
  check "Amr bayt is valid"
    (is_valid_bayt { sadr = amr_sadr; ajuz = amr_ajuz } Wafir);
  check "Amr sadr unambiguous"
    (Khalil_extracted.length (scan_all amr_sadr) = 1)

(* ================================================================ *)
(*  13. Classical verse — Rumi's Masnavi (Ramal)                   *)
(* ================================================================ *)

let () = section "Classical verse: Rumi Masnavi (Ramal)"

(* بشنو از نی چون حکایت می‌کند / از جدایی‌ها شکایت می‌کند *)
(* Ramal musaddas mahdhuf: failatun failatun failun *)
let rumi_1_sadr = [l;s;l;l; l;s;l;l; l;s;l]
let rumi_1_ajuz = [l;s;l;l; l;s;l;l; l;s;l]

(* کز نیستان تا مرا ببریده‌اند / در نفیرم مرد و زن نالیده‌اند *)
let rumi_2_sadr = [l;s;l;l; l;s;l;l; l;s;l]
let rumi_2_ajuz = [l;s;l;l; l;s;l;l; l;s;l]

let () =
  check "Rumi 1 sadr scans as Ramal"
    (match scan rumi_1_sadr with
     | ScanVariant (Ramal, _) -> true | _ -> false);
  check "Rumi 1 sadr: canonical + canonical + hadhf"
    (match scan rumi_1_sadr with
     | ScanVariant (Ramal, [Canonical; Canonical; Illa Hadhf]) -> true
     | _ -> false);
  check "Rumi 1 ajuz: canonical + canonical + hadhf"
    (match scan rumi_1_ajuz with
     | ScanVariant (Ramal, [Canonical; Canonical; Illa Hadhf]) -> true
     | _ -> false);
  check "Rumi 1 bayt is valid"
    (is_valid_bayt { sadr = rumi_1_sadr; ajuz = rumi_1_ajuz } Ramal);
  check "Rumi 2 bayt is valid"
    (is_valid_bayt { sadr = rumi_2_sadr; ajuz = rumi_2_ajuz } Ramal);
  check "Rumi 1 sadr unambiguous"
    (Khalil_extracted.length (scan_all rumi_1_sadr) = 1);
  check "Rumi 1 taqtii segments = 3"
    (match taqtii Ramal rumi_1_sadr with
     | Some segs -> Khalil_extracted.length segs = 3
     | None -> false)

(* ================================================================ *)
(*  14. Taqtii concatenation — all 16 meters                      *)
(* ================================================================ *)

let () = section "Taqtii concatenation (all 16 meters)"

let () =
  List.iter (fun m ->
    let p = meter_pattern m in
    let name = string_of_meter m in
    match taqtii m p with
    | Some segs ->
      let reconstructed = concat (map Khalil_extracted.fst segs) in
      check (Printf.sprintf "%s taqtii concatenates to original" name)
        (pattern_eqb reconstructed p);
      check (Printf.sprintf "%s taqtii segment count = foot count" name)
        (Khalil_extracted.length segs =
         Khalil_extracted.length (meter_foot_variants m))
    | None ->
      check (Printf.sprintf "%s taqtii should succeed" name) false
  ) all_meters

(* ================================================================ *)
(*  15. Poem structure — qasida validation                         *)
(* ================================================================ *)

let () = section "Poem structure: qasida"

let () =
  let h = meter_pattern Hazaj in
  let r = { ri_rawiy = 1; ri_majra = Kasra } in
  let r2 = { ri_rawiy = 2; ri_majra = Kasra } in
  let matla = { ab_sadr = h; ab_ajuz = h;
                ab_sadr_rhyme = r; ab_ajuz_rhyme = r } in
  let line = { ab_sadr = h; ab_ajuz = h;
               ab_sadr_rhyme = r2; ab_ajuz_rhyme = r } in
  check "1-line qasida valid"
    (is_valid_qasida { qas_first = matla; qas_rest = [];
                       qas_meter = Hazaj; qas_rhyme = r });
  check "2-line qasida valid"
    (is_valid_qasida { qas_first = matla; qas_rest = [line];
                       qas_meter = Hazaj; qas_rhyme = r });
  (* matla rhyme mismatch *)
  let bad_matla = { ab_sadr = h; ab_ajuz = h;
                    ab_sadr_rhyme = r; ab_ajuz_rhyme = r2 } in
  check "matla rhyme mismatch rejected"
    (not (is_valid_qasida { qas_first = bad_matla; qas_rest = [];
                            qas_meter = Hazaj; qas_rhyme = r2 }));
  (* meter mismatch *)
  check "wrong meter hemistich rejected"
    (not (is_valid_bayt { sadr = meter_pattern Tawil;
                          ajuz = meter_pattern Basit } Tawil))

(* ================================================================ *)
(*  16. Ghazal / Rubai / Maqtua bounds                            *)
(* ================================================================ *)

let () = section "Poetic forms: ghazal, rubai, maqtua"

let () =
  let h = meter_pattern Hazaj in
  let r = { ri_rawiy = 1; ri_majra = Kasra } in
  let r2 = { ri_rawiy = 2; ri_majra = Kasra } in
  let matla = { ab_sadr = h; ab_ajuz = h;
                ab_sadr_rhyme = r; ab_ajuz_rhyme = r } in
  let line = { ab_sadr = h; ab_ajuz = h;
               ab_sadr_rhyme = r2; ab_ajuz_rhyme = r } in
  (* ghazal: 5-15 lines *)
  check "5-line ghazal valid"
    (is_valid_ghazal { qas_first = matla;
                       qas_rest = [line; line; line; line];
                       qas_meter = Hazaj; qas_rhyme = r });
  check "4-line ghazal too short"
    (not (is_valid_ghazal { qas_first = matla;
                            qas_rest = [line; line; line];
                            qas_meter = Hazaj; qas_rhyme = r }));
  (* rubai: 2 lines, Hazaj only *)
  check "rubai valid"
    (is_valid_rubai { qas_first = matla; qas_rest = [line];
                      qas_meter = Hazaj; qas_rhyme = r });
  check "rubai wrong meter rejected"
    (not (is_valid_rubai { qas_first = matla; qas_rest = [line];
                           qas_meter = Rajaz; qas_rhyme = r }));
  check "rubai 3 lines rejected"
    (not (is_valid_rubai { qas_first = matla; qas_rest = [line; line];
                           qas_meter = Hazaj; qas_rhyme = r }));
  (* maqtua: 2-5 lines, no matla required *)
  let no_matla = { ab_sadr = h; ab_ajuz = h;
                   ab_sadr_rhyme = r2; ab_ajuz_rhyme = r } in
  check "2-line maqtua valid (no matla)"
    (is_valid_maqtua { qas_first = no_matla; qas_rest = [line];
                       qas_meter = Hazaj; qas_rhyme = r });
  check "1-line maqtua too short"
    (not (is_valid_maqtua { qas_first = no_matla; qas_rest = [];
                            qas_meter = Hazaj; qas_rhyme = r }))

(* ================================================================ *)
(*  17. Rhyme structure                                            *)
(* ================================================================ *)

let () = section "Rhyme structure"

let () =
  check "minimal rhyme valid" (is_valid_rhyme minimal_rhyme);
  check "ridf rhyme valid" (is_valid_rhyme ridf_rhyme);
  check "wasl rhyme valid" (is_valid_rhyme wasl_rhyme);
  check "tasis rhyme valid" (is_valid_rhyme tasis_rhyme);
  check "empty rhyme invalid" (not (is_valid_rhyme []));
  check "double rawiy invalid" (not (is_valid_rhyme [Rawiy; Rawiy]));
  check "tasis rhyme well-formed" (is_well_formed_rhyme tasis_rhyme);
  check "ridf rhyme well-formed" (is_well_formed_rhyme ridf_rhyme);
  check "wasl-before-rawiy malformed"
    (not (is_well_formed_rhyme [Wasl; Rawiy]));
  check "dakhil-before-tasis malformed"
    (not (is_well_formed_rhyme [Dakhil; Tasis; Rawiy]));
  check "ridf non-adjacent malformed"
    (not (is_well_formed_rhyme [Ridf; Wasl; Rawiy]))

(* ================================================================ *)
(*  18. Illa at terminal positions                                 *)
(* ================================================================ *)

let () = section "Illa at terminal positions"

let () =
  check "hadhf legal at Tawil arud"
    (is_legal_arud_illa Tawil Hadhf);
  check "qat legal at Kamil darb"
    (is_legal_darb_illa Kamil Qat);
  check "qasr legal at Tawil arud"
    (is_legal_arud_illa Tawil Qasr);
  check "batr legal at Mutaqarib darb"
    (is_legal_darb_illa Mutaqarib Batr);
  check "tasbigh legal at Ramal darb"
    (is_legal_darb_illa Ramal Tasbigh);
  check "kashf legal at Sari arud"
    (is_legal_arud_illa Sari Kashf);
  (* negative *)
  check "qat NOT legal at Tawil arud"
    (not (is_legal_arud_illa Tawil Qat));
  check "hadhf NOT legal at Basit arud"
    (not (is_legal_arud_illa Basit Hadhf))

(* ================================================================ *)
(*  19. Variant hemistich acceptance                               *)
(* ================================================================ *)

let () = section "Variant hemistich acceptance"

let () =
  (* khabn on foot 1 of Rajaz *)
  let rajaz_khabn = [s;l;s;l; l;l;s;l; l;l;s;l] in
  check "Rajaz with khabn foot 1 accepted"
    (is_valid_hemistich rajaz_khabn Rajaz);
  (* qatr at terminal of Rajaz *)
  let rajaz_qat = [l;l;s;l; l;l;s;l; l;l;l] in
  check "Rajaz with qat at terminal accepted"
    (is_valid_hemistich rajaz_qat Rajaz);
  (* Kamil with idmar on all 3 feet = Rajaz pattern *)
  let kamil_all_idmar = [l;l;s;l; l;l;s;l; l;l;s;l] in
  check "Kamil all-idmar accepted as Kamil"
    (is_valid_hemistich kamil_all_idmar Kamil);
  check "Kamil all-idmar also accepted as Rajaz"
    (is_valid_hemistich kamil_all_idmar Rajaz);
  (* gibberish rejected *)
  check "gibberish rejected as Tawil"
    (not (is_valid_hemistich [s;s;s] Tawil))

(* ================================================================ *)
(*  20. Scan-all on known ambiguous pattern                        *)
(* ================================================================ *)

let () = section "Scan-all ambiguity"

let () =
  let ambig = [s;l;s;l; l;l;s;l; l;l;s;l] in
  let results = scan_all ambig in
  check "ambiguous pattern matches 2 meters"
    (Khalil_extracted.length results = 2);
  check "ambiguous pattern is flagged"
    (is_ambiguous ambig)

(* ================================================================ *)
(*  Summary                                                        *)
(* ================================================================ *)

let () =
  Printf.printf "\n========================================\n";
  Printf.printf "Results: %d passed, %d failed\n" !passed !failed;
  if !failed > 0 then begin
    Printf.printf "Failed tests:\n";
    List.iter (fun name -> Printf.printf "  - %s\n" name) (List.rev !errors);
    exit 1
  end else begin
    Printf.printf "All tests passed.\n";
    exit 0
  end
