open Khalil_types

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| x,_ -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| _,y -> y

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _::l' -> succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a::l1 -> a::(app l1 m)

(** val add : int -> int -> int **)

let rec add = (+)

module Nat =
 struct
  (** val sub : int -> int -> int **)

  let rec sub n m =
    (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
      (fun _ -> n)
      (fun k ->
      (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
        (fun _ -> n)
        (fun l -> sub k l)
        m)
      n

  (** val ltb : int -> int -> bool **)

  let ltb n m =
    (<=) (succ n) m

  (** val divmod : int -> int -> int -> int -> int * int **)

  let rec divmod x y q u =
    (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
      (fun _ -> q,u)
      (fun x' ->
      (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
        (fun _ -> divmod x' y (succ q) y)
        (fun u' -> divmod x' y q u')
        u)
      x

  (** val modulo : int -> int -> int **)

  let modulo x y =
    (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
      (fun _ -> x)
      (fun y' -> sub y' (snd (divmod x y' 0 y')))
      y
 end

(** val nth_error : 'a1 list -> int -> 'a1 option **)

let rec nth_error l n =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> match l with
              | [] -> None
              | x::_ -> Some x)
    (fun n0 -> match l with
               | [] -> None
               | _::l0 -> nth_error l0 n0)
    n

(** val last : 'a1 list -> 'a1 -> 'a1 **)

let rec last l d =
  match l with
  | [] -> d
  | a::l0 -> (match l0 with
              | [] -> a
              | _::_ -> last l0 d)

(** val removelast : 'a1 list -> 'a1 list **)

let rec removelast = function
| [] -> []
| a::l0 -> (match l0 with
            | [] -> []
            | _::_ -> a::(removelast l0))

(** val concat : 'a1 list list -> 'a1 list **)

let rec concat = function
| [] -> []
| x::l0 -> app x (concat l0)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a::t -> (f a)::(map f t)

(** val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let rec flat_map f = function
| [] -> []
| x::t -> app (f x) (flat_map f t)

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| [] -> false
| a::l0 -> (||) (f a) (existsb f l0)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| [] -> true
| a::l0 -> (&&) (f a) (forallb f l0)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x::l0 -> if f x then x::(filter f l0) else filter f l0

(** val firstn : int -> 'a1 list -> 'a1 list **)

let rec firstn n l =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> [])
    (fun n0 -> match l with
               | [] -> []
               | a::l0 -> a::(firstn n0 l0))
    n

(** val skipn : int -> 'a1 list -> 'a1 list **)

let rec skipn n l =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> l)
    (fun n0 -> match l with
               | [] -> []
               | _::l0 -> skipn n0 l0)
    n

type pattern = weight list

(** val weight_eqb : weight -> weight -> bool **)

let weight_eqb w1 w2 =
  match w1 with
  | Short -> (match w2 with
              | Short -> true
              | _ -> false)
  | Long -> (match w2 with
             | Long -> true
             | _ -> false)
  | SuperLong -> (match w2 with
                  | SuperLong -> true
                  | _ -> false)

(** val pattern_eqb : pattern -> pattern -> bool **)

let rec pattern_eqb p1 p2 =
  match p1 with
  | [] -> (match p2 with
           | [] -> true
           | _::_ -> false)
  | w1::p1' ->
    (match p2 with
     | [] -> false
     | w2::p2' -> (&&) (weight_eqb w1 w2) (pattern_eqb p1' p2'))

(** val pattern_length : pattern -> int **)

let pattern_length =
  length

(** val weight_morae : weight -> int **)

let weight_morae = function
| Short -> succ 0
| Long -> succ (succ 0)
| SuperLong -> succ (succ (succ 0))

(** val pattern_morae : pattern -> int **)

let rec pattern_morae = function
| [] -> 0
| w::rest -> add (weight_morae w) (pattern_morae rest)

(** val all_weights : weight list **)

let all_weights =
  Short::(Long::(SuperLong::[]))

type letter_seq = letter list

(** val syllable_to_letters : weight -> letter_seq **)

let syllable_to_letters = function
| Short -> Mutaharrik::[]
| _ -> Mutaharrik::(Sakin::[])

(** val pattern_to_letters : pattern -> letter_seq **)

let rec pattern_to_letters = function
| [] -> []
| w::rest -> app (syllable_to_letters w) (pattern_to_letters rest)

(** val letters_to_pattern : letter_seq -> pattern option **)

let rec letters_to_pattern = function
| [] -> Some []
| l::rest ->
  (match l with
   | Mutaharrik ->
     (match rest with
      | [] ->
        (match letters_to_pattern rest with
         | Some p -> Some (Short::p)
         | None -> None)
      | l0::rest0 ->
        (match l0 with
         | Mutaharrik ->
           (match letters_to_pattern rest with
            | Some p -> Some (Short::p)
            | None -> None)
         | Sakin ->
           (match letters_to_pattern rest0 with
            | Some p -> Some (Long::p)
            | None -> None)))
   | Sakin -> None)

(** val wf_letter_seq : letter_seq -> bool **)

let rec wf_letter_seq = function
| [] -> true
| l::rest ->
  (match l with
   | Mutaharrik ->
     (match rest with
      | [] -> wf_letter_seq rest
      | l0::rest0 ->
        (match l0 with
         | Mutaharrik -> wf_letter_seq rest
         | Sakin -> wf_letter_seq rest0))
   | Sakin -> false)

(** val normalize_weight : weight -> weight **)

let normalize_weight w = match w with
| SuperLong -> Long
| _ -> w

(** val normalize_pattern : pattern -> pattern **)

let normalize_pattern p =
  map normalize_weight p

(** val no_superlong : pattern -> bool **)

let rec no_superlong = function
| [] -> true
| w::rest -> (match w with
              | SuperLong -> false
              | _ -> no_superlong rest)

(** val letters_to_pattern_guarded : letter_seq -> conversion_result **)

let letters_to_pattern_guarded ls =
  if wf_letter_seq ls
  then (match letters_to_pattern ls with
        | Some p -> ConvOk p
        | None -> ConvMalformedOutput)
  else ConvMalformedOutput

(** val safe_apply_variation :
    (letter_seq -> letter_seq option) -> pattern -> conversion_result **)

let safe_apply_variation vary p =
  let ls = pattern_to_letters p in
  (match vary ls with
   | Some ls' ->
     if wf_letter_seq ls'
     then (match letters_to_pattern ls' with
           | Some p' -> ConvOk p'
           | None -> ConvMalformedOutput)
     else ConvMalformedOutput
   | None -> ConvPreconditionFailed)

(** val nth_sakin_pos : int -> letter_seq -> int -> int option **)

let rec nth_sakin_pos n ls idx =
  match ls with
  | [] -> None
  | l::rest ->
    (match l with
     | Mutaharrik -> nth_sakin_pos n rest (succ idx)
     | Sakin ->
       ((fun fO fS n -> if n = 0 then fO () else fS (n - 1))
          (fun _ -> Some idx)
          (fun n' -> nth_sakin_pos n' rest (succ idx))
          n))

(** val nth_mutaharrik_pos : int -> letter_seq -> int -> int option **)

let rec nth_mutaharrik_pos n ls idx =
  match ls with
  | [] -> None
  | l::rest ->
    (match l with
     | Mutaharrik ->
       ((fun fO fS n -> if n = 0 then fO () else fS (n - 1))
          (fun _ -> Some idx)
          (fun n' -> nth_mutaharrik_pos n' rest (succ idx))
          n)
     | Sakin -> nth_mutaharrik_pos n rest (succ idx))

(** val delete_at : int -> letter_seq -> letter_seq **)

let rec delete_at n = function
| [] -> []
| l::rest ->
  ((fun fO fS n -> if n = 0 then fO () else fS (n - 1))
     (fun _ -> rest)
     (fun n' -> l::(delete_at n' rest))
     n)

(** val replace_at : int -> letter -> letter_seq -> letter_seq **)

let rec replace_at n new_l = function
| [] -> []
| l::rest ->
  ((fun fO fS n -> if n = 0 then fO () else fS (n - 1))
     (fun _ -> new_l::rest)
     (fun n' -> l::(replace_at n' new_l rest))
     n)

(** val insert_at : int -> letter -> letter_seq -> letter_seq **)

let rec insert_at n new_l ls = match ls with
| [] ->
  ((fun fO fS n -> if n = 0 then fO () else fS (n - 1))
     (fun _ -> new_l::ls)
     (fun _ -> new_l::[])
     n)
| l::rest ->
  ((fun fO fS n -> if n = 0 then fO () else fS (n - 1))
     (fun _ -> new_l::ls)
     (fun n' -> l::(insert_at n' new_l rest))
     n)

(** val sabab_khafif : pattern **)

let sabab_khafif =
  Long::[]

(** val sabab_thaqil : pattern **)

let sabab_thaqil =
  Short::(Short::[])

(** val is_sabab_khafif : pattern -> bool **)

let is_sabab_khafif p =
  pattern_eqb p sabab_khafif

(** val is_sabab_thaqil : pattern -> bool **)

let is_sabab_thaqil p =
  pattern_eqb p sabab_thaqil

(** val is_sabab : pattern -> bool **)

let is_sabab p =
  (||) (is_sabab_khafif p) (is_sabab_thaqil p)

(** val watad_majmu : pattern **)

let watad_majmu =
  Short::(Long::[])

(** val watad_mafruq : pattern **)

let watad_mafruq =
  Long::(Short::[])

(** val is_watad_majmu : pattern -> bool **)

let is_watad_majmu p =
  pattern_eqb p watad_majmu

(** val is_watad_mafruq : pattern -> bool **)

let is_watad_mafruq p =
  pattern_eqb p watad_mafruq

(** val is_watad : pattern -> bool **)

let is_watad p =
  (||) (is_watad_majmu p) (is_watad_mafruq p)

(** val all_sabab : pattern list **)

let all_sabab =
  sabab_khafif::(sabab_thaqil::[])

(** val all_watad : pattern list **)

let all_watad =
  watad_majmu::(watad_mafruq::[])

(** val all_building_blocks : pattern list **)

let all_building_blocks =
  app all_sabab all_watad

(** val faulun : pattern **)

let faulun =
  Short::(Long::(Long::[]))

(** val failun : pattern **)

let failun =
  Long::(Short::(Long::[]))

(** val mafailun : pattern **)

let mafailun =
  Short::(Long::(Long::(Long::[])))

(** val mustafilun : pattern **)

let mustafilun =
  Long::(Long::(Short::(Long::[])))

(** val failatun : pattern **)

let failatun =
  Long::(Short::(Long::(Long::[])))

(** val mafulatu : pattern **)

let mafulatu =
  Long::(Long::(Long::(Short::[])))

(** val mutafailun : pattern **)

let mutafailun =
  Short::(Short::(Long::(Short::(Long::[]))))

(** val mufaalatun : pattern **)

let mufaalatun =
  Short::(Long::(Short::(Short::(Long::[]))))

(** val foot_pattern : foot -> pattern **)

let foot_pattern = function
| Faulun -> faulun
| Failun -> failun
| Mafailun -> mafailun
| Mustafilun -> mustafilun
| Failatun -> failatun
| Mafulatu -> mafulatu
| Mutafailun -> mutafailun
| Mufaalatun -> mufaalatun

(** val is_foot : pattern -> bool **)

let is_foot p =
  (||)
    ((||)
      ((||)
        ((||)
          ((||)
            ((||) ((||) (pattern_eqb p faulun) (pattern_eqb p failun))
              (pattern_eqb p mafailun)) (pattern_eqb p mustafilun))
          (pattern_eqb p failatun)) (pattern_eqb p mafulatu))
      (pattern_eqb p mutafailun)) (pattern_eqb p mufaalatun)

(** val all_feet : foot list **)

let all_feet =
  Faulun::(Failun::(Mafailun::(Mustafilun::(Failatun::(Mafulatu::(Mutafailun::(Mufaalatun::[])))))))

(** val block_eq_dec : block -> block -> bool **)

let block_eq_dec b1 b2 =
  match b1 with
  | BlkSababKhafif -> (match b2 with
                       | BlkSababKhafif -> true
                       | _ -> false)
  | BlkSababThaqil -> (match b2 with
                       | BlkSababThaqil -> true
                       | _ -> false)
  | BlkWatadMajmu -> (match b2 with
                      | BlkWatadMajmu -> true
                      | _ -> false)
  | BlkWatadMafruq -> (match b2 with
                       | BlkWatadMafruq -> true
                       | _ -> false)

(** val block_pattern : block -> pattern **)

let block_pattern = function
| BlkSababKhafif -> sabab_khafif
| BlkSababThaqil -> sabab_thaqil
| BlkWatadMajmu -> watad_majmu
| BlkWatadMafruq -> watad_mafruq

(** val blocks_to_pattern : block list -> pattern **)

let blocks_to_pattern bs =
  concat (map block_pattern bs)

(** val faulun_blocks : block list **)

let faulun_blocks =
  BlkWatadMajmu::(BlkSababKhafif::[])

(** val failun_blocks : block list **)

let failun_blocks =
  BlkWatadMafruq::(BlkSababKhafif::[])

(** val mafailun_blocks : block list **)

let mafailun_blocks =
  BlkWatadMajmu::(BlkSababKhafif::(BlkSababKhafif::[]))

(** val mustafilun_blocks : block list **)

let mustafilun_blocks =
  BlkSababKhafif::(BlkSababKhafif::(BlkWatadMajmu::[]))

(** val failatun_blocks : block list **)

let failatun_blocks =
  BlkWatadMafruq::(BlkSababKhafif::(BlkSababKhafif::[]))

(** val mafulatu_blocks : block list **)

let mafulatu_blocks =
  BlkSababKhafif::(BlkSababKhafif::(BlkWatadMafruq::[]))

(** val mutafailun_blocks : block list **)

let mutafailun_blocks =
  BlkSababThaqil::(BlkSababKhafif::(BlkWatadMajmu::[]))

(** val mufaalatun_blocks : block list **)

let mufaalatun_blocks =
  BlkWatadMajmu::(BlkSababThaqil::(BlkSababKhafif::[]))

(** val foot_blocks : foot -> block list **)

let foot_blocks = function
| Faulun -> faulun_blocks
| Failun -> failun_blocks
| Mafailun -> mafailun_blocks
| Mustafilun -> mustafilun_blocks
| Failatun -> failatun_blocks
| Mafulatu -> mafulatu_blocks
| Mutafailun -> mutafailun_blocks
| Mufaalatun -> mufaalatun_blocks

(** val block_list_eqb : block list -> block list -> bool **)

let rec block_list_eqb l1 l2 =
  match l1 with
  | [] -> (match l2 with
           | [] -> true
           | _::_ -> false)
  | b1::r1 ->
    (match l2 with
     | [] -> false
     | b2::r2 -> if block_eq_dec b1 b2 then block_list_eqb r1 r2 else false)

(** val is_canonical_decomposition : foot -> block list -> bool **)

let is_canonical_decomposition f bs =
  block_list_eqb bs (foot_blocks f)

(** val foot_length : foot -> int **)

let foot_length f =
  length (foot_pattern f)

(** val is_trisyllabic : foot -> bool **)

let is_trisyllabic f =
  (=) (foot_length f) (succ (succ (succ 0)))

(** val is_quadrisyllabic : foot -> bool **)

let is_quadrisyllabic f =
  (=) (foot_length f) (succ (succ (succ (succ 0))))

(** val is_pentasyllabic : foot -> bool **)

let is_pentasyllabic f =
  (=) (foot_length f) (succ (succ (succ (succ (succ 0)))))

(** val pattern_to_foot : pattern -> foot option **)

let pattern_to_foot p =
  if pattern_eqb p faulun
  then Some Faulun
  else if pattern_eqb p failun
       then Some Failun
       else if pattern_eqb p mafailun
            then Some Mafailun
            else if pattern_eqb p mustafilun
                 then Some Mustafilun
                 else if pattern_eqb p failatun
                      then Some Failatun
                      else if pattern_eqb p mafulatu
                           then Some Mafulatu
                           else if pattern_eqb p mutafailun
                                then Some Mutafailun
                                else if pattern_eqb p mufaalatun
                                     then Some Mufaalatun
                                     else None

(** val all_patterns : int -> pattern list **)

let rec all_patterns n =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> []::[])
    (fun n' ->
    let ps = all_patterns n' in
    app (map (fun x -> Short::x) ps) (map (fun x -> Long::x) ps))
    n

(** val foot_length_patterns : pattern list **)

let foot_length_patterns =
  app (all_patterns (succ (succ (succ 0))))
    (app (all_patterns (succ (succ (succ (succ 0)))))
      (all_patterns (succ (succ (succ (succ (succ 0)))))))

(** val meter_feet : meter -> foot list **)

let meter_feet = function
| Tawil -> Faulun::(Mafailun::(Faulun::(Mafailun::[])))
| Madid -> Failatun::(Failun::(Failatun::[]))
| Basit -> Mustafilun::(Failun::(Mustafilun::(Failun::[])))
| Wafir -> Mufaalatun::(Mufaalatun::(Faulun::[]))
| Kamil -> Mutafailun::(Mutafailun::(Mutafailun::[]))
| Hazaj -> Mafailun::(Mafailun::[])
| Rajaz -> Mustafilun::(Mustafilun::(Mustafilun::[]))
| Ramal -> Failatun::(Failatun::(Failatun::[]))
| Sari -> Mustafilun::(Mustafilun::(Mafulatu::[]))
| Munsarih -> Mustafilun::(Mafulatu::(Mustafilun::[]))
| Khafif -> Failatun::(Mustafilun::(Failatun::[]))
| Mudari -> Mafailun::(Failatun::[])
| Muqtadab -> Mafulatu::(Mustafilun::[])
| Mujtathth -> Mustafilun::(Failatun::[])
| Mutaqarib -> Faulun::(Faulun::(Faulun::(Faulun::[])))
| Mutadarik -> Failun::(Failun::(Failun::(Failun::[])))

(** val meter_pattern : meter -> pattern **)

let meter_pattern m =
  concat (map foot_pattern (meter_feet m))

(** val meter_eq_dec : meter -> meter -> bool **)

let meter_eq_dec m1 m2 =
  match m1 with
  | Tawil -> (match m2 with
              | Tawil -> true
              | _ -> false)
  | Madid -> (match m2 with
              | Madid -> true
              | _ -> false)
  | Basit -> (match m2 with
              | Basit -> true
              | _ -> false)
  | Wafir -> (match m2 with
              | Wafir -> true
              | _ -> false)
  | Kamil -> (match m2 with
              | Kamil -> true
              | _ -> false)
  | Hazaj -> (match m2 with
              | Hazaj -> true
              | _ -> false)
  | Rajaz -> (match m2 with
              | Rajaz -> true
              | _ -> false)
  | Ramal -> (match m2 with
              | Ramal -> true
              | _ -> false)
  | Sari -> (match m2 with
             | Sari -> true
             | _ -> false)
  | Munsarih -> (match m2 with
                 | Munsarih -> true
                 | _ -> false)
  | Khafif -> (match m2 with
               | Khafif -> true
               | _ -> false)
  | Mudari -> (match m2 with
               | Mudari -> true
               | _ -> false)
  | Muqtadab -> (match m2 with
                 | Muqtadab -> true
                 | _ -> false)
  | Mujtathth -> (match m2 with
                  | Mujtathth -> true
                  | _ -> false)
  | Mutaqarib -> (match m2 with
                  | Mutaqarib -> true
                  | _ -> false)
  | Mutadarik -> (match m2 with
                  | Mutadarik -> true
                  | _ -> false)

(** val all_meters : meter list **)

let all_meters =
  Tawil::(Madid::(Basit::(Wafir::(Kamil::(Hazaj::(Rajaz::(Ramal::(Sari::(Munsarih::(Khafif::(Mudari::(Muqtadab::(Mujtathth::(Mutaqarib::(Mutadarik::[])))))))))))))))

(** val meter_syllable_count : meter -> int **)

let meter_syllable_count m =
  length (meter_pattern m)

(** val meter_foot_count : meter -> int **)

let meter_foot_count m =
  length (meter_feet m)

(** val is_dimeter : meter -> bool **)

let is_dimeter m =
  (=) (meter_foot_count m) (succ (succ 0))

(** val is_trimeter : meter -> bool **)

let is_trimeter m =
  (=) (meter_foot_count m) (succ (succ (succ 0)))

(** val is_tetrameter : meter -> bool **)

let is_tetrameter m =
  (=) (meter_foot_count m) (succ (succ (succ (succ 0))))

(** val pattern_to_meter : pattern -> meter option **)

let pattern_to_meter p =
  if pattern_eqb p (meter_pattern Tawil)
  then Some Tawil
  else if pattern_eqb p (meter_pattern Madid)
       then Some Madid
       else if pattern_eqb p (meter_pattern Basit)
            then Some Basit
            else if pattern_eqb p (meter_pattern Wafir)
                 then Some Wafir
                 else if pattern_eqb p (meter_pattern Kamil)
                      then Some Kamil
                      else if pattern_eqb p (meter_pattern Hazaj)
                           then Some Hazaj
                           else if pattern_eqb p (meter_pattern Rajaz)
                                then Some Rajaz
                                else if pattern_eqb p (meter_pattern Ramal)
                                     then Some Ramal
                                     else if pattern_eqb p
                                               (meter_pattern Sari)
                                          then Some Sari
                                          else if pattern_eqb p
                                                    (meter_pattern Munsarih)
                                               then Some Munsarih
                                               else if pattern_eqb p
                                                         (meter_pattern
                                                           Khafif)
                                                    then Some Khafif
                                                    else if pattern_eqb p
                                                              (meter_pattern
                                                                Mudari)
                                                         then Some Mudari
                                                         else if pattern_eqb
                                                                   p
                                                                   (meter_pattern
                                                                    Muqtadab)
                                                              then Some
                                                                    Muqtadab
                                                              else if 
                                                                    pattern_eqb
                                                                    p
                                                                    (meter_pattern
                                                                    Mujtathth)
                                                                   then 
                                                                    Some
                                                                    Mujtathth
                                                                   else 
                                                                    if 
                                                                    pattern_eqb
                                                                    p
                                                                    (meter_pattern
                                                                    Mutaqarib)
                                                                    then 
                                                                    Some
                                                                    Mutaqarib
                                                                    else 
                                                                    if 
                                                                    pattern_eqb
                                                                    p
                                                                    (meter_pattern
                                                                    Mutadarik)
                                                                    then 
                                                                    Some
                                                                    Mutadarik
                                                                    else None

(** val khalil_original : meter list **)

let khalil_original =
  Tawil::(Madid::(Basit::(Wafir::(Kamil::(Hazaj::(Rajaz::(Ramal::(Sari::(Munsarih::(Khafif::(Mudari::(Muqtadab::(Mujtathth::(Mutaqarib::[]))))))))))))))

(** val is_khalil_original : meter -> bool **)

let is_khalil_original = function
| Mutadarik -> false
| _ -> true

(** val meter_circle : meter -> circle **)

let meter_circle = function
| Tawil -> Mukhtalifa
| Madid -> Mukhtalifa
| Basit -> Mukhtalifa
| Wafir -> Mualifa
| Kamil -> Mualifa
| Hazaj -> Mujtallaba
| Rajaz -> Mujtallaba
| Ramal -> Mujtallaba
| Mutaqarib -> Muttafiqa
| Mutadarik -> Muttafiqa
| _ -> Mushtabaha

(** val circle_meters : circle -> meter list **)

let circle_meters = function
| Mukhtalifa -> Tawil::(Madid::(Basit::[]))
| Mualifa -> Wafir::(Kamil::[])
| Mujtallaba -> Hazaj::(Rajaz::(Ramal::[]))
| Mushtabaha ->
  Sari::(Munsarih::(Khafif::(Mudari::(Muqtadab::(Mujtathth::[])))))
| Muttafiqa -> Mutaqarib::(Mutadarik::[])

(** val all_circles : circle list **)

let all_circles =
  Mukhtalifa::(Mualifa::(Mujtallaba::(Mushtabaha::(Muttafiqa::[]))))

(** val is_in_circle : meter -> circle -> bool **)

let is_in_circle m c =
  existsb (fun m' -> if meter_eq_dec m m' then true else false)
    (circle_meters c)

(** val rotate : int -> pattern -> pattern **)

let rotate n p = match p with
| [] -> []
| _::_ ->
  app (skipn (Nat.modulo n (length p)) p) (firstn (Nat.modulo n (length p)) p)

(** val zihaf_eq_dec : zihaf -> zihaf -> bool **)

let zihaf_eq_dec z1 z2 =
  match z1 with
  | Khabn -> (match z2 with
              | Khabn -> true
              | _ -> false)
  | Tayy -> (match z2 with
             | Tayy -> true
             | _ -> false)
  | Qabd -> (match z2 with
             | Qabd -> true
             | _ -> false)
  | Kaff -> (match z2 with
             | Kaff -> true
             | _ -> false)
  | Waqs -> (match z2 with
             | Waqs -> true
             | _ -> false)
  | Asb -> (match z2 with
            | Asb -> true
            | _ -> false)
  | Idmar -> (match z2 with
              | Idmar -> true
              | _ -> false)
  | Aql -> (match z2 with
            | Aql -> true
            | _ -> false)
  | Shamm -> (match z2 with
              | Shamm -> true
              | _ -> false)

(** val _UU02bf_illa_eq_dec : illa -> illa -> bool **)

let _UU02bf_illa_eq_dec i1 i2 =
  match i1 with
  | Qat -> (match i2 with
            | Qat -> true
            | _ -> false)
  | Qasr -> (match i2 with
             | Qasr -> true
             | _ -> false)
  | Hadhf -> (match i2 with
              | Hadhf -> true
              | _ -> false)
  | Tasbigh -> (match i2 with
                | Tasbigh -> true
                | _ -> false)
  | Batr -> (match i2 with
             | Batr -> true
             | _ -> false)
  | Qatf -> (match i2 with
             | Qatf -> true
             | _ -> false)
  | Tarfil -> (match i2 with
               | Tarfil -> true
               | _ -> false)
  | Tadhyil -> (match i2 with
                | Tadhyil -> true
                | _ -> false)
  | Hadhadh -> (match i2 with
                | Hadhadh -> true
                | _ -> false)
  | Salm -> (match i2 with
             | Salm -> true
             | _ -> false)
  | Kashf -> (match i2 with
              | Kashf -> true
              | _ -> false)
  | Waqf -> (match i2 with
             | Waqf -> true
             | _ -> false)
  | Tashith -> (match i2 with
                | Tashith -> true
                | _ -> false)

(** val apply_khabn : pattern -> pattern option **)

let apply_khabn p =
  let ls = pattern_to_letters p in
  (match nth_error ls (succ 0) with
   | Some l ->
     (match l with
      | Mutaharrik -> None
      | Sakin -> letters_to_pattern (delete_at (succ 0) ls))
   | None -> None)

(** val apply_tayy : pattern -> pattern option **)

let apply_tayy p =
  let ls = pattern_to_letters p in
  (match nth_error ls (succ (succ (succ 0))) with
   | Some l ->
     (match l with
      | Mutaharrik -> None
      | Sakin -> letters_to_pattern (delete_at (succ (succ (succ 0))) ls))
   | None -> None)

(** val apply_qab_UU1e0d_ : pattern -> pattern option **)

let apply_qab_UU1e0d_ p =
  let ls = pattern_to_letters p in
  (match nth_error ls (succ (succ (succ (succ 0)))) with
   | Some l ->
     (match l with
      | Mutaharrik -> None
      | Sakin ->
        letters_to_pattern (delete_at (succ (succ (succ (succ 0)))) ls))
   | None -> None)

(** val apply_kaff : pattern -> pattern option **)

let apply_kaff p =
  let ls = pattern_to_letters p in
  (match nth_error ls (succ (succ (succ (succ (succ (succ 0)))))) with
   | Some l ->
     (match l with
      | Mutaharrik -> None
      | Sakin ->
        letters_to_pattern
          (delete_at (succ (succ (succ (succ (succ (succ 0)))))) ls))
   | None -> None)

(** val apply_waq_UU1e63_ : pattern -> pattern option **)

let apply_waq_UU1e63_ p =
  let ls = pattern_to_letters p in
  (match nth_error ls (succ 0) with
   | Some l ->
     (match l with
      | Mutaharrik -> letters_to_pattern (delete_at (succ 0) ls)
      | Sakin -> None)
   | None -> None)

(** val apply__UU02bf_a_UU1e63_b : pattern -> pattern option **)

let apply__UU02bf_a_UU1e63_b p =
  let ls = pattern_to_letters p in
  (match nth_error ls (succ (succ (succ (succ 0)))) with
   | Some l ->
     (match l with
      | Mutaharrik ->
        letters_to_pattern (replace_at (succ (succ (succ (succ 0)))) Sakin ls)
      | Sakin -> None)
   | None -> None)

(** val apply_qa_UU1e63_r : pattern -> pattern option **)

let rec apply_qa_UU1e63_r = function
| [] -> None
| w::rest ->
  (match w with
   | Short ->
     (match rest with
      | [] -> None
      | _::_ ->
        (match apply_qa_UU1e63_r rest with
         | Some rest' -> Some (w::rest')
         | None -> None))
   | Long ->
     (match rest with
      | [] -> Some (Short::[])
      | _::_ ->
        (match apply_qa_UU1e63_r rest with
         | Some rest' -> Some (w::rest')
         | None -> None))
   | SuperLong ->
     (match apply_qa_UU1e63_r rest with
      | Some rest' -> Some (w::rest')
      | None -> None))

(** val apply__UU1e25_adhf : pattern -> pattern option **)

let rec apply__UU1e25_adhf = function
| [] -> None
| w::rest ->
  (match rest with
   | [] -> Some []
   | _::_ ->
     (match apply__UU1e25_adhf rest with
      | Some rest' -> Some (w::rest')
      | None -> None))

(** val apply_qa_UU1e6d__UU02bf_ : pattern -> pattern option **)

let rec apply_qa_UU1e6d__UU02bf_ = function
| [] -> None
| w::rest ->
  (match rest with
   | [] -> None
   | _::l ->
     (match l with
      | [] -> Some (Long::[])
      | _::_ ->
        (match apply_qa_UU1e6d__UU02bf_ rest with
         | Some rest' -> Some (w::rest')
         | None -> None)))

(** val apply_tasb_UU012b_gh : pattern -> pattern option **)

let rec apply_tasb_UU012b_gh = function
| [] -> None
| w::rest ->
  (match w with
   | Short ->
     (match rest with
      | [] -> Some (Long::[])
      | _::_ ->
        (match apply_tasb_UU012b_gh rest with
         | Some rest' -> Some (w::rest')
         | None -> None))
   | Long ->
     (match rest with
      | [] -> None
      | _::_ ->
        (match apply_tasb_UU012b_gh rest with
         | Some rest' -> Some (w::rest')
         | None -> None))
   | SuperLong ->
     (match apply_tasb_UU012b_gh rest with
      | Some rest' -> Some (w::rest')
      | None -> None))

(** val apply_batr : pattern -> pattern option **)

let apply_batr p =
  match apply__UU1e25_adhf p with
  | Some p' -> apply_qa_UU1e6d__UU02bf_ p'
  | None -> None

(** val apply_qa_UU1e6d_f : pattern -> pattern option **)

let apply_qa_UU1e6d_f p =
  match apply__UU02bf_a_UU1e63_b p with
  | Some p' -> apply__UU1e25_adhf p'
  | None -> None

(** val last_two : pattern -> (weight * weight) option **)

let rec last_two = function
| [] -> None
| a::rest ->
  (match rest with
   | [] -> None
   | b::l -> (match l with
              | [] -> Some (a,b)
              | _::_ -> last_two rest))

(** val ends_with_watad_majmu : pattern -> bool **)

let ends_with_watad_majmu p =
  match last_two p with
  | Some p0 ->
    let w,w0 = p0 in
    (match w with
     | Short -> (match w0 with
                 | Long -> true
                 | _ -> false)
     | _ -> false)
  | None -> false

(** val ends_with_watad_mafruq : pattern -> bool **)

let ends_with_watad_mafruq p =
  match last_two p with
  | Some p0 ->
    let w,w0 = p0 in
    (match w with
     | Long -> (match w0 with
                | Short -> true
                | _ -> false)
     | _ -> false)
  | None -> false

(** val apply_tarf_UU012b_l : pattern -> pattern option **)

let apply_tarf_UU012b_l p =
  if ends_with_watad_majmu p then Some (app p (Long::[])) else None

(** val apply_tadhy_UU012b_l : pattern -> pattern option **)

let apply_tadhy_UU012b_l p =
  if ends_with_watad_majmu p then Some (app p (SuperLong::[])) else None

(** val drop_last_n : int -> pattern -> pattern option **)

let rec drop_last_n n p =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> Some p)
    (fun n' ->
    match apply__UU1e25_adhf p with
    | Some p' -> drop_last_n n' p'
    | None -> None)
    n

(** val apply__UU1e25_adh_UU0101_dh : pattern -> pattern option **)

let apply__UU1e25_adh_UU0101_dh p =
  if ends_with_watad_majmu p then drop_last_n (succ (succ 0)) p else None

(** val apply__UU1e63_alm : pattern -> pattern option **)

let apply__UU1e63_alm p =
  if ends_with_watad_mafruq p then drop_last_n (succ (succ 0)) p else None

(** val apply_kashf : pattern -> pattern option **)

let apply_kashf =
  apply__UU1e25_adhf

(** val ends_with : pattern -> weight -> bool **)

let rec ends_with p w =
  match p with
  | [] -> false
  | x::rest ->
    (match rest with
     | [] -> weight_eqb x w
     | _::_ -> ends_with rest w)

(** val apply__UU1e25_adhf_guarded : pattern -> pattern option **)

let apply__UU1e25_adhf_guarded p =
  if ends_with p Long then apply__UU1e25_adhf p else None

(** val apply_qa_UU1e6d__UU02bf__guarded : pattern -> pattern option **)

let apply_qa_UU1e6d__UU02bf__guarded p =
  if ends_with_watad_majmu p then apply_qa_UU1e6d__UU02bf_ p else None

(** val apply_kashf_guarded : pattern -> pattern option **)

let apply_kashf_guarded p =
  if ends_with_watad_mafruq p then apply__UU1e25_adhf p else None

(** val apply_waqf : pattern -> pattern option **)

let rec apply_waqf = function
| [] -> None
| w::rest ->
  (match w with
   | Short ->
     (match rest with
      | [] -> Some (Long::[])
      | _::_ ->
        (match apply_waqf rest with
         | Some rest' -> Some (w::rest')
         | None -> None))
   | Long ->
     (match rest with
      | [] -> None
      | _::_ ->
        (match apply_waqf rest with
         | Some rest' -> Some (w::rest')
         | None -> None))
   | SuperLong ->
     (match apply_waqf rest with
      | Some rest' -> Some (w::rest')
      | None -> None))

(** val apply_tash_UU02bf__UU012b_th : pattern -> pattern option **)

let apply_tash_UU02bf__UU012b_th = function
| [] -> None
| w1::l ->
  (match l with
   | [] -> None
   | w::l0 ->
     (match w with
      | Short ->
        (match l0 with
         | [] -> None
         | w0::rest ->
           (match w0 with
            | Long -> Some (w1::(Long::rest))
            | _ -> None))
      | _ -> None))

(** val apply_i_UU1e0d_m_UU0101_r : pattern -> pattern option **)

let apply_i_UU1e0d_m_UU0101_r p =
  let ls = pattern_to_letters p in
  (match nth_error ls (succ 0) with
   | Some l ->
     (match l with
      | Mutaharrik -> letters_to_pattern (replace_at (succ 0) Sakin ls)
      | Sakin -> None)
   | None -> None)

(** val apply_shamm : pattern -> pattern option **)

let apply_shamm p =
  let ls = pattern_to_letters p in
  (match nth_error ls (succ 0) with
   | Some l ->
     (match l with
      | Mutaharrik -> letters_to_pattern (replace_at (succ 0) Sakin ls)
      | Sakin -> None)
   | None -> None)

(** val apply__UU02bf_aql : pattern -> pattern option **)

let apply__UU02bf_aql p =
  let ls = pattern_to_letters p in
  (match nth_error ls (succ (succ (succ (succ 0)))) with
   | Some l ->
     (match l with
      | Mutaharrik ->
        letters_to_pattern (delete_at (succ (succ (succ (succ 0)))) ls)
      | Sakin -> None)
   | None -> None)

(** val compound_zihaf_eq_dec : compound_zihaf -> compound_zihaf -> bool **)

let compound_zihaf_eq_dec z1 z2 =
  match z1 with
  | Khazl -> (match z2 with
              | Khazl -> true
              | _ -> false)
  | Khabl -> (match z2 with
              | Khabl -> true
              | _ -> false)
  | Shakl -> (match z2 with
              | Shakl -> true
              | _ -> false)
  | Naqs -> (match z2 with
             | Naqs -> true
             | _ -> false)

(** val apply_khazl : pattern -> pattern option **)

let apply_khazl p =
  match apply_i_UU1e0d_m_UU0101_r p with
  | Some p' -> apply_tayy p'
  | None -> None

(** val apply_khabl : pattern -> pattern option **)

let apply_khabl p =
  let ls = pattern_to_letters p in
  (match nth_error ls (succ 0) with
   | Some l ->
     (match l with
      | Mutaharrik -> None
      | Sakin ->
        (match nth_error ls (succ (succ (succ 0))) with
         | Some l0 ->
           (match l0 with
            | Mutaharrik -> None
            | Sakin ->
              letters_to_pattern
                (delete_at (succ 0) (delete_at (succ (succ (succ 0))) ls)))
         | None -> None))
   | None -> None)

(** val apply_shakl : pattern -> pattern option **)

let apply_shakl p =
  let ls = pattern_to_letters p in
  (match nth_error ls (succ 0) with
   | Some l ->
     (match l with
      | Mutaharrik -> None
      | Sakin ->
        (match nth_error ls (succ (succ (succ (succ (succ (succ 0)))))) with
         | Some l0 ->
           (match l0 with
            | Mutaharrik -> None
            | Sakin ->
              letters_to_pattern
                (delete_at (succ 0)
                  (delete_at (succ (succ (succ (succ (succ (succ 0)))))) ls)))
         | None -> None))
   | None -> None)

(** val apply_naqs : pattern -> pattern option **)

let apply_naqs p =
  match apply__UU02bf_a_UU1e63_b p with
  | Some p' -> apply_kaff p'
  | None -> None

(** val all_compound_zihaf : compound_zihaf list **)

let all_compound_zihaf =
  Khazl::(Khabl::(Shakl::(Naqs::[])))

(** val all_zihaf : zihaf list **)

let all_zihaf =
  Khabn::(Tayy::(Qabd::(Kaff::(Waqs::(Asb::(Idmar::(Aql::(Shamm::[]))))))))

(** val all__UU02bf_illa : illa list **)

let all__UU02bf_illa =
  Qat::(Qasr::(Hadhf::(Tasbigh::(Batr::(Qatf::(Tarfil::(Tadhyil::(Hadhadh::(Salm::(Kashf::(Waqf::(Tashith::[]))))))))))))

(** val zihaf_applies_to : zihaf -> foot -> bool **)

let zihaf_applies_to z f =
  match match z with
        | Khabn -> apply_khabn (foot_pattern f)
        | Tayy -> apply_tayy (foot_pattern f)
        | Qabd -> apply_qab_UU1e0d_ (foot_pattern f)
        | Kaff -> apply_kaff (foot_pattern f)
        | Waqs -> apply_waq_UU1e63_ (foot_pattern f)
        | Asb -> apply__UU02bf_a_UU1e63_b (foot_pattern f)
        | Idmar -> apply_i_UU1e0d_m_UU0101_r (foot_pattern f)
        | Aql -> apply__UU02bf_aql (foot_pattern f)
        | Shamm -> apply_shamm (foot_pattern f) with
  | Some _ -> true
  | None -> false

(** val apply_zihaf : zihaf -> pattern -> pattern option **)

let apply_zihaf = function
| Khabn -> apply_khabn
| Tayy -> apply_tayy
| Qabd -> apply_qab_UU1e0d_
| Kaff -> apply_kaff
| Waqs -> apply_waq_UU1e63_
| Asb -> apply__UU02bf_a_UU1e63_b
| Idmar -> apply_i_UU1e0d_m_UU0101_r
| Aql -> apply__UU02bf_aql
| Shamm -> apply_shamm

(** val apply_compound_zihaf : compound_zihaf -> pattern -> pattern option **)

let apply_compound_zihaf = function
| Khazl -> apply_khazl
| Khabl -> apply_khabl
| Shakl -> apply_shakl
| Naqs -> apply_naqs

(** val apply__UU02bf_illa : illa -> pattern -> pattern option **)

let apply__UU02bf_illa = function
| Qat -> apply_qa_UU1e6d__UU02bf__guarded
| Qasr -> apply_qa_UU1e63_r
| Hadhf -> apply__UU1e25_adhf_guarded
| Tasbigh -> apply_tasb_UU012b_gh
| Batr -> apply_batr
| Qatf -> apply_qa_UU1e6d_f
| Tarfil -> apply_tarf_UU012b_l
| Tadhyil -> apply_tadhy_UU012b_l
| Hadhadh -> apply__UU1e25_adh_UU0101_dh
| Salm -> apply__UU1e63_alm
| Kashf -> apply_kashf_guarded
| Waqf -> apply_waqf
| Tashith -> apply_tash_UU02bf__UU012b_th

(** val assign_positions_aux :
    foot list -> foot_position -> (foot * foot_position) list **)

let rec assign_positions_aux fs terminal =
  match fs with
  | [] -> []
  | f::rest ->
    (match rest with
     | [] -> (f,terminal)::[]
     | _::_ -> (f,Hashw)::(assign_positions_aux rest terminal))

(** val assign_sadr_positions : meter -> (foot * foot_position) list **)

let assign_sadr_positions m =
  assign_positions_aux (meter_feet m) Arud

(** val assign_ajuz_positions : meter -> (foot * foot_position) list **)

let assign_ajuz_positions m =
  assign_positions_aux (meter_feet m) Darb

(** val zihaf_permitted : foot_position -> bool **)

let zihaf_permitted = function
| Hashw -> true
| _ -> false

(** val _UU02bf_illa_permitted : foot_position -> bool **)

let _UU02bf_illa_permitted = function
| Hashw -> false
| _ -> true

(** val zihaf_eqb : zihaf -> zihaf -> bool **)

let zihaf_eqb z1 z2 =
  if zihaf_eq_dec z1 z2 then true else false

(** val compound_zihaf_eqb : compound_zihaf -> compound_zihaf -> bool **)

let compound_zihaf_eqb z1 z2 =
  if compound_zihaf_eq_dec z1 z2 then true else false

(** val _UU02bf_illa_eqb : illa -> illa -> bool **)

let _UU02bf_illa_eqb i1 i2 =
  if _UU02bf_illa_eq_dec i1 i2 then true else false

(** val foot_permitted_zihaf : foot -> zihaf list **)

let foot_permitted_zihaf = function
| Faulun -> Qabd::[]
| Failun -> Khabn::(Qabd::[])
| Mafailun -> Qabd::(Kaff::[])
| Failatun -> Khabn::(Kaff::[])
| Mutafailun -> Idmar::(Waqs::(Shamm::[]))
| Mufaalatun -> Asb::(Aql::[])
| _ -> Khabn::(Tayy::[])

(** val foot_permitted_compound : foot -> compound_zihaf list **)

let foot_permitted_compound = function
| Mustafilun -> Khabl::[]
| Failatun -> Shakl::[]
| Mutafailun -> Khazl::[]
| Mufaalatun -> Naqs::[]
| _ -> []

(** val is_legal_zihaf_for_foot : zihaf -> foot -> bool **)

let is_legal_zihaf_for_foot z f =
  existsb (zihaf_eqb z) (foot_permitted_zihaf f)

(** val is_legal_compound_for_foot : compound_zihaf -> foot -> bool **)

let is_legal_compound_for_foot z f =
  existsb (compound_zihaf_eqb z) (foot_permitted_compound f)

(** val is_legal_zihaf_at : meter -> int -> zihaf -> bool **)

let is_legal_zihaf_at m pos z =
  match nth_error (meter_feet m) pos with
  | Some f -> is_legal_zihaf_for_foot z f
  | None -> false

(** val is_legal_compound_at : meter -> int -> compound_zihaf -> bool **)

let is_legal_compound_at m pos z =
  match nth_error (meter_feet m) pos with
  | Some f -> is_legal_compound_for_foot z f
  | None -> false

(** val compound_zihaf_applies_to : compound_zihaf -> foot -> bool **)

let compound_zihaf_applies_to z f =
  match apply_compound_zihaf z (foot_pattern f) with
  | Some _ -> true
  | None -> false

(** val permitted_arud_illa : meter -> illa list **)

let permitted_arud_illa = function
| Tawil -> Hadhf::(Qasr::[])
| Madid -> Hadhf::[]
| Wafir -> Qatf::[]
| Hazaj -> Hadhf::[]
| Ramal -> Hadhf::[]
| Sari -> Kashf::[]
| Mutaqarib -> Hadhf::[]
| _ -> []

(** val permitted_darb_illa : meter -> illa list **)

let permitted_darb_illa = function
| Tawil -> Hadhf::(Qasr::(Qat::[]))
| Madid -> Hadhf::(Qasr::(Qat::(Batr::[])))
| Wafir -> Qatf::(Hadhf::[])
| Kamil -> Qat::(Hadhadh::[])
| Hazaj -> Hadhf::(Qasr::[])
| Ramal -> Hadhf::(Qasr::(Qat::(Tasbigh::[])))
| Sari -> Kashf::(Waqf::(Salm::[]))
| Khafif -> Qasr::(Qat::(Tasbigh::[]))
| Mudari -> Qasr::[]
| Mujtathth -> Qasr::(Qat::[])
| Mutaqarib -> Hadhf::(Qasr::(Qat::(Batr::[])))
| Mutadarik -> Qat::(Tashith::[])
| _ -> Qat::[]

(** val is_legal_arud_illa : meter -> illa -> bool **)

let is_legal_arud_illa m i =
  existsb (_UU02bf_illa_eqb i) (permitted_arud_illa m)

(** val is_legal_darb_illa : meter -> illa -> bool **)

let is_legal_darb_illa m i =
  existsb (_UU02bf_illa_eqb i) (permitted_darb_illa m)

(** val meter_hashw_zihaf : meter -> foot -> zihaf list **)

let meter_hashw_zihaf m f =
  match m with
  | Tawil -> (match f with
              | Mafailun -> Qabd::[]
              | _ -> foot_permitted_zihaf f)
  | Madid ->
    (match f with
     | Failatun -> Khabn::[]
     | _ -> foot_permitted_zihaf f)
  | Basit ->
    (match f with
     | Mustafilun -> Khabn::[]
     | _ -> foot_permitted_zihaf f)
  | Wafir ->
    (match f with
     | Mufaalatun -> Asb::[]
     | _ -> foot_permitted_zihaf f)
  | Kamil ->
    (match f with
     | Mutafailun -> Idmar::(Shamm::[])
     | _ -> foot_permitted_zihaf f)
  | Khafif ->
    (match f with
     | Failatun -> Khabn::[]
     | _ -> foot_permitted_zihaf f)
  | _ -> foot_permitted_zihaf f

(** val is_legal_zihaf_at_strict : meter -> int -> zihaf -> bool **)

let is_legal_zihaf_at_strict m pos z =
  match nth_error (meter_feet m) pos with
  | Some f -> existsb (zihaf_eqb z) (meter_hashw_zihaf m f)
  | None -> false

(** val scan_exact : pattern -> scan_result **)

let scan_exact p =
  match pattern_to_meter p with
  | Some m -> ScanSuccess m
  | None -> ScanFailed

type annotated_variant = pattern * foot_annotation

(** val foot_hashw_variants : foot -> annotated_variant list **)

let foot_hashw_variants f =
  ((foot_pattern f),Canonical)::(app
                                  (flat_map (fun z ->
                                    match apply_zihaf z (foot_pattern f) with
                                    | Some p -> (p,(SimpleZihaf z))::[]
                                    | None -> []) (foot_permitted_zihaf f))
                                  (flat_map (fun z ->
                                    match apply_compound_zihaf z
                                            (foot_pattern f) with
                                    | Some p -> (p,(CompoundZihaf z))::[]
                                    | None -> []) (foot_permitted_compound f)))

(** val foot_terminal_variants : meter -> annotated_variant list **)

let foot_terminal_variants m =
  let f = last (meter_feet m) Faulun in
  ((foot_pattern f),Canonical)::(app
                                  (flat_map (fun z ->
                                    match apply_zihaf z (foot_pattern f) with
                                    | Some p -> (p,(SimpleZihaf z))::[]
                                    | None -> []) (foot_permitted_zihaf f))
                                  (app
                                    (flat_map (fun z ->
                                      match apply_compound_zihaf z
                                              (foot_pattern f) with
                                      | Some p -> (p,(CompoundZihaf z))::[]
                                      | None -> [])
                                      (foot_permitted_compound f))
                                    (flat_map (fun i ->
                                      match apply__UU02bf_illa i
                                              (foot_pattern f) with
                                      | Some p -> (p,(Illa i))::[]
                                      | None -> [])
                                      (app (permitted_arud_illa m)
                                        (permitted_darb_illa m)))))

(** val meter_foot_variants : meter -> annotated_variant list list **)

let meter_foot_variants m =
  let feet = meter_feet m in
  let init = removelast feet in
  app (map foot_hashw_variants init) ((foot_terminal_variants m)::[])

(** val match_variant_pattern :
    pattern -> annotated_variant list list -> foot_annotation list option **)

let rec match_variant_pattern p = function
| [] -> (match p with
         | [] -> Some []
         | _::_ -> None)
| vs::rest ->
  let rec try_variants = function
  | [] -> None
  | a::cs ->
    let v,ann = a in
    if pattern_eqb (firstn (length v) p) v
    then (match match_variant_pattern (skipn (length v) p) rest with
          | Some anns -> Some (ann::anns)
          | None -> try_variants cs)
    else try_variants cs
  in try_variants vs

(** val scan : pattern -> scan_result **)

let scan p =
  match pattern_to_meter p with
  | Some m -> ScanSuccess m
  | None ->
    let rec try_meters = function
    | [] -> ScanFailed
    | m::ms' ->
      (match match_variant_pattern p (meter_foot_variants m) with
       | Some anns -> ScanVariant (m, anns)
       | None -> try_meters ms')
    in try_meters all_meters

(** val scan_all : pattern -> (meter * foot_annotation list) list **)

let scan_all p =
  flat_map (fun m ->
    match match_variant_pattern p (meter_foot_variants m) with
    | Some anns -> (m,anns)::[]
    | None -> []) all_meters

(** val is_ambiguous : pattern -> bool **)

let is_ambiguous p =
  Nat.ltb (succ 0) (length (scan_all p))

(** val ambiguity_count : pattern -> int **)

let ambiguity_count p =
  length (scan_all p)

(** val cart_concat : annotated_variant list list -> pattern list **)

let rec cart_concat = function
| [] -> []::[]
| vs::rest ->
  let rps = cart_concat rest in
  flat_map (fun va -> map (fun rp -> app (fst va) rp) rps) vs

(** val meter_variant_patterns : meter -> pattern list **)

let meter_variant_patterns m =
  cart_concat (meter_foot_variants m)

(** val meters_share_variant : meter -> meter -> bool **)

let meters_share_variant m1 m2 =
  existsb (fun p ->
    match match_variant_pattern p (meter_foot_variants m2) with
    | Some _ -> true
    | None -> false) (meter_variant_patterns m1)

(** val overlap_pairs : (meter * meter) list **)

let overlap_pairs =
  filter (fun pair ->
    if meter_eq_dec (fst pair) (snd pair)
    then false
    else meters_share_variant (fst pair) (snd pair))
    (flat_map (fun m1 -> map (fun m2 -> m1,m2) all_meters) all_meters)

(** val is_known_overlap : meter -> meter -> bool **)

let is_known_overlap m1 m2 =
  match m1 with
  | Madid -> (match m2 with
              | Mutadarik -> true
              | _ -> false)
  | Kamil -> (match m2 with
              | Rajaz -> true
              | Mutadarik -> true
              | _ -> false)
  | Hazaj -> (match m2 with
              | Muqtadab -> true
              | _ -> false)
  | Rajaz -> (match m2 with
              | Kamil -> true
              | Sari -> true
              | _ -> false)
  | Sari -> (match m2 with
             | Rajaz -> true
             | _ -> false)
  | Munsarih -> (match m2 with
                 | Mutadarik -> true
                 | _ -> false)
  | Mudari -> (match m2 with
               | Mujtathth -> true
               | _ -> false)
  | Muqtadab -> (match m2 with
                 | Hazaj -> true
                 | _ -> false)
  | Mujtathth -> (match m2 with
                  | Mudari -> true
                  | _ -> false)
  | Mutadarik ->
    (match m2 with
     | Madid -> true
     | Kamil -> true
     | Munsarih -> true
     | _ -> false)
  | _ -> false

(** val is_full_line : pattern -> meter -> bool **)

let is_full_line p m =
  pattern_eqb p (app (meter_pattern m) (meter_pattern m))

(** val is_prefix : pattern -> pattern -> bool **)

let rec is_prefix p1 p2 =
  match p1 with
  | [] -> true
  | w1::p1' ->
    (match p2 with
     | [] -> false
     | w2::p2' -> (&&) (weight_eqb w1 w2) (is_prefix p1' p2'))

(** val candidate_meters : pattern -> meter list **)

let candidate_meters p =
  filter (fun m -> is_prefix p (meter_pattern m)) all_meters

(** val scan_summary : pattern -> meter option **)

let scan_summary =
  pattern_to_meter

type taqtii_segment = pattern * foot_annotation

type taqtii_result = taqtii_segment list

(** val segment_variant_pattern :
    pattern -> annotated_variant list list -> taqtii_result option **)

let rec segment_variant_pattern p = function
| [] -> (match p with
         | [] -> Some []
         | _::_ -> None)
| vs::rest ->
  let rec try_variants = function
  | [] -> None
  | a::cs ->
    let v,ann = a in
    if pattern_eqb (firstn (length v) p) v
    then (match segment_variant_pattern (skipn (length v) p) rest with
          | Some segs -> Some (((firstn (length v) p),ann)::segs)
          | None -> try_variants cs)
    else try_variants cs
  in try_variants vs

(** val taqtii : meter -> pattern -> taqtii_result option **)

let taqtii m p =
  segment_variant_pattern p (meter_foot_variants m)

type rhyme_pattern = rhyme_element list

(** val minimal_rhyme : rhyme_pattern **)

let minimal_rhyme =
  Rawiy::[]

(** val ridf_rhyme : rhyme_pattern **)

let ridf_rhyme =
  Ridf::(Rawiy::[])

(** val wasl_rhyme : rhyme_pattern **)

let wasl_rhyme =
  Rawiy::(Wasl::[])

(** val tasis_rhyme : rhyme_pattern **)

let tasis_rhyme =
  Tasis::(Dakhil::(Rawiy::[]))

(** val all_rhyme_elements : rhyme_element list **)

let all_rhyme_elements =
  Rawiy::(Wasl::(Ridf::(Tasis::(Dakhil::[]))))

(** val count_rawiy : rhyme_pattern -> int **)

let rec count_rawiy = function
| [] -> 0
| r::rest ->
  (match r with
   | Rawiy -> succ (count_rawiy rest)
   | _ -> count_rawiy rest)

(** val is_valid_rhyme : rhyme_pattern -> bool **)

let is_valid_rhyme rp =
  (=) (count_rawiy rp) (succ 0)

(** val rawiy_before_wasl : rhyme_pattern -> bool **)

let rec rawiy_before_wasl = function
| [] -> true
| r::rest ->
  (match r with
   | Rawiy -> true
   | Wasl -> false
   | _ -> rawiy_before_wasl rest)

(** val tasis_before_dakhil : rhyme_pattern -> bool **)

let rec tasis_before_dakhil = function
| [] -> true
| r::rest ->
  (match r with
   | Tasis -> true
   | Dakhil -> false
   | _ -> tasis_before_dakhil rest)

(** val ridf_adjacent_rawiy : rhyme_pattern -> bool **)

let rec ridf_adjacent_rawiy = function
| [] -> true
| r::rest ->
  (match r with
   | Ridf ->
     (match rest with
      | [] -> false
      | r0::rest0 ->
        (match r0 with
         | Rawiy -> ridf_adjacent_rawiy rest0
         | _ -> false))
   | _ -> ridf_adjacent_rawiy rest)

(** val is_well_formed_rhyme : rhyme_pattern -> bool **)

let is_well_formed_rhyme rp =
  (&&)
    ((&&) ((&&) (is_valid_rhyme rp) (rawiy_before_wasl rp))
      (tasis_before_dakhil rp)) (ridf_adjacent_rawiy rp)

type hemistich = pattern

type bayt = { sadr : hemistich; ajuz : hemistich }

type poem = bayt list

(** val is_valid_hemistich : hemistich -> meter -> bool **)

let is_valid_hemistich h m =
  match match_variant_pattern h (meter_foot_variants m) with
  | Some _ -> true
  | None -> false

(** val is_valid_bayt : bayt -> meter -> bool **)

let is_valid_bayt b m =
  (&&) (is_valid_hemistich b.sadr m) (is_valid_hemistich b.ajuz m)

(** val is_valid_poem : poem -> meter -> bool **)

let is_valid_poem p m =
  match p with
  | [] -> false
  | _::_ -> forallb (fun b -> is_valid_bayt b m) p

(** val haraka_eqb : haraka -> haraka -> bool **)

let haraka_eqb h1 h2 =
  match h1 with
  | Damma -> (match h2 with
              | Damma -> true
              | _ -> false)
  | Fatha -> (match h2 with
              | Fatha -> true
              | _ -> false)
  | Kasra -> (match h2 with
              | Kasra -> true
              | _ -> false)

type rhyme_id = { ri_rawiy : int; ri_majra : haraka }

(** val rhyme_id_eqb : rhyme_id -> rhyme_id -> bool **)

let rhyme_id_eqb r1 r2 =
  (&&) ((=) r1.ri_rawiy r2.ri_rawiy) (haraka_eqb r1.ri_majra r2.ri_majra)

type annotated_bayt = { ab_sadr : hemistich; ab_ajuz : hemistich;
                        ab_sadr_rhyme : rhyme_id; ab_ajuz_rhyme : rhyme_id }

(** val is_matla_proper : annotated_bayt -> meter -> bool **)

let is_matla_proper b m =
  (&&)
    ((&&) (is_valid_hemistich b.ab_sadr m) (is_valid_hemistich b.ab_ajuz m))
    (rhyme_id_eqb b.ab_sadr_rhyme b.ab_ajuz_rhyme)

(** val is_rhyme_consistent : annotated_bayt list -> rhyme_id -> bool **)

let is_rhyme_consistent lines r =
  forallb (fun b -> rhyme_id_eqb b.ab_ajuz_rhyme r) lines

type qasida = { qas_first : annotated_bayt; qas_rest : annotated_bayt list;
                qas_meter : meter; qas_rhyme : rhyme_id }

(** val qasida_lines : qasida -> annotated_bayt list **)

let qasida_lines q =
  q.qas_first::q.qas_rest

(** val is_valid_qasida : qasida -> bool **)

let is_valid_qasida q =
  let m = q.qas_meter in
  let r = q.qas_rhyme in
  (&&)
    ((&&) (is_matla_proper q.qas_first m)
      (forallb (fun b ->
        (&&) (is_valid_hemistich b.ab_sadr m) (is_valid_hemistich b.ab_ajuz m))
        q.qas_rest)) (is_rhyme_consistent (qasida_lines q) r)

(** val is_valid_ghazal : qasida -> bool **)

let is_valid_ghazal q =
  (&&)
    ((&&) (is_valid_qasida q)
      ((<=) (succ (succ (succ (succ (succ 0))))) (length (qasida_lines q))))
    ((<=) (length (qasida_lines q)) (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ 0))))))))))))))))

(** val is_valid_rubai : qasida -> bool **)

let is_valid_rubai q =
  if meter_eq_dec q.qas_meter Hazaj
  then (&&) (is_matla_proper q.qas_first Hazaj)
         (match q.qas_rest with
          | [] -> false
          | b2::l ->
            (match l with
             | [] ->
               (&&)
                 ((&&) (is_valid_hemistich b2.ab_sadr Hazaj)
                   (is_valid_hemistich b2.ab_ajuz Hazaj))
                 (rhyme_id_eqb b2.ab_ajuz_rhyme q.qas_rhyme)
             | _::_ -> false))
  else false

(** val is_valid_maqtua : qasida -> bool **)

let is_valid_maqtua q =
  let m = q.qas_meter in
  let r = q.qas_rhyme in
  (&&)
    ((&&)
      ((&&)
        (forallb (fun b ->
          (&&) (is_valid_hemistich b.ab_sadr m)
            (is_valid_hemistich b.ab_ajuz m)) (qasida_lines q))
        (is_rhyme_consistent (qasida_lines q) r))
      ((<=) (succ (succ 0)) (length (qasida_lines q))))
    ((<=) (length (qasida_lines q)) (succ (succ (succ (succ (succ 0))))))
