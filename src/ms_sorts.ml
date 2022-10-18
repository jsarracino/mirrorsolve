type srt_smt = 
  | Smt_bv of int option
  | Smt_int
  | Smt_bool 
  | Custom_sort of string

let list_all fs = 
  List.fold_left (fun acc f x -> acc x && f x) (fun _ -> true) fs
let between l r x = 
  Char.code l <= Char.code x && 
  Char.code x <= Char.code r

let is_upper c = between 'A' 'Z' c
let is_alpha_num c = 
  (between '0' '9' c) || 
  (between 'A' 'Z' c) || 
  (between 'a' 'z' c) || 
  c = '_'

let check_sort_name s = 
  let tests = [
      (fun s -> String.length s > 0)
    ; (fun s -> is_upper s.[0])
    ; (fun s -> String.for_all is_alpha_num s)
  ] in 
  list_all tests s

let repair_sort s = 
  begin match s with 
  | Custom_sort x -> Custom_sort (String.capitalize_ascii x)
  | _ -> s
  end

let valid_sort (s: srt_smt) : bool * string = 
  begin match s with 
  | Smt_bv (Some n) -> n > 0, "negative bitvector width"
  | Smt_bv None -> false, "missing bitvector width"
  | Custom_sort s -> 
    check_sort_name s, "empty name; or first letter must be uppercase; or name contains invalid symbols"
  | Smt_int 
  | Smt_bool -> true, "inconceivable"
  end
let pretty_sort (s: srt_smt) : string = 
  begin match repair_sort s with 
  | Smt_bv (Some n) -> Format.sprintf "(_ BitVec %n)" n
  | Smt_bv None -> assert false
  | Smt_int -> "Int"
  | Smt_bool -> "Bool"
  | Custom_sort s -> s
  end

let nme_ctr = ref 0

let default_sort_name srt : string = 
  if Constr.isInd srt then
    let x, _ = Constr.destInd srt in 
    let _, decl = Global.lookup_inductive x in 
      Libnames.string_of_qualid @@ Libnames.qualid_of_ident decl.mind_typename
  else (
    nme_ctr := !nme_ctr + 1; 
    Format.sprintf "%i" (!nme_ctr - 1)
  )


let sort_names = Hashtbl.create 20

let get_current_sorts _ = Hashtbl.to_seq sort_names
let add_sort srt opt_name = 
  let nme = 
    begin match opt_name with 
    | Some s -> s
    | None -> default_sort_name srt
    end in 
  Hashtbl.add sort_names srt nme

let sort_name_str = "sorts"
let print_sorts_decl _ = 
  let worker (_, nme) = "sorts_" ^ nme in
  let pref = Format.sprintf "Inductive %s := " sort_name_str in
  let mid = String.concat " | " @@ List.map worker (List.of_seq @@ get_current_sorts () ) in 
    pref ^ mid ^ "."