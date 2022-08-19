type srt_smt = 
  | Smt_bv of int option
  | Smt_int
  | Smt_bool 
  | Custom_sort of string

let valid_sort (s: srt_smt) : bool = 
  begin match s with 
  | Smt_bv (Some n) -> n > 0
  | Smt_bv None -> false
  | Custom_sort s -> 
    String.length s > 0 && s.[0] = Char.uppercase_ascii s.[0]
  | Smt_int 
  | Smt_bool -> true
  end
let pretty_sort (s: srt_smt) : string = 
  begin match s with 
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
    
(* assumes all the elements of curr_sorts are inductives *)
let print_sorts_decl _ = 
  let worker (_, nme) = "sorts_" ^ nme in
  let pref = "Inductive sorts := " in
  let mid = String.concat " | " @@ List.map worker (List.of_seq @@ get_current_sorts () ) in 
    pref ^ mid ^ "."

  let add_sorts_decl = Proofview.tclUNIT ()