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

(* type constr' = Constr.types with compare ;; *)

module ConstrSet = Set.Make(
  struct
    type t = Constr.t ;;
    let compare = Constr.compare ;;
  end
)

let curr_sorts = ref ConstrSet.empty
let get_current_sorts _ = ! curr_sorts
let add_sort s = 
  let nxt = (ConstrSet.add s @@ get_current_sorts () ) in 
  curr_sorts := nxt

(* assumes all the elements of curr_sorts are inductives *)
let print_sorts_decl _ = 
  let worker srt : string = 
    if Constr.isInd srt then
      let x, _ = Constr.destInd srt in 
      let _, decl = Global.lookup_inductive x in 
        "sorts_" ^ Libnames.string_of_qualid @@ Libnames.qualid_of_ident decl.mind_typename
    else 
      assert false
    in
  let pref = "Inductive sorts := " in
  let mid = String.concat " | " @@ List.map worker (List.of_seq @@ ConstrSet.to_seq @@ get_current_sorts () ) in 
    pref ^ mid ^ "."


  let add_sorts_decl = Proofview.tclUNIT ()