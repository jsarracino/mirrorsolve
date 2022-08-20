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

(* let name_of_string (s: string) : Names.lname = 
  CAst.make @@ Names.Name.mk_name @@ Names.Id.of_string s  *)

(* let make_sort_name nme = "sorts_" ^ nme *)

let get_doc_id () = 0 

let exec_cmd (cmd: string) = 
  let doc = Stm.get_doc @@ get_doc_id () in 
  let sid : Stateid.t = Stm.get_current_state ~doc in
  let c_cmd : Pcoq.Parsable.t = Pcoq.Parsable.make @@ Stream.of_string cmd in 
  begin match Stm.parse_sentence ~doc ~entry:Pvernac.main_entry sid c_cmd with
  | None -> ()
  | Some stmt -> (
    Feedback.msg_debug @@ Pp.(++) (Pp.str "interpreting command: ") @@ Pp.str cmd;
    let _ = Stm.add ~doc ~ontop:(Stm.get_current_state ~doc) false stmt in 
      ()
    (* Vernac.process_expr *)
  )
  end




let get_sort_ctor_name (ctor, name) : Constrexpr.local_binder_expr = 
  CLocalPattern (CAst.make @@ Constrexpr.CPatAtom None )
    (* (Some (Libnames.qualid_of_string @@ make_sort_name name))) *)

let gen_sorts_inductives () : (Vernacexpr.one_inductive_expr * Vernacexpr.decl_notation list) * string = 
  let name_str = "sorts" in 
  let name = CAst.make (Names.Id.of_string name_str) in 
  let ind_params = List.map get_sort_ctor_name @@ (List.of_seq @@ get_current_sorts () ), None in
  let constrexpr = None in 
  let vernacexpr = [] in 
    ((name, ind_params, constrexpr, vernacexpr), []), name_str

let add_sorts_decl () = 
  let template = Some false in 
  let udecl = None in 
  let inductives, sorts_name = gen_sorts_inductives () in 
  let cumulative = false in 
  let poly = true in 
  let typing_flags = None in 
  let private_ind = false in 
  let uniform = ComInductive.UniformParameters in 
  let finite = Declarations.Finite in (
    ComInductive.do_mutual_inductive ~template udecl [inductives] ~cumulative ~poly ?typing_flags ~private_ind ~uniform finite;
    Feedback.msg_info @@ Pp.str @@ Format.sprintf "Added new sorts inductive: %s" sorts_name
  )