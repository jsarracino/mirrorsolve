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

(* let name_of_string (s: string) : Names.lname = 
  CAst.make @@ Names.Name.mk_name @@ Names.Id.of_string s  *)

(* let make_sort_name nme = "sorts_" ^ nme *)

let get_doc_id () = 0 

let dest_ind_ctors x = 
  begin match x with
  | Vernacexpr.Constructors xs -> xs
  | _ -> assert false
  end

let exec_cmd (cmd: string) = 
  let doc = Stm.get_doc @@ get_doc_id () in 
  let sid : Stateid.t = Stm.get_current_state ~doc in
  let c_cmd : Pcoq.Parsable.t = Pcoq.Parsable.make @@ Stream.of_string cmd in 
  begin match Stm.parse_sentence ~doc ~entry:Pvernac.main_entry sid c_cmd with
  | None -> ()
  | Some { v = { expr = Vernacexpr.VernacInductive (v_kind, [(ind_e, notations)]); _}; _} -> (
    Feedback.msg_debug @@ Pp.(++) (Pp.str "interpreting command as inductive: ") @@ Pp.str cmd;
    let template = Some false in 
    let udecl = None in 
    let cumulative = false in 
    let poly = false in 
    let typing_flags = None in 
    let private_ind = false in 
    let uniform = ComInductive.UniformParameters in 
    let finite = Declarations.Finite in 
    let ((_, (name, _)), iparams, x, y) = ind_e in 
    let ind_expr : Vernacexpr.one_inductive_expr = (name, iparams, x, dest_ind_ctors y) in (
      ComInductive.do_mutual_inductive ~template udecl [(ind_expr, notations)] ~cumulative ~poly ?typing_flags ~private_ind ~uniform finite;
      Feedback.msg_debug @@ Pp.str @@ "added inductive type " ^ Names.Id.to_string name.v
      )
    )
  | Some _ -> 
    Feedback.msg_warning @@ Pp.str "unrecognized command"
  end

let sorts_case_info () : Constr.case_info = 
  let sort_ind : Names.inductive = 
    begin match Nametab.locate (Libnames.qualid_of_string sort_name_str) with 
    | IndRef x -> x 
    | _ -> assert false
    end in {
    ci_ind = sort_ind;
    ci_npar = 0;
    ci_cstr_ndecls = [| |];
    ci_cstr_nargs = [||];
    ci_relevance = Sorts.Relevant;
    ci_pp_info = {
      ind_tags = [];
      cstr_tags = [| |];
      style = RegularStyle
    };
  }

let mk_univ_instance (ci: Constr.case_info) : Univ.Instance.t = 
  let env = Global.env () in 
  let ((i, u), _) = Inductive.find_inductive env (Constr.mkInd ci.ci_ind) in 
  let _ = Feedback.msg_debug @@ Pp.(++) (Pp.str "coerced sorts inductive to:") (Univ.Instance.pr Univ.Level.pr u ) in 
  let _ = Feedback.msg_debug @@ Pp.(++) (Pp.str "underlying inductive:") (Constr.debug_print @@ (Constr.mkInd ci.ci_ind) ) in 
    u

let build_interp_case () : EConstr.case = 
  (* (ci,u,params,p,iv,c,brs) *)
  let ci = sorts_case_info () in 
  let u : EConstr.EInstance.t =  EConstr.EInstance.make @@ mk_univ_instance ci in 
  let params : Evd.econstr array = [| |] in 
  let ret_type : Evd.econstr Constr.pcase_return = ([||], EConstr.mkSort @@ Sorts.type1) in 
  let iv = Constr.NoInvert in 
  let scrutinee : Evd.econstr = EConstr.mkRel 0 in 
  let branches : Evd.econstr Constr.pcase_branch array = [| 
    ([| Context.anonR |], EConstr.mkSort @@ Sorts.set)
  |] in 
    (ci, u, params, ret_type, iv, scrutinee, branches)

let add_sorts_decl () = exec_cmd @@ print_sorts_decl ()
let add_interp_decl () = 
  let name : Names.Id.t = Names.Id.of_string @@ "interp_"^sort_name_str in
  (* let body : Evd.econstr = EConstr.mkSort @@ Sorts.set in  *)
  let udecl = UState.default_univ_decl in 
  let body : Evd.econstr = EConstr.mkCase @@ build_interp_case () in 
  let typ: Evd.econstr option = None in 
  let poly = false in 
  let scope = Locality.Global Locality.ImportDefaultBehavior in
  let kind = Decls.(IsDefinition Definition) in
  let info : Declare.Info.t = Declare.Info.make ~scope ~kind  ~udecl ~poly  () in 
  let args : Names.Name.t list = [Names.Name.mk_name @@ Names.Id.of_string "s" ] in 
  let cinfo:Evd.econstr option Declare.CInfo.t = Declare.CInfo.make ~name ~typ ~args () in 
  let opaque = false in 
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let _ = Declare.declare_definition ~info ~cinfo ~opaque ~body sigma 
  in 
    Feedback.msg_debug @@ Pp.str @@ "added sort interpretation " ^ Names.Id.to_string name