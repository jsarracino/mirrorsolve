

module C = Constr
module GR = Names.GlobRef

exception BadExpr of string

let bedef = BadExpr "bad expression"

exception MissingGlobConst of string

let warn msg : unit Proofview.tactic =
  Proofview.tclLIFT (Proofview.NonLogical.make (fun () ->
      Feedback.msg_warning (Pp.str msg)))

let debug msg : unit Proofview.tactic =
  Proofview.tclLIFT (Proofview.NonLogical.make (fun () ->
      Feedback.msg_debug (Pp.str msg)))

let get_coq ref = 
  try (UnivGen.constr_of_monomorphic_global (Coqlib.lib_ref ref)) with
    e -> 
      let lib_refs = Coqlib.get_lib_refs () in 
      let needle = List.find_opt (fun (name, _) -> name == ref) lib_refs in
        begin match needle with 
        | Some (_, x) -> raise @@ MissingGlobConst ("polymorphic global: " ^ ref)
        | None -> raise @@ MissingGlobConst ("unregistered global: " ^ ref)
        end


let c_eq_name = "p4a.core.eq"
let c_impl_name = "p4a.core.impl"
let c_tt_name = "p4a.core.tt"
let c_ff_name = "p4a.core.ff"
let c_fun_name = "p4a.core.fun"
let c_state1_name = "p4a.funs.state1"
let c_state2_name = "p4a.funs.state2"
let c_tscons_name = "p4a.core.tscons"

let c_tsnil_name = "p4a.core.tsnil"
let c_conflit_name = "p4a.funs.conf_lit"
let c_statelit_name = "p4a.funs.state_lit"

let c_inl_name = "p4a.core.inl"
let c_inr_name = "p4a.core.inr"

let c_true = get_coq "core.bool.true"
let c_false = get_coq "core.bool.false"
let c_pair = get_coq "core.prod.intro"


let find_add i tbl builder = 
  begin match Hashtbl.find_opt tbl i with 
  | Some x -> x
  | None -> 
    let nxt = builder () in 
    Hashtbl.add tbl i nxt;
    nxt
  end

module GSSorts = GenSym.Make(struct let v = "Sorts" end)


(* map from coq sorts to local smt sort symbols *)
let sort_sym_tbl : (Names.inductive, string) Hashtbl.t  = Hashtbl.create 10
let sort_sizes : (string, int) Hashtbl.t = Hashtbl.create 10
(* let get_sort_size sym = Hashtbl.find sym sort_sizes *)
let reg_coq_sort_size e sz = 
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma', e') = Constrintern.interp_constr_evars env sigma e in
  begin match C.kind (EConstr.to_constr sigma' e') with
  | C.Ind (x, _) -> 
    let sym = Hashtbl.find sort_sym_tbl x in 
    Hashtbl.add sort_sizes sym sz
  | _ -> raise bedef
  end 
let reg_sort (i: Names.inductive) = find_add i sort_sym_tbl GSSorts.gen_sym
module GSConstrs = GenSym.Make(struct let v = "Constrs" end)

(* map from coq inductive constructors to local smt constructor symbols *)
let constr_sym_tbl : (Names.constructor, string) Hashtbl.t  = Hashtbl.create 100

let reg_constr (i: Names.constructor) = find_add i constr_sym_tbl GSConstrs.gen_sym

let prim_tbl : (Names.constructor, string) Hashtbl.t = Hashtbl.create 20
let reg_prim i t = find_add i prim_tbl (fun _ -> t)

let print_ind (x: Names.inductive) : Pp.t = 
  let (ctor, _) = x in 
    Names.MutInd.print ctor
let print_ctor (x: Names.constructor) : Pp.t =
  let (ind, idx) = x in 
    Pp.(++) (print_ind ind) (Pp.(++) (Pp.str "@") (Pp.int idx))
let debug_tbls () = 
  Pp.pr_vertical_list (fun x -> x) @@ 
    [Pp.str "SORTS:"] @
    Hashtbl.fold (fun srt sym acc -> acc @ [Pp.(++) (print_ind srt) (Pp.(++) (Pp.str " => ") (Pp.str sym))]) sort_sym_tbl [] @ 
    [Pp.str "SORT SIZES:"] @
    Hashtbl.fold (fun sym sz acc -> acc @ [Pp.(++) (Pp.str sym) (Pp.(++) (Pp.str " => ") (Pp.int sz))]) sort_sizes [] @ 
    [Pp.str "INDS:"] @ 
    Hashtbl.fold (fun ctor sym acc -> acc @ [Pp.(++) (print_ctor ctor) (Pp.(++) (Pp.str " => ") (Pp.str sym))]) constr_sym_tbl [] @
    [Pp.str "PRIMS:"] @ 
    Hashtbl.fold (fun ctor sym acc -> acc @ [Pp.(++) (print_ctor ctor) (Pp.(++) (Pp.str " => ") (Pp.str sym))]) prim_tbl []

let reg_coq_ind_constr e = 
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma', e') = Constrintern.interp_constr_evars env sigma e in
  begin match C.kind (EConstr.to_constr sigma' e') with
  | C.Construct (ctor, _) -> 
    let _ = reg_constr ctor in 
    let _ = reg_sort (Names.inductive_of_constructor ctor) in
      ()
  | _ -> raise bedef
  end

let reg_prim_name e nme = 
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma', e') = Constrintern.interp_constr_evars env sigma e in
  let e'' = (EConstr.to_constr sigma' e') in
    begin match C.kind e'' with 
    | C.App(f, _) -> 
      begin match C.kind f with 
      | C.Construct(x, _) -> let _ = reg_prim x nme in ()
      | _ -> raise @@ BadExpr ("expected inductive ctor and got: " ^ (Pp.string_of_ppcmds (C.debug_print f)))
      end
    | C.Construct(x, _) -> let _ = reg_prim x nme in ()
    | _ -> raise @@ BadExpr ("expected inductive ctor and got: " ^ (Pp.string_of_ppcmds (C.debug_print e'')))
    end

(* let is_binop s = 
  s = c_eq_name *)

(* let args s = 2 *)


type bop = Impl | And | Or
type uop = Neg

type bexpr = 
  | Tru | Fls
  | Bop of bop * bexpr * bexpr
  | Uop of uop * bexpr

(* destruct a coq expression to a binop and produces the immediate children as a pair of coq expressions *)
(* let destruct_bop e = 
  (* TODO: factor out this logic into a hashtable *)
  let op = 
    if C.equal e c_impl then Some Impl else
    if C.equal e c_and then Some And else
    if C.equal e c_or then Some Or else 
      None in
  begin match op, e with 
  | Some _, C.App (_, _) -> None
  | _, _ -> None
  end *)

let ceq = C.equal

let a_last a = a.(Array.length a - 1)

let c_e_to_conf (e: C.t) : string =
  begin match C.kind e with 
  | C.App(f, es) -> 
    if C.equal f c_pair then 
      let el, er = es.(2), es.(3) in
      begin match C.kind el, C.kind er with 
      | C.App(_, els), C.App(_, ers) -> 
        let el', er' = els.(Array.length els - 2), ers.(Array.length ers - 2) in
        begin match C.kind el', C.kind er' with
        | C.Var x, C.Var y -> 
          Format.sprintf "%s %s" (Names.Id.to_string x) (Names.Id.to_string y)
        | C.Rel x, C.Rel y -> 
          Format.sprintf "pvar_%n pvar_%n" x y
        | _, _ -> 
          Feedback.msg_warning (Pp.(++) (Pp.str "els_last: ") (C.debug_print el')) ;
          Feedback.msg_warning (Pp.(++) (Pp.str "ers_last: ") (C.debug_print er')) ;
          raise @@ BadExpr "unexpected variable (see warning)"
        end
      | _, _ ->
        Feedback.msg_warning (Pp.(++) (Pp.str "el: ") (C.debug_print el)) ;
        Feedback.msg_warning (Pp.(++) (Pp.str "er: ") (C.debug_print er)) ;
        raise @@ BadExpr "unexpected variable (see warning)"
      end
    else
      raise @@ BadExpr ("missing pair constructor: " ^ (Pp.string_of_ppcmds (C.debug_print e)))
  | _ -> 
    raise @@ BadExpr ("missing state constructor: " ^ (Pp.string_of_ppcmds (C.debug_print e)))
  end

(* let rec take n xs = 
  if n = 0 then [] else 
    begin match xs with 
    | [] -> raise bedef
    | x :: xs' -> x :: take (n - 1) xs'
    end *)

let c_e_to_ind (e: C.t) : string = 
  let (f, es) = C.destApp e in 
  let (e', _) = C.destConstruct f in
    
  let op_name = Hashtbl.find prim_tbl e' in
  if op_name = c_inl_name then 
    
    let (f', es') = C.destApp es.(2) in
    let (e'', _) = C.destConstruct f in
    let op_name' = Hashtbl.find prim_tbl e'' in
    if op_name' = c_inl_name || op_name' = c_inr_name then 
      Hashtbl.find constr_sym_tbl (fst (C.destConstruct es'.(2))) 
    else
      raise @@ BadExpr ("missing state constructor: " ^ (Pp.string_of_ppcmds (C.debug_print es'.(2)))) 
  else if op_name = c_inr_name then 
    if C.equal c_true es.(2) then "(inr true)" 
    else if C.equal c_false es.(2) then "(inr false)" 
    else
      raise @@ BadExpr ("bad inr argument: " ^ (Pp.string_of_ppcmds (C.debug_print es.(2)))) 
  else 
    raise @@ BadExpr ("expected inl/inr and got : " ^ (Pp.string_of_ppcmds (C.debug_print f)))

let rec extract_ts_list (e: C.t) : C.t list = 
  begin match C.kind e with
  | C.App(f, [| _; _; |]) ->
    begin match C.kind f with
    | C.Construct(x, _) -> 
      begin match Hashtbl.find_opt prim_tbl x with 
      | Some name ->
        if name = c_tsnil_name then [] else
          raise @@ BadExpr ("unexpected symbol in ts list: " ^ name)
      | None -> 
        raise @@ BadExpr ("unexpected constructor in ts list: " ^ (Pp.string_of_ppcmds (C.debug_print e)))
      end
    | _ -> raise @@ BadExpr ("unexpected constructor in ts list app: " ^ (Pp.string_of_ppcmds (C.debug_print f)))
    end
  | C.App(f, [| _; _; _; _; h; t |]) ->
    begin match C.kind f with
    | C.Construct(x, _) -> 
      begin match Hashtbl.find_opt prim_tbl x with 
      | Some name ->
        if name = c_tscons_name then h :: extract_ts_list t else
          raise @@ BadExpr ("unexpected symbol in ts list: " ^ name)
      | None -> 
        raise @@ BadExpr ("unexpected constructor in ts list: " ^ (Pp.string_of_ppcmds (C.debug_print e)))
      end
    | _ -> raise @@ BadExpr ("unexpected constructor in ts list app: " ^ (Pp.string_of_ppcmds (C.debug_print f)))
    end
  | C.App(_, args) -> raise @@ BadExpr (Format.sprintf "there are %n args " (Array.length args))
  | _ -> raise @@ BadExpr ("unexpected expression in ts list: " ^ (Pp.string_of_ppcmds (C.debug_print e)))
  end

let rec pretty_expr (e: C.t) : string =
  begin match C.kind e with 
  | C.App(f, es) -> 
    let args = Array.map (fun e -> lazy (pretty_expr e)) es in

    begin match C.kind f with 
      
    | C.Construct (e', _) ->
      begin match Hashtbl.find_opt prim_tbl e' with 
      | Some op_name' ->
        if op_name' = c_eq_name then 
          let args' = Array.map Lazy.force (Array.sub args 3 2) in 
          begin match args' with 
          | [| a1; a2 |] -> Format.sprintf "(= %s %s)" a1 a2
          | _ -> raise @@ BadExpr "bad args to eq"
          end else 
        if op_name' = c_impl_name then 
          let args' = Array.map Lazy.force (Array.sub args 2 2) in 
          begin match args' with 
          | [| a1; a2 |] -> Format.sprintf "(=> %s %s)" a1 a2
          | _ -> raise @@ BadExpr "bad args to impl"
          end else 

        if op_name' = c_fun_name then 
          let fname = Lazy.force args.(4) in 
          let fargs = extract_ts_list es.(5) in
          if fname = c_state1_name then 
            let arg = List.hd fargs in Format.sprintf "(state1 %s)" (pretty_expr arg) else
          if fname = c_state2_name then 
            let arg = List.hd fargs in Format.sprintf "(state2 %s)" (pretty_expr arg) else
          (* conf_lit and state_lit *)
            fname else 
        if op_name' = c_state1_name then c_state1_name else
        if op_name' = c_state2_name then c_state2_name else
        if op_name' = c_conflit_name then 
          Format.sprintf "(mk_conf_lit %s)" (c_e_to_conf (a_last es)) else
        if op_name' = c_statelit_name then 
          (* let _ = Feedback.msg_debug (Pp.str @@ Format.sprintf "length of args: %n" (Array.length es)) in *)
          c_e_to_ind es.(6) else
        if op_name' = c_tt_name then "true" else
        if op_name' = c_ff_name then "false" else
            raise @@ BadExpr ("unhandled op_name: " ^ op_name')

      | None -> raise @@ BadExpr ("missing constructor "^Pp.string_of_ppcmds @@ C.debug_print f)
      end
        
    | _ -> raise @@ BadExpr ("app: " ^ Pp.string_of_ppcmds @@ C.debug_print f)
    end

  | C.Construct (x, _) -> 
    begin match Hashtbl.find_opt constr_sym_tbl x, Hashtbl.find_opt prim_tbl x with
    | Some _, Some _ -> raise @@ BadExpr ("double ctor binding: " ^Pp.string_of_ppcmds @@ C.debug_print e)
    | Some r, _ -> r
      
    | _, Some r -> r
    | None, None -> raise @@ BadExpr ("missing ctor binding: " ^Pp.string_of_ppcmds @@ C.debug_print e)
    end

  | _ -> raise @@ BadExpr ("outer: " ^Pp.string_of_ppcmds @@ C.debug_print e)
  end

let pretty env sigma e = 
  pretty_expr @@ EConstr.to_constr sigma e 

let debug_lib_refs _ = 
  let lib_ref_names = List.map fst (Coqlib.get_lib_refs ()) in
    Pp.pr_sequence Pp.str lib_ref_names

let build_query (vars: string list) (e: C.t) (refute_query: bool) : string = 
  let q_str = if refute_query then 
    Format.sprintf "(assert (not %s))" (pretty_expr e) else
    Format.sprintf "(assert %s)" @@ Smt.gen_binders (List.length vars) (pretty_expr e) in 

  let ctors = List.of_seq @@ Hashtbl.to_seq_values constr_sym_tbl  in 
  Smt.gen_query ctors vars q_str refute_query

let dump_query (vars: string list) (e: EConstr.t) : unit = 
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let query = build_query vars (EConstr.to_constr sigma e) true in
    Feedback.msg_info (Pp.str query)

let rec extract_foralls (e: C.t) : string list * C.t = 
  begin match C.kind e with
  | C.Prod(nme, _, bod) -> 
    let (nms, bod') = extract_foralls bod in 
    Pp.string_of_ppcmds (Names.Name.print (Context.binder_name nme)) :: nms, bod'
  | _ -> ([], e)
  end

let check_interp (e: C.t) : string = 
  begin match C.kind e with 
  | C.Prod _ -> 
    let (names, bod) = extract_foralls e in
    begin match C.kind bod with 
    | C.App(f, es) -> 
      begin match C.kind f with 
      | C.Const(n, _) -> 
        let name = Names.Constant.to_string n in 
        if name = "Poulet4.P4automata.FirstOrder.interp_fm" then
          let bod' = a_last es in
            build_query names bod' false else

          raise bedef
      | _ -> raise bedef
      end
    | _ -> raise bedef
    end
  | _ -> raise bedef
  end

  (*  *)