

module C = Constr
module GR = Names.GlobRef

exception BadExpr of string
exception UnboundPrimitive

let bedef = BadExpr "bad expression"

exception MissingGlobConst of string

type ('a, 'b) sum = Inl of 'a | Inr of 'b

let a_last a = a.(Array.length a - 1)

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
      let needle = List.find_opt (fun (name, _) -> name = ref) lib_refs in
        begin match needle with 
        | Some (_, x) -> raise @@ MissingGlobConst ("polymorphic global: " ^ ref)
        | None -> raise @@ MissingGlobConst ("unregistered global: " ^ ref)
        end


let c_eq_name = "p4a.core.eq"
let c_impl_name = "p4a.core.impl"
let c_and_name = "p4a.core.and"
let c_or_name = "p4a.core.or"
let c_not_name = "p4a.core.neg"

let c_tt_name = "p4a.core.tt"
let c_ff_name = "p4a.core.ff"
let c_fun_name = "p4a.core.fun"
let c_hcons_name = "p4a.core.hcons"

let c_hnil_name = "p4a.core.hnil"
let c_inl_name = "coq.core.inl"
let c_inr_name = "coq.core.inr"

let c_true = get_coq "core.bool.true"
let c_false = get_coq "core.bool.false"
let c_pair = get_coq "core.prod.intro"
let c_forall_name = "p4a.core.forall"
let c_var_name = "p4a.core.var"

let c_cnil_name = "p4a.core.cnil"
let c_snoc_name = "p4a.core.csnoc"

let c_bits_name = "p4a.sorts.bits"
let c_store_name = "p4a.sorts.store"
let c_zero = get_coq "num.nat.O"
let c_succ = get_coq "num.nat.S"

let c_prop_not = get_coq "core.not.type"

let c_bits_lit_name = "p4a.funs.bitslit"
let c_concat_name = "p4a.funs.concat"
let c_slice_name = "p4a.funs.slice"
let c_lookup_name = "p4a.funs.lookup"

let c_unit = get_coq "core.unit.tt"

let c_vhere_name = "p4a.core.vhere"
let c_vthere_name = "p4a.core.vthere"


let find_add i tbl builder = 
  begin match Hashtbl.find_opt tbl i with 
  | Some x -> x
  | None -> 
    let nxt = builder () in 
    Hashtbl.add tbl i nxt;
    nxt
  end

let prim_tbl : (Names.constructor, string) Hashtbl.t = Hashtbl.create 20
let reg_prim i t = find_add i prim_tbl (fun _ -> t)

let prim_tbl' : (C.t, string) Hashtbl.t = Hashtbl.create 20
let reg_prim' i t = find_add i prim_tbl' (fun _ -> t)


let rec c_nat_to_int (e: C.t) : int =
  if e = c_zero then 0 
  else if C.isApp e then 
    let (f, es) = C.destApp e in 
    if f = c_succ then
      1 + c_nat_to_int (a_last es)
    else
      let _ = Feedback.msg_debug (Pp.str "S:") in
      let _ = Feedback.msg_debug (Constr.debug_print c_succ) in
      let _ = Feedback.msg_debug (Pp.str "Expected S and got:") in
      let _ = Feedback.msg_debug (Constr.debug_print e) in
      raise @@ BadExpr "expected S in nat_to_int"
  else
    let _ = Feedback.msg_debug (Pp.str "S:") in
    let _ = Feedback.msg_debug (Constr.debug_print c_succ) in
    let _ = Feedback.msg_debug (Pp.str "Z:") in
    let _ = Feedback.msg_debug (Constr.debug_print c_zero) in
    let _ = Feedback.msg_debug (Pp.str "Expected S/Z and got:") in
    let _ = Feedback.msg_debug (Constr.debug_print e) in
    raise @@ BadExpr "expected S or 0 in nat_to_int"
    

type sort = 
  Bits of int | 
  Store

let extract_sort (e: C.t) : sort = 
  if C.isConstruct e then
    let (nme, _ ) = C.destConstruct e in
    if Hashtbl.find prim_tbl nme = c_store_name then Store
    else 
      let _ = Feedback.msg_debug (Pp.str "Expected store construct and got:") in
      let _ = Feedback.msg_debug (Constr.debug_print e) in
      raise @@ BadExpr "unexpected constructor for sorts (see debug)"  
  else if not @@ C.isApp e then 
    let _ = Feedback.msg_debug (Pp.str "Expected app for sort and got:") in
    let _ = Feedback.msg_debug (Constr.debug_print e) in
    raise @@ BadExpr "expected app for sort" 
  else
    let (f, es) = C.destApp e in 
    let (nme, _) = C.destConstruct f in 
    if Hashtbl.find prim_tbl nme = c_bits_name then 
      let (_, es) = C.destApp e in 
      Bits (c_nat_to_int (a_last es))
    else
      let _ = Feedback.msg_debug (Pp.str "Expected sort and got:") in
      let _ = Feedback.msg_debug (Constr.debug_print e) in
      raise @@ BadExpr "unexpected constructor for sorts (see debug)"      

let valid_sort (s: sort) : bool = 
  begin match s with 
  | Bits n -> n > 0
  | Store -> true
  end
let pretty_sort (s: sort) : string = 
  begin match s with 
  | Bits n -> Format.sprintf "(_ BitVec %n)" n
  | Store -> "Env"
  end
  
module EnvCtors = GenSym.Make(struct let v = "Env_ctor" end)

let env_ctor_tbl : (Names.constructor, string * sort) Hashtbl.t = Hashtbl.create 20
let reg_env_ctor i s = find_add i env_ctor_tbl (fun _ -> EnvCtors.gen_sym (), s)


(* parse something of the form: (ctor, sort) *)
let extract_ctor_decl e = 
  if not @@ C.isApp e then 
    raise bedef
  else
    let (f, es) = C.destApp e in 
    if f = c_pair then 
      let l, r = es.(Array.length es - 2), a_last es in 
      let (x, _) = C.destConstruct l in 
      (x, extract_sort r)
    else  
      raise bedef
let reg_c_env_ctors (es: C.t list) : unit = 
  let worker e = 
    let (c, s) = extract_ctor_decl e in 
      ignore @@ reg_env_ctor c s
    in
  List.iter worker es

let clear_env_ctors _ = 
  Hashtbl.clear env_ctor_tbl

let print_ind (x: Names.inductive) : Pp.t = 
  let (ctor, _) = x in 
    Names.MutInd.print ctor
let print_ctor (x: Names.constructor) : Pp.t =
  let (ind, idx) = x in 
    Pp.(++) (print_ind ind) (Pp.(++) (Pp.str "@") (Pp.int idx))
let debug_tbls () = 
  Pp.pr_vertical_list (fun x -> x) @@ 
    [Pp.str "PRIMS:"] @ 
    Hashtbl.fold (fun ctor sym acc -> acc @ [Pp.(++) (print_ctor ctor) (Pp.(++) (Pp.str " => ") (Pp.str sym))]) prim_tbl [] @
    [Pp.str "ENV CTORS:"] @ 
    Hashtbl.fold (fun ctor (sym, srt) acc -> acc @ [Pp.(++) (print_ctor ctor) (Pp.(++) (Pp.str " => ") (Pp.(++) (Pp.str sym) (Pp.str @@ Format.sprintf " : %s" (pretty_sort srt))))]) env_ctor_tbl [] 



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

let reg_prim_name' e nme = ignore @@ reg_prim' e nme

type bop = Impl | And | Or | Eq 
type uop = Neg

type bexpr = 
  | Tru | Fls
  | Bop of bop * bexpr * bexpr
  | Uop of uop * bexpr
  | Forall of string * sort * bexpr
  | App of string * (bexpr list)
  | TSym of string

let pretty_bop o = Pp.str @@ 
  begin match o with 
  | Impl -> "=>"
  | And -> "and"
  | Or -> "or"
  | Eq -> "="
  end

let join = Pp.pr_sequence (fun x -> x)

let pp_binding name srt = 
  Pp.surround @@ join [Pp.str name; Pp.str @@ pretty_sort srt]

let rec pretty_bexpr (e: bexpr) : Pp.t = 
  begin match e with 
  | Tru -> Pp.str "true" | Fls -> Pp.str "false"
  | Bop (o,l,r) -> 
    Pp.surround (Pp.pr_sequence bop_formatter [Inl o; Inr l; Inr r])
  | Uop (Neg, i) -> Pp.surround (join [Pp.str "not"; pretty_bexpr i])
  | Forall (v, s, i) -> Pp.surround @@ 
    join [Pp.str "forall"; Pp.surround (pp_binding v s); pretty_bexpr i]
  | App (f, es) -> Pp.surround @@ join ([Pp.str f] @ List.map pretty_bexpr es)
  | TSym s -> Pp.str s
  end
  and bop_formatter x = 
  begin match x with
  | Inl o -> pretty_bop o
  | Inr r -> pretty_bexpr r
  end
let c_sum_to_key (e: C.t) : C.t = 
  let (f, es) = C.destApp e in 
  let (e', _) = C.destConstruct f in
    
  let op_name = Hashtbl.find prim_tbl e' in
  if op_name = c_inl_name || op_name = c_inr_name then 
    a_last es
  else 
    let _ = Feedback.msg_debug (Pp.str (Format.sprintf "expected inl/inr in sum2key and got %s:" op_name)) in
    let _ = Feedback.msg_debug (C.debug_print e) in
    raise bedef
let rec extract_h_list (e: C.t) : C.t list = 
  let (f, args) = C.destApp e in 
  if C.isConstruct f then
    let (x, _) = C.destConstruct f in 
    begin match Hashtbl.find_opt prim_tbl x with 
    | Some name ->
      if name = c_hnil_name then [] 
      else if name = c_hcons_name then 
        (* A B a as h t *)
        args.(Array.length args - 2) :: extract_h_list (a_last args) 
      else
        raise @@ BadExpr ("unexpected symbol in hlist: " ^ name)
    | None -> 
      raise @@ BadExpr ("unexpected constructor in hlist: " ^ (Pp.string_of_ppcmds (C.debug_print e)))
    end
  else
  raise bedef

let rec extract_ctx (e: C.t) : C.t list = 
  let (f, es) = C.destApp e in 
  let (ctor, _) = C.destConstruct f in 
  let cname = Hashtbl.find prim_tbl ctor in
  if cname = c_cnil_name then []
  else if cname = c_snoc_name then 
    a_last es :: extract_ctx es.(1)
  else
    let _ = Feedback.msg_debug (Pp.str (Format.sprintf "Expected snoc/nil and got %s:" cname)) in
    let _ = Feedback.msg_debug (Constr.debug_print e) in
    raise @@ BadExpr "expected csnoc/cnil inside ctx list"

let rec c_n_tuple_to_bools (e: C.t) : bool list =
  if e = c_unit then []
  
  else if C.isApp e then 
    let (f, es) = C.destApp e in 
    if f = c_pair then
      let snoc_e = a_last es in 
      let snoc_v = 
        if snoc_e = c_true then true
        else if snoc_e = c_false then false
        else raise bedef in
      c_n_tuple_to_bools es.(Array.length es - 2) @ [snoc_v]
    else
      let _ = Feedback.msg_debug (Pp.str "pair:") in
      let _ = Feedback.msg_debug (Constr.debug_print c_pair) in
      let _ = Feedback.msg_debug (Pp.str "Expected pair and got:") in
      let _ = Feedback.msg_debug (Constr.debug_print f) in
      raise @@ BadExpr "expected pair in tuple2bool"
  else
    let _ = Feedback.msg_debug (Pp.str "pair:") in
    let _ = Feedback.msg_debug (Constr.debug_print c_pair) in
    let _ = Feedback.msg_debug (Pp.str "Expected pair and got:") in
    let _ = Feedback.msg_debug (Constr.debug_print e) in
    raise @@ BadExpr "expected app/pair in tuple2bool"

let print_bools (bs: bool list) : Pp.t = 
  Pp.(++) (Pp.str "#b") (Pp.prlist (fun b -> Pp.str (if b then "1" else "0")) bs)

let rec debruijn_idx (e: C.t) : int = 
  let (f, es) = C.destApp e in 
  let (x, _) = C.destConstruct f in
  let nme = Hashtbl.find prim_tbl x in
  if nme = c_vhere_name then 
    let ctx = extract_ctx es.(Array.length es - 2) in 
      List.length ctx
  else if nme = c_vthere_name then 
    debruijn_idx (a_last es)
  else 
    let _ = Feedback.msg_debug (Pp.str "Unexpected constructor in debruijn variable:") in
    let _ = Feedback.msg_debug (C.debug_print e) in
      raise bedef

let format_args (es: C.t array) : Pp.t = 
  let eis = Array.mapi (fun i e -> (i, e)) es in
  let builder (i, e) = Pp.(++) (Pp.str (Format.sprintf "%n => " i)) (C.debug_print e) in
  Pp.pr_vertical_list builder (Array.to_list eis)

let pretty_key (e: C.t) : string = 
  (* let _ = debug_pp @@ Pp.str "Key expression:" in
  let _ = debug_pp @@ C.debug_print e in *)
  let inner = c_sum_to_key e in
  let (x, _) = C.destConstruct inner in 
    fst @@ Hashtbl.find env_ctor_tbl x 
  
let str_starts_with pref s = 
  if String.length pref > String.length s then false
  else
    String.sub s 0 (String.length pref) = pref
let debug_flag = false

(* let debug_print (f: unit -> unit) : unit = 
  if debug_flag then f () else () *)

let debug_pp (msg: Pp.t) : unit = 
  if debug_flag then Feedback.msg_debug msg else ()

let rec extract_expr (e: C.t) : bexpr = 
  begin match Hashtbl.find_opt prim_tbl' e with 
  | Some nme -> 
    begin match nme with
    | x when x = c_eq_name ->  
      let (e1, e2) = rec_bop e in 
        Bop (Eq, e1, e2)
    | x when x = c_impl_name ->  
      let (e1, e2) = rec_bop e in 
        Bop (Impl, e1, e2)
    | x when x = c_and_name ->  
      let (e1, e2) = rec_bop e in 
        Bop (And, e1, e2)
    | x when x = c_or_name ->  
      let (e1, e2) = rec_bop e in 
        Bop (Or, e1, e2)
    | x when x = c_not_name ->  
      Uop (Neg, rec_unop e)
    | _ -> assert false
    end
  | _ -> assert false
  end
and
  rec_bop (e: C.t) : bexpr * bexpr = 
    let (_, es) = C.destApp e in 
      extract_expr es.(Array.length es - 2), extract_expr (a_last es)
and
  rec_unop (e: C.t) : bexpr = 
    let (_, es) = C.destApp e in 
      extract_expr (a_last es)



let rec pretty_expr (e: C.t) : string =
  try
    begin match C.kind e with 
    | C.App(f, es) -> 

      begin match C.kind f with 
        
      | C.Construct (e', _) ->
        begin match Hashtbl.find_opt prim_tbl e' with 
        | Some op_name' ->
          if op_name' = c_eq_name then 
            let _ = debug_pp @@ Pp.str "extracting eq" in
            let a1, a2 = pretty_expr es.(Array.length es - 2), pretty_expr (a_last es) in
            Format.sprintf "(= %s %s)" a1 a2
          else if op_name' = c_impl_name then 
            let _ = debug_pp @@ Pp.str "extracting impl" in
            let a1, a2 = pretty_expr es.(Array.length es - 2), pretty_expr (a_last es) in
            Format.sprintf "(=> %s %s)" a1 a2
          else if op_name' = c_and_name then 
            (* bunch of junk, l, r *)
            let _ = debug_pp @@ Pp.str "extracting and" in
            let l, r = pretty_expr es.(Array.length es - 2), pretty_expr (a_last es) in 
            Format.sprintf "(and %s %s)" l r
          else if op_name' = c_or_name then 
            (* bunch of junk, l, r *)
            let _ = debug_pp @@ Pp.str "extracting or" in
            let l = pretty_expr es.(Array.length es - 2) in 
            let r = pretty_expr (a_last es) in 
            Format.sprintf "(or %s %s)" l r
          else if op_name' = c_not_name then 
            (* bunch of junk, inner *)
            let _ = debug_pp @@ Pp.str "extracting not" in
            Format.sprintf "(not %s)" (pretty_expr (a_last es))
          else if op_name' = c_fun_name then 
            let _ = debug_pp @@ Pp.str "extracting fun with args:" in
            let _ = debug_pp @@ format_args es in
            let fname = pretty_expr es.(Array.length es - 2) in 
            let fargs = extract_h_list (a_last es) in
            let _ = debug_pp @@ Pp.str "found args:" in
            let _ = debug_pp @@ format_args (Array.of_list fargs) in
            if str_starts_with "#b" fname then 
              (* bits literal *)
              let _ = debug_pp @@ Pp.str "extracting bitslit fun" in
              fname
            else if str_starts_with "(_ extract" fname then
              let _ = debug_pp @@ Pp.str "extracting extract fun" in
              let arg = List.hd fargs in 
              Format.sprintf "(%s %s)" fname (pretty_expr arg)
            else if fname = c_concat_name then
              let _ = debug_pp @@ Pp.str "extracting concat fun" in
              begin match fargs with 
              | l :: r :: _ -> 
                Format.sprintf "(concat %s %s)" (pretty_expr l) (pretty_expr r)
              | _ -> raise bedef
              end
            else if str_starts_with "lookup_" fname then
              let _ = debug_pp @@ Pp.str "extracting lookup fun" in
              let split_str = String.split_on_char '_' fname in 
              begin match split_str with 
              | _ :: key :: rem -> 
                let arg = List.hd fargs in 
                  Format.sprintf "(%s %s)" (String.concat "_" (key :: rem)) (pretty_expr arg)
              | _ -> 
                let _ = Feedback.msg_debug (Pp.str "unexpected lookup format: ") in
                let _ = Feedback.msg_debug (Pp.str fname) in
                  raise bedef
              end
            else
            (* conf_lit and state_lit *)
              let _ = debug_pp @@ Pp.str (Format.sprintf "extracting wildcard %s" fname) in
              fname 
          else if op_name' = c_slice_name then 
            let _ = debug_pp @@ Pp.str "extracting slice" in
            (* n hi lo *)
            let hi = c_nat_to_int es.(Array.length es - 2) in 
            let lo = c_nat_to_int (a_last es) in 
            Format.sprintf "(_ extract %n %n)" hi lo
          else if op_name' = c_concat_name then 
            let _ = debug_pp @@ Pp.str "extracting concat" in
            (* n m *)
            c_concat_name
          else if op_name' = c_tt_name then 
            let _ = debug_pp @@ Pp.str "extracting true" in
            "true" 
          else if op_name' = c_ff_name then 
            let _ = debug_pp @@ Pp.str "extracting false" in
            "false" 
          else if op_name' = c_lookup_name then 
            let _ = debug_pp @@ Pp.str "extracting lookup" in
              Format.sprintf "lookup_%s" @@ pretty_key (a_last es)
          else if op_name' = c_bits_lit_name then 
            let _ = debug_pp @@ Pp.str "extracting bitslit" in
            Pp.string_of_ppcmds @@ print_bools @@ c_n_tuple_to_bools @@ (a_last es)
          else if op_name' = c_var_name then 
            let _ = debug_pp @@ Pp.str "extracting var" in
            let suff = debruijn_idx (a_last es) in
              Format.sprintf "fvar_%n" suff
          else if op_name' = c_forall_name then
            let _ = debug_pp @@ Pp.str "extracting forall" in
            let v_sort = extract_sort es.(2) in
            if not (valid_sort v_sort) then pretty_expr (a_last es) 
            else 
              let v_suff = List.length (extract_ctx es.(1)) in
              let v_name = Format.sprintf "fvar_%n" v_suff in
              let bod = pretty_expr (a_last es) in
                Format.sprintf "(forall ((%s %s)) %s)" v_name (pretty_sort v_sort) bod
          else
              raise @@ BadExpr ("unhandled op_name: " ^ op_name')

        | None -> raise @@ BadExpr ("missing constructor "^Pp.string_of_ppcmds @@ C.debug_print f)
        end
          
      | _ -> raise @@ BadExpr ("app: " ^ Pp.string_of_ppcmds @@ C.debug_print f)
      end

    | C.Construct (x, _) -> 
      let _ = debug_pp @@ Pp.str "extracting constant" in
      begin match Hashtbl.find_opt prim_tbl x with
      | Some r -> r
      | None -> raise @@ BadExpr ("missing ctor binding: " ^Pp.string_of_ppcmds @@ C.debug_print e)
      end

    | _ -> raise @@ BadExpr ("outer: " ^Pp.string_of_ppcmds @@ C.debug_print e)
    end
  with 
    Not_found -> 
      let _ = Feedback.msg_debug (Pp.str "Unbound table lookup in:") in
      let _ = Feedback.msg_debug (Constr.debug_print e) in
      raise UnboundPrimitive

let pretty env sigma e = 
  pretty_expr @@ EConstr.to_constr sigma e 

let debug_lib_refs _ = 
  let lib_ref_names = List.map fst (Coqlib.get_lib_refs ()) in
    Pp.pr_sequence Pp.str lib_ref_names


type query_opts = 
  { refute_query : bool ;
    negate_toplevel : bool ;
  }

let build_bv_query (vars: string list) (e: C.t) (opts: query_opts) : string = 
  let q_str = if opts.refute_query then 
    Format.sprintf "(assert (not %s))" (pretty_expr e) 
  else
    if opts.negate_toplevel then
      Format.sprintf "(assert (not %s))" @@ Smt.gen_binders (List.length vars) (pretty_expr e)
    else 
      Format.sprintf "(assert %s)" @@ Smt.gen_binders (List.length vars) (pretty_expr e) in
  Smt.gen_bv_query q_str 

let build_env_query (e: C.t) (opts: query_opts) : string = 
  let q_str = if opts.refute_query then 
    Format.sprintf "(assert (not %s))" (pretty_expr e) 
  else
    if opts.negate_toplevel then
      Format.sprintf "(assert (not %s))" @@ Smt.gen_binders 0 (pretty_expr e)
    else 
      Format.sprintf "(assert %s)" @@ Smt.gen_binders 0 (pretty_expr e) in
  let ctor_decls = Seq.map (fun (s, srt) -> (s, pretty_sort srt)) @@ Hashtbl.to_seq_values env_ctor_tbl in
    Smt.gen_env_query q_str ctor_decls

let dump_query (vars: string list) (e: EConstr.t) : unit = 
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let opts = { refute_query = true; negate_toplevel = false; } in
  let query = build_env_query (EConstr.to_constr sigma e) opts in
    Feedback.msg_info (Pp.str query)

let rec extract_foralls (e: C.t) : string list * C.t = 
  begin match C.kind e with
  | C.Prod(nme, _, bod) -> 
    let (nms, bod') = extract_foralls bod in 
    Pp.string_of_ppcmds (Names.Name.print (Context.binder_name nme)) :: nms, bod'
  | _ -> ([], e)
  end

let rec check_interp (e: C.t) (negate_toplevel: bool) : string = 
  if C.isApp e then 
    let (f, es) = C.destApp e in
    if C.equal f c_prop_not then 
      check_interp (a_last es) (not negate_toplevel)
    else 
      let (n, _) = C.destConst f in 
      let name = Names.Constant.to_string n in 
      if name = "Poulet4.P4automata.FirstOrder.interp_fm" then
        let opts = { refute_query = false; negate_toplevel = negate_toplevel; } in
        let bod' = a_last es in
          build_env_query bod' opts
      else
        raise @@ BadExpr "Expected negate or interp at interp toplevel"
  else
    if not @@ C.isProd e then raise bedef else
    let (_, bod) = extract_foralls e in
    let (f, es) = C.destApp bod in 
    let (n, _) = C.destConst f in 
    let name = Names.Constant.to_string n in 
    if name = "Poulet4.P4automata.FirstOrder.interp_fm" then
      let opts = { refute_query = false; negate_toplevel = negate_toplevel; } in
      let bod' = a_last es in
        build_env_query bod' opts 
    else
      raise bedef



