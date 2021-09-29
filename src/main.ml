

module C = Constr
module GR = Names.GlobRef

exception BadExpr of string
exception UnboundPrimitive

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
let c_state1_name = "p4a.funs.state1"
let c_state2_name = "p4a.funs.state2"
let c_hcons_name = "p4a.core.hcons"

let c_hnil_name = "p4a.core.hnil"
let c_conflit_name = "p4a.funs.conf_lit"
let c_statelit_name = "p4a.funs.state_lit"

let c_inl_name = "p4a.core.inl"
let c_inr_name = "p4a.core.inr"

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

type sort = 
  Bits of int | 
  Store

(* type valu = BitsLit of bool list *)

type bop = Impl | And | Or
type uop = Neg

type bexpr = 
  | Tru | Fls
  | Bop of bop * bexpr * bexpr
  | Uop of uop * bexpr


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
      Format.sprintf "(inl %s)" (Hashtbl.find constr_sym_tbl (fst (C.destConstruct es'.(2))))
    else
      raise @@ BadExpr ("missing state constructor: " ^ (Pp.string_of_ppcmds (C.debug_print es'.(2)))) 
  else if op_name = c_inr_name then 
    if C.equal c_true es.(2) then "(inr true)" 
    else if C.equal c_false es.(2) then "(inr false)" 
    else
      raise @@ BadExpr ("bad inr argument: " ^ (Pp.string_of_ppcmds (C.debug_print es.(2)))) 
  else 
    raise @@ BadExpr ("expected inl/inr and got : " ^ (Pp.string_of_ppcmds (C.debug_print f)))

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
let rec c_nat_to_int (e: C.t) : int =
  if C.equal e c_zero then 0 
  else if C.isApp e then 
    let (f, es) = C.destApp e in 
    if C.equal f c_succ then
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
   
let format_args (es: C.t array) : Pp.t = 
  let eis = Array.mapi (fun i e -> (i, e)) es in
  let builder (i, e) = Pp.(++) (Pp.str (Format.sprintf "%n => " i)) (C.debug_print e) in
  Pp.pr_vertical_list builder (Array.to_list eis)
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

let pretty_key (e: C.t) : string = 
  let _ = Feedback.msg_debug @@ Pp.str "Key expression:" in
  let _ = Feedback.msg_debug @@ C.debug_print e in
  "TODO_KEY"
  
let str_starts_with pref s = 
  if String.length pref > String.length s then false
  else
    String.sub s 0 (String.length pref) = pref
let debug_flag = false

(* let debug_print (f: unit -> unit) : unit = 
  if debug_flag then f () else () *)

let debug_pp (msg: Pp.t) : unit = 
  if debug_flag then Feedback.msg_debug msg else ()

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
            if fname = c_state1_name then 
              let _ = debug_pp @@ Pp.str "extracting state1 fun" in
              let arg = List.hd fargs in Format.sprintf "(state1 %s)" (pretty_expr arg) 
            else if fname = c_state2_name then 
              let _ = debug_pp @@ Pp.str "extracting state2 fun" in
              let arg = List.hd fargs in Format.sprintf "(state2 %s)" (pretty_expr arg) 
            else if str_starts_with "#b" fname then 
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
          else if op_name' = c_state1_name then 
            let _ = debug_pp @@ Pp.str "extracting state1" in
            c_state1_name 
          else if op_name' = c_state2_name then 
            let _ = debug_pp @@ Pp.str "extracting state2" in
            c_state2_name
          (* (_ extract m n) *)
          else if op_name' = c_slice_name then 
            let _ = debug_pp @@ Pp.str "extracting slice" in
            (* n hi lo *)
            let hi = c_nat_to_int es.(1) in 
            let lo = c_nat_to_int es.(2) in 
            Format.sprintf "(_ extract %n %n)" hi lo
          else if op_name' = c_concat_name then 
            let _ = debug_pp @@ Pp.str "extracting concat" in
            (* n m *)
            c_concat_name
            
          else if op_name' = c_conflit_name then 
            let _ = debug_pp @@ Pp.str "extracting mk_conf_lit" in
            Format.sprintf "(mk_conf_lit %s)" (c_e_to_conf (a_last es)) 
          else if op_name' = c_statelit_name then 
            let _ = debug_pp @@ Pp.str "extracting statelit" in
            (* let _ = debug_pp (Pp.str @@ Format.sprintf "length of args: %n" (Array.length es)) in *)
            (c_e_to_ind es.(6))
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
      begin match Hashtbl.find_opt constr_sym_tbl x, Hashtbl.find_opt prim_tbl x with
      | Some _, Some _ -> raise @@ BadExpr ("double ctor binding: " ^Pp.string_of_ppcmds @@ C.debug_print e)
      | Some r, _ -> r
        
      | _, Some r -> r
      | None, None -> raise @@ BadExpr ("missing ctor binding: " ^Pp.string_of_ppcmds @@ C.debug_print e)
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

let build_query (vars: string list) (e: C.t) (opts: query_opts) : string = 
  let q_str = if opts.refute_query then 
    Format.sprintf "(assert (not %s))" (pretty_expr e) 
  else
    if opts.negate_toplevel then
      Format.sprintf "(assert (not %s))" @@ Smt.gen_binders (List.length vars) (pretty_expr e)
    else 
      Format.sprintf "(assert %s)" @@ Smt.gen_binders (List.length vars) (pretty_expr e) in
  Smt.gen_bv_query q_str 

let dump_query (vars: string list) (e: EConstr.t) : unit = 
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let opts = { refute_query = true; negate_toplevel = false; } in
  let query = build_query vars (EConstr.to_constr sigma e) opts in
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
          build_query [] bod' opts
      else
        raise @@ BadExpr "Expected negate or interp at interp toplevel"
  else
    if not @@ C.isProd e then raise bedef else
    let (names, bod) = extract_foralls e in
    let (f, es) = C.destApp bod in 
    let (n, _) = C.destConst f in 
    let name = Names.Constant.to_string n in 
    if name = "Poulet4.P4automata.FirstOrder.interp_fm" then
      let opts = { refute_query = false; negate_toplevel = negate_toplevel; } in
      let bod' = a_last es in
        build_query names bod' opts 
    else
      raise bedef


