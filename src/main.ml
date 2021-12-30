

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

let get_coq ref : C.t = 
  try 
    let gref = Coqlib.lib_ref ref in
    let env = Global.env () in
    let sigma = Evd.from_env env in
    let sigma', evd = EConstr.fresh_global env sigma gref in 
      EConstr.to_constr sigma' evd
  with e ->
    let lib_refs = Coqlib.get_lib_refs () in 
    let needle = List.find_opt (fun (name, _) -> name = ref) lib_refs in
      begin match needle with 
      | Some (_, x) -> raise @@ MissingGlobConst ("polymorphic global: " ^ ref)
      | None -> raise @@ MissingGlobConst ("unregistered global: " ^ ref)
      end
let c_eq () = get_coq "p4a.core.eq"
let c_impl () = get_coq "p4a.core.impl"
let c_and () = get_coq "p4a.core.and"
let c_or () = get_coq "p4a.core.or"
let c_not () = get_coq "p4a.core.neg"

let c_tt () = get_coq "p4a.core.tt"
let c_ff () = get_coq "p4a.core.ff"
let c_fun () = get_coq "p4a.core.fun"

let c_hnil () = get_coq "p4a.core.hnil"
let c_hcons () = get_coq "p4a.core.hcons"
let c_inl () = get_coq "core.sum.inl"
let c_inr () = get_coq "core.sum.inr"

let c_true () = get_coq "core.bool.true"
let c_false () = get_coq "core.bool.false"
let c_pair () = get_coq "core.prod.intro"
let c_forall () = get_coq "p4a.core.forall"
let c_var () = get_coq "p4a.core.var"

let c_cnil () = get_coq "p4a.core.cnil"
let c_snoc () = get_coq "p4a.core.csnoc"

let c_bits () = get_coq "p4a.sorts.bits"
let c_store () = get_coq "p4a.sorts.store"
let c_zero () = get_coq "num.nat.O"
let c_succ () = get_coq "num.nat.S"

let c_pos_one () = get_coq "num.pos.xH"
let c_pos_dzero () = get_coq "num.pos.xO"
let c_pos_done () = get_coq "num.pos.xI"

let c_int_zero () = get_coq "num.Z.Z0"
let c_int_pos () = get_coq "num.Z.Zpos"
let c_int_neg () = get_coq "num.Z.Zneg"

let c_prop_not () = get_coq "core.not.type"

let c_bits_lit () = get_coq "p4a.funs.bitslit"
let c_concat () = get_coq "p4a.funs.concat"
let c_slice () = get_coq "p4a.funs.slice"
let c_lookup () = get_coq "p4a.funs.lookup"

let c_unit () = get_coq "core.unit.tt"

let c_vhere () = get_coq "p4a.core.vhere"
let c_vthere () = get_coq "p4a.core.vthere"
let c_int_sort = get_coq "p4a.core.smt_int"
let c_bool_sort = get_coq "p4a.core.smt_bool"

let c_builtin_bool_lit () = get_coq "p4a.core.bool_lit"
let c_builtin_int_lit () = get_coq "p4a.core.int_lit"


let find_add i tbl builder = 
  begin match Hashtbl.find_opt tbl i with 
  | Some x -> x
  | None -> 
    let nxt = builder () in 
    Hashtbl.add tbl i nxt;
    nxt
  end

let prim_tbl' : (C.t, string) Hashtbl.t = Hashtbl.create 20
let reg_prim' i t = find_add i prim_tbl' (fun _ -> t)

(* let c_char_to_char (e: C.t) : string 
let rec c_str_to_str (e: C.t) : string = 
  if e = c_str_nil () then ""
  else if C.isApp e then
    let (f, es) = C.destApp e in 
    if f = c_str_cons () then
      1 + c_nat_to_int (a_last es) *)

let c_bool_to_bool (e: C.t) : bool = 
  if e = c_true () then true
  else if e = c_false () then false
  else raise bedef

let rec c_nat_to_int (e: C.t) : int =
  if e = c_zero () then 0 
  else if C.isApp e then 
    let (f, es) = C.destApp e in 
    if f = c_succ () then
      1 + c_nat_to_int (a_last es)
    else
      let _ = Feedback.msg_debug (Pp.str "S:") in
      let _ = Feedback.msg_debug (Constr.debug_print @@ c_succ ()) in
      let _ = Feedback.msg_debug (Pp.str "Expected S and got:") in
      let _ = Feedback.msg_debug (Constr.debug_print e) in
      raise @@ BadExpr "expected S in nat_to_int"
  else
    let _ = Feedback.msg_debug (Pp.str "S:") in
    let _ = Feedback.msg_debug (Constr.debug_print @@ c_succ ()) in
    let _ = Feedback.msg_debug (Pp.str "Z:") in
    let _ = Feedback.msg_debug (Constr.debug_print @@ c_zero ()) in
    let _ = Feedback.msg_debug (Pp.str "Expected S/Z and got:") in
    let _ = Feedback.msg_debug (Constr.debug_print e) in
    raise @@ BadExpr "expected S or 0 in nat_to_int"

let rec c_pos_to_int (e: C.t) : int = 
  if e = c_pos_one () then 1
  else 
    let (f, es) = C.destApp e in
    let inner = c_pos_to_int @@ a_last es in 
    if f = c_pos_dzero () then 2 * inner 
    else if f = c_pos_done () then 2*inner + 1
    else raise bedef

  let c_int_to_int (e: C.t) : int =
    if e = c_int_zero () then 
      let _ = Feedback.msg_debug (Pp.str "returning 0") in
      0 
    else if C.isApp e then 
      let (f, es) = C.destApp e in 
      let inner = c_pos_to_int @@ a_last es in 
      if f = c_int_pos () then inner
      else if f = c_int_neg () then -1 * inner 
      else
        let _ = Feedback.msg_debug (Pp.str "Expected Pos/Neg and got:") in
        let _ = Feedback.msg_debug (Constr.debug_print f) in
        raise @@ BadExpr "expected pos/neg in int_to_int"
    else
      let _ = Feedback.msg_debug (Pp.str "Expected int constructor and got:") in
      let _ = Feedback.msg_debug (Constr.debug_print e) in
      raise @@ BadExpr "expected int constructor in int_to_int"
    

type sort = 
  | Bits of int
  | Smt_int
  | Smt_bool 


let sort_tbl : (C.t, sort) Hashtbl.t = Hashtbl.create 5

let lookup_sort (e: C.t) : sort option = Hashtbl.find_opt sort_tbl e
let add_sort = Hashtbl.add sort_tbl

(* assumes that sorts are always apps (even nullary sorts) *)
let extract_sort (e: C.t) : sort = 
  begin match lookup_sort e with 
  | Some x -> x
  | None ->
    let _ = Feedback.msg_debug (Pp.str "Expected sort and got:") in
    let _ = Feedback.msg_debug (Constr.debug_print e) in
    raise @@ BadExpr "unexpected constructor for sorts (see debug)"   
  end   
  
  (* if not @@ C.isApp e then 
    let _ = Feedback.msg_debug (Pp.str "Expected app for sort and got:") in
    let _ = Feedback.msg_debug (Constr.debug_print e) in
    raise @@ BadExpr "expected app for sort" 
  else
    let (f, es) = C.destApp e in 
    begin match lookup_sort f with 
    | Some x -> x
    | None ->
      let _ = Feedback.msg_debug (Pp.str "Expected sort and got:") in
      let _ = Feedback.msg_debug (Constr.debug_print f) in
      raise @@ BadExpr "unexpected constructor for sorts (see debug)"   
    end    *)

let equal_ctor (l: C.t) (r: unit -> C.t) : bool = 
  let (l', _) = C.destConstruct l in 
  let (r', _) = C.destConstruct (r ()) in 
    l' = r'

let valid_sort (s: sort) : bool = 
  begin match s with 
  | Bits n -> n > 0
  | Smt_int 
  | Smt_bool -> true
  end
let pretty_sort (s: sort) : string = 
  begin match s with 
  | Bits n -> Format.sprintf "(_ BitVec %n)" n
  | Smt_int -> "Int"
  | Smt_bool -> "Bool"
  end
  
type builtin_syms = 
  | Smt_int_lit
  | Smt_bool_lit

let pretty_builtin (b: builtin_syms) = 
  begin match b with 
  | Smt_int_lit -> "<int literal>"
  | Smt_bool_lit -> "<bool literal>"
  end

let builtin_arity (b: builtin_syms) = 
  begin match b with 
  | Smt_bool_lit
  | Smt_int_lit -> 1
  end

let fun_symb_tbl : (Names.constructor, string) Hashtbl.t = Hashtbl.create 100
let fun_arity_tbl : (Names.constructor, int) Hashtbl.t = Hashtbl.create 100
let fun_builtin_tbl : (Names.constructor, builtin_syms) Hashtbl.t = Hashtbl.create 5


let lookup_symb = Hashtbl.find_opt fun_symb_tbl
let lookup_arity = Hashtbl.find_opt fun_arity_tbl
let lookup_builtin = Hashtbl.find_opt fun_builtin_tbl

let add_fun (f: Names.constructor) (symb: string) (arity: int) : unit = 
  Hashtbl.add fun_symb_tbl f symb;
  Hashtbl.add fun_arity_tbl f arity

let add_builtin (f: Names.constructor) (b: builtin_syms) : unit = 
  Hashtbl.add fun_builtin_tbl f b;
  Hashtbl.add fun_arity_tbl f @@ builtin_arity b

(* 
let debug_tbls () = 
  Pp.pr_vertical_list (fun x -> x) @@ 
    [Pp.str "ENV CTORS:"] @ 
    Hashtbl.fold (fun ctor (sym, srt) acc -> acc @ [Pp.(++) (print_ctor ctor) (Pp.(++) (Pp.str " => ") (Pp.(++) (Pp.str sym) (Pp.str @@ Format.sprintf " : %s" (pretty_sort srt))))]) []  *)

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
    Pp.surround @@ Pp.pr_sequence bop_formatter [Inl o; Inr l; Inr r]
  | Uop (Neg, i) -> Pp.surround @@ join [Pp.str "not"; pretty_bexpr i]
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
let rec extract_h_list (e: C.t) : C.t list = 
  let (f, args) = C.destApp e in 
  if equal_ctor f c_hnil then [] 
  else if equal_ctor f c_hcons then 
    (* A B a as h t *)
    args.(Array.length args - 2) :: extract_h_list (a_last args) 
  else
    let _ = Feedback.msg_debug (Pp.str (Format.sprintf "unexpected symbol in hlist:")) in
    let _ = Feedback.msg_debug (C.debug_print e) in
      raise @@ BadExpr "unexpected symbol in hlist"

let rec extract_ctx (e: C.t) : C.t list = 
  let (f, es) = C.destApp e in 
  if equal_ctor f c_cnil then []
  else if equal_ctor f c_snoc then 
    a_last es :: extract_ctx es.(1)
  else
    let _ = Feedback.msg_debug (Pp.str (Format.sprintf "Expected snoc/nil and got:")) in
    let _ = Feedback.msg_debug (Constr.debug_print e) in
    raise @@ BadExpr "expected csnoc/cnil inside ctx list"

let rec c_n_tuple_to_bools (e: C.t) : bool list =
  if e = c_unit () then []
  
  else if C.isApp e then 
    let (f, es) = C.destApp e in 
    if equal_ctor f c_pair then
      let snoc_e = a_last es in 
      let snoc_v = c_bool_to_bool snoc_e in 
      c_n_tuple_to_bools es.(Array.length es - 2) @ [snoc_v]
    else
      let _ = Feedback.msg_debug (Pp.str "pair:") in
      let _ = Feedback.msg_debug (Constr.debug_print @@ c_pair ()) in
      let _ = Feedback.msg_debug (Pp.str "Expected pair and got:") in
      let _ = Feedback.msg_debug (Constr.debug_print f) in
      raise @@ BadExpr "expected pair in tuple2bool"
  else
    let _ = Feedback.msg_debug (Pp.str "pair:") in
    let _ = Feedback.msg_debug (Constr.debug_print @@ c_pair ()) in
    let _ = Feedback.msg_debug (Pp.str "Expected pair and got:") in
    let _ = Feedback.msg_debug (Constr.debug_print e) in
    raise @@ BadExpr "expected app/pair in tuple2bool"

let print_bools (bs: bool list) : Pp.t = 
  Pp.(++) (Pp.str "#b") (Pp.prlist (fun b -> Pp.str (if b then "1" else "0")) bs)

let rec debruijn_idx (e: C.t) : int = 
  let (f, es) = C.destApp e in 
  if equal_ctor f c_vhere then 
    List.length @@ extract_ctx es.(Array.length es - 2) 
  else if equal_ctor f c_vthere then 
    debruijn_idx (a_last es)
  else 
    let _ = Feedback.msg_debug (Pp.str "Unexpected constructor in debruijn variable:") in
    let _ = Feedback.msg_debug (C.debug_print e) in
      raise bedef

let format_args (es: C.t array) : Pp.t = 
  let eis = Array.mapi (fun i e -> (i, e)) es in
  let builder (i, e) = Pp.(++) (Pp.str (Format.sprintf "%n => " i)) (C.debug_print e) in
    Pp.pr_vertical_list builder (Array.to_list eis)

let debug_flag = true

(* let debug_print (f: unit -> unit) : unit = 
  if debug_flag then f () else () *)

let debug_pp (msg: Pp.t) : unit = 
  if debug_flag then Feedback.msg_debug msg else ()

let rec extract_expr (e: C.t) : bexpr = 
  if equal_ctor e c_eq then
    let (e1, e2) = rec_bop e in 
      Bop (Eq, e1, e2)
  else if equal_ctor e c_impl then
    let (e1, e2) = rec_bop e in 
      Bop (Impl, e1, e2)
  else if equal_ctor e c_and then  
    let (e1, e2) = rec_bop e in 
      Bop (And, e1, e2)
  else if equal_ctor e c_or then  
    let (e1, e2) = rec_bop e in 
      Bop (Or, e1, e2)
  else if equal_ctor e c_not then  
    Uop (Neg, rec_unop e)
  else
    assert false
and
  rec_bop (e: C.t) : bexpr * bexpr = 
    let (_, es) = C.destApp e in 
      extract_expr es.(Array.length es - 2), extract_expr (a_last es)
and
  rec_unop (e: C.t) : bexpr = 
    let (_, es) = C.destApp e in 
      extract_expr (a_last es)

let pretty_bool (e: C.t) : string = 
  let b = c_bool_to_bool e in
  string_of_bool b

let pretty_int (e: C.t) : string = 
  let x = c_int_to_int e in
  string_of_int x

let pretty_builtin (args: C.t array) (b: builtin_syms) (arity: int) = 
  let _ = debug_pp @@ Pp.str "printing builtin:" in 
  let _ = debug_pp @@ Pp.str (pretty_builtin b) in  
  let _ = debug_pp @@ Pp.str "with args:" in 
  let _ = debug_pp @@ format_args args in  
  begin match b, arity with 
  | Smt_int_lit, 1 -> 
    pretty_int @@ a_last args
  | Smt_bool_lit, 1 -> 
    pretty_bool @@ a_last args
  | _, _ -> raise bedef
  end

let rec pretty_fun (f: C.t) (args: C.t list) : string = 
  if C.isConstruct f then 
    let (f_name, _) = C.destConstruct f in 
    begin match lookup_symb f_name, lookup_builtin f_name, lookup_arity f_name with 
    | Some fs, None, Some n ->
      if n = List.length args then
        if n = 0 then 
          fs
        else
          Format.sprintf "(%s %s)" fs @@ String.concat " " (List.map pretty_tm args)
      else
        raise bedef
    | None, Some b, Some n -> 
      pretty_builtin [||] b n
    | _, _, _ -> raise bedef
    end
  else if C.isApp f then
    let _ = debug_pp @@ Pp.str "extracting builtin" in 
    let (f', f_args) = C.destApp f in 
    let _ = debug_pp @@ Pp.str "expecting construct:" in 
    let _ = debug_pp @@ (C.debug_print f') in 
    let (f'', _) = C.destConstruct f' in
    let _ = debug_pp @@ Pp.str "found constructor" in 
    begin match lookup_builtin f'', lookup_arity f'' with 
    | Some sym, Some n -> pretty_builtin f_args sym n
    | _, _ -> raise bedef
    end
  else
    let _ = debug_pp @@ Pp.str "expected construct for fun symbol, instead got:" in
    let _ = debug_pp @@ (C.debug_print f) in
    raise bedef


    (* if C.isApp fe then
      let (f', args') = C.destApp fe in 
        if equal_ctor f' c_concat then
          let _ = debug_pp @@ Pp.str "extracting concat fun" in
          begin match fargs with 
          | l :: r :: _ -> 
            (* The concatenation order in smtlib2 is suffix-then-prefix. *)
            Format.sprintf "(concat %s %s)" (pretty_expr r) (pretty_expr l)
          | _ -> raise bedef
          end
        else if equal_ctor f' c_slice then 
          let _ = debug_pp @@ Pp.str "extracting slice" in
          (* n hi lo *)
          let hi = c_nat_to_int es'.(Array.length es' - 2) in 
          let lo = c_nat_to_int (a_last es') in 
          Format.sprintf "((_ extract %n %n) %s)" hi lo (pretty_expr @@ List.hd fargs)
        else if equal_ctor f' c_lookup then 
          let _ = debug_pp @@ Pp.str "extracting lookup fun" in
          Format.sprintf "(%s %s)" (pretty_key (a_last es')) (pretty_expr @@ List.hd fargs)
        else if equal_ctor f' c_bits_lit then 
          let _ = debug_pp @@ Pp.str "extracting bitslit" in
          Pp.string_of_ppcmds @@ print_bools @@ c_n_tuple_to_bools @@ (a_last es')
        else 
          let _ = debug_pp @@ Pp.str "unexpected function symbol:" in
          let _ = debug_pp @@ C.debug_print f' in
          raise bedef
    else 
      let _ = debug_pp @@ Pp.str "unexpected function interior:" in
      let _ = debug_pp @@ C.debug_print f in
      raise bedef *)
and pretty_tm (tm: C.t) : string = 
  let _ = debug_pp @@ Pp.str "extracting tm:" in
  let _ = debug_pp @@ (Constr.debug_print tm) in
  if C.isApp tm then 
    let (f, es) = C.destApp tm in 
      if equal_ctor f c_fun then 
        let _ = debug_pp @@ Pp.str "extracting fun with args:" in
        let _ = debug_pp @@ format_args es in
        let fargs = extract_h_list (a_last es) in
        let fe = es.(Array.length es - 2) in 
        pretty_fun fe fargs
      else if equal_ctor f c_var then 
        let _ = debug_pp @@ Pp.str "extracting var" in
        let suff = debruijn_idx (a_last es) in
          Format.sprintf "fvar_%n" suff
      else
        raise bedef
  else 
    raise bedef

  
let rec pretty_fm (e: C.t) : string =
  try
    begin match C.kind e with 
    | C.App(f, es) -> 
      if equal_ctor f c_eq then 
        let _ = debug_pp @@ Pp.str "extracting eq" in
        let a1, a2 = pretty_tm es.(Array.length es - 2), pretty_tm (a_last es) in
          Format.sprintf "(= %s %s)" a1 a2
      else if equal_ctor f c_impl then 
        let _ = debug_pp @@ Pp.str "extracting impl" in
        let a1, a2 = pretty_fm es.(Array.length es - 2), pretty_fm (a_last es) in
          Format.sprintf "(=> %s %s)" a1 a2
      else if equal_ctor f c_and then 
        (* bunch of junk, l, r *)
        let _ = debug_pp @@ Pp.str "extracting and" in
        let l, r = pretty_fm es.(Array.length es - 2), pretty_fm (a_last es) in 
          Format.sprintf "(and %s %s)" l r
      else if equal_ctor f c_or then 
        (* bunch of junk, l, r *)
        let _ = debug_pp @@ Pp.str "extracting or" in
        let l = pretty_fm es.(Array.length es - 2) in 
        let r = pretty_fm (a_last es) in 
          Format.sprintf "(or %s %s)" l r
      else if equal_ctor f c_not then 
        (* bunch of junk, inner *)
        let _ = debug_pp @@ Pp.str "extracting not" in
          Format.sprintf "(not %s)" (pretty_fm (a_last es))

      else if equal_ctor f c_tt then 
        let _ = debug_pp @@ Pp.str "extracting true" in
        "true" 
      else if equal_ctor f c_ff then 
        let _ = debug_pp @@ Pp.str "extracting false" in
        "false" 
      else if equal_ctor f c_forall then
        let _ = debug_pp @@ Pp.str "extracting forall" in
        let v_sort = extract_sort es.(2) in
        if not (valid_sort v_sort) then pretty_fm (a_last es) 
        else 
          let v_suff = List.length (extract_ctx es.(1)) in
          let v_name = Format.sprintf "fvar_%n" v_suff in
          let bod = pretty_fm (a_last es) in
            Format.sprintf "(forall ((%s %s)) %s)" v_name (pretty_sort v_sort) bod
          
      else 
        let _ = Feedback.msg_debug (Pp.str "unrecognized fm symbol: ") in 
        let _ = Feedback.msg_debug @@ C.debug_print f in 
          raise @@ BadExpr ("missing ctor binding")

    | _ -> raise @@ BadExpr ("outer: " ^Pp.string_of_ppcmds @@ C.debug_print e)
    end
  with 
    Not_found -> 
      let _ = Feedback.msg_debug (Pp.str "Unbound table lookup in:") in
      let _ = Feedback.msg_debug (Constr.debug_print e) in
      raise UnboundPrimitive

let pretty env sigma e = 
  pretty_fm @@ EConstr.to_constr sigma e 

let debug_lib_refs _ = 
  let lib_ref_names = List.map fst (Coqlib.get_lib_refs ()) in
    Pp.pr_sequence Pp.str lib_ref_names


type query_opts = 
  { refute_query : bool ;
    negate_toplevel : bool ;
  }

let build_query (vars: string list) (e: C.t) (opts: query_opts) : string = 
  let q_str = if opts.refute_query then 
    Format.sprintf "(assert (not %s))" (pretty_fm e) 
  else
    if opts.negate_toplevel then
      Format.sprintf "(assert (not %s))" @@ Smt.gen_binders (List.length vars) (pretty_fm e)
    else 
      Format.sprintf "(assert %s)" @@ Smt.gen_binders (List.length vars) (pretty_fm e) in
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
    if C.equal f @@ c_prop_not () then 
      check_interp (a_last es) (not negate_toplevel)
    else 
      let (n, _) = C.destConst f in 
      let name = Names.Constant.to_string n in 
      if name = "MirrorSolve.FirstOrder.interp_fm" then
        let opts = { refute_query = false; negate_toplevel = negate_toplevel; } in
        let bod' = a_last es in
          build_query [] bod' opts
      else
        let _ = Feedback.msg_debug (Pp.str "unrecognized name: ") in 
        let _ = Feedback.msg_debug @@ Pp.str name in 
        raise @@ BadExpr "Expected negate or interp at interp toplevel"
  else
    if not @@ C.isProd e then raise bedef else
    let (vs, bod) = extract_foralls e in
    let (f, es) = C.destApp bod in 
    let (n, _) = C.destConst f in 
    let name = Names.Constant.to_string n in 
    if name = "MirrorSolve.FirstOrder.interp_fm" then
      let opts = { refute_query = false; negate_toplevel = negate_toplevel; } in
      let bod' = a_last es in
        build_query vs bod' opts 
    else
      raise bedef



let set_backend_solver name = 
  let open Smt in 
  let solver = 
    begin match name with 
    | "z3" -> Some Z3
    | "cvc4" -> Some CVC4
    | "boolector" -> Some Boolector
    | _ -> None
    end
  in
  begin match solver with 
  | Some s -> set_solver s
  | None -> 
    let _ = Feedback.msg_warning (Pp.str ("Unrecognized solver name: " ^ name)) in
      Feedback.msg_warning (Pp.str "Expected z3/cvc4/boolector")
  end

let reg_sym (e: EConstr.t) (sym: string) (ar: int) : unit = 
  let env = Global.env () in 
  let sigma = Evd.from_env env in 
  let e' = EConstr.to_constr sigma e in 
  if C.isConstruct e' then
    let (f, _) = C.destConstruct e' in 
    add_fun f sym ar
  else
    raise bedef

let reg_builtin (l: EConstr.t) (r: EConstr.t) : unit = 
  let env = Global.env () in 
  let sigma = Evd.from_env env in 
  let l' = EConstr.to_constr sigma l in 
  let r' = EConstr.to_constr sigma r in 
  if C.isConstruct l' then
    let (f, _) = C.destConstruct l' in 
    if equal_ctor r' c_builtin_bool_lit then
      add_builtin f Smt_bool_lit
    else if equal_ctor r' c_builtin_int_lit then
      add_builtin f Smt_int_lit
    else
      raise bedef
  else
    raise bedef

let conv_sort (e: C.t) : sort option = 
  if equal_ctor e (fun _ -> c_int_sort) then Some Smt_int 
  else if equal_ctor e (fun _ -> c_bool_sort) then Some Smt_bool
  else None

let reg_sort (l: EConstr.t) (r: EConstr.t) : unit = 
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let le = EConstr.to_constr sigma l in 
  let re = EConstr.to_constr sigma r in 
    begin match conv_sort re with 
    | Some x -> add_sort le x
    | None -> raise bedef
    end
