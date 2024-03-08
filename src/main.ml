

module C = Constr
module GR = Names.GlobRef

exception BadExpr of string
exception UnboundPrimitive

let bedef = BadExpr "bad expression"

let debug_flag =
  Goptions.declare_bool_option_and_ref
    ~key:["MirrorSolve";"Debug"]
    ~value:false
    ()

let debug_pp (msg: Pp.t) : unit = 
  if debug_flag .get() then Feedback.msg_debug msg else ()
let format_args (es: C.t array) : Pp.t = 
  let eis = Array.mapi (fun i e -> (i, e)) es in
  let builder (i, e) = Pp.(++) (Pp.str (Format.sprintf "%n => " i)) (C.debug_print e) in
    Pp.pr_vertical_list builder (Array.to_list eis)

    

type ('a, 'b) sum = Inl of 'a | Inr of 'b

let a_last a = a.(Array.length a - 1)

let warn msg : unit Proofview.tactic =
  Proofview.tclLIFT (Proofview.NonLogical.make (fun () ->
  Feedback.msg_warning (Pp.str msg)))

let debug msg : unit Proofview.tactic =
  Proofview.tclLIFT (Proofview.NonLogical.make (fun () ->
  Feedback.msg_debug (Pp.str msg)))

open Util

let c_eq () = get_coq "ms.core.eq"
let c_impl () = get_coq "ms.core.impl"
let c_and () = get_coq "ms.core.and"
let c_or () = get_coq "ms.core.or"
let c_not () = get_coq "ms.core.neg"
let c_rel () = get_coq "ms.core.rel"

let c_tt () = get_coq "ms.core.tt"
let c_ff () = get_coq "ms.core.ff"
let c_fun () = get_coq "ms.core.fun"

let c_interp_fm () = get_coq "ms.core.interp_fm"

let c_wrap_hyps () = get_coq "ms.hyps.wrap_hyps"
(* let c_interp_hyps () = get_coq "ms.hyps.interp_hyps" *)
let c_interp_wh () = get_coq "ms.hyps.interp_wh"


(* Register nil as core.list.nil.
Register cons as core.list.cons. *)
let c_nil () = get_coq "core.list.nil"
let c_cons () = get_coq "core.list.cons"

let c_hnil () = get_coq "ms.core.hnil"
let c_hcons () = get_coq "ms.core.hcons"
let c_inl () = get_coq "core.sum.inl"
let c_inr () = get_coq "core.sum.inr"

let c_true () = get_coq "core.bool.true"
let c_false () = get_coq "core.bool.false"
let c_pair () = get_coq "core.prod.intro"
let c_forall () = get_coq "ms.core.forall"
let c_var () = get_coq "ms.core.var"

let c_cnil () = get_coq "ms.core.cnil"
let c_snoc () = get_coq "ms.core.csnoc"

let c_bits () = get_coq "ms.sorts.bits"
let c_store () = get_coq "ms.sorts.store"
let c_zero () = get_coq "num.nat.O"
let c_succ () = get_coq "num.nat.S"

let c_pos_one () = get_coq "num.pos.xH"
let c_pos_dzero () = get_coq "num.pos.xO"
let c_pos_done () = get_coq "num.pos.xI"

let c_int_zero () = get_coq "num.Z.Z0"
let c_int_pos () = get_coq "num.Z.Zpos"
let c_int_neg () = get_coq "num.Z.Zneg"

let c_n_zero () = get_coq "num.N.N0"
let c_n_pos () = get_coq "num.N.Npos"

let c_prop_not () = get_coq "core.not.type"

let c_bits_lit () = get_coq "ms.funs.bitslit"
let c_concat () = get_coq "ms.funs.concat"
let c_slice () = get_coq "ms.funs.slice"
let c_lookup () = get_coq "ms.funs.lookup"

let c_unit () = get_coq "core.unit.tt"

let c_vhere () = get_coq "ms.core.vhere"
let c_vthere () = get_coq "ms.core.vthere"
let c_int_sort () = get_coq "ms.core.smt_int"
let c_bool_sort () = get_coq "ms.core.smt_bool"
let c_bv_sort () = get_coq "ms.core.smt_bv"
let c_cust_sort () = get_coq "ms.core.smt_custom"

let c_si_rec = get_coq "ms.core.smt_ind_rec"
let c_si_sort = get_coq "ms.core.smt_ind_sort"
let c_si_cases = get_coq "ms.core.smt_ind_cases"

let c_bv_lit = get_coq "ms.bv.f_lit"
let c_bv_cat = get_coq "ms.bv.f_cat"
let c_bv_extr = get_coq "ms.bv.f_extr"

let c_smt_bv_ctor = get_coq "ms.bv.smt_bv_ctor"


let c_builtin_bool_lit () = get_coq "ms.core.bool_lit"
let c_builtin_int_lit () = get_coq "ms.core.int_lit"

let c_ms_fun_sym () = get_coq "ms.core.fun_sym"

let c_ufun_ctor () = get_coq "ms.uf.ufun"
let c_cfun_ctor () = get_coq "ms.uf.cfun"

let c_char_ctor = get_coq "core.ascii.ascii"

let c_str_cons = get_coq "core.string.string"
let c_str_nil = get_coq "core.string.empty"

let c_mk_smt_sig () = get_coq "ms.smt.mk_smt_sig"

let c_smt_sort_base () = get_coq "ms.core.smt_sort_base"
let c_smt_sort_ind () = get_coq "ms.core.smt_sort_ind"

let c_smt_psf () = get_coq "ms.smt.psf"
let c_smt_psr () = get_coq "ms.smt.psr"
let c_smt_psl () = get_coq "ms.smt.psl"

let c_smt_fprim () = get_coq "ms.core.fprim"
let c_smt_funinterp () = get_coq "ms.core.funinterp"

let equal_const (l: C.t) (r: C.t) : bool = 
  if C.isConst l && C.isConst r then 
    let (l', _) = C.destConst l in 
    let (r', _) = C.destConst r in 
      l' = r'
  else false

let equal_ctor (l: C.t) (r: unit -> C.t) : bool = 
  try 
    let (l', _) = C.destConstruct l in 
    let (r', _) = C.destConstruct (r ()) in 
      l' = r'
  with
    | MissingGlobConst s -> 
      let _ = Feedback.msg_debug (Pp.str @@ Format.sprintf "unbound constructor: %s" s) in 
        false
    | e -> 
      let _ = Feedback.msg_debug (Pp.str @@ Format.sprintf "couldn't compare these terms (probably one is not a constructor):") in
      let _ = Feedback.msg_debug @@ Constr.debug_print l in 
      let _ = Feedback.msg_debug @@ Constr.debug_print (r ()) in  
        raise e


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
    let _ = debug_pp @@ Pp.str "extracting int from:" in
    let _ = debug_pp @@ C.debug_print e in
    if e = c_int_zero () then 
      let _ = debug_pp @@ Pp.str "returning 0" in
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
    
let c_binnat_to_int (e: C.t) : int =
  if e = c_n_zero () then 0 
  else if C.isApp e then 
    let (f, es) = C.destApp e in 
    if f = c_n_pos () then
      c_pos_to_int (a_last es)
    else
      let _ = Feedback.msg_debug (Pp.str "Expected pos and got:") in
      let _ = Feedback.msg_debug (Constr.debug_print f) in
      raise @@ BadExpr "expected pos in binnat_to_int"
  else
    let _ = Feedback.msg_debug (Pp.str "Expected n0/npos and got:") in
    let _ = Feedback.msg_debug (Constr.debug_print e) in
    raise @@ BadExpr "expected 0 or pos in binnat_to_int"


let rec interp_digs (bs: bool list) : int = 
  begin match bs with 
  | [] -> 0
  | d :: ds -> (if d then 1 else 0) + 2 * interp_digs ds
  end

let extract_char (e: C.t) : char = 
  if C.isApp e then 
    let (f, args) = C.destApp e in 
    if f = c_char_ctor then 
      let code = interp_digs @@ Array.to_list @@ Array.map c_bool_to_bool args in 
        Char.chr code
    else
      let _ = Feedback.msg_debug (Pp.str "Expected char constructor and got") in
      let _ = Feedback.msg_debug (Constr.debug_print f) in
        raise bedef
  else
    let _ = Feedback.msg_debug (Pp.str "Expected app in char and got") in
    let _ = Feedback.msg_debug (Constr.debug_print e) in
      raise bedef

let rec extract_str_list (e: C.t) : char list = 
  if C.isApp e then 
    let (f, args) = C.destApp e in 
    if f = c_str_cons then 
      let nxt = extract_char @@ args.(Array.length args - 2) in 
        nxt :: extract_str_list (a_last args)
    else
      let _ = Feedback.msg_debug (Pp.str "Expected str cons constructor and got") in
      let _ = Feedback.msg_debug (Constr.debug_print f) in
        raise bedef
  else if C.isConstruct e then 
    if e = c_str_nil then []
    else
      let _ = Feedback.msg_debug (Pp.str "Expected str nil constructor and got") in
      let _ = Feedback.msg_debug (Constr.debug_print e) in
        raise bedef
  else
    let _ = Feedback.msg_debug (Pp.str "Expected app/construct in str and got") in
    let _ = Feedback.msg_debug (Constr.debug_print e) in
      raise bedef

let extract_str (e: C.t) : string = 
  String.of_seq @@ List.to_seq @@ extract_str_list e

let rec extract_list (inner: C.t -> 'a) (e: C.t) : 'a list =
  if C.isApp e then 
    let (f, es) = C.destApp e in 
    if equal_ctor f c_cons then
      let v = inner es.(Array.length es - 2) in
      let vs = extract_list inner (a_last es) in  
        v :: vs
    else if equal_ctor f c_nil then []
    else
      let _ = Feedback.msg_debug (Pp.str "Expected cons and got:") in
      let _ = Feedback.msg_debug (Constr.debug_print f) in
      raise @@ BadExpr "expected cons in extract_list"
  else
    let _ = Feedback.msg_debug (Pp.str "Expected nil/cons and got:") in
    let _ = Feedback.msg_debug (Constr.debug_print e) in
    raise @@ BadExpr "expected nil/cons in extract_list"

let extract_pair (l: C.t -> 'a) (r: C.t -> 'b) (x: C.t) : 'a * 'b = 
  if C.isApp x then 
    let f, es = C.destApp x in 
    if equal_ctor f c_pair then 
      l es.(Array.length es - 2), r (a_last es)
    else
      let _ = Feedback.msg_debug (Pp.str "Expected pair constructor and got:") in
      let _ = Feedback.msg_debug (Constr.debug_print f) in
      raise @@ BadExpr "expected pair constructor in extract_pair"
  else
    let _ = Feedback.msg_debug (Pp.str "Expected an app and got:") in
    let _ = Feedback.msg_debug (Constr.debug_print x) in
    raise @@ BadExpr "expected app in extract_pair"

open Ms_sorts

type func_decl = {
  arg_tys : srt_smt list;
  ret_ty : srt_smt;
  name: string;
}
let pretty_func_decl (fd: func_decl) : string = 
  let prefix = Format.sprintf "(declare-fun %s (" fd.name in 
  let args = String.concat " " @@ List.map pretty_sort fd.arg_tys in 
  let suffix = Format.sprintf ") %s)" @@ pretty_sort fd.ret_ty in 
    prefix ^ args ^ suffix

let conv_sort (e: C.t) (args: C.t Array.t) : srt_smt option = 
  if equal_ctor e c_cust_sort then Some (Custom_sort (extract_str @@ a_last args))
  else if equal_ctor e c_int_sort then Some Smt_int 
  else if equal_ctor e c_bool_sort then Some Smt_bool
  else if equal_ctor e c_bv_sort then Some (Smt_bv None)
  else 
    let _ = Feedback.msg_debug @@ Pp.str "unhandled case for:" in 
    let _ = Feedback.msg_debug @@ Constr.debug_print e in 
    None

module ConstructorMap = Map.Make ( struct
  type t = Names.constructor ;;
  let compare l r = 
    let env = Global.env() in 
    Environ.QConstruct.compare env l r
end) ;;

(* let prim_sort_tbl : (Names.constructor, srt_smt) Hashtbl.t = 
  let worker x = fst @@ C.destConstruct @@ x () in 
  Hashtbl.of_seq @@ List.to_seq @@ [
      (worker c_bv_sort, Smt_bv None)
    ; (worker c_int_sort, Smt_int)
    ; (worker c_bool_sort, Smt_bool)
  ] *)

let sort_tbl : (Names.constructor, srt_smt) Hashtbl.t = 
  Hashtbl.create 5 
  ;;
  let bv_sort = c_bv_sort() in 
  begin try
  let v, _ = C.destConstruct bv_sort in 
  Hashtbl.add sort_tbl v (Smt_bv None) with 
    | MissingGlobConst _ -> ()
    | e -> raise e
  end

let conv_srt_tbl (tbl: (Names.constructor, srt_smt) Hashtbl.t) =
  ConstructorMap.of_seq @@ Hashtbl.to_seq tbl

let init_sorts () = conv_srt_tbl @@ sort_tbl

let add_sort (e: C.t) v = 
  if C.isConstruct e then 
    let (k, _) = C.destConstruct e in 
    Hashtbl.add sort_tbl k v
  else
    let _ = Feedback.msg_debug (Pp.str "Expected construct for sort in add_sort and got:") in
    let _ = Feedback.msg_debug (Constr.debug_print e) in
      raise bedef

let custom_sorts sorts : string list = 
  let worker srt = 
    begin match srt with 
    | Custom_sort s -> Some s
    | _ -> None
    end in
  let sorts = ConstructorMap.to_seq sorts in
    List.filter_map worker (List.of_seq @@ Seq.map snd sorts)

type ind_decl = Ind_decl of (string * srt_smt list) list

(* Tests whether a ind_decl uses the sort named by name *)
let references (name: string) (id: ind_decl) : bool = 
  let Ind_decl(ctors) = id in 
  let worker (x: srt_smt) = 
    begin match x with 
    | Custom_sort s' -> s' = name
    | _ -> false
    end in 
  List.exists (fun (_, args) -> List.exists worker args) ctors

module StringMap = Map.Make ( String ) ;;
let ind_tbl : (string, ind_decl) Hashtbl.t = Hashtbl.create 5

let add_ind (name: string) (ctor: C.t) (decl: ind_decl) = 
  add_sort ctor (Custom_sort name) ;
  Hashtbl.add ind_tbl name decl

let conv_str_tbl (tbl: (string, 'a) Hashtbl.t) =
  StringMap.of_seq @@ Hashtbl.to_seq tbl

let init_inds () = conv_str_tbl ind_tbl

let pretty_ind_decl (name: string) (decl: ind_decl) = 
  let Ind_decl decls = decl in 
  let worker ctor i s : string = Format.sprintf "( proj_%s_%i %s )" ctor i (pretty_sort s) in 
  let arms = List.map 
    (fun (ctor, args) -> Format.sprintf "( %s %s)" ctor 
      (String.concat "" @@ List.mapi (worker ctor) args)
    ) 
    decls in 
  Format.sprintf "( declare-datatype %s ( \n\t\t%s \n\t) \n)" (String.capitalize_ascii name) (String.concat "\n\t\t" arms)

let debug_tbl (tbl : ('a, 'b) Hashtbl.t) (printer: 'a -> 'b -> Pp.t) : Pp.t = 
  Pp.pr_vertical_list (fun (x, y) -> printer x y) @@ List.of_seq @@ Hashtbl.to_seq tbl

let debug_constr_map (tbl : 'v ConstructorMap.t) (printer: ConstructorMap.key -> 'v -> Pp.t) : Pp.t = 
  Pp.pr_vertical_list (fun (x, y) -> printer x y) @@ List.of_seq @@ ConstructorMap.to_seq tbl

let debug_string_map (tbl : 'v StringMap.t) (printer: StringMap.key -> 'v -> Pp.t) : Pp.t = 
  Pp.pr_vertical_list (fun (x, y) -> printer x y) @@ List.of_seq @@ StringMap.to_seq tbl

type builtin_syms = 
  | Smt_int_lit
  | Smt_bool_lit
  | Smt_bv_lit

let pretty_builtin (b: builtin_syms) = 
  begin match b with 
  | Smt_int_lit -> "<int literal>"
  | Smt_bool_lit -> "<bool literal>"
  | Smt_bv_lit -> "<bv literal>"
  end

let builtin_arity (b: builtin_syms) = 
  begin match b with 
  | Smt_bv_lit
  | Smt_bool_lit
  | Smt_int_lit -> 1
  end

type printing_ctx = {
  ctx_sorts : Ms_sorts.srt_smt ConstructorMap.t ;
  ctx_inds : ind_decl StringMap.t ;
  ctx_fun_decls : func_decl StringMap.t;
  ctx_fun_symbs : string ConstructorMap.t ;
  ctx_fun_arity : int ConstructorMap.t ;
  ctx_fun_builtin : builtin_syms ConstructorMap.t ;
}

let empty_ctx = {
  ctx_sorts = ConstructorMap.empty ;
  ctx_inds = StringMap.empty ;
  ctx_fun_decls = StringMap.empty ;
  ctx_fun_symbs = ConstructorMap.empty;
  ctx_fun_arity = ConstructorMap.empty ;
  ctx_fun_builtin = ConstructorMap.empty ;
}

let debug_ctx (ctx: printing_ctx) = 
  let worker_c f = (fun (k: Names.Ind.t * int) v -> 
      Pp.(++) (Pp.(++) (C.debug_print @@ C.UnsafeMonomorphic.mkConstruct k) (Pp.str " |-> ")) (Pp.str @@ f v)
    ) in
  let worker_ind = (fun k v -> 
      Pp.(++) (Pp.(++) (Pp.str k) (Pp.str " |-> ")) (Pp.str @@ pretty_ind_decl k v)
    ) in
  let worker_fd = (fun k v -> 
      Pp.(++) (Pp.(++) (Pp.str k) (Pp.str " |-> ")) (Pp.str @@ pretty_func_decl v)
    ) in
  let _ = Feedback.msg_debug @@ Pp.str "ctx_sorts:" in 
  let _ = Feedback.msg_debug @@ debug_constr_map ctx.ctx_sorts (worker_c pretty_sort) in 
  let _ = Feedback.msg_debug @@ Pp.str "ctx_inds:" in 
  let _ = Feedback.msg_debug @@ debug_string_map ctx.ctx_inds worker_ind in 
  let _ = Feedback.msg_debug @@ Pp.str "ctx_uf_decls:" in 
  let _ = Feedback.msg_debug @@ debug_string_map ctx.ctx_fun_decls worker_fd in 
  let _ = Feedback.msg_debug @@ Pp.str "ctx_fun_symbs:" in 
  let _ = Feedback.msg_debug @@ debug_constr_map ctx.ctx_fun_symbs (worker_c (fun x -> x)) in 
  let _ = Feedback.msg_debug @@ Pp.str "ctx_fun_arity:" in 
  let _ = Feedback.msg_debug @@ debug_constr_map ctx.ctx_fun_arity (worker_c string_of_int) in 
  let _ = Feedback.msg_debug @@ Pp.str "ctx_fun_builtin:" in 
  let _ = Feedback.msg_debug @@ debug_constr_map ctx.ctx_fun_builtin (worker_c pretty_builtin) in 
    ()



let lookup_ctx_sort ctx x = ConstructorMap.find_opt x ctx.ctx_sorts
let lookup_ctx_symb ctx x = ConstructorMap.find_opt x ctx.ctx_fun_symbs
let lookup_ctx_arity ctx x = ConstructorMap.find_opt x ctx.ctx_fun_arity
let lookup_ctx_builtin ctx x = ConstructorMap.find_opt x ctx.ctx_fun_builtin


let extract_prim_sort (ctx: printing_ctx) (e: C.t) =
  if C.isConstruct e then 
    let (ctor, _) = C.destConstruct e in 
      begin match lookup_ctx_sort ctx ctor with 
      | Some x -> x
      | None ->
        let _ = Feedback.msg_debug (Pp.str "Expected sort and got:") in
        let _ = Feedback.msg_debug (Constr.debug_print e) in
        let _ = debug_ctx ctx in 
        raise @@ BadExpr "unexpected constructor for sorts (see debug)"   
      end 
  else
    let _ = Feedback.msg_debug (Pp.str "Expected construct for sort and got:") in
    let _ = Feedback.msg_debug (Constr.debug_print e) in
      raise bedef

let extract_sort (ctx: printing_ctx) (e: C.t) =
  if C.isApp e then 
    let (f, es) = C.destApp e in 
      begin match extract_prim_sort ctx f with 
      | Smt_bv None -> Smt_bv (Some (c_binnat_to_int es.(0)))
      | x -> x
      end
  else
    extract_prim_sort ctx e


let extract_ind_base (base: srt_smt) (e: C.t) = 
  let _ = debug_pp @@ Pp.str "extracting ind base from:" in
  let _ = debug_pp @@ Constr.debug_print e in  
  if C.isApp e then 
    (* SISort <sort> *)
    let f, es = C.destApp e in 
    let ctor, args = 
      if C.isApp @@ a_last es then C.destApp @@ a_last es else a_last es, [||] in 
    begin match conv_sort ctor args with 
    | Some s -> s
    | None -> 
      let _ = Feedback.msg_debug @@ Pp.str "couldn't convert sort for:" in 
      let _ = Feedback.msg_debug @@ Constr.debug_print @@ a_last es in 
      raise bedef
    end
  else
    if e = c_si_rec then base else
      let _ = Feedback.msg_debug (Pp.str "Expected smt_ind_base and got:") in
      let _ = Feedback.msg_debug (Constr.debug_print e) in
        raise bedef

let extract_ind_case (base: srt_smt) (e: C.t) : string * srt_smt list =
    (* the overall structure is string * list sort *)
  let _ = debug_pp @@ Pp.str "extracting ind case..." in 
  if C.isApp e then 
    let _, es = C.destApp e in 
    let args = extract_list (extract_ind_base base) (a_last es) in 
    let cname = extract_str (es.(Array.length es - 2)) in 
      cname, args
  else
    let _ = Feedback.msg_debug (Pp.str "Expected app in ind_case and got:") in
    let _ = Feedback.msg_debug (Constr.debug_print e) in
      raise bedef

let extract_ind_decl (base: srt_smt) (e: C.t) = 
  let _ = debug_pp @@ Pp.str "extracting ind decl..." in 
  if C.isApp e then 
    (* SICases <cases> *)
    let _, es = C.destApp e in 
    Ind_decl (extract_list (extract_ind_case base) (a_last es))
  else
    let _ = Feedback.msg_debug (Pp.str "Expected app in extract_ind_decl and got:") in
    let _ = Feedback.msg_debug (Constr.debug_print e) in
      raise bedef

(* extract a member of SMT.v:smt_sort *)
let extract_smt_srt x = 
  let f, es = C.destApp x in 
  if equal_ctor f c_smt_sort_base then 
    let inner = a_last es in 
    if C.isApp inner then 
      let f, args = C.destApp inner in
        Inl (conv_sort f args)
    else
      Inl (conv_sort inner [||])
  else if equal_ctor f c_smt_sort_ind then
    let name = extract_str es.(0) in 
    Inr (name, extract_ind_decl (Custom_sort name) @@ a_last es)
  else
    raise bedef


let load_ctx_sort (x: C.t)  = 
  let extract_ctor x = 
    if C.isConstruct x then 
      fst (C.destConstruct x)
    else raise @@ BadExpr "expected construct in extract_ctor" in
  extract_pair extract_ctor extract_smt_srt x
let load_ctx_sorts (x: C.t) = 
  let _ = debug_pp @@ Pp.str "loading ctx from:" in 
  let _ = debug_pp @@ C.debug_print x in 
    extract_list load_ctx_sort x

let add_ctx_sort_ind (ctx: printing_ctx) (kv: (ConstructorMap.key * (srt_smt option, string * ind_decl) sum)) : printing_ctx = 
  let k, ov = kv in 
  begin match ov with 
  | Inl (Some srt) -> { ctx with 
      ctx_sorts = ConstructorMap.add k srt ctx.ctx_sorts
    }
  | Inr (name, i_decl) -> { ctx with 
      ctx_sorts = ConstructorMap.add k (Custom_sort name) ctx.ctx_sorts ;
      ctx_inds = StringMap.add name i_decl ctx.ctx_inds ;
    }
  | _ -> raise bedef
  end

let extract_smt_ufun (x: C.t) = 
  let f, es = C.destApp x in
  if equal_ctor f c_smt_funinterp then 
    Some (extract_str @@ a_last es)
  else if equal_ctor f c_smt_fprim then 
    if C.isApp @@ a_last es then 
      let f', es' = C.destApp @@ a_last es in 
        if equal_ctor f' c_ms_fun_sym then 
          let _ = debug_pp @@ Pp.str "coercing to string:" in 
          let _ = debug_pp @@ C.debug_print (a_last es') in 
          let r = (extract_str @@ a_last es') in 
          let _ = debug_pp @@ Pp.(++) (Pp.str "result is:" ) (Pp.str r) in
          Some r
        else 
          None
    else
      None
  else
    None


let load_packed_sfun (x: C.t)  = 
  let _ = debug_pp @@ Pp.str "loading packed sfun (psf/psr):" in 
  let _ = debug_pp @@ C.debug_print x in 
  let f, es = C.destApp x in 
  if equal_ctor f c_smt_psf || equal_ctor f c_smt_psr then 
    Some (fst (C.destConstruct @@ a_last es))
  else if equal_ctor f c_smt_psl then 
    None
  else 
    let _ = Feedback.msg_debug @@ Pp.str "expected psf/psr/psl in load_packed_sfun" in 
    let _ = Feedback.msg_debug @@ C.debug_print f in 
    raise @@ BadExpr "bad construct in load_packed_sfun"

let load_packed_psl (x: C.t)  = 
  let _ = debug_pp @@ Pp.str "loading packed sfun (psl):" in 
  let _ = debug_pp @@ C.debug_print x in 
  let f, es = C.destApp x  in 
  if equal_ctor f c_smt_psf || equal_ctor f c_smt_psr then 
    None
  else if equal_ctor f c_smt_psl then 
    Some (fst @@ C.destConstruct @@ a_last es)
  else 
    let _ = Feedback.msg_debug @@ Pp.str "expected psf/psr/psl in load_packed_sfun" in 
    let _ = Feedback.msg_debug @@ C.debug_print f in 
    raise @@ BadExpr "bad construct in load_packed_sfun"
  


let load_packed_sfun_name (x: C.t) = 
  begin match extract_pair load_packed_sfun extract_smt_ufun x with
  | Some ctor, Some name -> Some (ctor, name)
  | _, _ -> None
  end

let load_fun_symbs (x: C.t) = 
  ConstructorMap.of_seq @@ List.to_seq @@
    List.filter_map load_packed_sfun_name @@ extract_list (fun x -> x) x

let load_packed_sfun_arity (ctx : printing_ctx) (x: C.t)  = 
  let _ = debug_pp @@ Pp.str "loading packed sfun arity:" in 
  let _ = debug_pp @@ C.debug_print x in
  let f, es = C.destApp x  in 
  if equal_ctor f c_smt_psf || equal_ctor f c_smt_psr then 
    let args = extract_list (extract_sort ctx) es.(1) in 
      Inl (fst (C.destConstruct @@ a_last es), List.length args)
  else if equal_ctor f c_smt_psl then 
      Inr (fst (C.destConstruct @@ a_last es))
  else 
    let _ = Feedback.msg_debug @@ Pp.str "expected psf/psr/psl in load_packed_sfun" in 
    let _ = Feedback.msg_debug @@ C.debug_print f in 
    raise @@ BadExpr "bad construct in load_packed_sfun"

let load_fun_decl (ctx: printing_ctx) (x: C.t) : func_decl option = 
  let l, r = extract_pair (fun x -> x) (fun x -> x) x in 
  let lf, les = C.destApp l in 
  let rf, res = C.destApp r in 
  if equal_ctor rf c_smt_funinterp then 
    let name = extract_str @@ a_last res in 
    if equal_ctor lf c_smt_psf || equal_ctor lf c_smt_psr then 
      let arg_tys = extract_list (extract_sort ctx) les.(1) in 
      let ret_ty = extract_sort ctx les.(2) in 
        Some {arg_tys; ret_ty; name}
    else
      None
  else
    None

let load_arity (ctx: printing_ctx) (x: C.t) = 
  let sfun, r = extract_pair (load_packed_sfun_arity ctx) (fun x -> x) x in 
  begin match sfun with 
  | Inl x -> x
  | Inr x -> 
    let f, es = C.destApp r in 
    if equal_ctor f c_smt_fprim then
      (x, 1)
    else
      raise @@ BadExpr "expected fprim in load arity"
  end

let load_fun_decls (ctx: printing_ctx) (x: C.t) = 
  let worker x = 
    begin match x with 
    | Some fd -> Some (fd.name, fd)
    | None -> None
    end in 
  StringMap.of_seq @@ List.to_seq @@ List.filter_map worker @@ extract_list (load_fun_decl ctx) x

let extract_builtin (x: C.t) = 
  let f, es = C.destApp x in 
  if equal_ctor f c_smt_fprim then 
    let inner = a_last es in
    if C.isConstruct inner then 
      if equal_ctor inner c_builtin_bool_lit then
        Some (Smt_bool_lit)
      else if equal_ctor inner c_builtin_int_lit then
        Some (Smt_int_lit)
      else
        None
    else
      None
  else
    None

let load_builtin (x: C.t) = 
  begin match extract_pair load_packed_psl extract_builtin x with 
  | Some x, Some y -> Some (x, y)
  | _, _ -> None
  end

let load_fun_arity (ctx: printing_ctx) (x: C.t) = 
  ConstructorMap.of_seq @@ List.to_seq @@ extract_list (load_arity ctx) x
let load_fun_builtin (ctx: printing_ctx)  (x: C.t) = 
  ConstructorMap.of_seq @@ 
    Seq.filter_map (fun x -> x) @@ 
      List.to_seq @@ extract_list load_builtin x

let rec load_ctx (x: C.t) = 
  if C.isApp x then 
    let f, args = C.destApp x in 
    if equal_ctor f c_mk_smt_sig then 
      let c_sorts = args.(Array.length args - 2) in 
      let c_funs = a_last args in 
      let sorts_inds = load_ctx_sorts c_sorts in 
      let init_ctx = List.fold_left add_ctx_sort_ind empty_ctx sorts_inds in { init_ctx with
        ctx_fun_decls = load_fun_decls init_ctx c_funs ;
        ctx_fun_symbs = load_fun_symbs c_funs;
        ctx_fun_arity = load_fun_arity init_ctx c_funs ; 
        ctx_fun_builtin = load_fun_builtin init_ctx c_funs ; 
      }
    else
      let _ = Feedback.msg_debug @@ Pp.str "unexpected smt_sig builder in load_ctx:" in
      let _ = Feedback.msg_debug @@ C.debug_print f in
      let _ = Feedback.msg_debug @@ Pp.str "actual builder is:" in
      let _ = Feedback.msg_debug @@ C.debug_print (c_mk_smt_sig () ) in
      raise bedef
  else if C.isConst x then 
    begin match Util.fetch_const x with 
    | Some x -> load_ctx x
    | None -> 
      let _ = Feedback.msg_debug @@ Pp.str "could not resolve constant??" in 
      let _ = Feedback.msg_debug @@ C.debug_print x in 
      raise @@ BadExpr "opaque constant in load_ctx"
    end
  else
    let _ = Feedback.msg_debug @@ Pp.str "unexpected ctx in load_ctx:" in
    let _ = Feedback.msg_debug @@ C.debug_print x in
    raise bedef
      
  

let fun_symb_tbl : (Names.constructor, string) Hashtbl.t = Hashtbl.create 100
let fun_arity_tbl : (Names.constructor, int) Hashtbl.t = Hashtbl.create 100
let fun_builtin_tbl : (Names.constructor, builtin_syms) Hashtbl.t = Hashtbl.create 5
let fun_decl_tbl : (string, func_decl) Hashtbl.t = Hashtbl.create 5


let init_fun_decls () = conv_str_tbl fun_decl_tbl

let init_printing_ctx () = {
  ctx_sorts = init_sorts () ;
  ctx_inds = init_inds () ;
  ctx_fun_decls = init_fun_decls ();
  ctx_fun_symbs = ConstructorMap.of_seq @@ Hashtbl.to_seq fun_symb_tbl ;
  ctx_fun_arity = ConstructorMap.of_seq @@ Hashtbl.to_seq fun_arity_tbl ;
  ctx_fun_builtin = ConstructorMap.of_seq @@ Hashtbl.to_seq fun_builtin_tbl ;
}

(* let lookup_fun_decl = Hashtbl.find_opt fun_decl_tbl *)

let add_fun (f: Names.constructor) (symb: string) (arity: int) : unit = 
  Hashtbl.add fun_symb_tbl f symb;
  Hashtbl.add fun_arity_tbl f arity

let add_builtin (f: Names.constructor) (b: builtin_syms) : unit = 
  Hashtbl.add fun_builtin_tbl f b;
  Hashtbl.add fun_arity_tbl f @@ builtin_arity b

let add_fun_decl = Hashtbl.add fun_decl_tbl

let init_concat (_: unit) =
  let (concat_symb, _) = C.destConstruct c_bv_cat in 
  add_fun concat_symb "concat" 2

let init_bv_lit (_: unit) =
  let (bv_symb, _) = C.destConstruct c_bv_lit in 
  add_builtin bv_symb Smt_bv_lit

let _ = init_concat () ;; init_bv_lit ()

(* 
let debug_tbls () = 
  Pp.pr_vertical_list (fun x -> x) @@ 
    [Pp.str "ENV CTORS:"] @ 
    Hashtbl.fold (fun ctor (sym, srt) acc -> acc @ [Pp.(++) (print_ctor ctor) (Pp.(++) (Pp.str " => ") (Pp.(++) (Pp.str sym) (Pp.str @@ Format.sprintf " : %s" (pretty_sort srt))))]) []  *)

type bop = Impl | And | Or | Eq 
type uop = Neg

type bexpr = 
  | Tru | Fls
  | Bop of bop * bexpr * bexpr
  | Uop of uop * bexpr
  | Forall of string * srt_smt * bexpr
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

let pretty_bv (e: C.t) : string =
  let _ = debug_pp @@ Pp.str "extracting bv literal with arg" in
  let _ = debug_pp @@ C.debug_print e in 
  begin match C.kind e with 
  | C.App(f, es) -> 
    if f = c_smt_bv_ctor then 
      (* argument 1 is a list of bools *)
      Pp.string_of_ppcmds @@ print_bools @@ extract_list c_bool_to_bool es.(1)
    else  
      let _ = debug_pp @@ Pp.str "unrecognized function argument for bv arg" in
      let _ = debug_pp @@ C.debug_print f in 
        raise bedef
  | _ -> 
    let _ = debug_pp @@ Pp.str "unrecognized kind for bv arg" in
      raise bedef
  end

let pretty_builtin (args: C.t array) (b: builtin_syms) (arity: int) = 
  let _ = debug_pp @@ Pp.str "printing builtin:" in 
  let _ = debug_pp @@ Pp.str (pretty_builtin b) in  
  let _ = debug_pp @@ Pp.str "and arity:" in 
  let _ = debug_pp @@ Pp.int arity in  
  let _ = debug_pp @@ Pp.str "with args:" in 
  let _ = debug_pp @@ format_args args in  
  begin match b, arity with 
  | Smt_bv_lit, 1 -> 
    pretty_bv @@ a_last args
  | Smt_int_lit, 1 -> 
    pretty_int @@ a_last args
  | Smt_bool_lit, 1 -> 
    pretty_bool @@ a_last args
  | _, _ -> 
    raise @@ BadExpr "bad builtin/arity in pretty_builtin"
  end

let rec pretty_fun (ctx: printing_ctx) (f: C.t) (args: C.t list) : string = 
  if C.isConstruct f then 
    let (f_name, _) = C.destConstruct f in 
    begin match lookup_ctx_symb ctx f_name, lookup_ctx_builtin ctx f_name, lookup_ctx_arity ctx f_name with 
    | Some fs, None, Some n ->
      if n = List.length args then
        if n = 0 then 
          fs
        else
          let pretty_args = if fs = "concat" then List.rev @@ (List.map (pretty_tm ctx) args) else (List.map (pretty_tm ctx) args) in 
          Format.sprintf "(%s %s)" fs @@ String.concat " " pretty_args
      else
        let _ = Feedback.msg_debug @@ Pp.str "mismatch in declared and actual arities for:" in 
        let _ = Feedback.msg_debug @@ Pp.str @@ Format.sprintf "%s : %i vs %i" fs n (List.length args) in 
        raise bedef
    | None, Some b, Some n -> 
      pretty_builtin [||] b n
    | None, None, _ -> 
      let _ = Feedback.msg_debug @@ Pp.str "missing fun symbol:" in 
      let _ = Feedback.msg_debug @@ Constr.debug_print f in 
      raise bedef
    (* | None, Some name, None -> *)
    | Some name, _, None -> 
        let _ = Feedback.msg_debug @@ Pp.str (Format.sprintf "missing arity for %s" name) in 
        raise bedef
    | _, _, _ -> 
        let _ = Feedback.msg_debug @@ Pp.str "odd case:" in 
        let _ = Feedback.msg_debug @@ Constr.debug_print f in 
        raise bedef
    end
  else if C.isApp f then
    let _ = debug_pp @@ Pp.str "extracting builtin" in 
    let (f', f_args) = C.destApp f in 
    let _ = debug_pp @@ Pp.str "expecting construct:" in 
    let _ = debug_pp @@ (C.debug_print f') in 
    let (f'', _) = C.destConstruct f' in
    let _ = debug_pp @@ Pp.str "found constructor" in 
    if equal_ctor f' (fun _ -> c_bv_extr) then 
      let _ = debug_pp @@ Pp.str "extracting slice with args" in
      let _ = debug_pp @@ format_args @@ Array.of_list args in
      (* n hi lo *)
      let hi = c_binnat_to_int @@ f_args.(Array.length f_args - 2) in 
      let lo = c_binnat_to_int @@ a_last f_args in 
      let inner = pretty_tm ctx @@ List.nth args 0 in 
        Format.sprintf "((_ extract %n %n) %s)" hi lo inner
    else if equal_ctor f' c_ufun_ctor then
      (* handle uninterpreted fun *)
      let f_name = f_args.(Array.length f_args - 4) in 
      let name = extract_str f_name in 
      begin match Hashtbl.find_opt fun_decl_tbl name with 
      | Some fdecl -> 
        let arity = List.length fdecl.arg_tys in 
        if arity = 0 then name else 
          Format.sprintf "(%s %s)" name @@ String.concat " " @@ List.map (pretty_tm ctx) args
      | _ -> 
        let _ = debug_pp @@ Pp.str @@ Format.sprintf "missing uf definition for %s" name in
        let _ = Feedback.msg_debug @@ Pp.str "ufs:" in 
        let _ = Feedback.msg_debug @@ debug_tbl fun_decl_tbl @@ 
          (fun k v -> 
            Pp.(++) (Pp.(++) (Pp.str k) (Pp.str " |-> ")) (Pp.str @@ pretty_func_decl v)
          ) in 
        raise bedef
      end
    else if equal_ctor f' c_cfun_ctor then 
      (* recurse on interior for concrete functions *)
      pretty_fun ctx (a_last f_args) args
    else 
      begin match lookup_ctx_symb ctx f'', lookup_ctx_builtin ctx f'', lookup_ctx_arity ctx f'' with 
      | None, Some sym, Some n -> pretty_builtin f_args sym n
      | Some fs, None, Some n -> 
        if n = List.length args then
          if n = 0 then 
            fs
          else
            let pretty_args = if fs = "concat" then List.rev @@ (List.map (pretty_tm ctx) args) else (List.map (pretty_tm ctx) args) in 
            Format.sprintf "(%s %s)" fs @@ String.concat " " pretty_args
        else
          raise bedef
      | _, _, _ -> 
        let _ = debug_pp @@ Pp.str "did not find a matching symb/builtin for the constructor" in 
          raise bedef
      end
  else 
    let _ = debug_pp @@ Pp.str "unexpected function interior:" in
    let _ = debug_pp @@ C.debug_print f in
    raise bedef
and pretty_tm (ctx: printing_ctx) (tm: C.t) : string = 
  let _ = debug_pp @@ Pp.str "extracting tm:" in
  let _ = debug_pp @@ (Constr.debug_print tm) in
  if C.isApp tm then 
    let (f, es) = C.destApp tm in 
      if equal_ctor f c_fun then 
        let _ = debug_pp @@ Pp.str "extracting fun with args:" in
        let _ = debug_pp @@ format_args es in
        let fargs = extract_h_list (a_last es) in
        let _ = debug_pp @@ Pp.str "extracted args to:" in 
        let _ = debug_pp @@ format_args (Array.of_list fargs) in 
        let fe = es.(Array.length es - 2) in 
        pretty_fun ctx fe fargs
      else if equal_ctor f c_var then 
        let _ = debug_pp @@ Pp.str "extracting var" in
        let suff = debruijn_idx (a_last es) in
          Format.sprintf "fvar_%n" suff
      else
        raise bedef
  else 
    raise bedef

  
let rec pretty_fm (ctx: printing_ctx) (e: C.t) : string =
  try
    begin match C.kind e with 
    | C.App(f, es) -> 
      if equal_ctor f c_eq then 
        let _ = debug_pp @@ Pp.str "extracting eq" in
        let a1, a2 = pretty_tm ctx es.(Array.length es - 2), pretty_tm ctx (a_last es) in
          Format.sprintf "(= %s %s)" a1 a2
      else if equal_ctor f c_impl then 
        let _ = debug_pp @@ Pp.str "extracting impl" in
        let a1, a2 = pretty_fm ctx es.(Array.length es - 2), pretty_fm ctx (a_last es) in
          Format.sprintf "(=> %s %s)" a1 a2
      else if equal_ctor f c_and then 
        (* bunch of junk, l, r *)
        let _ = debug_pp @@ Pp.str "extracting and" in
        let l, r = pretty_fm ctx es.(Array.length es - 2), pretty_fm ctx (a_last es) in 
          Format.sprintf "(and %s %s)" l r
      else if equal_ctor f c_or then 
        (* bunch of junk, l, r *)
        let _ = debug_pp @@ Pp.str "extracting or" in
        let l = pretty_fm ctx es.(Array.length es - 2) in 
        let r = pretty_fm ctx (a_last es) in 
          Format.sprintf "(or %s %s)" l r
      else if equal_ctor f c_not then 
        (* bunch of junk, inner *)
        let _ = debug_pp @@ Pp.str "extracting not" in
          Format.sprintf "(not %s)" (pretty_fm ctx (a_last es))
      else if equal_ctor f c_rel then 
        let _ = debug_pp @@ Pp.str "extracting a relation:" in
        let _ = debug_pp @@ C.debug_print f in 
        let _ = debug_pp @@ Pp.str "with args:" in 
        let _ = debug_pp @@ format_args es in
        let fargs = extract_h_list (a_last es) in
        let _ = debug_pp @@ Pp.str "extracted args to:" in 
        let _ = debug_pp @@ format_args (Array.of_list fargs) in 
        let fe = es.(Array.length es - 2) in 
        pretty_fun ctx fe fargs

      else if equal_ctor f c_tt then 
        let _ = debug_pp @@ Pp.str "extracting true" in
        "true" 
      else if equal_ctor f c_ff then 
        let _ = debug_pp @@ Pp.str "extracting false" in
        "false" 
      else if equal_ctor f c_forall then
        let _ = debug_pp @@ Pp.str "extracting forall" in
        let v_sort = repair_sort @@ extract_sort ctx es.(2) in
        let sort_ok, sort_warning = valid_sort v_sort in 
        if not sort_ok then 
          let _ = Feedback.msg_debug @@ Pp.(++) (Pp.str "WARNING: invalid sort, ") (Pp.str sort_warning) in 
          let _ = Feedback.msg_debug @@ Pp.str @@ pretty_sort v_sort in 
          pretty_fm ctx (a_last es) 
        else 
          let v_suff = List.length (extract_ctx es.(1)) in
          let v_name = Format.sprintf "fvar_%n" v_suff in
          let bod = pretty_fm ctx (a_last es) in
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

let pretty env sigma sorts e = 
  pretty_fm sorts @@ EConstr.to_constr sigma e 

let debug_lib_refs _ = 
  let lib_ref_names = List.map fst (Coqlib.get_lib_refs ()) in
    Pp.pr_sequence Pp.str lib_ref_names


type query_opts = 
  { refute_query : bool ;
    negate_toplevel : bool ;
    hyps :  C.t list ;
  }

let in_map k mp = 
  begin match StringMap.find_opt mp k with 
  | Some _ -> true
  | None -> false
  end

(* graph for strings *)
let add_dependent_edges (g: Ms_graph.str_graph) (lhs: string) (inds: ind_decl StringMap.t) = 
  let dep_decls = StringMap.filter (fun s ind -> s <> lhs && references lhs ind) inds in 
    Seq.fold_left (fun g' (s, _) -> Ms_graph.add_edge g' lhs s) g (StringMap.to_seq dep_decls)

(* topologically sort inds to make sure that no inductives have undefined references *)
let order_inds (inds: ind_decl StringMap.t) (names: string list) : string list = 
  let init_graph = Ms_graph.empty in 
  let with_nodes = List.fold_left Ms_graph.add_node init_graph names in 
  let with_edges = List.fold_left (fun g x -> add_dependent_edges g x inds) with_nodes names in
    Ms_graph.topo_sort with_edges

let extract_interp_fm (e: C.t) : C.t option  = 
  let _ = debug_pp @@ Pp.str "Extracting interp_fm from:" in 
  let _ = debug_pp @@ Constr.debug_print e in 
  if C.isApp e then 
    let (f, es) = C.destApp e in 
    let _ = debug_pp @@ Pp.str "Inspecting f for interp_fm?" in 
    let _ = debug_pp @@ Constr.debug_print f in 
    if equal_const f (c_interp_fm ()) then 
      Some (a_last es)
    else raise bedef
  else raise bedef

let extract_interp_fm_err e = 
  begin match extract_interp_fm e with 
  | Some x -> x
  | None -> raise bedef
  end
  
let build_query (ctx: printing_ctx) (opts: query_opts) (e: C.t)  : string = 
  let ind_sorts, us_sorts = List.partition (in_map ctx.ctx_inds) @@ custom_sorts ctx.ctx_sorts in 
  let us_decls = List.map (fun s -> Format.sprintf "(declare-sort %s 0)" s) us_sorts in 
  let ind_decls = List.map (fun s -> pretty_ind_decl s (StringMap.find s ctx.ctx_inds)) (order_inds ctx.ctx_inds ind_sorts) in 
  let fun_decls = List.map pretty_func_decl @@ List.map snd @@ List.of_seq @@ StringMap.to_seq @@ ctx.ctx_fun_decls in 
  let assumpts = List.map (fun x -> Format.sprintf "(assert %s)" (pretty_fm ctx x)) opts.hyps in
  let prefix = String.concat "\n" @@ us_decls @ ind_decls @ fun_decls @ assumpts in 
  let q_str = if opts.refute_query then 
    Format.sprintf "(assert (not %s))" (pretty_fm ctx e) 
  else
    Format.sprintf "(assert %s)" (pretty_fm ctx e) in 
  Smt.gen_bv_query (String.concat "\n" [prefix; q_str])

let dump_query ?(hyps: C.t list = []) (ctx: printing_ctx) (e: EConstr.t) : unit = 
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let opts = { refute_query = true; negate_toplevel = false; hyps = hyps} in
  let query = build_query ctx opts (EConstr.to_constr sigma e) in
    Feedback.msg_info (Pp.str query)

let rec check_interp ?(ctx_e  = None) ?(hyps: C.t list = []) (e: C.t) (negate_toplevel: bool) : string = 
  let ctx = 
    begin match ctx_e with 
    | Some ctx_e -> load_ctx ctx_e
    | None -> init_printing_ctx () 
    end in 
  if C.isApp e then 
    let (f, es) = C.destApp e in
    if C.equal f @@ c_prop_not () then 
      check_interp ~ctx_e (a_last es) (not negate_toplevel)
    else 
      let (n, _) = C.destConst f in 
      let name = Names.Constant.to_string n in 
      if name = "MirrorSolve.FirstOrder.interp_fm" then
        let opts = { refute_query = negate_toplevel; negate_toplevel = negate_toplevel; hyps = hyps } in
        let bod' = a_last es in
          build_query ctx opts bod'
      else
        let _ = Feedback.msg_debug (Pp.str "unrecognized name: ") in 
        let _ = Feedback.msg_debug @@ Pp.str name in 
        raise @@ BadExpr "Expected negate or interp at interp toplevel"
  else
    raise bedef


let extract_hyps (e: C.t) : (C.t list * C.t) option = 
  let _ = debug_pp @@ Pp.str "Extracting hyps from:" in 
  let _ = debug_pp @@ Constr.debug_print e in 
  let (f, es) = C.destApp e in 
  let _ = debug_pp @@ Pp.str "Symb is:" in 
  let _ = debug_pp @@ Constr.debug_print f in 
  if f = c_wrap_hyps () then 
    begin match Util.opt_sequence (extract_list extract_interp_fm es.(Array.length es - 2)) with 
    | Some hyp_es -> Some (hyp_es, a_last es)
    | None -> 
      let _ = debug_pp @@ Pp.str "Interior of hyps did not parse as list of interp_fm?" in 
      let _ = debug_pp @@ Constr.debug_print es.(Array.length es - 2) in 
      None
    end
  else
    None

let check_interp_wrapped_hyps ?(ctx_e = None) (e: C.t) : string = 
  let (f, es) = C.destApp e in 
  if f = c_interp_wh () then 
    begin match extract_hyps (a_last es) with 
    | Some (hyps, goal) -> 
      check_interp ~ctx_e ~hyps goal true
    | None -> 
      let _ = Feedback.msg_debug (Pp.str "couldn't extract hyps: ") in 
      let _ = Feedback.msg_debug @@ C.debug_print (a_last es) in 
      raise @@ BadExpr "couldn't extract hyps in check_interp_hyps"
    end
  else
    raise bedef



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
      let _ = Feedback.msg_warning (Pp.(++) (Pp.str ("Unrecognized construct: ")) @@ Constr.debug_print r') in
      raise bedef
  else
    let _ = Feedback.msg_warning (Pp.(++) (Pp.str ("Expected construct and got: ")) @@ Constr.debug_print l') in
    raise bedef

let reg_sort (l: EConstr.t) (r: EConstr.t) : unit = 
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let le = EConstr.to_constr sigma l in 
  let re = EConstr.to_constr sigma r in 
    begin match conv_sort re [||] with 
    | Some x -> add_sort le x
    | None -> raise bedef
    end

let reg_custom_sort (e: EConstr.t) (name: string) : unit = 
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let e' = EConstr.to_constr sigma e in 
    add_sort e' (Custom_sort name)


(* let rec all_some (xs: 'a option list) : 'a list option = 
  begin match xs with 
  | [] -> Some []
  | Some x :: xs' -> 
    begin match all_some xs with 
    | Some xs'' -> Some (x :: xs'')
    | None -> None
    end
  | None :: _ -> None
  end *)

let reg_uf_decl (name: string) (ret_e: EConstr.t) (args: EConstr.t list) : unit = 
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let force = EConstr.to_constr sigma in 
  let r_e = force ret_e in 
  let args_e = List.map force args in 
  let ctx = init_printing_ctx () in 
  try 
    let r_ty, args_ty = extract_sort ctx r_e, List.map (extract_sort ctx) args_e in  
      add_fun_decl name {arg_tys = args_ty; ret_ty = r_ty; name = name}
  with
    | e -> 
      let _ = Feedback.msg_warning (Pp.(++) (Pp.str ("Could not convert UF sorts in ")) @@ Constr.debug_print r_e) in
      let _ = Feedback.msg_warning @@ format_args (Array.of_list args_e) in raise e

let reg_ind_decl (name: string) (ctor_e: EConstr.t) (ind_decl_e : EConstr.t) : unit = 
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let ind_e = EConstr.to_constr sigma ind_decl_e in 
  let ctor = EConstr.to_constr sigma ctor_e in 
  let _ = debug_pp @@ Pp.str "extracting decl now" in 
  let decl = extract_ind_decl (Custom_sort name) ind_e in 
  add_ind name ctor decl

let load_printing_ctx (x: C.t) = 
  let ctx = load_ctx x in 
  let _ = debug_pp @@ Pp.str "loading ctx:" in 
  let _ = debug_ctx ctx in 
  let _ = Hashtbl.add_seq sort_tbl @@ ConstructorMap.to_seq ctx.ctx_sorts in 
  let _ = Hashtbl.add_seq ind_tbl @@ StringMap.to_seq ctx.ctx_inds in 
  let _ = Hashtbl.add_seq fun_decl_tbl @@ StringMap.to_seq ctx.ctx_fun_decls in
  let _ = Hashtbl.add_seq fun_symb_tbl @@ ConstructorMap.to_seq ctx.ctx_fun_symbs in 
  let _ = Hashtbl.add_seq fun_arity_tbl @@ ConstructorMap.to_seq ctx.ctx_fun_arity in 
  let _ = Hashtbl.add_seq fun_builtin_tbl @@ ConstructorMap.to_seq ctx.ctx_fun_builtin in 
  ()
