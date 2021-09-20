

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
        | Some (_, x) -> raise @@ MissingGlobConst ref
        | None -> raise @@ MissingGlobConst ref
        end

(* let c_tru = get_coq "mirrorsolve.bexpr.t.tru"
let c_fls = get_coq " mirrorsolve.bexpr.t.fls" *)
(* 
let c_lit = get_coq "p4a.fo_bv.funs.bool_lit"
let c_tt = get_coq "coq.init.bool.tt"
let c_ff = get_coq "coq.init.bool.ff" *)
(* let c_impl = get_coq "p4a.fo_bv.core.fimpl" *)
(* let c_and = get_coq "p4a.fo_bv.core.fand"
let c_or = get_coq "p4a.fo_bv.core.for"
let c_neg = get_coq "p4a.fo_bv.core.fneg" *)

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
    Hashtbl.fold (fun ctor sym acc -> acc @ [Pp.(++) (print_ctor ctor) (Pp.(++) (Pp.str " => ") (Pp.str sym))]) constr_sym_tbl [] 

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
let rec pretty_expr (e: C.t) : string =
  (* let (gr, u) = Constr.destRef e in *)
  (* if C.equal e c_tru then "TT"
  else if C.equal e c_fls then "FF"
  else if C.equal e c_fls then "FF"
  else if C.equal e c_and then "FF"
  else if C.equal e c_fls then "FF" *)
  begin match C.kind e with 
  | C.App(f, es) -> 
    begin match C.kind f with 
    | C.Const (x, _) -> 
      let name = Names.Constant.to_string x in 
      let args = Array.map pretty_expr es in
      begin match name with 
      | "Poulet4.P4automata.FirstOrder.FImpl" -> 
        begin match args with 
        | [| a1; a2 |] -> Format.sprintf "(=> %s %s)" a1 a2
        | _ -> raise @@ BadExpr "bad args to impl"
        end
      | _ -> raise @@ BadExpr ("bad constant name" ^ name)
      end
    | _ -> raise @@ BadExpr (Pp.string_of_ppcmds @@ C.debug_print f)
    end
  | C.Construct (x, _) -> Hashtbl.find constr_sym_tbl x
  | _ -> raise @@ BadExpr (Pp.string_of_ppcmds @@ C.debug_print e)
  end


  (* if C.equal e c_lit then "TT/FF"
  (* else if gr == c_fls then "FF" *)
  else "foo" *)
let pretty env sigma e = 
  pretty_expr @@ EConstr.to_constr sigma e 

let debug_lib_refs _ = 
  let lib_ref_names = List.map fst (Coqlib.get_lib_refs ()) in
    Pp.pr_sequence Pp.str lib_ref_names

