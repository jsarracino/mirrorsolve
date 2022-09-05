exception BadExpr of string
exception UnboundPrimitive

val bedef : exn

val warn : string -> unit Proofview.tactic
val debug: string -> unit Proofview.tactic

val c_inl : unit -> Constr.t
val c_inr : unit -> Constr.t
val c_bits : unit -> Constr.t
val c_store : unit -> Constr.t
val c_bits_lit : unit -> Constr.t
val c_concat : unit -> Constr.t
val c_slice : unit -> Constr.t
val c_lookup : unit -> Constr.t

val c_nat_to_int : Constr.t -> int


val c_si_sort : Constr.t
val c_si_cases : Constr.t

val reg_sort : EConstr.constr -> EConstr.constr -> unit
val reg_sym : EConstr.constr -> string -> int -> unit
val reg_builtin : EConstr.constr -> EConstr.constr -> unit
val reg_uf_decl : string -> EConstr.constr -> EConstr.constr list -> unit
val reg_custom_sort : EConstr.constr -> string -> unit

(* sum of constructor names and sort products *)
type ind_decl = Ind_decl of (string * Ms_sorts.srt_smt list) list

type func_decl = {
  arg_tys : Ms_sorts.srt_smt list;
  ret_ty : Ms_sorts.srt_smt;
  name: string;
}

module SortTbl : (Map.S with type key = Names.constructor)

val init_sorts : unit -> Ms_sorts.srt_smt SortTbl.t

(* Map.Make ( struct
  type t = Names.constructor ;;
  let compare l r = 
    let env = Global.env() in 
    Environ.QConstruct.compare env l r
end) ;; *)

(* val uf_sym_tbl : (string, func_decl) Hashtbl.t
val lookup_uf : string -> func_decl option
val add_uf : string -> func_decl -> unit *)

type bop = Impl | And | Or | Eq 
type uop = Neg

type bexpr = 
  | Tru | Fls
  | Bop of bop * bexpr * bexpr
  | Uop of uop * bexpr
  | Forall of string * Ms_sorts.srt_smt * bexpr
  | App of string * (bexpr list)
  | TSym of string


val extract_expr : Constr.t -> bexpr
val pretty_bexpr : bexpr -> Pp.t

val pretty_fm : Ms_sorts.srt_smt SortTbl.t -> Constr.t -> string
val pretty: Environ.env -> Evd.evar_map -> Ms_sorts.srt_smt SortTbl.t -> EConstr.constr -> string

val debug_lib_refs : unit -> Pp.t

type query_opts = 
  { refute_query : bool ;
    negate_toplevel : bool ;
  }

val build_query : Constr.t -> query_opts -> string
val dump_query : EConstr.t -> unit
val check_interp : Constr.t -> bool -> string
val extract_ctx : Constr.t -> Constr.t list

val pretty_func_decl : func_decl -> string

val print_bools : bool list -> Pp.t
val c_n_tuple_to_bools : Constr.t -> bool list
val format_args : Constr.t array -> Pp.t

val set_backend_solver : string -> unit
val set_smt_language : string -> unit

val reg_ind_decl : string -> EConstr.t -> EConstr.t -> unit