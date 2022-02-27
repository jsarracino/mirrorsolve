exception BadExpr of string
exception UnboundPrimitive

val bedef : exn

val warn : string -> unit Proofview.tactic
val debug: string -> unit Proofview.tactic

val get_coq : string -> Constr.t

(* val c_tru : Names.GlobRef.t *)
(* val c_tru : Constr.t
val c_fls : Constr.t *)
(* val c_impl : Constr.t
val c_and : Constr.t
val c_or : Constr.t
val c_neg : Constr.t *)

type sort = 
  Bits of int | 
  Store

type bop = Impl | And | Or | Eq 
type uop = Neg

type bexpr = 
  | Tru | Fls
  | Bop of bop * bexpr * bexpr
  | Uop of uop * bexpr
  | Forall of string * sort * bexpr
  | App of string * (bexpr list)
  | TSym of string


val extract_expr : Constr.t -> bexpr
val pretty_bexpr : bexpr -> Pp.t

val pretty_expr : Constr.t -> string
val pretty: Environ.env -> Evd.evar_map -> EConstr.constr -> string

val debug_lib_refs : unit -> Pp.t
val debug_tbls : unit -> Pp.t

val reg_prim_name': Constr.t -> string -> unit

type query_opts = 
  { refute_query : bool ;
    negate_toplevel : bool ;
  }


val build_bv_query : string list -> Constr.t -> query_opts -> string
val build_env_query : Constr.t -> query_opts -> string
val dump_query : string list -> EConstr.t -> unit
val check_interp : Constr.t -> bool -> string
val extract_ctx : Constr.t -> Constr.t list
val pretty_sort : sort -> string

val print_bools : bool list -> Pp.t
val c_n_tuple_to_bools : Constr.t -> bool list
val format_args : Constr.t array -> Pp.t
val reg_c_env_ctors : Constr.t list -> unit
val clear_env_ctors : unit -> unit

val set_backend_solver : string -> unit

val c_nat_to_int : Constr.t -> int