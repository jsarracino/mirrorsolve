exception BadExpr of string

val bedef : exn

val warn : string -> unit Proofview.tactic
val debug: string -> unit Proofview.tactic

val get_coq : string -> Constr.t

val ceq : Constr.t -> Constr.t -> bool

(* val c_tru : Names.GlobRef.t *)
(* val c_tru : Constr.t
val c_fls : Constr.t *)
(* val c_impl : Constr.t
val c_and : Constr.t
val c_or : Constr.t
val c_neg : Constr.t *)

type bop = Impl | And | Or
type uop = Neg

type bexpr = 
  | Tru | Fls
  | Bop of bop * bexpr * bexpr
  | Uop of uop * bexpr

val pretty_expr : Constr.t -> string
val pretty: Environ.env -> Evd.evar_map -> EConstr.constr -> string

val debug_lib_refs : unit -> Pp.t
val debug_tbls : unit -> Pp.t

val reg_coq_sort_size : Constrexpr.constr_expr -> int -> unit
val reg_coq_ind_constr : Constrexpr.constr_expr -> unit
val reg_prim_name : Constrexpr.constr_expr -> string -> unit

val build_query : string list -> Constr.t -> bool -> string
val dump_query : string list -> EConstr.t -> unit
val check_interp : Constr.t -> string