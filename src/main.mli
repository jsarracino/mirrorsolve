exception BadExpr of string
exception UnboundPrimitive

val bedef : exn

val warn : string -> unit Proofview.tactic
val debug: string -> unit Proofview.tactic

val get_coq : string -> Constr.t

val c_inl : unit -> Constr.t
val c_inr : unit -> Constr.t
val c_bits : unit -> Constr.t
val c_store : unit -> Constr.t
val c_bits_lit : unit -> Constr.t
val c_concat : unit -> Constr.t
val c_slice : unit -> Constr.t
val c_lookup : unit -> Constr.t

val c_nat_to_int : Constr.t -> int

val reg_sort : EConstr.constr -> EConstr.constr -> unit
val reg_fun : EConstr.constr -> string -> int -> unit

type sort = 
  Bits of int | 
  SMT_Int

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

val pretty_fm : Constr.t -> string
val pretty: Environ.env -> Evd.evar_map -> EConstr.constr -> string

val debug_lib_refs : unit -> Pp.t

val reg_prim_name': Constr.t -> string -> unit

type query_opts = 
  { refute_query : bool ;
    negate_toplevel : bool ;
  }

val build_query : string list -> Constr.t -> query_opts -> string
val dump_query : string list -> EConstr.t -> unit
val check_interp : Constr.t -> bool -> string
val extract_ctx : Constr.t -> Constr.t list
val pretty_sort : sort -> string

val print_bools : bool list -> Pp.t
val c_n_tuple_to_bools : Constr.t -> bool list
val format_args : Constr.t array -> Pp.t

val set_backend_solver : string -> unit