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
val reg_sym : EConstr.constr -> string -> int -> unit
val reg_builtin : EConstr.constr -> EConstr.constr -> unit
val reg_uf_decl : string -> EConstr.constr -> EConstr.constr list -> unit
val reg_custom_sort : EConstr.constr -> string -> unit


type sort = 
  | Smt_bv of int option
  | Smt_int
  | Smt_bool 
  | Custom_sort of string

type func_decl = {
  arg_tys : sort list;
  ret_ty : sort;
  name: string;
}

(* val uf_sym_tbl : (string, func_decl) Hashtbl.t
val lookup_uf : string -> func_decl option
val add_uf : string -> func_decl -> unit *)

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

val build_query : Constr.t -> query_opts -> string
val dump_query : EConstr.t -> unit
val check_interp : Constr.t -> bool -> string
val extract_ctx : Constr.t -> Constr.t list
val pretty_sort : sort -> string

val pretty_func_decl : func_decl -> string

val print_bools : bool list -> Pp.t
val c_n_tuple_to_bools : Constr.t -> bool list
val format_args : Constr.t array -> Pp.t

val set_backend_solver : string -> unit