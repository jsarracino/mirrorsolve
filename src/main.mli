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

val references : string -> ind_decl -> bool 

type func_decl = {
  arg_tys : Ms_sorts.srt_smt list;
  ret_ty : Ms_sorts.srt_smt;
  name: string;
}

type builtin_syms = 
  | Smt_int_lit
  | Smt_bool_lit
  | Smt_bv_lit

module ConstructorMap : (Map.S with type key = Names.constructor)
module StringMap : (Map.S with type key = string)

type printing_ctx = {
  ctx_sorts : Ms_sorts.srt_smt ConstructorMap.t ;
  ctx_inds : ind_decl StringMap.t;
  ctx_fun_decls : func_decl StringMap.t;
  ctx_fun_symbs : string ConstructorMap.t ;
  ctx_fun_arity : int ConstructorMap.t ;
  ctx_fun_builtin : builtin_syms ConstructorMap.t ;
}

val init_printing_ctx : unit -> printing_ctx
val init_sorts : unit -> Ms_sorts.srt_smt ConstructorMap.t

val lookup_ctx_sort : printing_ctx -> ConstructorMap.key -> Ms_sorts.srt_smt option
val lookup_ctx_symb : printing_ctx -> ConstructorMap.key -> string option
val lookup_ctx_arity : printing_ctx -> ConstructorMap.key -> int option
val lookup_ctx_builtin : printing_ctx -> ConstructorMap.key -> builtin_syms option



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

val pretty_fm : printing_ctx -> Constr.t -> string
val pretty: Environ.env -> Evd.evar_map -> printing_ctx -> EConstr.constr -> string

val debug_lib_refs : unit -> Pp.t

type query_opts = 
  { refute_query : bool ;
    negate_toplevel : bool ;
  }

val build_query : printing_ctx -> query_opts -> Constr.t -> string
val dump_query : printing_ctx -> EConstr.t -> unit
val check_interp : ?ctx_e: Constr.t option -> Constr.t -> bool -> string
val extract_ctx : Constr.t -> Constr.t list

val pretty_func_decl : func_decl -> string

val print_bools : bool list -> Pp.t
val c_n_tuple_to_bools : Constr.t -> bool list
val format_args : Constr.t array -> Pp.t

val set_smt_language : string -> unit

val reg_ind_decl : string -> EConstr.t -> EConstr.t -> unit

val load_printing_ctx : Constr.t -> unit