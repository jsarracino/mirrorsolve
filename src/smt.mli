type solver_t = Z3 | CVC4 | Boolector
val show_solver_t : solver_t -> string
val solver : solver_t ref
val set_solver : solver_t -> unit
val get_solver : unit -> solver_t

val gen_query : string list -> string list -> string -> bool -> string
val gen_binders : int -> string -> string

val gen_bv_query : string -> string
val gen_env_query : string -> (string * string) Seq.t -> string
val gen_record_decl : string -> (string * string) Seq.t -> string

type smt_result = SAT | UNSAT | Other of string
val run_smt : string -> smt_result