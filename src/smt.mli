type solver_t = Z3 | CVC4 | Boolector | CVC5
val show_solver : solver_t -> string
val str_to_solver : string -> solver_t option

val solver : solver_t ref
val set_solver : solver_t -> unit
val get_solver : unit -> solver_t

type language_t = All | BV
val show_language : language_t -> string
val str_to_language : string -> language_t option

val language : language_t ref
val set_language : language_t -> unit
val get_language : unit -> language_t


val gen_query : string list -> string list -> string -> bool -> string
val gen_binders : int -> string -> string

val gen_bv_query : string -> string
val gen_env_query : string -> (string * string) Seq.t -> string
val gen_record_decl : string -> (string * string) Seq.t -> string

type smt_result = SAT | UNSAT | Other of string
val run_smt : string -> smt_result