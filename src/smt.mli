val gen_query : string list -> string list -> string -> bool -> string
val gen_binders : int -> string -> string

val gen_bv_query : string -> string

type smt_result = SAT | UNSAT | Other of string
val run_smt : string -> smt_result