val split_last : 'a list -> ('a list * 'a) option

val get_coq : string -> Constr.t

val fetch_const : Constr.t -> Constr.t option
val fetch_const_type : Constr.t -> Constr.t option

exception MissingGlobConst of string

val opt_sequence : 'a option list -> 'a list option