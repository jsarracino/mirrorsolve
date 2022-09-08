val split_last : 'a list -> ('a list * 'a) option

val get_coq : string -> Constr.t

val fetch_const : Constr.t -> Constr.t option

exception MissingGlobConst of string