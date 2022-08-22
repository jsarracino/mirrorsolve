val split_last : 'a list -> ('a list * 'a) option

val get_coq : string -> Constr.t

exception MissingGlobConst of string