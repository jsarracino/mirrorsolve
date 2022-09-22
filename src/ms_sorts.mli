type srt_smt = 
  | Smt_bv of int option
  | Smt_int
  | Smt_bool 
  | Custom_sort of string

val repair_sort : srt_smt -> srt_smt
val valid_sort : srt_smt -> bool * string
val pretty_sort : srt_smt -> string


val sort_names : (Constr.t, string) Hashtbl.t

val get_current_sorts : unit -> (Constr.t * string) Seq.t
val add_sort : Constr.types -> string option -> unit
val print_sorts_decl : unit -> string
val add_sorts_decl : unit -> unit
val add_interp_decl : unit -> unit

val exec_cmd : string -> unit
