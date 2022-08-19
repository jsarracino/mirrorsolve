type srt_smt = 
  | Smt_bv of int option
  | Smt_int
  | Smt_bool 
  | Custom_sort of string

val valid_sort : srt_smt -> bool
val pretty_sort : srt_smt -> string

(* module ConstrCompare : Set.OrderedType *)

module ConstrSet : Set.S with type elt = Constr.types

val get_current_sorts : unit -> ConstrSet.t
val add_sort : Constr.types -> unit
val print_sorts_decl : unit -> string
val add_sorts_decl : unit Proofview.tactic
