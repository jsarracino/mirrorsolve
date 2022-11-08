open Hints

(* val print_hints : hint_db -> unit *)

val ltac_apply : Ltac_plugin.Tacinterp.value -> Ltac_plugin.Tacinterp.value list -> unit Proofview.tactic
val to_ltac_val : EConstr.t -> Ltac_plugin.Tacinterp.value

val lookup_tbl : string -> hint_db

val apply_hints : Ltac_plugin.Tacinterp.value -> hint_db -> unit Proofview.tactic

val pretty_hints : (Constr.t -> string) -> hint_db -> string

