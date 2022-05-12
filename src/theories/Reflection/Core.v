
Require Export MetaCoq.Template.All.
(* Require Import MetaCoq.Checker.All. *)

Require Import MetaCoq.Template.Checker.

Definition eq_term (l r: term) : bool := 
  @eq_term config.default_checker_flags init_graph l r.