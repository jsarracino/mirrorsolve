open Hints

open Ltac_plugin
open Tacexpr
open Tacinterp
open Names

let ltac_lcall tac args =
  let (location, name) = Loc.tag (Names.Id.of_string tac)
    (* Loc.tag @@ Names.Id.of_string tac *)
  in
  CAst.make ?loc:location (Tacexpr.TacArg(Tacexpr.TacCall
                              (CAst.make (Locus.ArgVar (CAst.make ?loc:location name),args))))
let ltac_apply (f : Value.t) (args: Tacinterp.Value.t list) =
  let fold arg (i, vars, lfun) =
    let id = Names.Id.of_string ("x" ^ string_of_int i) in
    let (l,n) = (Loc.tag id) in
    let x = Reference (Locus.ArgVar (CAst.make ?loc:l n)) in
    (succ i, x :: vars, Id.Map.add id arg lfun)
  in
  let (_, args, lfun) = List.fold_right fold args (0, [], Id.Map.empty) in
  let lfun = Id.Map.add (Id.of_string "F") f lfun in
  let ist = { (Tacinterp.default_ist ()) with Tacinterp.lfun = lfun; } in
  Tacinterp.eval_tactic_ist ist (ltac_lcall "F" args)

let to_ltac_val c = Tacinterp.Value.of_constr c

let apply_hint (f: Value.t) (hints: FullHint.t list) : unit Proofview.tactic = 
  let acts = 
    (* Feedback.msg_debug @@ Pp.str "hints:" ;  *)
    List.map (fun full_hint ->
      begin match FullHint.repr full_hint with
      | Res_pf x
      | ERes_pf x
      | Give_exact x
      | Res_pf_THEN_trivial_fail x -> 
        let (_, hint_eterm) = Hints.hint_as_term x in 
        let foo = to_ltac_val hint_eterm in 
          ltac_apply f [foo]
      | _ -> 
        let _ = Feedback.msg_warning @@ Pp.str "unrecognized hint" in 
        Proofview.tclUNIT ()
      end
    ) hints in 
  List.fold_left (fun a acc -> Proofview.tclTHEN a acc) (Proofview.tclUNIT ()) acts

let apply_hints f tbl : unit Proofview.tactic = 
  Hint_db.fold (fun _ _ x acc -> Proofview.tclTHEN (apply_hint f x) acc) tbl (Proofview.tclUNIT ())

let lookup_tbl (name: string) : hint_db = Hints.searchtable_map name

let pretty_hints (f: Constr.t -> string) (tbl: hint_db) : string = 
  let pretty_full_hint (x: FullHint.t) = 
    begin match FullHint.repr x with
      | Res_pf x
      | ERes_pf x
      | Give_exact x
      | Res_pf_THEN_trivial_fail x -> 
        let (_, hint_eterm) = Hints.hint_as_term x in 
        let env = Global.env () in
        let sigma = Evd.from_env env in
        let e = Util.fetch_const_type (EConstr.to_constr sigma hint_eterm) in 
        begin match e with 
        | Some e -> 
          let _ = Feedback.msg_debug (Pp.str "adding as an assumption: ") in 
          let _ = Feedback.msg_debug @@ Constr.debug_print e in 
            f e
        | None -> 
          let _ = Feedback.msg_warning @@ Pp.str "unrecognized hint type:" in
          let _ = Feedback.msg_debug @@ Constr.debug_print (EConstr.to_constr sigma hint_eterm) in 
          ""
        end
      | _ -> 
        let _ = Feedback.msg_warning @@ Pp.str "unrecognized hint" in ""
      end in
  let worker _ _ fhs acc = 
    let prefix = acc ^ "\n" in 
    prefix ^ String.concat "\n" (List.map pretty_full_hint fhs)
  in 
  Hint_db.fold worker tbl ""


(* let debug_hint_tbl name = 
  searchtable_map *)