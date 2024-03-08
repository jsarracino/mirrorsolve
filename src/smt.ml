type solver_t = Z3 | CVC4 | Boolector | CVC5
let show_solver s = 
  begin match s with 
  | Z3 -> "z3"
  | CVC4 -> "cvc4"
  | Boolector -> "boolector"
  | CVC5 -> "cvc5"
  end

let str_to_solver s = 
  begin match s with 
  | "z3" -> Some Z3
  | "cvc4" -> Some CVC4
  | "cvc5" -> Some CVC5
  | "boolector" -> Some Boolector
  | _ -> None
  end

let opt_solver_str =
  Goptions.declare_string_option_and_ref
    ~key:["MirrorSolve";"Solver"]
    ~value:"z3"
    ()

let solver_flags_str =
  Goptions.declare_stringopt_option_and_ref
    ~key:["MirrorSolve";"Solver";"Flags"]
    ~value:None
    ()

let solver_query_debug =
  Goptions.declare_bool_option_and_ref
    ~value:false
    ~key:["MirrorSolve";"Query";"Debug"]
    ()

let get_solver () = 
  begin match str_to_solver (opt_solver_str . get()) with 
  | Some x -> x
  | None -> Z3
  end

type language_t = All | BV
let show_language l = 
  begin match l with 
  | All -> "ALL"
  | BV -> "BV"
  end
let str_to_language l = 
  begin match l with 
  | "ALL" -> Some All
  | "BV" -> Some BV
  | _ -> None
  end
  
let language = ref All

let set_language = (:=) language
let get_language _ = !language

let lang () = Printf.sprintf {|(set-logic %s)|} (show_language @@ get_language ())
let preamble = {|

(declare-datatypes ((sum 2)) 
   ((par (S U) 
    (
      (inl (left S)) 
      (inr (right U))
    )
)))

(declare-datatypes ((prod 2)) 
   ((par (S U) 
    (
      (pair (fst S) (snd S)) 
    )
)))

|}

let conf_definitions = {| 

(declare-datatypes ((config 0)) 
   ((
      (mk_config (state1 (sum auto_state Bool)) (state2 (sum auto_state Bool))) 
   ))
  )

(define-fun mk_conf_lit 
  ((x (sum auto_state Bool)) (y (sum auto_state Bool))) 
  config 
  (mk_config x y)
)

|}

let gen_enum_decl names = 
  let joined_names = String.concat "\n" (List.map (fun s -> Format.sprintf "(%s)" s) names) in
  Format.sprintf {| 

(declare-datatypes ((auto_state 0)) 
   ((
      %s
   ))
)
|} joined_names


let gen_record_decl ty decls = 
  let joined_decls = String.concat "\n" (List.map (fun (n, srt) -> Format.sprintf "(%s %s)" n srt) (List.of_seq decls)) in
  Format.sprintf {| 

(declare-datatypes ((%s 0)) 
   (((mk_%s
      %s
   )))
)
|} ty ty joined_decls

let gen_var_decls vars = 
  let decls = List.map (fun vn -> Format.sprintf "(declare-fun %s () (sum auto_state Bool))" vn) vars in
  String.concat "\n" decls
  
let trailer = {| 

(check-sat)

|}

let gen_query names vars query include_vars = 
  String.concat "\n" [
    lang ();
    preamble; 
    gen_enum_decl names; 
    conf_definitions; 
    if include_vars then gen_var_decls vars else ""; 
    query; 
    trailer;
  ]

let gen_binders len query = 
  let ty_str = "(sum auto_state Bool)" in 
  (* let len = List.length vars in *)
  let idxs = List.init len (fun i -> Format.sprintf "pvar_%n" (len - i)) in
  let binds = List.map (fun ix -> Format.sprintf "(%s %s)" ix ty_str) idxs in
  if len > 0 then
    let bind_bod = String.concat "\n" binds in
    Format.sprintf "(forall (%s) %s)" bind_bod query else

    query

let gen_bv_query query = 
  String.concat "\n" [
    lang (); 
    query; 
    trailer;
  ]

let gen_env_query query bindings = 
  String.concat "\n" [
    lang ();
    (* gen_record_decl "Env" bindings;  *)
    query; 
    trailer;
  ]

type smt_result = SAT | UNSAT | Other of string

let close_all = 
  List.iter Unix.close 

let validate_solver (s: solver_t) = 
  let open Unix in 
  try begin match system (show_solver s ^" --version") with 
    | WEXITED _ -> ()
    | _ -> 
      let _ = Feedback.msg_debug @@ Pp.(++) (Pp.str "error returning from ") (Pp.str @@ show_solver s) in 
      let _ = Feedback.msg_debug @@ Pp.(++) (Pp.str "PATH: ") (Pp.str @@ getenv "PATH") in 
      raise @@ Failure ("Bad/missing solver: " ^ show_solver s)
    end
  with Unix_error(err, _, _) -> 
    let _ = Feedback.msg_debug @@ Pp.(++) (Pp.str "error running ") (Pp.str @@ show_solver s) in 
    let _ = Feedback.msg_debug @@ Pp.(++) (Pp.str "PATH: ") (Pp.str @@ getenv "PATH") in 
    raise @@ Failure ("Bad/missing solver: " ^ show_solver s)

let make_args () = 
  begin match solver_flags_str .get() with 
  | Some x -> 
    (* Array.of_list @@ Str.split (Str.regexp "[\r\n\t ]*") x *)
    [| x |]
  | None -> [| |]
  end

let run_smt query = 
  let open Unix in


  let _ = validate_solver (get_solver ()) in 

  let query_file = Filename.temp_file "vc" ".smt2" in
  let rep_query = Str.global_replace (Str.regexp "'") "_pr" query in 
  let smt_ch = open_out query_file in
  Stdlib.output_string smt_ch rep_query ;
  Stdlib.close_out smt_ch;

  
  if solver_query_debug .get() 
    then Feedback.msg_debug @@ Pp.str (Format.sprintf "put smt query in %s" query_file)
  else ();

  let in_in, in_out = pipe ~cloexec:true () in
  let out_in, out_out = pipe ~cloexec:true () in 
  let err_in, err_out = pipe ~cloexec:true () in 

  let cmd = show_solver (get_solver ()) in
  let s_args = make_args () in 
  let s_args_str = String.concat " " (Array.to_list s_args) in 

  if solver_query_debug .get() 
    then Feedback.msg_debug @@ Pp.str (Format.sprintf "query command: %s %s" cmd s_args_str)
  else ();

  let args = Array.concat [[| cmd |]; s_args; [| query_file |]] in
  let smt_pid = create_process cmd args in_in out_out err_out in

  let _ = waitpid [] smt_pid in 
  let ln = Stdlib.input_line (in_channel_of_descr out_in) in 

  close_all [in_in; in_out; out_in; out_out; err_out; err_in];
  
  if ln = "sat" then SAT
  else if ln = "unsat" then UNSAT
  else Other ln