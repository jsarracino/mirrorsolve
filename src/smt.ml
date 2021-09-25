
let preamble = {|

(set-logic ALL)

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

let gen_adt_decl names = 
  let joined_names = String.concat "\n" (List.map (fun s -> Format.sprintf "(%s)" s) names) in
  Format.sprintf {| 

(declare-datatypes ((auto_state 0)) 
   ((
      %s
   ))
)
|} joined_names

let gen_var_decls vars = 
  let decls = List.map (fun vn -> Format.sprintf "(declare-fun %s () (sum auto_state Bool))" vn) vars in
  String.concat "\n" decls
  
let trailer = {| 

(check-sat)
(get-model)

|}

let gen_query adt_names vars query include_vars = 
  String.concat "\n" [
    preamble; 
    gen_adt_decl adt_names; 
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

type smt_result = SAT | UNSAT | Other of string


let run_smt query = 
  let open Unix in

  let query_file = Filename.temp_file "vc" ".smt2" in
  let smt_ch = open_out query_file in
  Stdlib.output_string smt_ch query ;
  Stdlib.close_out smt_ch;

  Feedback.msg_debug @@ Pp.str (Format.sprintf "put smt query in %s" query_file) ;

  let in_in, in_out = pipe ~cloexec:true () in
  let out_in, out_out = pipe ~cloexec:true () in 
  let err_in, err_out = pipe ~cloexec:true () in 

  (* close unused pipes *)
  close in_out; close err_in;

  let args = [| "z3"; query_file |] in
  let smt_pid = Unix.create_process "z3" args in_in out_out err_out in

  (* Get an output channel to read from solver's stdout *)
  (* let lexbuf = Lexing.from_channel (in_channel_of_descr out_in) in *)
  
  let _ = waitpid [] smt_pid in 
  (* let _ = close_process (out_c, in_c) in *)
  (* Lexing.read *)
  let ln = Stdlib.input_line (in_channel_of_descr out_in) in 
  close out_in;
  if ln = "sat" then SAT
  else if ln = "unsat" then UNSAT
  else Other ln