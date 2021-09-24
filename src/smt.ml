
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
