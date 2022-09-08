let rec split_last xs = 
  begin match xs with
  | [] -> None
  | x :: [] -> Some ([], x)
  | x :: xs -> 
    begin match split_last xs with 
    | Some (xs', r) -> Some (x :: xs', r)
    | None -> None
    end
  end

exception MissingGlobConst of string
let get_coq ref : Constr.t = 
  try 
    let gref = Coqlib.lib_ref ref in
    let env = Global.env () in
    let sigma = Evd.from_env env in
    let sigma', evd = EConstr.fresh_global env sigma gref in 
      EConstr.to_constr sigma' evd
  with e ->
    let lib_refs = Coqlib.get_lib_refs () in 
    let needle = List.find_opt (fun (name, _) -> name = ref) lib_refs in
      begin match needle with 
      | Some (_, x) -> raise @@ MissingGlobConst ("polymorphic global: " ^ ref)
      | None -> raise @@ MissingGlobConst ("unregistered global: " ^ ref)
      end


let fetch_const (x: Constr.t) = 
  if Constr.isConst x then 
    let v, _ = Constr.destConst x in 
    let x' = Global.lookup_constant v in
    begin match x'.const_body with 
    | Def x -> Some x
    | _ -> None
    end
  else 
    None