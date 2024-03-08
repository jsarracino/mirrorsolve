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
      UnivGen.constr_of_monomorphic_global env gref 
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

let fetch_const_type (x: Constr.t) = 
  if Constr.isConst x then 
    let v, _ = Constr.destConst x in 
    let x' = Global.lookup_constant v in
    Some x'.const_type 
  else
    None

let rec opt_sequence xs = 
  begin match xs with 
  | Some x :: xs' -> 
    Option.map (fun xs' -> (x :: xs')) (opt_sequence xs')
  | [] -> Some []
  | _ -> None
  end 