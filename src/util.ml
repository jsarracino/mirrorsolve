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