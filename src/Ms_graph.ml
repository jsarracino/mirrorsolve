type str_graph = {
  nodes : string list ;
  edges : (string * string) list
}

let empty = {nodes = []; edges = []}

let add_node (g: str_graph) (s: string) = 
  {g with nodes = List.sort_uniq compare @@ s :: g.nodes}
let add_edge (g: str_graph) (l: string) (r: string) = 
  {g with edges = List.sort_uniq compare @@ (l, r) :: g.edges}

let rec remove x xs = 
  begin match xs with 
  | [] -> []
  | x' :: xs' -> 
    if x' = x then xs' else x' :: remove x xs'
  end

let remove_edge (g: str_graph) (l: string) (r: string) = 
  {g with edges = remove (l, r) g.edges}


(* 
  We implement the following psuedocode for topo sort (pulled from Wikipedia, apparently due to Kahn): 

L ← Empty list that will contain the sorted elements
S ← Set of all nodes with no incoming edge

while S is not empty do
    remove a node n from S
    add n to L
    for each node m with an edge e from n to m do
    remove edge e from the graph
    if m has no other incoming edges then
        insert m into S


if graph has edges then
    return error   (graph has at least one cycle)
else 
    return L   (a topologically sorted order)

*)

module SS = Set.Make(String);;

(* all nodes lhs such that (lhs, rhs) \in edges *)
let nodes_incoming (rhs: string) (g: str_graph) = 
  List.sort_uniq compare @@ List.map fst @@ List.filter (fun (_, y) -> y = rhs) g.edges

(* all nodes rhs such that (lhs, rhs) \in edges *)
let nodes_outgoing (lhs: string) (g: str_graph) = 
  List.sort_uniq compare @@ List.map snd @@ List.filter (fun (x, y) -> x = lhs) g.edges

let is_lonely g s = 
  begin match nodes_incoming s g with 
  | [] -> true
  | _ -> false
  end 
let no_preds_set (g: str_graph) = 
  SS.of_list @@ List.filter (is_lonely g) g.nodes

let rec topo_sort_worker (ss: SS.t) (g: str_graph) (ret: string list) : string list = 
  if SS.is_empty ss then ret else 
  let nxt = SS.choose ss in 
  let ss' = SS.remove nxt ss in 
  let ret' = nxt :: ret in 

  (* for each node m with an edge e from n to m do
    remove edge e from the graph
    if m has no other incoming edges then
        insert m into S *)
  let next_successors = nodes_outgoing nxt g in 
  let ss'', g' = List.fold_left (
    fun (s_acc, g_acc) m -> 
      let g_acc' = remove_edge g_acc nxt m in   
      let s_acc' = if is_lonely g_acc' m then SS.add m s_acc else s_acc in
        (s_acc', g_acc')
    ) (ss', g) next_successors in 
  topo_sort_worker ss'' g' ret'


let topo_sort g  =  List.rev @@ topo_sort_worker (no_preds_set g) g []