open Ctypes

let prioritizer nodes n edges m =
  (* Calling the int_id function *)
  (* let x = 42 in
  let result = C.Functions.int_id x in
  Format.printf "int_id(%d) = %d\n" 42 result; *)

  (* Calling the prioritizer function *)

  (* Suppose our inputs are encoded as OCaml lists *)
  (* let nodes = [ 1; 2; 3; 4; 5 ] in *)
  (* let edges = [ [ 1; 2 ]; [ 2; 3 ]; [ 3; 5 ]; [ 3; 4 ]; [ 4; 5 ] ] in *)
  (* let edges = [] in *)

  (* First, we will need to convert them to C arrays *)
  let nodes_arr = CArray.of_list int nodes in
  let edges_arr =
    let inner =
      List.map (fun e -> CArray.of_list int e |> CArray.start) edges
    in
    let outer = CArray.of_list (ptr int) inner in
    outer
  in
  (* let n = List.length nodes in
  let m = List.length edges in *)

  (* Now, we pass arguments into prioritizer *)
  let result =
    C.Functions.prioritizer (CArray.start nodes_arr) n (CArray.start edges_arr)
      m
  in
  CArray.from_ptr result n |> CArray.to_list
  |> List.iteri (fun i x -> Format.printf "priority[%d] = %d\n" i x)


(* let nodes : int list = [104; 107; 105 ]
let edges : (int list) list = [[0; 2]; [1; 2] ]
(* let edges : (int list) list = [ ] *)
let n : int = List.length nodes
let m : int = List.length edges

let _ = prioritizer nodes n edges m *)