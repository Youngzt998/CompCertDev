open Ctypes

let prioritizer nodes n edges m =
  (* Calling the prioritizer function *)

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
