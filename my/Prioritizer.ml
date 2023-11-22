open Ctypes

let prioritize nodes n edges m =
  (* First, we will need to convert them to C arrays *)
  let nodes_arr = CArray.of_list int nodes in
  let edges_arr =
    let inner = List.map (fun e -> CArray.of_list int e |> CArray.start) edges in
    let outer = CArray.of_list (ptr int) inner in
    outer
  in

  let n = List.length nodes in
  let m = List.length edges in


  (* Now, we pass arguments into prioritizer *)
  let result0 =
    C.Functions.prioritizer (CArray.start nodes_arr) n (CArray.start edges_arr) m
  in
  let result1 =
    C.Functions.prioritizer (CArray.start nodes_arr) n (CArray.start edges_arr) m
  in

  CArray.from_ptr result0 n
  |> CArray.to_list
  |> List.iteri (fun i x -> Format.printf "priority[%d] = %d\n" i x)
  ;
  CArray.from_ptr result1 n
  |> CArray.to_list
  |> List.iteri (fun i x -> Format.printf "priority[%d] = %d\n" i x)

;;
