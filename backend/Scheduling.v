Require Import ExtrOcamlIntConv.

Parameter prioritizer : list int -> int -> list (list int) -> int -> unit.

Definition schedule := prioritizer.
