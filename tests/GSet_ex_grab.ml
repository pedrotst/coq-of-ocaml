type 'a term =
  | T_Int : int -> int term
  (* | T_String : string -> string term *)
  | T_Sum : int term * int term -> int term
  | T_Pair : 'a term * 'b term -> ('a * 'b) term
[@@coq_gset_gadt]

let rec interp : type a. a term -> a = function[@coq_grab_existentials]
  | T_Int n -> n
  (* | T_String s -> s *)
  | T_Sum (s1, s2) -> interp s1 + interp s2
  | T_Pair (p1, p2) -> (interp p1, interp p2)
