type 'a term =
  | T_Int : int -> int term
  | T_String : string -> string term
  | T_Sum : int term * int term -> int term
  (* | T_Pair : 'a term * 'b term -> ('a * 'b) term *)
[@@coq_swaddle_gadt]

type 'a set =
  | Empty : 'a set
  | NonEmpty : Ord

let rec get_int (e : int term) : int =
  match[@coq_swaddle_match][@coq_match_with_default] e with
  | T_Int n -> n
  | T_Sum (e1, e2) -> get_int e1 + get_int e2
  | _ -> .

let rec interp : type a. a term -> a = function
  | T_Int n -> n
  | T_String s -> s
  | T_Sum (s1, s2) -> interp s1 + interp s2
