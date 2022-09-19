type _ term =
  | TInt : int -> int term
  | TBool : bool -> bool term
[@@coq_swaddle_gadt]

type ('a, 'b, 'c) reco =
  { x : 'a term;
    y : 'c term;
    z : 'b }
[@@coq_swaddle_gadt]

type 'a term_synm = 'a term

type ('a, 'b, 'c) reco_synm = ('a, 'b, 'c) reco

let f (t : int term_synm) : int =
  match t with
  | TInt n -> n

let f (type a) (t : bool term) =
  match t with
  | TBool b -> b
