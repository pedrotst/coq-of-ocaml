type 'a udu' =
  | Unit : unit udu'
  | Double_unit : (unit * unit) udu'
  | XX : 'a udu'
(* [@@coq_swaddle_gadt] *)

let unit_twelve (x : unit udu') =
  match [@coq_swaddle_match][@coq_match_with_default]x with
  | Unit -> 12
  | XX -> 15
