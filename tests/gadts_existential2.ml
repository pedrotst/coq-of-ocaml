type 'b wrap1 =
  | Cw1 : ('a -> ('b * 'b)) -> 'b wrap1

type 'b wrap2 =
  | Cw2 : ('a -> 'b) -> 'b wrap2

let w2_of_w1 (w : 'b wrap2) : 'b wrap1  =
  match [@coq_grab_existentials]w with
  | Cw2 f ->
    Cw1 (fun y -> (f y, f y))
