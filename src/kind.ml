open SmartPrint

type t =
  | Set
  | Swaddle
  | Arrow of t * t

let rec to_string (k : t) : string =
  match k with
  | Set -> "Set"
  | Swaddle -> "GSet"
  | Arrow (k1, k2) -> (to_string k1) ^ " -> " ^ (to_string k2)

let to_coq (k : t) : SmartPrint.t =
  !^ (to_string k)

let union k1 k2 : t =
  match k1, k2 with
  | Arrow _ , _ -> k1
  | _, Arrow _ -> k2
  | Swaddle, _ | _, Swaddle -> Swaddle
  | _ -> Set

let rec set_arrows (arity : int) : t =
  if arity = 0 then
    Set
  else
    Arrow (Set, set_arrows (arity - 1))
