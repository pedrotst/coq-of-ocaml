type ('a, 'b) eq = Eq : ('b, 'b) eq

type 'a my_list =
  | Nil
  | Cons of 'a * 'a my_list

type zero = Z

type 'a suc = S of 'a

(* data Suc a *)

type ('a, _) my_vector =
  | V_nil : ('a, zero) my_vector
  | V_cons: 'a * (('a, 'n) my_vector) -> ('a, 'n suc) my_vector

let get_head : ('a, 'b suc) my_vector -> 'a =
  function[@coq_match_with_default]
  | V_cons (x, _) -> x

let lvector = V_cons (1, (V_cons (3, V_nil)))

type ('a, _) my_vector_gadget =
  | V_nil_g : ('a, zero) my_vector_gadget
  | V_cons_g: 'a * (('a, 'n) my_vector_gadget) -> ('a, 'n suc) my_vector_gadget
[@@coq_swaddle_gadt]

let vhead (vec: ('a, 'b suc) my_vector_gadget) : 'a =
  match [@coq_swaddle_match][@coq_match_with_default]vec with
  | V_cons_g (x, _) -> x

(* type 'a car = {
 *   year : int;
 *   miliage: int;
 *   something: 'a;
 * } *)

let vtail (vec: ('a, 'b suc) my_vector_gadget) : ('a, 'b) my_vector_gadget =
  match [@coq_swaddle_match][@coq_match_with_default]vec with
  | V_cons_g (_, xs) -> xs
