
type zero = Z

type 's succ = S

type ('s, 'a) node =
  (* | Empty : (zero, 'a) node *)
  | Leaf1 : 'a -> (zero, 'a) node
  | Leaf2 : ('a * 'a) -> (zero, 'a) node
  | Node1 : (('s, 'a) node * 'a * ('s,'a) node) -> ('s succ, 'a) node
  | Node2 : (('s, 'a) node * 'a * ('s, 'a) node * 'a * ('s,'a) node) -> ('s succ, 'a) node

type 'a btree =
  | Root0 : 'a btree
  (* | Root1 : 'a -> 'a btree *)
  | RootN : ('s, 'a) node -> 'a btree

let insert_node : type a s . a -> (s, a) node -> (_, a) node =
  fun el n ->
  match n with
  | Leaf1 el' -> Leaf2 (el, el')
  | Leaf2 (el1, el2) ->
    let lhs = Leaf1 el1 in
    let rhs = Leaf1 el2 in
    Node1 (lhs, el, rhs)
  | Node1 (lhs, el', rhs) ->
    Node2 (lhs, el, el', rhs)
  | Node2 (lhs, el1, chs, el2, rhs) ->

let insert : type a. a -> a btree -> a btree =
  fun el bt ->
  match bt with
  | Root0 -> RootN (Leaf1 el)
  (* | Root1 el' -> RootN (Leaf2 (el, el')) *)
  | RootN n ->
