Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Inductive zero : Set :=
| Z : zero.

Inductive succ (s : Set) : Set :=
| S : succ s.

Arguments S {_}.

Inductive node (a : Set) : Set :=
| Leaf1 : a -> node a
| Leaf2 : a * a -> node a
| Node1 : node a * a * node a -> node a
| Node2 : node a * a * node a * a * node a -> node a.

Arguments Leaf1 {_}.
Arguments Leaf2 {_}.
Arguments Node1 {_}.
Arguments Node2 {_}.

Inductive btree (a : Set) : Set :=
| Root0 : btree a
| RootN : node a -> btree a.

Arguments Root0 {_}.
Arguments RootN {_}.

Definition insert_node {a : Set} (el : a) (n : node a) : node a :=
  match n with
  | Leaf1 el' => Leaf2 (el, el')
  | Leaf2 (el1, el2) =>
    let lhs := Leaf1 el1 in
    let rhs := Leaf1 el2 in
    op_startypeminuserrorstar
  | Node1 (lhs, el', rhs) => op_startypeminuserrorstar
  | Node2 (lhs, el1, chs, el2, rhs) =>
    let insert (el : a) (bt : btree a) : btree a :=
      match bt with
      | Root0 => RootN (Leaf1 el)
      | RootN n => op_startypeminusholestar
      end in
    op_startypeminusholestar
  end.
