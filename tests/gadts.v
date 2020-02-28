(** Generated by coq-of-ocaml *)
Require Import OCaml.OCaml.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Unset Positivity Checking.
Unset Guard Checking.

Inductive gre (a : Set) : Set :=
| Arg : a -> gre a.

Arguments Arg {_}.

Inductive foo : Set :=
| Bar : forall {a b c : Set}, a -> Z -> b -> c -> foo
| Other : Z -> foo.

Inductive expr : Set :=
| Int : Z -> expr
| String : string -> expr
| Sum : expr -> expr -> expr
| Pair : expr -> expr -> expr.

Fixpoint proj_int (e : expr) {struct e} : Z :=
  match e with
  | Int n => n
  | Sum e1 e2 => Z.add (proj_int e1) (proj_int e2)
  | _ => unreachable_gadt_branch
  end.

Inductive one_case : Set :=
| SingleCase : one_case
| Impossible : one_case.

Definition x : Z :=
  match SingleCase with
  | SingleCase => 0
  | _ => unreachable_gadt_branch
  end.
