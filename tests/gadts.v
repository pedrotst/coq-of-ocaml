Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Inductive gre (a : Set) : Set :=
| Arg : a -> gre a.

Arguments Arg {_}.

Reserved Notation "'foo".

Inductive foo_gadt : Set :=
| Bar : forall {a b c : Set}, a -> Z -> b -> c -> foo_gadt
| Other : Z -> foo_gadt

where "'foo" := (fun (a b : Set) => foo_gadt).

Definition foo := 'foo.

Reserved Notation "'expr".

Inductive expr_gadt : Set :=
| Int : Z -> expr_gadt
| String : string -> expr_gadt
| Sum : expr_gadt -> expr_gadt -> expr_gadt
| Pair : expr_gadt -> expr_gadt -> expr_gadt

where "'expr" := (fun (a : Set) => expr_gadt).

Definition expr := 'expr.

Fixpoint proj_int (e : expr Z) : Z :=
  match e with
  | Int n => n
  | Sum e1 e2 => Z.add (proj_int e1) (proj_int e2)
  | _ => 0
  end.

Reserved Notation "'one_case".

Inductive one_case_gadt : Set :=
| SingleCase : one_case_gadt
| Impossible : one_case_gadt

where "'one_case" := (fun (a : Set) => one_case_gadt).

Definition one_case := 'one_case.

Definition x : Z :=
  match SingleCase with
  | SingleCase => 0
  | _ => 1
  end.
