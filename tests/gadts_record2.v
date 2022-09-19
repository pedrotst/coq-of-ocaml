Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Inductive exp : Set :=
| E_Int : int -> exp.

Module my_record.
  Record record : Set := Build {
    x : exp;
    y : int }.
  Definition with_x x (r : record) :=
    Build x r.(y).
  Definition with_y y (r : record) :=
    Build r.(x) y.
End my_record.
Definition my_record := my_record.record.

Definition get_x (r : my_record) : exp :=
  let '{| my_record.x := x; my_record.y := y |} := r in
  x.
