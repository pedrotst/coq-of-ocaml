Require Import String.
Require Import Basics.

Inductive GSet : Type :=
| G_tconstr : string -> Set -> GSet
| G_arrow : GSet -> GSet -> GSet
| G_tuple : GSet -> GSet -> GSet
.

Fixpoint decodeG (s : GSet) : Set :=
  match s with
  | G_tconstr s t => t
  | G_arrow t1 t2 => decodeG t1 -> decodeG t2
  | G_tuple t1 t2 =>
    (decodeG t1) * (decodeG t2)
  end.

Notation G_int := (G_tconstr "int" int).
Notation G_string := (G_tconstr "string" string).
Notation G_bool := (G_tconstr "bool" bool).
Notation G_unit := (G_tconstr "unit" unit).
Notation G_float := (G_tconstr "float" int).
Notation G_option A := (G_tconstr "option" (option A)).
Notation G_list A := (G_tconstr "list" (list A)).
