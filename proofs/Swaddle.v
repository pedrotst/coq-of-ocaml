Require Import String.
Require Import Basics.

Inductive swaddle : Type :=
| swaddled_tconstr : string -> Set -> swaddle
| swaddled_arrow : swaddle -> swaddle -> swaddle
| swaddled_tuple : swaddle -> swaddle -> swaddle
.

Fixpoint unswaddle (s : swaddle) : Set :=
  match s with
  | swaddled_tconstr s t => t
  | swaddled_arrow t1 t2 => unswaddle t1 -> unswaddle t2
  | swaddled_tuple t1 t2 =>
    (unswaddle t1) * (unswaddle t2)
  end.

Notation swaddled_int := (swaddled_tconstr "int" int).
Notation swaddled_string := (swaddled_tconstr "string" string).
Notation swaddled_bool := (swaddled_tconstr "bool" bool).
Notation swaddled_unit := (swaddled_tconstr "unit" unit).
Notation swaddled_float := (swaddled_tconstr "float" int).
Notation swaddled_option A := (swaddled_tconstr "option" (option A)).
Notation swaddled_list A := (swaddled_tconstr "list" (list A)).
