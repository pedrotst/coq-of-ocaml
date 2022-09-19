Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

(** Records for the constructor parameters *)
Module ConstructorRecords_term.
  Module term.
    Module T_Rec.
      Record record {x y : Set} : Set := Build {
        x : x;
        y : y }.
      Arguments record : clear implicits.
      Definition with_x {t_x t_y} x (r : record t_x t_y) :=
        Build t_x t_y x r.(y).
      Definition with_y {t_x t_y} y (r : record t_x t_y) :=
        Build t_x t_y r.(x) y.
    End T_Rec.
    Definition T_Rec_skeleton := T_Rec.record.
  End term.
End ConstructorRecords_term.
Import ConstructorRecords_term.

Reserved Notation "'term.T_Rec".

Inductive term : GSet -> Set :=
| T_Int : int -> term G_int
| T_String : string -> term G_string
| T_Pair : forall {a b : GSet}, term a -> term b -> term (G_tuple a b)
| T_Rec : forall {a b : GSet}, 'term.T_Rec a (decodeG b) -> term b

where "'term.T_Rec" :=
  (fun (t_a : GSet) (t_b : Set) => term.T_Rec_skeleton (term t_a) t_b).

Module term.
  Include ConstructorRecords_term.term.
  Definition T_Rec := 'term.T_Rec.
End term.

Fixpoint interp {a : GSet} (function_parameter : term a) : decodeG a :=
  match function_parameter with
  | T_Int n => n
  | T_String s => s
  | T_Pair p1 p2 => ((interp p1), (interp p2))
  | T_Rec {| term.T_Rec.x := x; term.T_Rec.y := y |} => y
  end.
