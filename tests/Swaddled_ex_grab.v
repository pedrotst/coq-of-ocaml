Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Inductive term : swaddle -> Set :=
| T_Int : int -> term swaddled_int
| T_Sum : term swaddled_int -> term swaddled_int -> term swaddled_int
| T_Pair : forall {a b : swaddle}, term a -> term b -> term (swaddled_tuple a b).

Fixpoint interp {a : swaddle} (function_parameter : term a) : unswaddle a :=
  match function_parameter with
  | T_Int n => n
  | T_Sum s1 s2 => Z.add (interp s1) (interp s2)
  | T_Pair p1 p2 =>
    let 'existT _ [__1, __0] [p2, p1] as exi :=
      existT (A := [swaddle ** swaddle])
        (fun '[__1, __0] => [term __1 ** term __0]) [_, _] [p2, p1]
      return
        let fst := projT1 exi in
        let __0 := Primitive.snd fst in
        let __1 := Primitive.fst fst in
        unswaddle __0 * unswaddle __1 in
    ((interp p1), (interp p2))
  end.

Inductive t : Type :=
| Empty : t
| Node : forall {a : Type}, a -> t.

Fixpoint t_of_list {a : Type} (l : list a) : t :=
  match l with
  | [] => Empty
  | cons _ l => Node (t_of_list l)
  end.
