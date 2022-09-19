Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Inductive term : GSet -> Set :=
| T_Int : int -> term G_int
| T_Sum : term G_int -> term G_int -> term G_int
| T_Pair : forall {a b : GSet}, term a -> term b -> term (G_tuple a b).

Fixpoint interp {a : GSet} (function_parameter : term a) : decodeG a :=
  match function_parameter with
  | T_Int n => n
  | T_Sum s1 s2 => Z.add (interp s1) (interp s2)
  | T_Pair p1 p2 =>
    let 'existT _ [__1, __0] [p2, p1] as exi :=
      existT (A := [GSet ** GSet]) (fun '[__1, __0] => [term __1 ** term __0])
        [_, _] [p2, p1]
      return
        let fst := projT1 exi in
        let __0 := Primitive.snd fst in
        let __1 := Primitive.fst fst in
        decodeG __0 * decodeG __1 in
    ((interp p1), (interp p2))
  end.
