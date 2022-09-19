Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Inductive wrap1 (b : Set) : Set :=
| Cw1 : forall {a : Set}, (a -> b * b) -> wrap1 b.

Arguments Cw1 {_ _}.

Inductive wrap2 (b : Set) : Set :=
| Cw2 : forall {a : Set}, (a -> b) -> wrap2 b.

Arguments Cw2 {_ _}.

Definition w2_of_w1 {b : Set} (w : wrap2 b) : wrap1 b :=
  let 'Cw2 f := w in
  let 'existT _ [__Cw2_'a, b] f as exi :=
    existT (A := [Set ** Set]) (fun '[__Cw2_'a, b] => __Cw2_'a -> b) [_, _] f
    return
      let fst := projT1 exi in
      let b := Primitive.snd fst in
      let __Cw2_'a := Primitive.fst fst in
      wrap1 b in
  Cw1 (fun (y : __Cw2_'a) => ((f y), (f y))).
