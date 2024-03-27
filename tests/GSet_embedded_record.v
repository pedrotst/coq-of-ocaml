Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Module Test.
  (** Records for the constructor parameters *)
  Module ConstructorRecords_term.
    Module term.
      Module T_Pair.
        Record record {x1 x2 x3 : Set} : Set := Build {
          x1 : x1;
          x2 : x2;
          x3 : x3 }.
        Arguments record : clear implicits.
        Definition with_x1 {t_x1 t_x2 t_x3} x1 (r : record t_x1 t_x2 t_x3) :=
          Build t_x1 t_x2 t_x3 x1 r.(x2) r.(x3).
        Definition with_x2 {t_x1 t_x2 t_x3} x2 (r : record t_x1 t_x2 t_x3) :=
          Build t_x1 t_x2 t_x3 r.(x1) x2 r.(x3).
        Definition with_x3 {t_x1 t_x2 t_x3} x3 (r : record t_x1 t_x2 t_x3) :=
          Build t_x1 t_x2 t_x3 r.(x1) r.(x2) x3.
      End T_Pair.
      Definition T_Pair_skeleton := T_Pair.record.
    End term.
  End ConstructorRecords_term.
  Import ConstructorRecords_term.
  
  Reserved Notation "'term.T_Pair".
  
  Inductive term : GSet -> Set :=
  | T_Pair : forall {a b : GSet},
    'term.T_Pair (decodeG a) (decodeG b) -> term (G_tuple a b)
  
  where "'term.T_Pair" :=
    (fun (t_a t_b : Set) => term.T_Pair_skeleton int t_a t_b).
  
  Module term.
    Include ConstructorRecords_term.term.
    Definition T_Pair := 'term.T_Pair.
  End term.
End Test.

Fixpoint interp {a : GSet} (t : Test.term a) : int :=
  let
    'Test.T_Pair {|
      Test.term.T_Pair.x1 := x1;
        Test.term.T_Pair.x2 := x2;
        Test.term.T_Pair.x3 := x3
        |} := t in
  x1.
