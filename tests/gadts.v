Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Inductive gre (a : Set) : Set :=
| Arg : a -> gre a.

Arguments Arg {_}.

Inductive foo : Set :=
| Bar : forall {a b c : Set}, a -> int -> b -> c -> foo
| Other : int -> foo.

Inductive expr : Set :=
| Int : int -> expr
| String : string -> expr
| Sum : expr -> expr -> expr
| Pair : expr -> expr -> expr.

Fixpoint proj_int (e : expr) : int :=
  match e with
  | Int n => n
  | Sum e1 e2 => Z.add (proj_int e1) (proj_int e2)
  | _ => unreachable_gadt_branch
  end.

Inductive term : GSet -> Set :=
| T_Lift : forall {a : GSet}, decodeG a -> term a
| T_Int : int -> term G_int
| T_String : string -> term G_string
| T_Sum : term G_int -> term G_int -> term G_int
| T_Pair : forall {a b : GSet}, term a -> term b -> term (G_tuple a b).

Fixpoint get_int (e : term G_int) : int :=
  match e in term t0 return t0 = G_int -> int with
  | T_Lift v => fun eq0 => ltac:(subst; exact v)
  | T_Int n => fun eq0 => ltac:(subst; exact n)
  | T_Sum e1 e2 =>
    fun eq0 => ltac:(subst; exact (Z.add (get_int e1) (get_int e2)))
  | _ => ltac:(discriminate)
  end eq_refl.

(** Records for the constructor parameters *)
Module ConstructorRecords_exp.
  Module exp.
    Module T_Record.
      Record record {x y z : Set} : Set := Build {
        x : x;
        y : y;
        z : z }.
      Arguments record : clear implicits.
      Definition with_x {t_x t_y t_z} x (r : record t_x t_y t_z) :=
        Build t_x t_y t_z x r.(y) r.(z).
      Definition with_y {t_x t_y t_z} y (r : record t_x t_y t_z) :=
        Build t_x t_y t_z r.(x) y r.(z).
      Definition with_z {t_x t_y t_z} z (r : record t_x t_y t_z) :=
        Build t_x t_y t_z r.(x) r.(y) z.
    End T_Record.
    Definition T_Record_skeleton := T_Record.record.
  End exp.
End ConstructorRecords_exp.
Import ConstructorRecords_exp.

Reserved Notation "'exp.T_Record".

Inductive exp : GSet -> Set :=
| T_Record : forall {a : GSet} {b : Set}, 'exp.T_Record a b -> exp a

where "'exp.T_Record" :=
  (fun (t_a : GSet) (t_b : Set) => exp.T_Record_skeleton (term t_a) t_b
    (decodeG t_a)).

Module exp.
  Include ConstructorRecords_exp.exp.
  Definition T_Record := 'exp.T_Record.
End exp.

Inductive one_case : Set :=
| SingleCase : one_case
| Impossible : one_case.

Definition x : int :=
  match SingleCase with
  | SingleCase => 0
  | _ => unreachable_gadt_branch
  end.

Inductive gadt_list : Set :=
| GNil : gadt_list
| GCons : forall {a : Set}, a -> gadt_list -> gadt_list.

Definition gadt_empty_list : gadt_list := GNil.
