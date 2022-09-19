Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Inductive term : GSet -> Set :=
| T_Int : int -> term G_int
| T_String : string -> term G_string
| T_Sum : term G_int -> term G_int -> term G_int.

Fixpoint get_int (e : term G_int) : int :=
  match e in term t0 return t0 = G_int -> int with
  | T_Int n => fun eq0 => ltac:(subst; exact n)
  | T_Sum e1 e2 =>
    fun eq0 => ltac:(subst; exact (Z.add (get_int e1) (get_int e2)))
  | _ => ltac:(discriminate)
  end eq_refl.

Fixpoint interp {a : GSet} (function_parameter : term a) : decodeG a :=
  match function_parameter with
  | T_Int n => n
  | T_String s => s
  | T_Sum s1 s2 => Z.add (interp s1) (interp s2)
  end.
