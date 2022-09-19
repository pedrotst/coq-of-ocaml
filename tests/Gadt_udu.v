Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Inductive udu' : Set :=
| Unit : udu'
| Double_unit : udu'
| XX : udu'.

Definition unit_twelve (x : udu') : int :=
  match x with
  | Unit => 12
  | XX => 15
  | _ => unreachable_gadt_branch
  end.
