Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Inductive term : swaddle -> Set :=
| TInt : int -> term swaddled_int
| TBool : bool -> term swaddled_bool.

Module reco.
  Record record {a : swaddle} {b : Set} {c : swaddle} : Set := Build {
    x : term a;
    y : term c;
    z : b }.
  Arguments record : clear implicits.
  Definition with_x {t_a t_b t_c} x (r : record t_a t_b t_c) :=
    Build t_a t_b t_c x r.(y) r.(z).
  Definition with_y {t_a t_b t_c} y (r : record t_a t_b t_c) :=
    Build t_a t_b t_c r.(x) y r.(z).
  Definition with_z {t_a t_b t_c} z (r : record t_a t_b t_c) :=
    Build t_a t_b t_c r.(x) r.(y) z.
End reco.
Definition reco := reco.record.

Definition term_synm (a : swaddle) := term a.

Definition reco_synm (a : swaddle) (b : Set) (c : swaddle) := reco a b c.

(* Definition f (t : term_synm int) : int := *)
(*   let 'TInt n := t in *)
(*   n. *)

Definition f (t : term swaddled_bool) : bool :=
  let 'TBool b := t in
  b.
