Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Inductive eq (b : Set) : Set :=
| Eq : eq b.

Arguments Eq {_}.

Inductive my_list (a : Set) : Set :=
| Nil : my_list a
| Cons : a -> my_list a -> my_list a.

Arguments Nil {_}.
Arguments Cons {_}.

Inductive zero : Set :=
| Z : zero.

Inductive suc : swaddle -> Set :=
| S : forall {a : swaddle}, unswaddle a -> suc a.

Inductive my_vector : swaddle -> swaddle -> Set :=
| V_nil : forall {a : swaddle}, my_vector a (swaddled_tconstr "zero" zero)
| V_cons : forall {a n : swaddle},
  unswaddle a -> my_vector a n ->
  my_vector a (swaddled_tconstr "suc_var" (suc n)).

Definition get_tail {a b : swaddle}
  (v : my_vector a (swaddled_tconstr "suc_var" (suc b))) : my_vector a b.
  refine (match v in my_vector t0 t1
                return t0 = a ->
                       t1 = swaddled_tconstr "suc_var" (suc b) ->
                       (* t1 = b -> *)
                       my_vector a b
          with
          | V_cons x _ => fun eq0 eq1 => _
                                       (* ltac:(subst; exact x) *)
          | _ =>
                  ltac:(discriminate)
          end eq_refl eq_refl).
  subst.
  inversion eq1.
  exact m.
  - intros eq0 eq1.
    inversion eq1.
  - rewrite <- eq0.
    inversion eq1.
    subst.
    (* injection H0. *)
    inversion H0.
  admit.
  Defined.
