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

Inductive suc (a : Set) : Set :=
| S : a -> suc a.

Arguments S {_}.

Inductive my_vector (a : Set) : Set :=
| V_nil : my_vector a
| V_cons : a -> my_vector a -> my_vector a.

Arguments V_nil {_}.
Arguments V_cons {_}.

Definition get_head {a : Set} (function_parameter : my_vector a) : a :=
  match function_parameter with
  | V_cons x _ => x
  | _ => unreachable_gadt_branch
  end.

Definition lvector : my_vector int := V_cons 1 (V_cons 3 V_nil).

Inductive my_vector_gadget : swaddle -> swaddle -> Set :=
| V_nil_g : forall {a : swaddle},
  my_vector_gadget a (swaddled_tconstr "zero" zero)
| V_cons_g : forall {a n : swaddle},
  unswaddle a -> my_vector_gadget a n ->
  my_vector_gadget a (swaddled_tconstr "suc_var" (suc (unswaddle n))).

Definition vhead {a : swaddle} {b : Set}
  (vec : my_vector_gadget a (swaddled_tconstr "suc_var" (suc b)))
  : unswaddle a :=
  match vec in my_vector_gadget t0 t1 return t0 = a -> t1 =
    swaddled_tconstr "suc_var" (suc b) -> unswaddle a with
  | V_cons_g x _ => fun eq0 eq1 => ltac:(subst; exact x)
  | _ => ltac:(discriminate)
  end eq_refl eq_refl.

Definition vtail {a b : swaddle}
  (vec : my_vector_gadget a (swaddled_tconstr "suc_var" (suc (unswaddle b))))
  : my_vector_gadget a b :=
  match vec in my_vector_gadget t0 t1 return t0 = a -> t1 =
    swaddled_tconstr "suc_var" (suc (unswaddle b)) -> my_vector_gadget a b with
  | V_cons_g _ xs => fun eq0 eq1 => ltac:(subst; exact xs)
  | _ => ltac:(discriminate)
  end eq_refl eq_refl.
