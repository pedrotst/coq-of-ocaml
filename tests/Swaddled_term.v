Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Inductive term : swaddle -> Set :=
| T_Lift : forall (a : swaddle), unswaddle a -> term a
| T_Int : int -> term swaddled_int
| T_String : string -> term swaddled_string
(* | T_Sum : term swaddled_int -> term swaddled_int -> term swaddled_int. *)
| T_Pair : forall (l r : swaddle),
    term l -> term r -> term (swaddled_tconstr "tuple" (unswaddle l * unswaddle r)).

(* Class Representable (A : Type) := { *)
(*     repr : A -> string *)
(*   }. *)

(* Definition str_repr {A : swaddle} (t : term A) : string := *)
(*   match t with *)
(*   | T_Lift _ i => "var" *)
(*   | T_Int i => "int" *)
(*   | T_String s => "string" *)
(*   | T_Sum _ _ => "int" *)
(*   end. *)

(* Instance swaddle_repr : Representable swaddle := { *)
(*     repr := fun s => match s with *)
(*                   | swaddled_tconstr s t => s *)
(*                   | swaddled_arrow t1 t2 => "t" *)
(*                   | swaddled_tuple t1 t2 => "t" *)
(*                   end *)
(*   }. *)

(* Instance term_repr : forall a, Representable (term a) := { *)
(*     repr := fun _ => repr a *)
(*   }. *)

Open Scope nat.

Definition foo : (S 0) = 0 -> False.
intro H. inversion H.
Defined.

Fixpoint get_int (e : term swaddled_int) : int.
  refine (match e in term t0 return (t0 = swaddled_int) -> int with
          | T_Lift a x => fun (eq0 : a = swaddled_int) =>
                           @eq_rect_r swaddle swaddled_int (fun y => unswaddle y -> int) (fun (z : unswaddle swaddled_int) => z) a eq0 x
                           (* ltac:(rewrite eq0 in *; exact x) *)
          | T_Int n => fun eq0 => ltac:(subst; exact n)
          (* | T_Sum e1 e2 => *)
            (* fun eq0 => ltac:(subst; exact (Z.add (get_int e1) (get_int e2))) *)
          | _ => fun H => ltac:(inversion H)
          end eq_refl).
Defined.


Fixpoint get_int (e : term swaddled_int) : int :=
  match e in term t0 return t0 = swaddled_int -> int with
  | T_Int n => fun eq0 => ltac:(subst; exact n)
  | T_Sum e1 e2 =>
    fun eq0 => ltac:(subst; exact (Z.add (get_int e1) (get_int e2)))
  | _ => ltac:(discriminate)
  end eq_refl.

Fixpoint interp {a : swaddle} (function_parameter : term a) : unswaddle a :=
  match function_parameter with
  | T_Int n => n
  | T_String s => s
  | T_Sum s1 s2 => Z.add (interp s1) (interp s2)
  end.
