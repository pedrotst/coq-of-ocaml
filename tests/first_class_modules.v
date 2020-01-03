Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Module S.
  Module SET.
    Record signature {elt t : Set} := {
      elt := elt;
      t := t;
      empty : t;
      is_empty : t -> bool;
      mem : elt -> t -> bool;
      add : elt -> t -> t;
      singleton : elt -> t;
      remove : elt -> t -> t;
      union : t -> t -> t;
      inter : t -> t -> t;
      diff : t -> t -> t;
      compare : t -> t -> Z;
      equal : t -> t -> bool;
      subset : t -> t -> bool;
      iter : (elt -> unit) -> t -> unit;
      map : (elt -> elt) -> t -> t;
      fold : forall {a : Set}, (elt -> a -> a) -> t -> a -> a;
      for_all : (elt -> bool) -> t -> bool;
      __exists : (elt -> bool) -> t -> bool;
      filter : (elt -> bool) -> t -> t;
      partition : (elt -> bool) -> t -> t * t;
      cardinal : t -> Z;
      elements : t -> list elt;
      min_elt_opt : t -> option elt;
      max_elt_opt : t -> option elt;
      choose_opt : t -> option elt;
      split : elt -> t -> t * bool * t;
      find_opt : elt -> t -> option elt;
      find_first_opt : (elt -> bool) -> t -> option elt;
      find_last_opt : (elt -> bool) -> t -> option elt;
      of_list : list elt -> t;
    }.
    Arguments signature : clear implicits.
  End SET.
End S.

Inductive type_annot : Set :=
| Type_annot : string -> type_annot.

Inductive field_annot : Set :=
| Field_annot : string -> field_annot.

Definition pair (a b : Set) := a * b.

Inductive comb : Set :=
| Comb : comb.

Inductive leaf : Set :=
| Leaf : leaf.

Reserved Notation "'comparable_struct".

Inductive comparable_struct_gadt : Set :=
| Int_key : option type_annot -> comparable_struct_gadt
| String_key : option type_annot -> comparable_struct_gadt
| Bool_key : option type_annot -> comparable_struct_gadt
| Pair_key : comparable_struct_gadt * option field_annot ->
  comparable_struct_gadt * option field_annot -> option type_annot ->
  comparable_struct_gadt

where "'comparable_struct" := (fun (_ _ : Set) => comparable_struct_gadt).

Definition comparable_struct := 'comparable_struct.

Definition comparable_ty (a : Set) := comparable_struct a comb.

Module Boxed_set.
  Record signature {elt OPS_t : Set} := {
    elt := elt;
    elt_ty : comparable_ty elt;
    OPS : S.SET.signature elt OPS_t;
    boxed : OPS.(S.SET.t);
    size : Z;
  }.
  Arguments signature : clear implicits.
End Boxed_set.

Definition set (elt : Set) := {OPS_t : _ & Boxed_set.signature elt OPS_t}.

Module IncludedFoo.
  Record signature {bar : Set} := {
    bar := bar;
    foo : bar;
  }.
  Arguments signature : clear implicits.
End IncludedFoo.

Module Triple.
  Record signature {a b c bar : Set} := {
    a := a;
    b := b;
    c := c;
    va : a;
    vb : b;
    vc : c;
    bar := bar;
    foo : bar;
  }.
  Arguments signature : clear implicits.
End Triple.

Definition tripe : {'(a, b, c, bar) : _ & Triple.signature a b c bar} :=
  existT _ (((_, _), _), _)
    {|
      Triple.va := 0;
      Triple.vb := false;
      Triple.vc := "" % string;
      Triple.foo := 12
      |}.

Module UsingTriple.
  Record signature {elt' T_a T_b T_c T_bar OPS'_elt OPS'_t : Set} := {
    elt' := elt';
    T : Triple.signature T_a T_b T_c T_bar;
    OPS' : S.SET.signature OPS'_elt OPS'_t;
    OPS'' : S.SET.signature elt' (list string);
    table (a : Set) := list a;
  }.
  Arguments signature : clear implicits.
End UsingTriple.

Definition set_update {a : Set} (v : a) (b : bool) (Box : set a) : set a :=
  let Box := projT2 Box in
  existT _ _
    {|
      Boxed_set.elt_ty := Box.(Boxed_set.elt_ty);
      Boxed_set.OPS := Box.(Boxed_set.OPS);
      Boxed_set.boxed :=
        if b then
          Box.(Boxed_set.OPS).(S.SET.add) v Box.(Boxed_set.boxed)
        else
          Box.(Boxed_set.OPS).(S.SET.remove) v Box.(Boxed_set.boxed);
      Boxed_set.size :=
        let mem := Box.(Boxed_set.OPS).(S.SET.mem) v Box.(Boxed_set.boxed) in
        if mem then
          if b then
            Box.(Boxed_set.size)
          else
            Z.sub Box.(Boxed_set.size) 1
        else
          if b then
            Z.add Box.(Boxed_set.size) 1
          else
            Box.(Boxed_set.size)
      |}.

Definition set_mem {elt : Set} (v : elt) (Box : set elt) : bool :=
  let Box := projT2 Box in
  Box.(Boxed_set.OPS).(S.SET.mem) v Box.(Boxed_set.boxed).

Definition set_fold {acc elt : Set} (f : elt -> acc -> acc) (Box : set elt)
  : acc -> acc :=
  let Box := projT2 Box in
  Box.(Boxed_set.OPS).(S.SET.fold) f Box.(Boxed_set.boxed).
