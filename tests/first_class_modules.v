Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Module S.
  Module SET.
    Record signature {elt t : Set} : Set := {
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
      compare : t -> t -> int;
      equal : t -> t -> bool;
      subset : t -> t -> bool;
      iter : (elt -> unit) -> t -> unit;
      map : (elt -> elt) -> t -> t;
      fold : forall {a : Set}, (elt -> a -> a) -> t -> a -> a;
      for_all : (elt -> bool) -> t -> bool;
      _exists : (elt -> bool) -> t -> bool;
      filter : (elt -> bool) -> t -> t;
      partition : (elt -> bool) -> t -> t * t;
      cardinal : t -> int;
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
  End SET.
  Definition SET := @SET.signature.
  Arguments SET {_ _}.
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

Inductive comparable_struct : Set :=
| Int_key : option type_annot -> comparable_struct
| String_key : option type_annot -> comparable_struct
| Bool_key : option type_annot -> comparable_struct
| Pair_key :
  comparable_struct * option field_annot ->
  comparable_struct * option field_annot -> option type_annot ->
  comparable_struct.

Definition comparable_ty := comparable_struct.

Module Boxed_set.
  Record signature {elt OPS_t : Set} : Set := {
    elt := elt;
    elt_ty : comparable_ty;
    OPS : S.SET (elt := elt) (t := OPS_t);
    boxed : OPS.(S.SET.t);
    size : int;
  }.
End Boxed_set.
Definition Boxed_set := @Boxed_set.signature.
Arguments Boxed_set {_ _}.

Definition set (elt : Set) :=
  {OPS_t : Set @ Boxed_set (elt := elt) (OPS_t := OPS_t)}.

Module IncludedFoo.
  Record signature {bar : Set} : Set := {
    bar := bar;
    foo : bar;
  }.
End IncludedFoo.
Definition IncludedFoo := @IncludedFoo.signature.
Arguments IncludedFoo {_}.

Module Triple.
  Record signature {a b c bar : Set} : Set := {
    a := a;
    b := b;
    c := c;
    va : a;
    vb : b;
    vc : c;
    bar := bar;
    foo : bar;
  }.
End Triple.
Definition Triple := @Triple.signature.
Arguments Triple {_ _ _ _}.

Definition tripe
  : {'[a, b, c, bar] : [Set ** Set ** Set ** Set] @
    Triple (a := a) (b := b) (c := c) (bar := bar)} :=
  existS (A := [Set ** Set ** Set ** Set]) _ [_, _, _, _]
    (let a : Set := int in
    let b : Set := bool in
    let c : Set := string in
    let va := 0 in
    let vb := false in
    let vc := "" in
    let bar : Set := int in
    let foo := 12 in
    {|
      Triple.va := va;
      Triple.vb := vb;
      Triple.vc := vc;
      Triple.foo := foo
    |}).

Module UsingTriple.
  Record signature {elt' T_a T_b T_c T_bar OPS'_elt OPS'_t : Set} : Set := {
    elt' := elt';
    T : Triple (a := T_a) (b := T_b) (c := T_c) (bar := T_bar);
    OPS' : S.SET (elt := OPS'_elt) (t := OPS'_t);
    OPS'' : S.SET (elt := elt') (t := list string);
    table := forall {a : Set}, list a;
  }.
End UsingTriple.
Definition UsingTriple := @UsingTriple.signature.
Arguments UsingTriple {_ _ _ _ _ _ _}.

Definition set_update {a : Set} (v : a) (b : bool) (Box : set a) : set a :=
  let 'existS _ _ Box := Box in
  existS (A := Set) _ _
    (let elt : Set := a in
    let elt_ty := Box.(Boxed_set.elt_ty) in
    let OPS := Box.(Boxed_set.OPS) in
    let boxed :=
      if b then
        Box.(Boxed_set.OPS).(S.SET.add) v Box.(Boxed_set.boxed)
      else
        Box.(Boxed_set.OPS).(S.SET.remove) v Box.(Boxed_set.boxed) in
    let size :=
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
          Box.(Boxed_set.size) in
    {|
      Boxed_set.elt_ty := elt_ty;
      Boxed_set.OPS := OPS;
      Boxed_set.boxed := boxed;
      Boxed_set.size := size
    |}).

Definition set_mem {elt : Set} (v : elt) (Box : set elt) : bool :=
  let 'existS _ _ Box := Box in
  Box.(Boxed_set.OPS).(S.SET.mem) v Box.(Boxed_set.boxed).

Definition set_fold {elt acc : Set} (f : elt -> acc -> acc) (Box : set elt)
  : acc -> acc :=
  let 'existS _ _ Box := Box in
  Box.(Boxed_set.OPS).(S.SET.fold) f Box.(Boxed_set.boxed).

Definition set_nested {elt : Set} (Box : set elt) : set elt :=
  let 'existS _ _ Box := Box in
  existS (A := Set) _ _
    (let result_value :=
      existS (A := Set) _ _
        (let elt : Set := elt in
        let elt_ty := Box.(Boxed_set.elt_ty) in
        let OPS := Box.(Boxed_set.OPS) in
        let boxed := Box.(Boxed_set.boxed) in
        let size := Box.(Boxed_set.size) in
        {|
          Boxed_set.elt_ty := elt_ty;
          Boxed_set.OPS := OPS;
          Boxed_set.boxed := boxed;
          Boxed_set.size := size
        |}) in
    let elt : Set := elt in
    let elt_ty := Box.(Boxed_set.elt_ty) in
    let OPS := Box.(Boxed_set.OPS) in
    let boxed := Box.(Boxed_set.boxed) in
    let size :=
      let Result := result_value in
      let 'existS _ _ Result := Result in
      Result.(Boxed_set.size) in
    {|
      Boxed_set.elt_ty := elt_ty;
      Boxed_set.OPS := OPS;
      Boxed_set.boxed := boxed;
      Boxed_set.size := size
    |}).

Module MAP.
  Record signature {key : Set} {t : Set -> Set} : Set := {
    key := key;
    t := t;
    empty : forall {a : Set}, t a;
    is_empty : forall {a : Set}, t a -> bool;
    mem : forall {a : Set}, key -> t a -> bool;
  }.
End MAP.
Definition MAP := @MAP.signature.
Arguments MAP {_ _}.
