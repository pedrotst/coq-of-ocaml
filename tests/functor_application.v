Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

(** Some documentation *)
Module Source.
  Record signature {t : Set} : Set := {
    t := t;
    (** The description of [x] *)
    x : t;
    id : forall {a : Set}, a -> a;
  }.
End Source.
Definition Source := @Source.signature.
Arguments Source {_}.

Module Target.
  Record signature {t : Set} : Set := {
    t := t;
    y : t;
  }.
End Target.
Definition Target := @Target.signature.
Arguments Target {_}.

Module M.
  Definition t := int.
  
  Definition x : int := 12.
  
  Definition id {A : Set} (x : A) : A := x.
  
  Definition module :=
    {|
      Source.x := x;
      Source.id _ := id
    |}.
End M.
Definition M : Source (t := _) := M.module.

Module F.
  Class FArgs {X_t : Set} := {
    X : Source (t := X_t);
  }.
  Arguments Build_FArgs {_}.
  
  Definition t `{FArgs} := X.(Source.t).
  
  Definition y `{FArgs} : X.(Source.t) := X.(Source.x).
  
  Definition functor `{FArgs} :=
    {|
      Target.y := y
    |}.
End F.
Definition F {X_t : Set} (X : Source (t := X_t)) : Target (t := X.(Source.t)) :=
  let '_ := F.Build_FArgs X in
  F.functor.

Definition FM := F M.

Module FSubst.
  Class FArgs {X_t : Set} := {
    X : Source (t := X_t);
  }.
  Arguments Build_FArgs {_}.
  
  Definition y `{FArgs} : X.(Source.t) := X.(Source.x).
  
  Definition functor `{FArgs} :=
    {|
      Target.y := y
    |}.
End FSubst.
Definition FSubst {X_t : Set} (X : Source (t := X_t))
  : Target (t := X.(Source.t)) :=
  let '_ := FSubst.Build_FArgs X in
  FSubst.functor.

Module Sum.
  Class FArgs := {
    X : Source (t := int);
    Y : Source (t := int);
  }.
  
  Definition t `{FArgs} := int.
  
  Definition y `{FArgs} : int := Z.add X.(Source.x) Y.(Source.x).
  
  Definition functor `{FArgs} :=
    {|
      Target.y := y
    |}.
End Sum.
Definition Sum (X : Source (t := int)) (Y : Source (t := int)) : Target (t := _)
  :=
  let '_ := Sum.Build_FArgs X Y in
  Sum.functor.

Module WithM.
  (** Inclusion of the module [M] *)
  Definition t := M.(Source.t).
  
  Definition x := M.(Source.x).
  
  Definition id {a : Set} := M.(Source.id) (a := a).
  
  Definition z : int := 0.
End WithM.

Module WithSum.
  Definition F_include := F M.
  
  (** Inclusion of the module [F_include] *)
  Definition t := F_include.(Target.t).
  
  Definition y := F_include.(Target.y).
  
  Definition z : int := 0.
End WithSum.

Module GenFun.
  Definition t := int.
  
  Definition y : int := 23.
  
  Definition module :=
    {|
      Target.y := y
    |}.
End GenFun.
Definition GenFun : Target (t := _) := GenFun.module.

Definition AppliedGenFun : Target (t := _) := GenFun.

Module LargeTarget.
  Record signature {t : Set} : Set := {
    t := t;
    y : t;
    z : t;
  }.
End LargeTarget.
Definition LargeTarget := @LargeTarget.signature.
Arguments LargeTarget {_}.

Module LargeF.
  Class FArgs {X_t : Set} := {
    X : Source (t := X_t);
  }.
  Arguments Build_FArgs {_}.
  
  Definition t `{FArgs} := X.(Source.t).
  
  Definition y `{FArgs} : X.(Source.t) := X.(Source.x).
  
  Definition z `{FArgs} : X.(Source.t) := y.
  
  Definition functor `{FArgs} :=
    {|
      LargeTarget.y := y;
      LargeTarget.z := z
    |}.
End LargeF.
Definition LargeF {X_t : Set} (X : Source (t := X_t)) : LargeTarget (t := _) :=
  let '_ := LargeF.Build_FArgs X in
  LargeF.functor.

Definition CastedLarge : Target (t := _) :=
  let functor_result := LargeF M in
  {|
    Target.y := functor_result.(LargeTarget.y)
  |}.
