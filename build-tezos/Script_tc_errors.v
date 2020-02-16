(** Generated by coq-of-ocaml *)
Require Import OCaml.OCaml.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Unset Positivity Checking.
Unset Guard Checking.

Require Import Tezos.Environment.
Require Tezos.Alpha_context.

Import Alpha_context.

Import Alpha_context.Script.

Inductive namespace : Set :=
| Type_namespace : namespace
| Constant_namespace : namespace
| Instr_namespace : namespace
| Keyword_namespace : namespace.

Inductive kind : Set :=
| Int_kind : kind
| String_kind : kind
| Bytes_kind : kind
| Prim_kind : kind
| Seq_kind : kind.

Definition unparsed_stack_ty : Set :=
  list (Alpha_context.Script.expr * Alpha_context.Script.annot).

Definition type_map : Set := list (Z * (unparsed_stack_ty * unparsed_stack_ty)).

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)
