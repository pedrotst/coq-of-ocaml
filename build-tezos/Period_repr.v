(** Generated by coq-of-ocaml *)
Require Import OCaml.OCaml.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Unset Positivity Checking.
Unset Guard Checking.

Require Import Tezos.Environment.

Definition t : Set := Int64.t.

Definition period : Set := t.

Definition op_eq := (|Compare.Int64|).(Compare.S.op_eq).

Definition op_ltgt := (|Compare.Int64|).(Compare.S.op_ltgt).

Definition op_lt := (|Compare.Int64|).(Compare.S.op_lt).

Definition op_lteq := (|Compare.Int64|).(Compare.S.op_lteq).

Definition op_gteq := (|Compare.Int64|).(Compare.S.op_gteq).

Definition op_gt := (|Compare.Int64|).(Compare.S.op_gt).

Definition compare := (|Compare.Int64|).(Compare.S.compare).

Definition equal := (|Compare.Int64|).(Compare.S.equal).

Definition max := (|Compare.Int64|).(Compare.S.max).

Definition min := (|Compare.Int64|).(Compare.S.min).

Definition encoding : Data_encoding.encoding int64 :=
  Data_encoding.__int64_value.

Definition rpc_arg : RPC_arg.arg int64 := RPC_arg.__int64_value.

Definition pp (ppf : Format.formatter) (v : int64) : unit :=
  Format.fprintf ppf
    (CamlinternalFormatBasics.Format
      (CamlinternalFormatBasics.Int64 CamlinternalFormatBasics.Int_d
        CamlinternalFormatBasics.No_padding
        CamlinternalFormatBasics.No_precision
        CamlinternalFormatBasics.End_of_format) "%Ld") v.

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Top-level evaluations are ignored *)
(* top_level_evaluation *)

Definition of_seconds (__t_value : (|Compare.Int64|).(Compare.S.t))
  : Error_monad.tzresult (|Compare.Int64|).(Compare.S.t) :=
  if
    (|Compare.Int64|).(Compare.S.op_gteq) __t_value
      (* ❌ Constant of type int64 is converted to int *)
      0 then
    Error_monad.ok __t_value
  else
    Error_monad.__error_value extensible_type_value.

Definition to_seconds {A : Set} (__t_value : A) : A := __t_value.

Definition of_seconds_exn (__t_value : (|Compare.Int64|).(Compare.S.t))
  : (|Compare.Int64|).(Compare.S.t) :=
  match of_seconds __t_value with
  | Pervasives.Ok __t_value => __t_value
  | _ => Pervasives.invalid_arg "Period.of_seconds_exn"
  end.

Definition mult (i : (|Compare.Int32|).(Compare.S.t)) (__p_value : int64)
  : Error_monad.tzresult int64 :=
  if
    (|Compare.Int32|).(Compare.S.op_lt) i
      (* ❌ Constant of type int32 is converted to int *)
      0 then
    Error_monad.__error_value extensible_type_value
  else
    Error_monad.ok (Int64.mul (Int64.of_int32 i) __p_value).

Definition zero : (|Compare.Int64|).(Compare.S.t) :=
  of_seconds_exn
    (* ❌ Constant of type int64 is converted to int *)
    0.

Definition one_second : (|Compare.Int64|).(Compare.S.t) :=
  of_seconds_exn
    (* ❌ Constant of type int64 is converted to int *)
    1.

Definition one_minute : (|Compare.Int64|).(Compare.S.t) :=
  of_seconds_exn
    (* ❌ Constant of type int64 is converted to int *)
    60.

Definition one_hour : (|Compare.Int64|).(Compare.S.t) :=
  of_seconds_exn
    (* ❌ Constant of type int64 is converted to int *)
    3600.
