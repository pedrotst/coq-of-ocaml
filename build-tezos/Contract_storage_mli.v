(** Generated by coq-of-ocaml *)
Require Import OCaml.OCaml.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Unset Positivity Checking.
Unset Guard Checking.

Require Import Tezos.Environment.
Require Tezos.Contract_repr.
Require Tezos.Raw_context.
Require Tezos.Script_expr_hash.
Require Tezos.Script_repr.
Require Tezos.Tez_repr.

(* extensible_type_definition `error` *)

Parameter __exists :
  Raw_context.t -> Contract_repr.t -> Lwt.t (Error_monad.tzresult bool).

Parameter must_exist :
  Raw_context.t -> Contract_repr.t -> Lwt.t (Error_monad.tzresult unit).

Parameter allocated :
  Raw_context.t -> Contract_repr.t -> Lwt.t (Error_monad.tzresult bool).

Parameter must_be_allocated :
  Raw_context.t -> Contract_repr.t -> Lwt.t (Error_monad.tzresult unit).

Parameter __list_value : Raw_context.t -> Lwt.t (list Contract_repr.t).

Parameter check_counter_increment :
  Raw_context.t -> (|Signature.Public_key_hash|).(S.SPublic_key_hash.t) ->
  Z.t -> Lwt.t (Error_monad.tzresult unit).

Parameter increment_counter :
  Raw_context.t -> (|Signature.Public_key_hash|).(S.SPublic_key_hash.t) ->
  Lwt.t (Error_monad.tzresult Raw_context.t).

Parameter get_manager_key :
  Raw_context.t -> (|Signature.Public_key_hash|).(S.SPublic_key_hash.t) ->
  Lwt.t (Error_monad.tzresult (|Signature.Public_key|).(S.SPublic_key.t)).

Parameter is_manager_key_revealed :
  Raw_context.t -> (|Signature.Public_key_hash|).(S.SPublic_key_hash.t) ->
  Lwt.t (Error_monad.tzresult bool).

Parameter reveal_manager_key :
  Raw_context.t -> (|Signature.Public_key_hash|).(S.SPublic_key_hash.t) ->
  (|Signature.Public_key|).(S.SPublic_key.t) ->
  Lwt.t (Error_monad.tzresult Raw_context.t).

Parameter get_balance :
  Raw_context.t -> Contract_repr.t -> Lwt.t (Error_monad.tzresult Tez_repr.t).

Parameter get_counter :
  Raw_context.t -> (|Signature.Public_key_hash|).(S.SPublic_key_hash.t) ->
  Lwt.t (Error_monad.tzresult Z.t).

Parameter get_script_code :
  Raw_context.t -> Contract_repr.t ->
  Lwt.t (Error_monad.tzresult (Raw_context.t * option Script_repr.lazy_expr)).

Parameter get_script :
  Raw_context.t -> Contract_repr.t ->
  Lwt.t (Error_monad.tzresult (Raw_context.t * option Script_repr.t)).

Parameter get_storage :
  Raw_context.t -> Contract_repr.t ->
  Lwt.t (Error_monad.tzresult (Raw_context.t * option Script_repr.expr)).

Module big_map_diff_item.
  Module Update.
    Record record {big_map diff_key diff_key_hash diff_value : Set} : Set := {
      big_map : big_map;
      diff_key : diff_key;
      diff_key_hash : diff_key_hash;
      diff_value : diff_value }.
    Arguments record : clear implicits.
  End Update.
  Definition Update_skeleton := Update.record.
  
  Module Alloc.
    Record record {big_map key_type value_type : Set} : Set := {
      big_map : big_map;
      key_type : key_type;
      value_type : value_type }.
    Arguments record : clear implicits.
  End Alloc.
  Definition Alloc_skeleton := Alloc.record.
End big_map_diff_item.

Reserved Notation "'big_map_diff_item.Update".
Reserved Notation "'big_map_diff_item.Alloc".

Inductive big_map_diff_item : Set :=
| Update : 'big_map_diff_item.Update -> big_map_diff_item
| Clear : Z.t -> big_map_diff_item
| Copy : Z.t -> Z.t -> big_map_diff_item
| Alloc : 'big_map_diff_item.Alloc -> big_map_diff_item

where "'big_map_diff_item.Update" :=
  (big_map_diff_item.Update_skeleton Z.t Script_repr.expr Script_expr_hash.t
    (option Script_repr.expr))
and "'big_map_diff_item.Alloc" :=
  (big_map_diff_item.Alloc_skeleton Z.t Script_repr.expr Script_repr.expr).

Module ConstructorRecordNotations_big_map_diff_item.
  Module big_map_diff_item.
    Definition Update := 'big_map_diff_item.Update.
    Definition Alloc := 'big_map_diff_item.Alloc.
  End big_map_diff_item.
End ConstructorRecordNotations_big_map_diff_item.
Import ConstructorRecordNotations_big_map_diff_item.

Definition big_map_diff : Set := list big_map_diff_item.

Parameter big_map_diff_encoding : Data_encoding.t big_map_diff.

Parameter update_script_storage :
  Raw_context.t -> Contract_repr.t -> Script_repr.expr -> option big_map_diff ->
  Lwt.t (Error_monad.tzresult Raw_context.t).

Parameter credit :
  Raw_context.t -> Contract_repr.t -> Tez_repr.t ->
  Lwt.t (Error_monad.tzresult Raw_context.t).

Parameter spend :
  Raw_context.t -> Contract_repr.t -> Tez_repr.t ->
  Lwt.t (Error_monad.tzresult Raw_context.t).

Parameter originate_raw :
  Raw_context.t -> option bool -> Contract_repr.t -> Tez_repr.t ->
  Script_repr.t * option big_map_diff ->
  option (|Signature.Public_key_hash|).(S.SPublic_key_hash.t) ->
  Lwt.t (Error_monad.tzresult Raw_context.t).

Parameter fresh_contract_from_current_nonce :
  Raw_context.t ->
  Lwt.t (Error_monad.tzresult (Raw_context.t * Contract_repr.t)).

Parameter originated_from_current_nonce :
  Raw_context.t -> Raw_context.t ->
  Lwt.t (Error_monad.tzresult (list Contract_repr.t)).

Parameter init : Raw_context.t -> Lwt.t (Error_monad.tzresult Raw_context.t).

Parameter used_storage_space :
  Raw_context.t -> Contract_repr.t -> Lwt.t (Error_monad.tzresult Z.t).

Parameter paid_storage_space :
  Raw_context.t -> Contract_repr.t -> Lwt.t (Error_monad.tzresult Z.t).

Parameter set_paid_storage_space_and_return_fees_to_pay :
  Raw_context.t -> Contract_repr.t -> Z.t ->
  Lwt.t (Error_monad.tzresult (Z.t * Raw_context.t)).
