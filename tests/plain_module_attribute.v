Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Module T.
  Record signature {t : Set} : Set := {
    t := t;
    to_string : t -> string;
  }.
End T.
Definition T := @T.signature.
Arguments T {_}.

Module M.
  Definition t := int.
  
  Definition to_string : int -> string := CoqOfOCaml.Stdlib.string_of_int.
End M.

Definition int_to_string : int -> string := M.to_string.
