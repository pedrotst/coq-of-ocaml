Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Definition foo := string.

Reserved Notation "'double".
Reserved Notation "'simple".

Inductive tree (a : Set) : Set :=
| Tree : list (node a) -> tree a

with node (a : Set) : Set :=
| Leaf : string -> node a
| Node : tree a -> node a

with unrelated (a : Set) : Set :=
| Unrelated : 'double ('simple a) -> unrelated a

where "'simple" := (fun (t_b : Set) => t_b)
and "'double" := (fun (t_b : Set) => t_b * 'simple t_b).

Definition double := 'double.
Definition simple := 'simple.

Arguments Tree {_}.
Arguments Leaf {_}.
Arguments Node {_}.
Arguments Unrelated {_}.

Module re_bis.
  Record record {bis : Set} : Set := Build {
    bis : bis }.
  Arguments record : clear implicits.
  Definition with_bis {t_bis} bis (r : record t_bis) :=
    Build t_bis bis.
End re_bis.
Definition re_bis_skeleton := re_bis.record.

Module re.
  Record record {payload message : Set} : Set := Build {
    payload : payload;
    message : message }.
  Arguments record : clear implicits.
  Definition with_payload {t_payload t_message} payload
    (r : record t_payload t_message) :=
    Build t_payload t_message payload r.(message).
  Definition with_message {t_payload t_message} message
    (r : record t_payload t_message) :=
    Build t_payload t_message r.(payload) message.
End re.
Definition re_skeleton := re.record.

Reserved Notation "'re".
Reserved Notation "'re_bis".

Inductive ind : Set :=
| Ind : 're int -> ind

where "'re" := (fun (t_a : Set) => re_skeleton t_a string)
and "'re_bis" := (re_bis_skeleton unit).

Definition re := 're.
Definition re_bis := 're_bis.
