(** Generated by coq-of-ocaml *)
Require Import OCaml.OCaml.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Unset Positivity Checking.
Unset Guard Checking.

Require Import Tezos.Environment.
Require Tezos.Blinded_public_key_hash.
Require Tezos.Block_header_repr.
Require Tezos.Contract_repr.
Require Tezos.Raw_level_repr.
Require Tezos.Script_repr.
Require Tezos.Seed_repr.
Require Tezos.Tez_repr.
Require Tezos.Vote_repr.
Require Tezos.Voting_period_repr.

Module Kind.
  Inductive seed_nonce_revelation : Set :=
  | Seed_nonce_revelation_kind : seed_nonce_revelation.
  
  Inductive double_endorsement_evidence : Set :=
  | Double_endorsement_evidence_kind : double_endorsement_evidence.
  
  Inductive double_baking_evidence : Set :=
  | Double_baking_evidence_kind : double_baking_evidence.
  
  Inductive activate_account : Set :=
  | Activate_account_kind : activate_account.
  
  Inductive endorsement : Set :=
  | Endorsement_kind : endorsement.
  
  Inductive proposals : Set :=
  | Proposals_kind : proposals.
  
  Inductive ballot : Set :=
  | Ballot_kind : ballot.
  
  Inductive reveal : Set :=
  | Reveal_kind : reveal.
  
  Inductive transaction : Set :=
  | Transaction_kind : transaction.
  
  Inductive origination : Set :=
  | Origination_kind : origination.
  
  Inductive delegation : Set :=
  | Delegation_kind : delegation.
  
  Reserved Notation "'manager".
  
  Inductive manager_gadt : Set :=
  | Reveal_manager_kind : manager_gadt
  | Transaction_manager_kind : manager_gadt
  | Origination_manager_kind : manager_gadt
  | Delegation_manager_kind : manager_gadt
  
  where "'manager" := (fun (_ : Set) => manager_gadt).
  
  Definition manager := 'manager.
End Kind.

Module raw.
  Record record : Set := Build {
    shell : Operation.shell_header;
    proto : MBytes.t }.
  Definition with_shell shell (r : record) :=
    Build shell r.(proto).
  Definition with_proto proto (r : record) :=
    Build r.(shell) proto.
End raw.
Definition raw := raw.record.

Parameter raw_encoding : Data_encoding.t raw.

Module contents.
  Module Endorsement.
    Record record {level : Set} : Set := {
      level : level }.
    Arguments record : clear implicits.
  End Endorsement.
  Definition Endorsement_skeleton := Endorsement.record.
  
  Module Seed_nonce_revelation.
    Record record {level nonce : Set} : Set := {
      level : level;
      nonce : nonce }.
    Arguments record : clear implicits.
  End Seed_nonce_revelation.
  Definition Seed_nonce_revelation_skeleton := Seed_nonce_revelation.record.
  
  Module Double_endorsement_evidence.
    Record record {op1 op2 : Set} : Set := {
      op1 : op1;
      op2 : op2 }.
    Arguments record : clear implicits.
  End Double_endorsement_evidence.
  Definition Double_endorsement_evidence_skeleton :=
    Double_endorsement_evidence.record.
  
  Module Double_baking_evidence.
    Record record {bh1 bh2 : Set} : Set := {
      bh1 : bh1;
      bh2 : bh2 }.
    Arguments record : clear implicits.
  End Double_baking_evidence.
  Definition Double_baking_evidence_skeleton := Double_baking_evidence.record.
  
  Module Activate_account.
    Record record {id activation_code : Set} : Set := {
      id : id;
      activation_code : activation_code }.
    Arguments record : clear implicits.
  End Activate_account.
  Definition Activate_account_skeleton := Activate_account.record.
  
  Module Proposals.
    Record record {source period proposals : Set} : Set := {
      source : source;
      period : period;
      proposals : proposals }.
    Arguments record : clear implicits.
  End Proposals.
  Definition Proposals_skeleton := Proposals.record.
  
  Module Ballot.
    Record record {source period proposal ballot : Set} : Set := {
      source : source;
      period : period;
      proposal : proposal;
      ballot : ballot }.
    Arguments record : clear implicits.
  End Ballot.
  Definition Ballot_skeleton := Ballot.record.
  
  Module Manager_operation.
    Record record {source fee counter operation gas_limit storage_limit : Set} :
      Set := {
      source : source;
      fee : fee;
      counter : counter;
      operation : operation;
      gas_limit : gas_limit;
      storage_limit : storage_limit }.
    Arguments record : clear implicits.
  End Manager_operation.
  Definition Manager_operation_skeleton := Manager_operation.record.
End contents.

Module manager_operation.
  Module Transaction.
    Record record {amount parameters entrypoint destination : Set} : Set := {
      amount : amount;
      parameters : parameters;
      entrypoint : entrypoint;
      destination : destination }.
    Arguments record : clear implicits.
  End Transaction.
  Definition Transaction_skeleton := Transaction.record.
  
  Module Origination.
    Record record {delegate script credit preorigination : Set} : Set := {
      delegate : delegate;
      script : script;
      credit : credit;
      preorigination : preorigination }.
    Arguments record : clear implicits.
  End Origination.
  Definition Origination_skeleton := Origination.record.
End manager_operation.

Module operation.
  Record record {shell protocol_data : Set} : Set := Build {
    shell : shell;
    protocol_data : protocol_data }.
  Arguments record : clear implicits.
  Definition with_shell {t_shell t_protocol_data} shell
    (r : record t_shell t_protocol_data) :=
    Build t_shell t_protocol_data shell r.(protocol_data).
  Definition with_protocol_data {t_shell t_protocol_data} protocol_data
    (r : record t_shell t_protocol_data) :=
    Build t_shell t_protocol_data r.(shell) protocol_data.
End operation.
Definition operation_skeleton := operation.record.

Module protocol_data.
  Record record {contents signature : Set} : Set := Build {
    contents : contents;
    signature : signature }.
  Arguments record : clear implicits.
  Definition with_contents {t_contents t_signature} contents
    (r : record t_contents t_signature) :=
    Build t_contents t_signature contents r.(signature).
  Definition with_signature {t_contents t_signature} signature
    (r : record t_contents t_signature) :=
    Build t_contents t_signature r.(contents) signature.
End protocol_data.
Definition protocol_data_skeleton := protocol_data.record.

Reserved Notation "'contents.Endorsement".
Reserved Notation "'contents.Seed_nonce_revelation".
Reserved Notation "'contents.Double_endorsement_evidence".
Reserved Notation "'contents.Double_baking_evidence".
Reserved Notation "'contents.Activate_account".
Reserved Notation "'contents.Proposals".
Reserved Notation "'contents.Ballot".
Reserved Notation "'contents.Manager_operation".
Reserved Notation "'manager_operation.Transaction".
Reserved Notation "'manager_operation.Origination".
Reserved Notation "'contents_list".
Reserved Notation "'protocol_data".
Reserved Notation "'operation".
Reserved Notation "'contents".
Reserved Notation "'manager_operation".
Reserved Notation "'counter".

Inductive contents_list_gadt : Set :=
| Single : forall {kind : Set}, 'contents kind -> contents_list_gadt
| Cons : forall {kind : Set},
  'contents (Kind.manager kind) -> contents_list_gadt -> contents_list_gadt

with contents_gadt : Set :=
| Endorsement : 'contents.Endorsement -> contents_gadt
| Seed_nonce_revelation : 'contents.Seed_nonce_revelation -> contents_gadt
| Double_endorsement_evidence :
  'contents.Double_endorsement_evidence -> contents_gadt
| Double_baking_evidence : 'contents.Double_baking_evidence -> contents_gadt
| Activate_account : 'contents.Activate_account -> contents_gadt
| Proposals : 'contents.Proposals -> contents_gadt
| Ballot : 'contents.Ballot -> contents_gadt
| Manager_operation : forall {kind : Set},
  'contents.Manager_operation kind -> contents_gadt

with manager_operation_gadt : Set :=
| Reveal : (|Signature.Public_key|).(S.SPublic_key.t) -> manager_operation_gadt
| Transaction : 'manager_operation.Transaction -> manager_operation_gadt
| Origination : 'manager_operation.Origination -> manager_operation_gadt
| Delegation :
  option (|Signature.Public_key_hash|).(S.SPublic_key_hash.t) ->
  manager_operation_gadt

where "'contents_list" := (fun (_ : Set) => contents_list_gadt)
and "'protocol_data" := (fun (t_kind : Set) =>
  protocol_data_skeleton ('contents_list t_kind) (option Signature.t))
and "'operation" := (fun (t_kind : Set) =>
  operation_skeleton Operation.shell_header ('protocol_data t_kind))
and "'contents" := (fun (_ : Set) => contents_gadt)
and "'manager_operation" := (fun (_ : Set) => manager_operation_gadt)
and "'counter" := (Z.t)
and "'contents.Endorsement" := (contents.Endorsement_skeleton Raw_level_repr.t)
and "'contents.Seed_nonce_revelation" :=
  (contents.Seed_nonce_revelation_skeleton Raw_level_repr.t Seed_repr.nonce)
and "'contents.Double_endorsement_evidence" :=
  (contents.Double_endorsement_evidence_skeleton ('operation Kind.endorsement)
    ('operation Kind.endorsement))
and "'contents.Double_baking_evidence" :=
  (contents.Double_baking_evidence_skeleton Block_header_repr.t
    Block_header_repr.t)
and "'contents.Activate_account" :=
  (contents.Activate_account_skeleton
    (|Ed25519|).(S.SIGNATURE.Public_key_hash).(S.SPublic_key_hash.t)
    Blinded_public_key_hash.activation_code)
and "'contents.Proposals" :=
  (contents.Proposals_skeleton
    (|Signature.Public_key_hash|).(S.SPublic_key_hash.t) Voting_period_repr.t
    (list (|Protocol_hash|).(S.HASH.t)))
and "'contents.Ballot" :=
  (contents.Ballot_skeleton (|Signature.Public_key_hash|).(S.SPublic_key_hash.t)
    Voting_period_repr.t (|Protocol_hash|).(S.HASH.t) Vote_repr.ballot)
and "'contents.Manager_operation" := (fun (t_kind : Set) =>
  contents.Manager_operation_skeleton
    (|Signature.Public_key_hash|).(S.SPublic_key_hash.t) Tez_repr.tez 'counter
    ('manager_operation t_kind) Z.t Z.t)
and "'manager_operation.Transaction" :=
  (manager_operation.Transaction_skeleton Tez_repr.tez Script_repr.lazy_expr
    string Contract_repr.contract)
and "'manager_operation.Origination" :=
  (manager_operation.Origination_skeleton
    (option (|Signature.Public_key_hash|).(S.SPublic_key_hash.t)) Script_repr.t
    Tez_repr.tez (option Contract_repr.t)).

Module
  ConstructorRecordNotations_contents_list_gadt_contents_gadt_manager_operation_gadt.
  Module contents.
    Definition Endorsement := 'contents.Endorsement.
    Definition Seed_nonce_revelation := 'contents.Seed_nonce_revelation.
    Definition Double_endorsement_evidence :=
      'contents.Double_endorsement_evidence.
    Definition Double_baking_evidence := 'contents.Double_baking_evidence.
    Definition Activate_account := 'contents.Activate_account.
    Definition Proposals := 'contents.Proposals.
    Definition Ballot := 'contents.Ballot.
    Definition Manager_operation := 'contents.Manager_operation.
  End contents.
  Module manager_operation.
    Definition Transaction := 'manager_operation.Transaction.
    Definition Origination := 'manager_operation.Origination.
  End manager_operation.
End
  ConstructorRecordNotations_contents_list_gadt_contents_gadt_manager_operation_gadt.
Import
  ConstructorRecordNotations_contents_list_gadt_contents_gadt_manager_operation_gadt.

Definition contents_list := 'contents_list.
Definition protocol_data := 'protocol_data.
Definition operation := 'operation.
Definition contents := 'contents.
Definition manager_operation := 'manager_operation.
Definition counter := 'counter.

Module internal_operation.
  Record record {kind : Set} : Set := Build {
    source : Contract_repr.contract;
    operation : manager_operation kind;
    nonce : Z }.
  Arguments record : clear implicits.
  Definition with_source {t_kind} source (r : record t_kind) :=
    Build t_kind source r.(operation) r.(nonce).
  Definition with_operation {t_kind} operation (r : record t_kind) :=
    Build t_kind r.(source) operation r.(nonce).
  Definition with_nonce {t_kind} nonce (r : record t_kind) :=
    Build t_kind r.(source) r.(operation) nonce.
End internal_operation.
Definition internal_operation := internal_operation.record.

Inductive packed_manager_operation : Set :=
| Manager : forall {kind : Set},
  manager_operation kind -> packed_manager_operation.

Inductive packed_contents : Set :=
| Contents : forall {kind : Set}, contents kind -> packed_contents.

Inductive packed_contents_list : Set :=
| Contents_list : forall {kind : Set},
  contents_list kind -> packed_contents_list.

Parameter of_list : list packed_contents -> packed_contents_list.

Parameter to_list : packed_contents_list -> list packed_contents.

Inductive packed_protocol_data : Set :=
| Operation_data : forall {kind : Set},
  protocol_data kind -> packed_protocol_data.

Module packed_operation.
  Record record : Set := Build {
    shell : Operation.shell_header;
    protocol_data : packed_protocol_data }.
  Definition with_shell shell (r : record) :=
    Build shell r.(protocol_data).
  Definition with_protocol_data protocol_data (r : record) :=
    Build r.(shell) protocol_data.
End packed_operation.
Definition packed_operation := packed_operation.record.

Parameter pack : forall {kind : Set}, operation kind -> packed_operation.

Inductive packed_internal_operation : Set :=
| Internal_operation : forall {kind : Set},
  internal_operation kind -> packed_internal_operation.

Parameter manager_kind : forall {kind : Set},
  manager_operation kind -> Kind.manager kind.

Parameter encoding : Data_encoding.t packed_operation.

Parameter contents_encoding : Data_encoding.t packed_contents.

Parameter contents_list_encoding : Data_encoding.t packed_contents_list.

Parameter protocol_data_encoding : Data_encoding.t packed_protocol_data.

Parameter unsigned_operation_encoding :
  Data_encoding.t (Operation.shell_header * packed_contents_list).

Parameter __raw_value : forall {A : Set}, operation A -> raw.

Parameter hash_raw : raw -> (|Operation_hash|).(S.HASH.t).

Parameter __hash_value : forall {A : Set},
  operation A -> (|Operation_hash|).(S.HASH.t).

Parameter hash_packed : packed_operation -> (|Operation_hash|).(S.HASH.t).

Parameter acceptable_passes : packed_operation -> list Z.

(* extensible_type_definition `error` *)

(* extensible_type_definition `error` *)

Parameter check_signature : forall {A : Set},
  (|Signature.Public_key|).(S.SPublic_key.t) -> (|Chain_id|).(S.HASH.t) ->
  operation A -> Lwt.t (Error_monad.tzresult unit).

Parameter check_signature_sync : forall {A : Set},
  (|Signature.Public_key|).(S.SPublic_key.t) -> (|Chain_id|).(S.HASH.t) ->
  operation A -> Error_monad.tzresult unit.

Parameter internal_operation_encoding :
  Data_encoding.t packed_internal_operation.

Reserved Notation "'eq".

Inductive eq_gadt : Set :=
| Eq : eq_gadt

where "'eq" := (fun (_ _ : Set) => eq_gadt).

Definition eq := 'eq.

Parameter equal : forall {a b : Set},
  operation a -> operation b -> option (eq a b).

Module Encoding.
  Module case.
    Module Case.
      Record record {tag name encoding select proj inj : Set} : Set := {
        tag : tag;
        name : name;
        encoding : encoding;
        select : select;
        proj : proj;
        inj : inj }.
      Arguments record : clear implicits.
    End Case.
    Definition Case_skeleton := Case.record.
  End case.
  
  Reserved Notation "'case.Case".
  
  Inductive case (b : Set) : Set :=
  | Case : forall {a : Set}, 'case.Case a b -> case b
  
  where "'case.Case" := (fun (t_a t_b : Set) =>
    case.Case_skeleton Z string (Data_encoding.t t_a)
      (packed_contents -> option (contents t_b)) (contents t_b -> t_a)
      (t_a -> contents t_b)).
  
  Module ConstructorRecordNotations_case.
    Module case.
      Definition Case := 'case.Case.
    End case.
  End ConstructorRecordNotations_case.
  Import ConstructorRecordNotations_case.
  
  Arguments Case {_ _}.
  
  Parameter endorsement_case : case Kind.endorsement.
  
  Parameter seed_nonce_revelation_case : case Kind.seed_nonce_revelation.
  
  Parameter double_endorsement_evidence_case :
    case Kind.double_endorsement_evidence.
  
  Parameter double_baking_evidence_case : case Kind.double_baking_evidence.
  
  Parameter activate_account_case : case Kind.activate_account.
  
  Parameter proposals_case : case Kind.proposals.
  
  Parameter ballot_case : case Kind.ballot.
  
  Parameter reveal_case : case (Kind.manager Kind.reveal).
  
  Parameter transaction_case : case (Kind.manager Kind.transaction).
  
  Parameter origination_case : case (Kind.manager Kind.origination).
  
  Parameter delegation_case : case (Kind.manager Kind.delegation).
  
  Module Manager_operations.
    Module case.
      Module MCase.
        Record record {tag name encoding select proj inj : Set} : Set := {
          tag : tag;
          name : name;
          encoding : encoding;
          select : select;
          proj : proj;
          inj : inj }.
        Arguments record : clear implicits.
      End MCase.
      Definition MCase_skeleton := MCase.record.
    End case.
    
    Reserved Notation "'case.MCase".
    Reserved Notation "'case".
    
    Inductive case_gadt : Set :=
    | MCase : forall {a kind : Set}, 'case.MCase a kind -> case_gadt
    
    where "'case" := (fun (_ : Set) => case_gadt)
    and "'case.MCase" := (fun (t_a t_kind : Set) =>
      case.MCase_skeleton Z string (Data_encoding.t t_a)
        (packed_manager_operation -> option (manager_operation t_kind))
        (manager_operation t_kind -> t_a) (t_a -> manager_operation t_kind)).
    
    Module ConstructorRecordNotations_case_gadt.
      Module case.
        Definition MCase := 'case.MCase.
      End case.
    End ConstructorRecordNotations_case_gadt.
    Import ConstructorRecordNotations_case_gadt.
    
    Definition case := 'case.
    
    Parameter reveal_case : case Kind.reveal.
    
    Parameter transaction_case : case Kind.transaction.
    
    Parameter origination_case : case Kind.origination.
    
    Parameter delegation_case : case Kind.delegation.
  End Manager_operations.
End Encoding.
