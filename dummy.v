From mathcomp Require Import all_ssreflect.
From Michocoq Require Import semantics
Import syntax comparable error.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import String.
Open Scope string_scope.

Definition parameter_ty := unit.
Definition storage_ty := unit.
Module dummy(C:ContractContext).
Require Import String.
Open Scope string_scope.
Module semantics := Semantics C. Import semantics.

Definition dummy_contract
  : full_contract false parameter_ty (Some "dummy") storage_ty :=
  {
    CDR;
    NIL operation;
    PAIR
  }.

Definition dummy_file :=
  {|
    contract_file_parameter := parameter_ty;
    contract_file_annotation := Some "dummy";
    contract_file_storage := storage_ty;
    contract_tff := false;
    contract_file_code := dummy_contract
  |}.
End dummy.
