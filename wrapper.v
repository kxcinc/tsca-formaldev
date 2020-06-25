From mathcomp Require Import all_ssreflect.
From Michocoq Require Import semantics util macros.
Import syntax comparable error.
Require Import ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition parameter_ty := Comparable_type bytes.
Definition storage_ty :=
  (pair
     (lambda (pair bytes bytes) (pair (list operation) bytes)) (* wfunc *)
     (pair bytes (* wstorage *)
           (option (pair address (pair string string))))).
Module wrapper(C : ContractContext).
Module semantics := Semantics C. Import semantics.
Require Import String.
Open Scope string_scope.

Definition wrapper : full_contract false parameter_ty None storage_ty :=
{DUP; CDR; DIP1 {CAR}};;;
{
  SWAP;
  DIP1 {DUP; CDR; CAR};
  PAIR;
  DIP1 {DUP; CAR};
  EXEC;
  UNPAIR;
  DIIP {UNPAIR};
  DIIIP {UNPAIR; DROP1};
  DIIP {SWAP};
  DIP1 {PAIR};
  DIP1 {SWAP; PAIR};
  PAIR
}.
End wrapper.
