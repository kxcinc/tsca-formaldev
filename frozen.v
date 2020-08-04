From mathcomp Require Import all_ssreflect.
From Michocoq Require Import semantics util macros.
Import syntax comparable error.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition parameter_ty := pair (mutez (* amount *)) (address (* beneficiary *)).
Definition storage_ty :=
  pair (set (* fund_owners *) address) (timestamp (* unfrozen *)).

Module frozen(C : ContractContext).
Module semantics := Semantics C. Import semantics.
Require Import String.
Open Scope string_scope.

Definition zero :=
  Mutez_constant (Mk_mutez (extract (tez.of_Z BinNums.Z0) I)).

Definition validate_invocation {self_type S} :
  instruction_seq self_type false (pair parameter_ty storage_ty ::: S) S :=
  {
    AMOUNT; PUSH mutez zero; COMPARE; LT;
    IF_TRUE {FAILWITH} { };
    UNPAIR; DIP1 {UNPAIR}; SWAP; SOURCE; @MEM _ _ _ (mem_set _) _;
    IF_TRUE { } {FAILWITH};
    SWAP; NOW; COMPARE; GT;
    IF_TRUE {FAILWITH} { };
    UNPAIR; BALANCE; COMPARE; GT;
    IF_TRUE {FAILWITH} { };
    DROP1
  }.
Definition perform_withdraw {self_type S} :
  instruction_seq self_type false (parameter_ty ::: S) (operation ::: S) :=
  {
    UNPAIR; SWAP; CONTRACT (Some "") unit;
    IF_NONE {FAILWITH} {SWAP; PUSH unit Unit; TRANSFER_TOKENS}
  }.

Definition frozen : full_contract false parameter_ty None storage_ty :=
  DUP;; validate_invocation;;;
  UNPAIR;; perform_withdraw;;;
  {DIP1 {NIL operation}; CONS; PAIR}.
End frozen.
