From mathcomp Require Import all_ssreflect.
From Michocoq Require Import semantics util macros.
Import syntax comparable error.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module crowdfunding(C : ContractContext).
Module semantics := Semantics C. Import semantics.
Require Import String.
Open Scope string_scope.
Open Scope michelson_scope.

Definition parameter_ty :=
  or key_hash (Some "refund_address")
     (or address (Some "beneficiary") address (Some "eligible_address")) None.

Definition storage_ty :=
  (pair
     (pair (set (* %raisers *) address) (big_map (* %refund_table *) address mutez))
     (pair (pair (bool (* %withdrawn *)) (timestamp (* %funding_start *)))
           (pair (timestamp (* %funding_end *)) (timestamp (* %unconditional_refund_start *))))).

Definition funding_start {self_type S} :
  instruction_seq self_type false
                  (storage_ty ::: S)
                  (timestamp ::: storage_ty ::: S) :=
  {DUP; UNPAIR; DROP1; UNPAIR; UNPAIR; DROP1; DIP1 {DROP1}}.

Definition funding_end {self_type S} :
  instruction_seq self_type false
                  (storage_ty ::: S)
                  (timestamp ::: storage_ty ::: S) :=
  {DUP; UNPAIR; DROP1; UNPAIR; DROP1; UNPAIR; DIP1 {DROP1}}.

Definition refund_table {self_type S} :
  instruction_seq self_type false
                  (storage_ty ::: S)
                  (big_map address mutez::: storage_ty ::: S) :=
  {DUP; UNPAIR; DIP1 {DROP1}; UNPAIR; DROP1}.

Definition update_refund_table {self_type S} :
  instruction_seq self_type false
                  (big_map address mutez::: storage_ty ::: S)
                  (storage_ty ::: S) :=
  {SWAP; UNPAIR; UNPAIR; DIP1 {DROP1; SWAP}; PAIR; PAIR}.

Definition validate_time {self_type S} :
  instruction_seq self_type false
                  (storage_ty ::: S)
                  (storage_ty ::: S) :=
  funding_start;;; {NOW; COMPARE; LE;
  DIP1 funding_end; DIP1 {NOW; SWAP; COMPARE; LE}; AND; NOT;
  IF_TRUE {FAILWITH} { }}.

Definition unconditional_refund_start {self_type S} :
  instruction_seq self_type false
                  (storage_ty ::: S)
                  (timestamp ::: storage_ty ::: S) :=
  {DUP; UNPAIR; DROP1; UNPAIR; DROP1; UNPAIR; DROP1}.

Definition raisers {self_type S} :
  instruction_seq self_type false
                  (storage_ty ::: S)
                  (set address::: storage_ty ::: S) :=
  {DUP; UNPAIR; DIP1 {DROP1}; UNPAIR; DIP1 {DROP1}}.

Definition withdrawn {self_type S} :
  instruction_seq self_type false
                  (storage_ty ::: S)
                  (bool ::: storage_ty ::: S) :=
  {DUP; UNPAIR; DROP1; UNPAIR; DIP1 {DROP1}; UNPAIR; DIP1 {DROP1}}.

Definition set_withdrawn {self_type S} :
  instruction_seq self_type false
                  (storage_ty ::: S)
                  (storage_ty ::: S) :=
  {UNPAIR; DIP1 {UNPAIR; UNPAIR; DROP1; PUSH bool True; PAIR; PAIR}; PAIR}.

Definition validate_withdraw {self_type S} :
  instruction_seq self_type false
                  (storage_ty ::: S)
                  (storage_ty ::: S) :=
 funding_start;;; NOW;; COMPARE;; LE;;
 {DIP1 funding_end; DIP1 {NOW; SWAP; COMPARE; LE}; AND; NOT};;;
 DIP1 {NOW; DIP1 unconditional_refund_start; SWAP; COMPARE; LE};;
 @OR _ _ bitwise_bool _;; IF_TRUE {FAILWITH} { };;
 withdrawn;;; IF_TRUE {FAILWITH} { };;
 raisers;;; {SOURCE; @MEM _ _ _ (mem_set address) _;
             NOT; IF_TRUE {FAILWITH} { }}.

Definition create_transfer {self_type S} :
  instruction_seq self_type false
                  (mutez ::: address ::: storage_ty ::: S)
                  (operation ::: storage_ty ::: S) :=
  {DIP1 {CONTRACT None unit}; SWAP;
   IF_NONE {FAILWITH}
           {SWAP; UNIT; TRANSFER_TOKENS}}.

Definition validate_refund {self_type S} :
  instruction_seq self_type false
                  (storage_ty ::: S)
                  (storage_ty ::: S) :=
{NOW; DIP1 unconditional_refund_start; SWAP; COMPARE; LT};;;
 IF_TRUE {FAILWITH} { };; withdrawn;;; {IF_TRUE {FAILWITH} { }}.

Definition crowdfunding : full_contract false parameter_ty None storage_ty.
  apply: (DUP;; _).
  apply: (CAR;; _).
  apply: (DIP1 {CDR};; _).
  apply: (IF_LEFT (_ : instruction_seq (Some (parameter_ty, None)) false _ _) (_ : instruction_seq (Some (parameter_ty, None)) false _ _);; NOOP).
   apply: (IMPLICIT_ACCOUNT;; ADDRESS;; _).
   apply: (DUP;; _).
   apply: (DIIP refund_table;; _).
   apply: (DIP1 {@GET _ _ _ (get_bigmap address mutez) _};; _).
   apply: (DIP1 {IF_SOME {AMOUNT; @ADD _ _ _ add_tez_tez _} {AMOUNT}};; _).
   apply: (DIP1 {SOME};; _).
   apply: (DIIP refund_table;; _).
   apply: (@UPDATE _ _ _ _ (update_bigmap address mutez) _;; _).
   apply: (DIP1 validate_time;; _).
   apply: (update_refund_table;;; _).
   apply: (NIL operation;; PAIR;; NOOP).
  apply: (IF_LEFT (_ : instruction_seq (Some (parameter_ty, None)) false _ _) (_ : instruction_seq (Some (parameter_ty, None)) false _ _);; NOOP).
   apply: (DIP1 validate_withdraw;; _).
   apply: (BALANCE;; _).
   apply: (create_transfer;;; _).
   apply: (NIL operation;; SWAP;; CONS;; DIP1 set_withdrawn;; PAIR;; NOOP).
  apply: (DIP1 refund_table;; DUP;; _).
  apply: (DIP1 {@GET _ _ _ (get_bigmap address mutez) _};; SWAP;; _).
  apply: (IF_NONE {FAILWITH} (_ : instruction_seq _ false _ _);; NOOP).
  apply: (SWAP;; DIP1 {SWAP};; _).
  apply: (NONE mutez;; DIIP refund_table;; SWAP;; (_ : instruction_seq _ false _ _)).
  apply: (DUP;; _).
  apply: (DIP1 {@UPDATE _ _ _ _ (update_bigmap address mutez) _};; _).
  apply: (DIIP validate_refund;; _).
  apply: (DIP1 update_refund_table;; _).
  apply: (DIP1 {SWAP};; SWAP;; create_transfer;;; _).
  apply: (NIL operation;; SWAP;; CONS;; DIP1 set_withdrawn;; PAIR;; NOOP).
Defined.
End crowdfunding.
