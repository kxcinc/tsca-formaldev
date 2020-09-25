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
    AMOUNT; PUSH mutez zero; COMPARE; LE;
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

Lemma frozen_correct
      (env : @proto_env (Some (parameter_ty, None)))
      (fuel : Datatypes.nat)
      (m : tez.mutez)
      (addr : data address)
      (unfrozen : data timestamp)
      (fund_owners : data (set address))
      (psi : stack (pair (list operation) storage_ty ::: [::]) -> Prop) :
  fuel > 5 ->
  precond (eval_seq env frozen fuel ((m, addr), (fund_owners, unfrozen), tt)) psi
<-> match contract_ env (Some "") unit addr with
  | Some c =>
    psi ([:: transfer_tokens env unit tt m c], (fund_owners, unfrozen), tt)
    /\ tez.compare (extract (tez.of_Z BinNums.Z0) I) (amount env) = Gt
    /\ set.mem address_constant address_compare (source env) fund_owners
    /\ (BinInt.Z.compare (now env) unfrozen = Lt
       \/ BinInt.Z.compare (now env) unfrozen = Eq)
    /\ (tez.compare (balance env) m = Lt
       \/ tez.compare (balance env) m = Eq)
  | None => False
  end.
Proof.
  move=> F; have<-: 6 + (fuel - 6) = fuel by rewrite addnC subnK.
  split => H.
  + case C : (contract_ env (Some "") unit addr).
    - move: H;
      rewrite eval_seq_precond_correct /eval_seq_precond /= C /=.
      repeat case: ifP => //.
      set C1 := (tez.compare _ _); case: C1 => //;
      set C2 := (tez.compare _ _); case: C2 => //;
      set C3 := (BinInt.Z.compare _ _); case: C3 => // *;
      repeat split => //; auto.
    - move: H; rewrite eval_seq_precond_correct /eval_seq_precond /= C /=.
      by repeat case: ifP.
  + rewrite eval_seq_precond_correct /eval_seq_precond /=.
    move: H; case: (contract_ env (Some "") unit addr) => // ?.
    by case => []H1 []-> []-> [][]-> []->.
Qed.

Lemma frozen_decrease :
  precond (eval


End frozen.
