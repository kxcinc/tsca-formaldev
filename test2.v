From mathcomp Require Import all_ssreflect.
From Michocoq Require Import semantics util macros.
Import syntax comparable error.
Require Import ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition parameter_ty := (or int address).
Definition storage_ty := (pair mutez (map address mutez)).
Module ST : (SelfType with Definition self_type := parameter_ty).
  Definition self_type := parameter_ty.
End ST.
Module tmp(C:ContractContext)(E:Env ST C).
Require Import String.
Open Scope string_scope.
Module semantics := Semantics ST C E. Import semantics.

Definition DUUUUUP {a b c d e S T} :
  instruction T Datatypes.false
              (a ::: b ::: c ::: d ::: e ::: S)
              (e ::: a ::: b ::: c ::: d ::: e ::: S) :=
  DUPn (A := a ::: b ::: c ::: d ::: nil) 4 erefl.

Definition broker: full_contract false ST.self_type storage_ty.
refine ((DUP;; CDR;; DIP1 CAR);;
        SWAP;; (DIP1 UNPAIR (* acc; transferred *));;
        (IF_LEFT (DROP1;; SENDER) NOOP (* sendee *));;
        AMOUNT (* amount *);;
        (DUP;; DIP1 (PUSH nat (Nat_constant 2));;
        (@EDIV _ _ _ (Mk_ediv mutez nat _ _ Ediv_variant_tez_nat) _);;
        (IF_NONE ((PUSH nat (Nat_constant 0));; FAILWITH)
                 (CAR;; (* sending *)
                  (DUUUP;; DIP1 DUUUUUP;; GET;;
                   IF_NONE (PUSH mutez
                                 (Mutez_constant (Mk_mutez (exist _ (int64bv.of_Z 0) erefl))))
                           NOOP (* bal *);;
                   DIP1 DUP;;
                   (@ADD _ _ _ (Mk_add _ _ _ Add_variant_tez_tez) _);;
                   SOME;; DUUUUP;; DIIP DUUUUUP;; UPDATE (* transferred *);;
                   DIIP SWAP;;
                   DIIIP (@ADD _ _ _ (Mk_add _ _ _ Add_variant_tez_tez) _);;
                   DIIP SWAP;; DIP1 SWAP;; SWAP;; PAIR;;
                   (* new_store *)
                   DIIP
                     ((CONTRACT unit);;
                      IF_NONE (PUSH syntax_type.string "sendee invalid";; FAILWITH) NOOP);;
                   (* sendee_contract *)
                   DIP1 (PUSH unit Unit;; TRANSFER_TOKENS) (* op *) ;; SWAP;;
                   DIP1 (PUSH (list operation) (Concrete_list nil));; CONS;; PAIR;; DIP1 DROP1)
       )))).
by do !constructor.
Defined.
End tmp.
