From mathcomp Require Import all_ssreflect.
From Michocoq Require Import semantics util macros.
Import syntax comparable error.
Require Import ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition parameter_ty := Comparable_type bytes.
Definition storage_ty := (pair bytes bytes).
Module ST : (SelfType with Definition self_type := parameter_ty).
  Definition self_type := parameter_ty.
End ST.
Module tmp(C:ContractContext)(E:Env ST C).
Require Import String.
Open Scope string_scope.
Module semantics := Semantics ST C E. Import semantics.
Definition wrapper : full_contract false ST.self_type storage_ty :=
(DUP;; CDR;; DIP1 CAR);;
(DUP;; CAR);;
DUP;;
UNPACK (lambda (pair bytes bytes) (pair (list operation) bytes));;
IF_NONE (PUSH syntax_type.string "wfunc cannot be unpacked";; FAILWITH)
        (DUP;; DIP1 DROP1);;
DIP1 (DIP1 CDR);; DIP1 (DIP1 SWAP);; DIP1 (DIP1 PAIR);; SWAP;; DIP1 SWAP;;
DIP1 EXEC;; DIP1 UNPAIR;; DIP1 SWAP;; PAIR;; SWAP;; PAIR.

Definition pack_lambda
(A : instruction None false (pair bytes bytes ::: [::])
                            (pair (list operation) bytes ::: [::])) :=
pack env _ (existT _ false A : data (lambda (pair bytes bytes)
                                            (pair (list operation) bytes))).

Definition pack_exec
(A : instruction None false (pair bytes bytes ::: [::])
                            (pair (list operation) bytes ::: [::]))
: instruction (Some ST.self_type) false (pair bytes bytes ::: [::])
              (pair (list operation) storage_ty ::: [::]) :=
LAMBDA _ _ A;; SWAP;;
EXEC;; UNPAIR;; DIP1 (PUSH _ (Bytes_constant (pack_lambda A)));;
DIP1 PAIR;; PAIR.

Section pack_unpack.
Hypothesis pack_unpack : forall a x, unpack env a (pack env a x) = Some x.

Lemma bind_id T (A1 : M (T * Datatypes.unit)) :
  bind A1 (fun '(x, tt) => Return (x, tt)) = A1.
Proof. by case: A1 => []//[]// + []. Qed.

Lemma wrapper_correct'
(arg : data bytes)
(wstore : data bytes)
(A : instruction None false (pair bytes bytes ::: [::])
                            (pair (list operation) bytes ::: [::]))
(fuel : Datatypes.nat) :
  fuel > 10 ->
  eval (no_self env) A (7 + (fuel - 7)) (arg, wstore, tt)
= eval (no_self env) A (fuel - 7) (arg, wstore, tt) ->
  eval env wrapper (6 + fuel) ((arg, ((pack_lambda A), wstore)), tt)
= eval env (pack_exec A) (4 + fuel) ((arg, wstore), tt).
Proof.
  move=> Hf sA /=.
  have?: 6 < fuel by apply/(leq_trans _ Hf).
  have<-: (fuel - 7) + 7 = fuel by rewrite subnK.
  rewrite pack_unpack addnC; set A1 := (eval _ A _ _).
  rewrite /= !bind_id; set A2 := (eval _ A _ _).
  have->: A1 = A2 by subst A1 A2; rewrite sA.
  have<-: 4 + ((fuel - 7) - 4) = fuel - 7
   by rewrite addnC subnK // /leq subnBA // subn_eq0 (leq_trans _ Hf).
  by case: A2 => []//= [][] /=.
Qed.

Lemma wrapper_correct
(arg : data bytes)
(wstore : data bytes)
(A : instruction None false (pair bytes bytes ::: [::])
                            (pair (list operation) bytes ::: [::]))
(fuel : Datatypes.nat) :
  fuel > 10 ->
  is_true (success (eval (no_self env) A (fuel - 7) (arg, wstore, tt))) ->
  eval env wrapper (6 + fuel) ((arg, ((pack_lambda A), wstore)), tt)
= eval env (pack_exec A) (4 + fuel) ((arg, wstore), tt).
Proof.
  move=> Hf sA.
  apply/wrapper_correct' => //.
  by apply/esym/eval_deterministic_le; first by apply/leP/leq_addl.
Qed.

Lemma wrapper_correct''
(arg : data bytes)
(wstore : data bytes)
(A : instruction None false (pair bytes bytes ::: [::])
                            (pair (list operation) bytes ::: [::]))
(fuel : Datatypes.nat) :
  fuel > 10 ->
  (forall x, x > fuel - 7 -> eval (no_self env) A x (arg, wstore, tt)
                      = eval (no_self env) A (fuel - 7) (arg, wstore, tt)) ->
  eval env wrapper (6 + fuel) ((arg, ((pack_lambda A), wstore)), tt)
= eval env (pack_exec A) (4 + fuel) ((arg, wstore), tt).
Proof.
  move=> Hf sA.
  apply/wrapper_correct'/sA => //.
  by rewrite addSn; apply/leq_addl.
Qed.
End pack_unpack.
End tmp.
24m
