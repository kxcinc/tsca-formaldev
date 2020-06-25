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

Local Definition exec
(A : instruction_seq None false (pair bytes bytes ::: [::])
                 (pair (list operation) bytes ::: [::]))
: instruction_seq (Some (parameter_ty, None)) false
                  (pair (pair bytes bytes) (option (pair address (pair syntax_type.string syntax_type.string))) ::: [::])
              (pair (list operation) storage_ty ::: [::]) :=
{
  UNPAIR;
  LAMBDA (pair bytes bytes) (pair (list operation) bytes) A;
  SWAP;
  EXEC;
  UNPAIR;
  DIP1 {PAIR; PUSH _ (Instruction false A); PAIR};
  PAIR
}.
Import Notations.

Lemma bind_id T (A1 : M (T * Datatypes.unit)) :
  bind A1 (fun '(x, tt) => Return (x, tt)) = A1.
Proof. by case: A1 => []//[]// + []. Qed.

Definition exec_correct_success
(arg : data bytes)
(wstore : data bytes)
(avt_id : data (option (pair address (pair syntax_type.string syntax_type.string))))
(env : @proto_env (Some (parameter_ty, None)))
(A : instruction_seq None false (pair bytes bytes ::: [::])
                 (pair (list operation) bytes ::: [::]))
fuel returned_operations new_storage :
  4 <= fuel ->
  eval_seq (no_self env) A fuel (arg, wstore, tt) = Return (returned_operations, new_storage, tt) ->
  eval_seq env (exec A) fuel.+1 (arg, wstore, avt_id, tt) =
  Return (returned_operations,
          ((existT _ false A : data (lambda (pair bytes bytes)
                                            (pair (list operation) bytes))),
           (new_storage, avt_id)), tt).
Proof.
  move=> Hfuel.
  have<-: 3 + (fuel - 3) = fuel by rewrite addnC subnK // (ltn_trans _ Hfuel).
  by rewrite /eval_seq /= => ->.
Qed.

Definition exec_correct_fail
(arg : data bytes)
(wstore : data bytes)
(avt_id : data (option (pair address (pair syntax_type.string syntax_type.string))))
(env : @proto_env (Some (parameter_ty, None)))
(A : instruction_seq None false (pair bytes bytes ::: [::])
                 (pair (list operation) bytes ::: [::]))
fuel e :
  4 <= fuel ->
  eval_seq (no_self env) A fuel (arg, wstore, tt) = Failed _ e ->
  eval_seq env (exec A) fuel.+1 (arg, wstore, avt_id, tt) = Failed _ e.
Proof.
  move=> Hfuel.
  have<-: 3 + (fuel - 3) = fuel by rewrite addnC subnK // (ltn_trans _ Hfuel).
  by rewrite /eval_seq /= => ->.
Qed.

Lemma wrapper_correct_success
(arg : data bytes)
(wstore : data bytes)
(avt_id : data (option (pair address (pair syntax_type.string syntax_type.string))))
(env : @proto_env (Some (parameter_ty, None)))
(A : instruction_seq None false (pair bytes bytes ::: [::])
                 (pair (list operation) bytes ::: [::]))
(fuel : Datatypes.nat) returned_operations new_storage :
  4 <= fuel ->
  eval_seq (no_self env) A fuel (arg, wstore, tt) = Return (returned_operations, new_storage, tt) ->
  eval_seq env wrapper fuel.+1 (arg, ((existT _ false A : data (lambda (pair bytes bytes)
                                         (pair (list operation) bytes))), (wstore, avt_id)), tt)
= Return (returned_operations,
          ((existT _ false A : data (lambda (pair bytes bytes)
                                            (pair (list operation) bytes))),
           (new_storage, avt_id)), tt).
  rewrite !return_precond !eval_seq_precond_correct => Hfuel.
  have<-: 4 + (fuel - 4) = fuel by rewrite addnC subnK.
  move: (eval_seq_precond_eqv _ (no_self env) false _ _ A (4 + (fuel - 4)) (arg, wstore, tt)
  (fun '(y, tt) =>
     let (x, _) := y in
     let (_, y1) := y in
     (x, (existT (fun tff : Datatypes.bool => instruction_seq None tff (pair (Comparable_type bytes) (Comparable_type bytes) ::: [::]) (pair (list operation) (Comparable_type bytes) ::: [::])) false A, (y1, avt_id)), tt) =
     (returned_operations, (existT (fun tff : Datatypes.bool => instruction_seq None tff (pair (Comparable_type bytes) (Comparable_type bytes) ::: [::]) (pair (list operation) (Comparable_type bytes) ::: [::])) false A, (new_storage, avt_id)), tt))
    (eq^~ (returned_operations, new_storage, tt))).
  rewrite /eval_seq_precond /= => H H0.
  rewrite H; first by apply H0.
  case => [] [] a b [].
  split; by case => -> ->.
Qed.

Lemma wrapper_correct'
(arg : data bytes)
(wstore : data bytes)
(avt_id : data (option (pair address (pair syntax_type.string syntax_type.string))))
(env : @proto_env (Some (parameter_ty, None)))
(A : instruction_seq None false (pair bytes bytes ::: [::])
                 (pair (list operation) bytes ::: [::]))
(fuel : Datatypes.nat) :
  fuel > 10 ->
  eval_seq (no_self env) A (7 + (fuel - 7)) (arg, wstore, tt)
= eval_seq (no_self env) A (fuel - 7) (arg, wstore, tt) ->
  eval_seq env wrapper fuel (arg, ((existT _ false A : data (lambda (pair bytes bytes)
                                         (pair (list operation) bytes))), (wstore, avt_id)), tt)
= eval_seq env (exec A) fuel (arg, wstore, avt_id, tt).
Proof.
  move=> Hf sA /=.
  have?: 6 < fuel by apply/(leq_trans _ Hf).
  have<-: (fuel - 7) + 7 = fuel by rewrite subnK.
  suff->: 6 + (fuel - 7 + 7) = 4 + ((fuel - 7 + 7) + 2).
  rewrite /eval_seq /=.
set X := RHS.

  rewrite /=.
  rewrite !bind_id.
  vm_compute.

  simpl.
  rewrite /wrapper /=.
  rewrite /=.
  rewrite addnC.
  set A1 := (eval _ A _ _).
  rewrite /= !bind_id; set A2 := (eval _ A _ _).
  have->: A1 = A2 by subst A1 A2; rewrite sA.
  have<-: 4 + ((fuel - 7) - 4) = fuel - 7
   by rewrite addnC subnK // /leq subnBA // subn_eq0 (leq_trans _ Hf).
  by case: A2 => []//= [][] /=.


  Check eval_seq env A.
LAMBDA _ _ A;; SWAP;;
EXEC;; UNPAIR;; DIP1 (PUSH _ (Bytes_constant (pack_lambda A)));;
DIP1 PAIR;; PAIR.


Check (instruction None false (lambda (pair bytes bytes) (pair (list operation) bytes))).

End wrapper.
