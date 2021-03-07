From mathcomp Require Import all_ssreflect.
From Michocoq Require Import semantics util macros.
Import syntax comparable error.
Require Import ccgen_util.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module crowdfunding(C : ContractContext).
Module semantics := Semantics C. Import semantics.
Require Import String.
Open Scope string_scope.
Open Scope michelson_scope.

Definition parameter_ty :=
  or key_hash None
     (or address None address None) None.

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
  funding_start;;; {NOW; COMPARE; GE;
  DIP1 funding_end; DIP1 {NOW; SWAP; COMPARE; GE}; AND; NOT;
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
 funding_start;;; NOW;; COMPARE;; GE;;
 {DIP1 funding_end; DIP1 {NOW; SWAP; COMPARE; GE}; AND; NOT};;;
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
{NOW; DIP1 unconditional_refund_start; SWAP; COMPARE; GT};;;
 IF_TRUE {FAILWITH} { };; withdrawn;;; {IF_TRUE {FAILWITH} { }}.

Definition crowdfunding : full_contract false parameter_ty None storage_ty :=
  {DUP; CAR; DIP1 {CDR};
  IF_LEFT
  (IMPLICIT_ACCOUNT;;
   ADDRESS;;
   DUP;;
   DIIP refund_table;;
   DIP1 {@GET _ _ _ (get_bigmap address mutez) _};;
   DIP1 {IF_SOME {AMOUNT; @ADD _ _ _ add_tez_tez _} {AMOUNT}};;
   DIP1 {SOME};;
   DIIP refund_table;;
   @UPDATE _ _ _ _ (update_bigmap address mutez) _;;
   DIP1 validate_time;; update_refund_table;;; {NIL operation; PAIR})
 {IF_LEFT
  (DIP1 validate_withdraw;;
  BALANCE;;
  create_transfer;;;
  {NIL operation; SWAP; CONS; DIP1 set_withdrawn; PAIR})
  {DIP1 refund_table; DUP; DIP1 {@GET _ _ _ (get_bigmap address mutez) _}; SWAP;
   IF_NONE {FAILWITH}
     (SWAP;;
      DIP1 {SWAP};;
      NONE mutez;;
      DIIP refund_table;;
      SWAP;;
      DUP;;
      DIP1 {@UPDATE _ _ _ _ (update_bigmap address mutez) _};;
      DIIP validate_refund;;
      DIP1 update_refund_table;;
      DIP1 {SWAP};;
      SWAP;;
      create_transfer;;;
      {NIL operation; SWAP; CONS; PAIR})}}}.

Local Definition geq a b :=
  BinInt.Z.compare a b = Gt \/ BinInt.Z.compare a b = Eq.

Local Definition gt a b :=
  BinInt.Z.compare a b = Gt.

Import Notations.

Lemma crowdfunding_correct_contribute
      (env : @proto_env (Some (parameter_ty, None)))
      (fuel : Datatypes.nat)
      (refund_address : data key_hash)
      (raisers : data (set address))
      (refund_table : data (big_map address mutez))
      (funding_start : data timestamp)
      (funding_end : data timestamp)
      (unconditional_refund_start : data timestamp)
      (withdrawn : data bool)
      (psi : stack (pair (list operation) storage_ty ::: [::]) -> Prop) :
let refund_amount x := map.get _ _ _
                             (address_ _ (implicit_account x)) in
let insert := map.insert address_constant tez.mutez address_compare
                     (compare_eq_iff address) (gt_trans address)
                     (Implicit refund_address) in
fuel > 5 ->
precond (eval_seq env crowdfunding fuel
         (inl refund_address,
          ((raisers, refund_table),
           ((withdrawn, funding_start),
            (funding_end, unconditional_refund_start))), tt)) psi <->
let changed_refund_table :=
match refund_amount refund_address refund_table with
| Some x =>
  let! z := tez.of_Z (BinInt.Z.add (tez.to_Z (amount env)) (tez.to_Z x)) in
  Return (insert z refund_table)
| None =>
  Return (insert (amount env) refund_table)
end in
precond changed_refund_table (fun t =>
geq (now env) funding_start /\ geq funding_end (now env)
/\ psi ([::],
     ((raisers, t),
      ((withdrawn, funding_start),
       (funding_end, unconditional_refund_start))), tt)).
Proof.
  move=> ra ins F; have<-: 6 + (fuel - 6) = fuel by rewrite addnC subnK.
  rewrite /geq; subst ra ins; split.
  + rewrite eval_seq_precond_correct /eval_seq_precond /=.
    set H := map.get _ _ _ _ _.
    case: H => [a|].
    - set T := tez.of_Z _.
      case: T => //= T [] /negP/negP /andP[].
      case: (BinInt.Z.compare (now env) funding_start) => //;
      case: (BinInt.Z.compare funding_end (now env)) => //; auto.
    - case=> [] /negP/negP /andP[] /=.
      case: (BinInt.Z.compare (now env) funding_start) => //;
      case: (BinInt.Z.compare funding_end (now env)) => //; auto.
  + rewrite eval_seq_precond_correct /eval_seq_precond /=.
    set H := map.get _ _ _ _ _.
    case: H => [a|/=].
    - set T := tez.of_Z _.
      case: T => //= T [] + [].
      case: (BinInt.Z.compare (now env) funding_start) => //;
      case: (BinInt.Z.compare funding_end (now env)) => //; auto;
      (try by case);
      (try by move=> + []).
    - case => + [].
      case: (BinInt.Z.compare (now env) funding_start) => //;
      case: (BinInt.Z.compare funding_end (now env)) => //; auto;
      (try by case);
      (try by move=> + []).
Qed.

Lemma crowdfunding_correct_withdraw
      (env : @proto_env (Some (parameter_ty, None)))
      (fuel : Datatypes.nat)
      (beneficiary : data address)
      (raisers : data (set address))
      (refund_table : data (big_map address mutez))
      (funding_start : data timestamp)
      (funding_end : data timestamp)
      (unconditional_refund_start : data timestamp)
      (withdrawn : data bool)
      (psi : stack (pair (list operation) storage_ty ::: [::]) -> Prop) :
fuel > 7 ->
precond (eval_seq env crowdfunding fuel
         (inr (inl beneficiary),
          ((raisers, refund_table),
           ((withdrawn, funding_start),
            (funding_end, unconditional_refund_start))), tt)) psi <->
geq (now env) funding_start /\ geq funding_end (now env)
/\ gt unconditional_refund_start (now env)
/\ withdrawn = false
/\ set.mem address_constant address_compare (source env) raisers
/\ exists y, contract_ None unit beneficiary = Some y
   /\ psi ([:: transfer_tokens env unit tt (balance env) y],
          (raisers, refund_table,
          (true, funding_start, (funding_end, unconditional_refund_start))), tt).
Proof.
  move=> F; have<-: 8 + (fuel - 8) = fuel by rewrite addnC subnK.
  rewrite eval_seq_precond_correct /eval_seq_precond /=.
  rewrite /gt /geq; split.
  + case => + [] + [].
    case: (BinInt.Z.compare (now env) funding_start) => //;
    case: (BinInt.Z.compare funding_end (now env)) => //;
    by (rewrite /= BinInt.Z.compare_antisym;
    case: (BinInt.Z.compare (now env) unconditional_refund_start) => // + + a *;
    repeat split => //; auto; by move/negP/negP: a).
  + case=> + [] + [] + [] + [].
    case: (BinInt.Z.compare (now env) funding_start) => //;
    case: (BinInt.Z.compare funding_end (now env)) => //;
    case=> [] // ? [] // ? -> ? a *;
    repeat split => //; auto; by apply/negP/negP.
Qed.

Lemma crowdfunding_correct_refund
      (env : @proto_env (Some (parameter_ty, None)))
      (fuel : Datatypes.nat)
      (eligible_address : data address)
      (raisers : data (set address))
      (refund_table : data (big_map address mutez))
      (funding_start : data timestamp)
      (funding_end : data timestamp)
      (unconditional_refund_start : data timestamp)
      (withdrawn : data bool)
      (psi : stack (pair (list operation) storage_ty ::: [::]) -> Prop) :
let remove := map.remove address_constant tez.mutez address_compare
              (compare_eq_iff address) (lt_trans address) (gt_trans address) in
let get := map.get address_constant tez.mutez address_compare in
fuel > 7 ->
precond (eval_seq env crowdfunding fuel
         (inr (inr eligible_address),
          ((raisers, refund_table),
           ((withdrawn, funding_start),
            (funding_end, unconditional_refund_start))), tt)) psi <->
exists y, get eligible_address refund_table = Some y
/\ geq (now env) unconditional_refund_start
/\ withdrawn = false
/\ (exists y0, contract_ None unit eligible_address = Some y0
   /\ psi ([:: transfer_tokens env unit tt y y0],
           (raisers, remove eligible_address refund_table,
           (withdrawn, funding_start, (funding_end, unconditional_refund_start))), tt)).
Proof.
  move=> rm get F; have<-: 8 + (fuel - 8) = fuel by rewrite addnC subnK.
  rewrite eval_seq_precond_correct /eval_seq_precond /=.
  subst rm get; rewrite /gt /geq; split.
  + case=> y [] H1 [] H2 [] H3 H4; exists y.
    repeat split; auto.
    rewrite /= BinInt.Z.compare_antisym.
    by case: H2; case: (BinInt.Z.compare unconditional_refund_start (now env)); auto.
  + case=> y [] H1 [] H2 [] H3 H4; exists y.
    repeat split; auto.
    rewrite /= BinInt.Z.compare_antisym.
    by case: H2; case: (BinInt.Z.compare (now env) unconditional_refund_start); auto.
Qed.

(* 90 days = (60*60*24*90) seconds *)
Definition funding_start_latest :=
  Comparable_constant _ (BinInt.Z_of_nat [Num of 7776000]
                         : simple_comparable_data int).

(* 270 days = (60*60*24*270) seconds *)
Definition funding_period_longest :=
  Comparable_constant _ (BinInt.Z_of_nat [Num of 23328000]
                         : simple_comparable_data int).

(* 90 days = (60*60*24*90) seconds *)
Definition redeem_period_longest :=
  Comparable_constant _ (BinInt.Z_of_nat [Num of 7776000]
                         : simple_comparable_data int).

Local Notation SUB := (@SUB _ _ _ sub_timestamp_timestamp _).
Local Notation OR := (@OR _ _ bitwise_bool _).

Definition validation_snippet :
    instruction_seq None false (storage_ty ::: mutez ::: [::]) [::] :=
 DIP1 {DROP1};;
 raisers;;;
 @SIZE _ _ (size_set _) _;;
 PUSH _ (Comparable_constant _ (BinNums.N0 : simple_comparable_data nat));;
 COMPARE;;
 EQ;;
 IF_TRUE {PUSH _ (Comparable_constant syntax_type.string "there must be at least one registered raiser"); FAILWITH} { };;
 funding_start;;;
 DIP1 {NOW};;
 COMPARE;;
 LT;;
 DIP1 funding_end;;
 DIIP funding_start;;
 DIP1 {COMPARE; LT};;
 OR;;
 DIP1 unconditional_refund_start;;
 DIIP funding_end;;
 DIP1 {COMPARE; LT};;
 OR;;
 IF_TRUE {PUSH syntax_type.string (Comparable_constant syntax_type.string "timestamp parameters given in wrong order"); FAILWITH} { };;
 funding_start;;;
 NOW;;
 SWAP;;
 SUB;;
 PUSH int funding_start_latest;;
 SWAP;;
 COMPARE;;
 GT;;
 IF_TRUE {PUSH syntax_type.string (Comparable_constant syntax_type.string "funding_start too late"); FAILWITH} { };;
 funding_end;;;
 DIP1 funding_start;;
 SUB;;
 PUSH int funding_period_longest;;
 SWAP;;
 COMPARE;;
 GT;;
 IF_TRUE {PUSH syntax_type.string (Comparable_constant syntax_type.string "funding period too long"); FAILWITH} { };;
 unconditional_refund_start;;;
 {DIP1 funding_end; SUB; PUSH int redeem_period_longest; SWAP; COMPARE; GT;
  IF_TRUE {PUSH _ (Comparable_constant syntax_type.string "redeem period too long"); FAILWITH} { }; DROP1}.

Definition crowdfunding_genprog_validation_snippet :=
  make_typed_validation_snippet validation_snippet.
End crowdfunding.
