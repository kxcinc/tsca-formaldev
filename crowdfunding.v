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
  match BinInt.Z.compare a b with
  | Gt | Eq => true
  | _ => false
  end.

Local Definition gt a b :=
  match BinInt.Z.compare a b with
  | Gt => true
  | _ => false
  end.

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

Lemma crowdfunding_fail_contribute
      (env : @proto_env (Some (parameter_ty, None)))
      (fuel : Datatypes.nat)
      (refund_address : data key_hash)
      (raisers : data (set address))
      (refund_table : data (big_map address mutez))
      (funding_start : data timestamp)
      (funding_end : data timestamp)
      (unconditional_refund_start : data timestamp)
      (withdrawn : data bool) :
fuel <= 5 ->
~~ success (eval_seq env crowdfunding fuel
         (inl refund_address,
          ((raisers, refund_table),
           ((withdrawn, funding_start),
            (funding_end, unconditional_refund_start))), tt)).
Proof.
  case: fuel => //.
  repeat case => //.
  rewrite /eval_seq /=.
  case: (map.get _ _ _ _ ) => // a.
  case: (tez.of_Z _) => //.
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
    case: (BinInt.Z.compare (now env) funding_start) => // _;
    case: (BinInt.Z.compare funding_end (now env)) => // _;
    case: (BinInt.Z.compare unconditional_refund_start (now env)) => // _ *;
    repeat split => //; auto; by apply/negP/negP.
Qed.

Lemma crowdfunding_fail_withdraw
      (env : @proto_env (Some (parameter_ty, None)))
      (fuel : Datatypes.nat)
      (beneficiary : data address)
      (raisers : data (set address))
      (refund_table : data (big_map address mutez))
      (funding_start : data timestamp)
      (funding_end : data timestamp)
      (unconditional_refund_start : data timestamp)
      (withdrawn : data bool) :
fuel <= 7 ->
~~ success (eval_seq env crowdfunding fuel
         (inr (inl beneficiary),
          ((raisers, refund_table),
           ((withdrawn, funding_start),
            (funding_end, unconditional_refund_start))), tt)).
Proof.
  case: fuel => //.
  repeat case => //.
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

Lemma crowdfunding_fail_refund
      (env : @proto_env (Some (parameter_ty, None)))
      (fuel : Datatypes.nat)
      (eligible_address : data address)
      (raisers : data (set address))
      (refund_table : data (big_map address mutez))
      (funding_start : data timestamp)
      (funding_end : data timestamp)
      (unconditional_refund_start : data timestamp)
      (withdrawn : data bool) :
fuel <= 7 ->
~~ success (eval_seq env crowdfunding fuel
         (inr (inr eligible_address),
          ((raisers, refund_table),
           ((withdrawn, funding_start),
            (funding_end, unconditional_refund_start))), tt)).
Proof.
  case: fuel => //.
  repeat case => //;
  rewrite /eval_seq /=;
  case: (map.get _ _ _ _ ) => //.
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

Hypothesis new_env :
  forall {N : self_info},
    @proto_env N -> data (list operation) -> @proto_env N.

Hypothesis now_gt :
  forall N env ops,
    geq (now (@new_env N env ops)) (now env).

Section Composition.
Definition comp {tffB T U}
           (N : self_info)
           (env : @proto_env N)
           (A : stack (pair (list operation) U ::: [::]))
           (paramB : data T)
           fuelB
           (B : instruction_seq N tffB (pair T U :: [::])
                                (pair (list operation) U :: [::])) :=
  let '(opsA, storage, tt) := A in
  match eval_seq env B fuelB (paramB, storage, tt) with
  | Return (opsB, storage, tt) =>
    (new_env env opsB, (cat opsA opsB, storage, tt))
  | Failed _ =>
    (env, (opsA, storage, tt))
  end.

Definition compN {tff T U N}
           (I : instruction_seq N tff (pair T U :: [::])
                                (pair (list operation) U :: [::]))
           xs env storage :=
  foldr (fun b a => comp a.1 a.2 b.1 b.2 I) (env, ([::], storage, tt)) xs.
End Composition.

Inductive Operation :=
| TransferTokens : forall
    (env : @proto_env (Some (parameter_ty, None)))
    (m : tez.mutez)
    (d : data (contract unit))
    (da : data address), Operation.

Definition eval_seq_another
      (env : @proto_env (Some (parameter_ty, None)))
      (fuel : Datatypes.nat)
      (A : stack (pair parameter_ty storage_ty ::: [::])) :=
  let refund_amount x := map.get _ _ _
                             (address_ _ (implicit_account x)) in
  let remove := map.remove address_constant tez.mutez address_compare
              (compare_eq_iff address) (lt_trans address) (gt_trans address) in
  let get := map.get address_constant tez.mutez address_compare in
  let '((raisers, refund_table),
           ((withdrawn, funding_start),
            (funding_end, unconditional_refund_start))) := A.1.2 in
  match A.1.1 with
  | inr (inr eligible_address) =>
    match get eligible_address refund_table with
    | Some y =>
      match contract_ None unit eligible_address with
      | Some y0 =>
        if (7 < fuel) && geq (now env) unconditional_refund_start && (withdrawn == false)
        then Return ([:: TransferTokens env y y0 eligible_address],
                (raisers, remove eligible_address refund_table,
                 (withdrawn, funding_start, (funding_end, unconditional_refund_start))), tt)
        else Failed _ Overflow
      | None => Failed _ Overflow
      end
    | None => Failed _ Overflow
    end
  | inr (inl beneficiary) =>
    match contract_ None unit beneficiary with
    | None => Failed _ Overflow
    | Some y =>
      if (7 < fuel) && geq (now env) funding_start && geq funding_end (now env)
         && gt unconditional_refund_start (now env)
         && (set.mem address_constant address_compare (source env) raisers)
         && (withdrawn == false)
      then Return ([:: TransferTokens env (balance env) y beneficiary],
          (raisers, refund_table,
          (true, funding_start, (funding_end, unconditional_refund_start))), tt)
      else Failed _ Overflow
    end
  | inl refund_address =>
    let insert := map.insert address_constant tez.mutez address_compare
                     (compare_eq_iff address) (gt_trans address)
                     (Implicit refund_address) in
    let! t :=
        match refund_amount refund_address refund_table with
        | Some x =>
          let! z := tez.of_Z (BinInt.Z.add (tez.to_Z (amount env)) (tez.to_Z x)) in
          Return (insert z refund_table)
        | None =>
          Return (insert (amount env) refund_table)
        end in
    if (5 < fuel) && geq (now env) funding_start && geq funding_end (now env)
    then Return ([::],
            ((raisers, t),
             ((withdrawn, funding_start),
              (funding_end, unconditional_refund_start))), tt)
    else Failed _ Overflow
  end.

Local Definition conv (o : Operation) :=
  match o with
  | TransferTokens env m d _ =>
    transfer_tokens env unit tt m d
  end.

Local Definition destination (o : Operation) :=
  match o with
  | TransferTokens env m d da => da
  end.

Lemma eval_seq_eq env fuel A :
  success (eval_seq env crowdfunding fuel A) ->
  eval_seq env crowdfunding fuel A =
  let! (ops, storage, tt) := eval_seq_another env fuel A in
  Return (seq.map conv ops, storage, tt).
Proof.
  case: A => [][] op st [].
  case: st => [][] raisers refund_table [][] withdrawn funding_start
              [] funding_end unconditional_refund_start.
  case: op => [refund_address|[beneficiary|eligible_address]] s.
  + have f5 : 5 < fuel.
     rewrite ltnNge.
     apply/negP => /(crowdfunding_fail_contribute
     env refund_address raisers refund_table funding_start funding_end unconditional_refund_start withdrawn).
     by rewrite s.
    have: is_true (success (eval_seq env crowdfunding fuel (inl refund_address, (raisers, refund_table, (withdrawn, funding_start, (funding_end, unconditional_refund_start))), tt)))
     by rewrite s.
    rewrite success_precond crowdfunding_correct_contribute //= /eval_seq_another /=.
    set B := match _ with | Some _ => _ | None => _ end .
    case Beq : B => //= [][] Ha [] Hb _.
    rewrite Ha Hb f5 return_precond crowdfunding_correct_contribute //.
    subst B; rewrite Beq /=.
    by auto.
  + have f7 : 7 < fuel.
     rewrite ltnNge.
     apply/negP => /(crowdfunding_fail_withdraw
     env beneficiary raisers refund_table funding_start funding_end unconditional_refund_start withdrawn).
     by rewrite s.
    have: is_true (success (eval_seq env crowdfunding fuel (inr (inl beneficiary), (raisers, refund_table, (withdrawn, funding_start, (funding_end, unconditional_refund_start))), tt)))
     by rewrite s.
    rewrite success_precond crowdfunding_correct_withdraw //= /eval_seq_another /=.
    case=> []a1 []a2 []a3 []a4 []a5 []y [] Hy _.
    rewrite a1 a2 a3 a4 a5 f7 Hy return_precond crowdfunding_correct_withdraw //.
    repeat split => //.
    by exists y; auto.
  + have f7 : 7 < fuel.
     rewrite ltnNge.
     apply/negP => /(crowdfunding_fail_refund
     env eligible_address raisers refund_table funding_start funding_end unconditional_refund_start withdrawn).
     by rewrite s.
    have: is_true (success (eval_seq env crowdfunding fuel (inr (inr eligible_address), (raisers, refund_table, (withdrawn, funding_start, (funding_end, unconditional_refund_start))), tt)))
     by rewrite s.
    rewrite success_precond crowdfunding_correct_refund //= /eval_seq_another /=.
    case=> []y []Hy []a1 []a2 []y0 []Hy0 _.
    rewrite Hy Hy0 a1 a2 f7 return_precond crowdfunding_correct_refund //.
    exists y; repeat split => //.
    exists y0; by auto.
Qed.

Lemma eval_seq_fail env fuel A :
  ~~ success (eval_seq env crowdfunding fuel A) <->
  ~~ success (eval_seq_another env fuel A).
Proof.
  case: A => [][] op st [].
  case: st => [][] raisers refund_table [][] withdrawn funding_start
              [] funding_end unconditional_refund_start.
  case: op => [refund_address|[beneficiary|eligible_address]];
  split; apply/contra => s.
  + apply/Bool.Is_true_eq_true.
    rewrite -/Is_true -/is_true success_precond.
    have f5: 5 < fuel.
     rewrite ltnNge.
     apply/negP => f5.
     move: s.
     rewrite /eval_seq_another /= ltnNge f5 /=.
     by case: (match _ with | Some _ => _ | None => _ end).
    rewrite crowdfunding_correct_contribute //=.
    move: s.
    rewrite /eval_seq_another /=.
    set B := (match _ with | Some _ => _ | None => _ end).
    case Beq : B => //.
    rewrite f5 /=.
    case: (geq (now env) funding_start) => //.
    by case: (geq funding_end (now env)).
  + apply/Bool.Is_true_eq_true.
    rewrite -/Is_true -/is_true success_precond.
    have f5: 5 < fuel.
     rewrite ltnNge.
     apply/negP => /(crowdfunding_fail_contribute
     env refund_address raisers refund_table funding_start funding_end unconditional_refund_start withdrawn).
     by rewrite s.
    rewrite /eval_seq_another /= f5 /=.
    move/Bool.Is_true_eq_left: s.
    rewrite -/Is_true -/is_true success_precond crowdfunding_correct_contribute //=.
    set B := (match _ with | Some _ => _ | None => _ end).
    case Beq : B => //=.
    case: (geq (now env) funding_start) => [|[]//].
    by case: (geq funding_end (now env)) => [|[] _ []].
  + apply/Bool.Is_true_eq_true.
    rewrite -/Is_true -/is_true success_precond.
    have f7: 7 < fuel.
     rewrite ltnNge.
     apply/negP => f7.
     move: s.
     rewrite /eval_seq_another /= ltnNge f7 /=.
     by case: (contract_ None unit beneficiary).
    rewrite crowdfunding_correct_withdraw //=.
    move: s.
    rewrite /eval_seq_another /=.
    case Ceq: (contract_ _ _ _) => [a|//].
    rewrite f7 /=.
    case: (geq (now env) funding_start) => //.
    case: (geq funding_end (now env)) => //.
    case: (gt unconditional_refund_start (now env)) => //.
    case: (set.mem address_constant address_compare (source env) raisers) => //.
    case: withdrawn => //= _.
    repeat split => //.
    by exists a.
  + apply/Bool.Is_true_eq_true.
    rewrite -/Is_true -/is_true success_precond.
    have f7: 7 < fuel.
     rewrite ltnNge.
     apply/negP => /(crowdfunding_fail_withdraw
     env beneficiary raisers refund_table funding_start funding_end unconditional_refund_start withdrawn).
     by rewrite s.
    rewrite /eval_seq_another /= f7 /=.
    move/Bool.Is_true_eq_left: s.
    rewrite -/Is_true -/is_true success_precond crowdfunding_correct_withdraw //=.
    by case=> []-> []-> []-> []-> []-> []y []-> _ /=.
  + apply/Bool.Is_true_eq_true.
    rewrite -/Is_true -/is_true success_precond.
    have f7: 7 < fuel.
     rewrite ltnNge.
     apply/negP => f7.
     move: s.
     rewrite /eval_seq_another /= ltnNge f7 /=.
     case: (map.get  _ _ _ _ _) => //.
     by case: (contract_ _ _ _).
    rewrite crowdfunding_correct_refund //=.
    move: s.
    rewrite /eval_seq_another /= f7 /=.
    case Teq: (map.get  _ _ _ _ _) => [t|//].
    case Ceq: (contract_ _ _ _) => [a|//].
    case: (geq (now env) unconditional_refund_start) => //.
    case: withdrawn => //= _.
    exists t; repeat split => //.
    by exists a.
  + apply/Bool.Is_true_eq_true.
    rewrite -/Is_true -/is_true success_precond.
    have f7: 7 < fuel.
     rewrite ltnNge.
     apply/negP => /(crowdfunding_fail_refund
     env eligible_address raisers refund_table funding_start funding_end unconditional_refund_start withdrawn).
     by rewrite s.
    rewrite /eval_seq_another /= f7 /=.
    move/Bool.Is_true_eq_left: s.
    rewrite -/Is_true -/is_true success_precond crowdfunding_correct_refund //=.
    by case=> []x []-> []-> []-> []x0 []-> _.
Qed.

Definition comp_another
           (env : @proto_env (Some (parameter_ty, None)))
           (A : seq Operation * data storage_ty * Datatypes.unit)
           (paramB : data parameter_ty)
           fuelB :=
  let '(opsA, storage, tt) := A in
  match eval_seq_another env fuelB (paramB, storage, tt) with
  | Return (opsB, storage, tt) =>
    (new_env env (seq.map conv opsB), (cat opsA opsB, storage, tt))
  | Failed _ =>
    (env, (opsA, storage, tt))
  end.

Definition compN_another xs env storage :=
  foldr (fun b a => comp_another a.1 a.2 b.1 b.2) (env, ([::], storage, tt)) xs.

Lemma comp_eq env ops st paramB fuelB :
  comp env (seq.map conv ops, st, tt) paramB fuelB crowdfunding
= let '(env, (ops, st, tt)) := comp_another env (ops, st, tt) paramB fuelB in
  (env, (seq.map conv ops, st, tt)).
Proof.
  rewrite /comp /comp_another.
  set A := eval_seq_another _ _ _.
  case Aeq : A => [|a].
   have/eval_seq_fail: ~~ success A by rewrite Aeq.
   by case: (eval_seq env crowdfunding fuelB (paramB, st, tt)).
  set C := eval_seq env crowdfunding fuelB (paramB, st, tt).
  have/eval_seq_eq: success C.
   apply/negP => /negP /eval_seq_fail.
   by subst A; rewrite Aeq.
  subst C => ->.
  subst A; rewrite Aeq.
  case: a Aeq => [][] opsA st0 [] /= ?.
  by rewrite map_cat.
Qed.

Lemma compN_eq env xs storage :
  compN crowdfunding xs env storage
= let '(env, (ops, st, tt)) := compN_another xs env storage in
  (env, (seq.map conv ops, st, tt)).
Proof.
  elim: xs env storage => // x xs IH env storage.
  rewrite /= !IH //=.
  case: (compN_another xs env storage) => [] env0 [][] ops st [].
  case s: (success (eval_seq env0 crowdfunding x.2 (x.1, st, tt))).
  + rewrite /= eval_seq_eq //.
    case: (eval_seq_another env0 x.2 (x.1, st, tt)) => [//|] [][]? ? [].
    by rewrite map_cat.
  + have: ~~ success (eval_seq_another env0 x.2 (x.1, st, tt))
     by rewrite -eval_seq_fail s.
    move: s => /=.
    case: (eval_seq env0 crowdfunding x.2 (x.1, st, tt)) => //.
    by case: (eval_seq_another env0 x.2 (x.1, st, tt)).
Qed.

Definition address_constant_eq a b :=
  match a, b with
  | Implicit (Mk_key_hash x), Implicit (Mk_key_hash y) => eqb x y
  | Originated (Mk_smart_contract_address x),
    Originated (Mk_smart_contract_address y) => eqb x y
  | _, _ => false
  end.

Lemma comparable_data_eqP :
  Equality.axiom (address_constant_eq).
Proof.
  case=> [][]x [][]y; apply/(iffP idP) => //= [];
  (try by move/eqb_spec => ->);
  by case=> ->; apply/eqb_spec.
Qed.

Canonical comparable_data_eqMixin := EqMixin comparable_data_eqP.
Canonical comparable_data_eqType :=
  Eval hnf in EqType _ comparable_data_eqMixin.

Definition operation_constant_eq a b :=
  match a, b with
  | Mk_operation x, Mk_operation y => eqb x y
  end.

Lemma operation_constant_eqP :
  Equality.axiom operation_constant_eq.
Proof.
  case=> []x []y; apply/(iffP idP) => /= [/eqb_spec -> //|[]->].
  by apply/eqb_spec.
Qed.

Canonical operation_constant_eqMixin := EqMixin operation_constant_eqP.
Canonical operation_constant_eqType :=
  Eval hnf in EqType (data operation) operation_constant_eqMixin.

Lemma size_crowdfunding_operations env x y z a b:
  eval_seq_another env x (y, z, tt) = Return (a, b, tt) ->
  seq.size a <= 1.
Proof.
  rewrite /eval_seq_another.
  case: y => [refund_address|[beneficiary|eligible_address]] /=.
  + case: z => [] [] ? ? [] [] ? ? [] ? ?.
    case: (match _ with | Some _ => _ | None => _ end) => //= ?.
    by case: ifP => // ? [] <-.
  + case: z => [] [] ? ? [] [] ? ? [] ? ?.
    case: (contract_ None unit beneficiary) => // ?.
    by case: ifP => // ? [] <-.
  + case: z => [] [] ? ? [] [] ? ? [] ? ?.
    case: (map.get address_constant tez.mutez address_compare eligible_address _) => // ?.
    case: (contract_ None unit _) => // ?.
    by case: ifP => // ? [] <-.
Qed.

Lemma compN_withdraw xs env storage :
  (compN_another xs env storage).2.1.2.2.1.1 = true ->
  seq.size (compN_another xs env storage).2.1.1 <= 1.
Proof.
  elim: xs storage env => // x xs IH storage env.
  move: IH.
  rewrite /= /comp_another.
  case eq: (compN_another xs env storage) => [b0 b1].
  case: b1 eq => [][]a b [] eq.
  rewrite /= -eq.
  case: x => [][|[]]? b1 IH.
  + rewrite /eval_seq_another /=.
    case: b eq => [][] raisers refund_table [][] withdrawn funding_start
              [] funding_end unconditional_refund_start /= eq.
    case: (map.get address_constant tez.mutez address_compare _ _) => /=.
      move=> ?.
      case: (tez.of_Z _) => [?|? /=].
       by apply/IH.
      case: ifP => ?.
      rewrite /= cats0.
      move: (IH storage env).
      by rewrite !eq.
     by apply/IH.
    case: ifP => ?.
     rewrite /= cats0.
     move: (IH storage env).
     by rewrite !eq /=.
    by apply/IH.
  + rewrite /eval_seq_another /=.
    case: b eq => [][] raisers refund_table [][] withdrawn funding_start
              [] funding_end unconditional_refund_start /= eq.
    case: (contract_ None unit _) => ? /=.
     case: ifP .
     rewrite /=.


    rewrite /=.


    rewrite /=.

      apply/IH.
  rewrite /=.

Lemma refund_refund
      (xs : seq (data parameter_ty * Datatypes.nat))
      env storage :
let '(env, (ops, storage, tt)) := compN_another xs env storage in
@uniq [eqType of data address] (seq.map destination ops).
Proof.
  suff: @uniq [eqType of data address] (seq.map destination (compN_another xs env storage).2.1.1)
  by case: (compN_another xs env storage) => [] env0 [][] ?? [].
  elim: xs env storage => //= x xs IH env storage.
  case compN_eq: (compN_another xs env storage) => [env0 [][] ops st []].
  rewrite /comp_another /=.
  case eq: (eval_seq_another env0 x.2 (x.1, st, tt)) => [/=|[] a []].
   have<-: (compN_another xs env storage).2.1.1 = ops by rewrite compN_eq.
   by apply/IH.
  case: a eq => [] opsB st0 /= H.
  rewrite map_cat uniq_catC cat_uniq.
  have<-: (compN_another xs env storage).2.1.1 = ops by rewrite compN_eq.
  rewrite IH andbT.
  case: x H => [][refund_address|[beneficiary|eligible_address]] fuel;
  rewrite /eval_seq_another /=.
  + case: st compN_eq => [][] raisers refund_table [][] withdrawn funding_start
              [] funding_end unconditional_refund_start compN_eq.
    case: (map.get address_constant tez.mutez address_compare (Implicit refund_address) refund_table) => [?|/=].
     case: (tez.of_Z _) => //= ?.
     case: ifP => // ? [] <- ? /=.
     by elim: [seq destination i | i <- _].
    case: ifP => // ? [] <- ? /=.
    by elim: [seq destination i | i <- _].
  + case: st compN_eq => [][] raisers refund_table [][] withdrawn funding_start
              [] funding_end unconditional_refund_start compN_eq.
    case: (contract_ None unit beneficiary) => // ?.
    case: ifP => // C [] <- ? /=.
    suff->: (compN_another xs env storage).2.1.1 = [::] by [].
    have: (compN_another xs env storage).2.1.2.2.1.1 = false.
     rewrite compN_eq /=; case: C.
     by case/andP => ? /eqP.
    elim: xs {IH compN_eq} => //= x xs IH.
    rewrite /comp_another /=.
    (compN_another xs env storage).2.1.1
    beneficiary;
    eligible_address; eligible_address; ...

  move: H.
  rewrite /=.


   have:te /=.
  case eq: (eval_seq_another (compN_another xs env storage).1 x.2 (x.1, storage0, tt)) => //.
  rewrite /=.
  move eq: (compN _ _ _ _) => A.
  case: A eq => [][] /= res storage' []/= eqA IH.
  rewrite /comp.
  move eq: (eval_seq env crowdfunding x.2 (x.1, storage', tt)) => B.
  case: B eq => // [] a.
  rewrite return_precond eval_seq_precond_correct -eval_seq_precond_correct.
  case: storage' eqA => [][] raisers refund_table [][] withdrawn funding_start
                     [] funding_end unconditional_refund_start eqA.

Definition collect_eligible_address (xs : seq (data parameter_ty * Datatypes.nat))
  := undup (foldl cat [::] (seq.map (fun x => match x.1 with
                                   | inr (inr y) => [:: y]
                                   | _ => [::]
                                   end) xs)).

Definition enough_fuel (a : data parameter_ty * Datatypes.nat) :=
  match a.1 with
  | inr (inr _) | inr (inl _) => a.2 > 7
  | inl _ => a.2 > 5
  end.
Lemma size_crowdfunding_operations env x y z a b:
  eval_seq env crowdfunding x (y, z, tt) = Return (a, b, tt) ->
  seq.size a <= 1.
Proof.
  rewrite return_precond.
  case: z => [][] raisers refund_table [][] withdrawn funding_start
              [] funding_end unconditional_refund_start.
  case: y => [|[]] y H; move: (H).
  + rewrite crowdfunding_correct_contribute.
     case: (map.get _ _ _ _ ) => /= [?|[]?[]?[]<- //].
     case: (tez.of_Z _) => //= ?[]?[]?[]<- //.
    rewrite leqNgt; apply/negP => C.
    move: H (crowdfunding_fail_contribute env y raisers refund_table funding_start funding_end unconditional_refund_start withdrawn (eq^~ (a, b, tt)) C).
    by rewrite -return_precond => ->.
  + rewrite crowdfunding_correct_withdraw.
     by case=> []?[]?[]?[]?[]?[]?[]?[]<-.
    rewrite leqNgt; apply/negP => C.
    move: H (crowdfunding_fail_withdraw env y raisers refund_table funding_start funding_end unconditional_refund_start withdrawn (eq^~ (a, b, tt)) C).
    by rewrite -return_precond => ->.
  + rewrite crowdfunding_correct_refund.
     by case=> []?[]?[]?[]?[]?[]?[]<-.
    rewrite leqNgt; apply/negP => C.
    move: H (crowdfunding_fail_refund env y raisers refund_table funding_start funding_end unconditional_refund_start withdrawn (eq^~ (a, b, tt)) C).
    by rewrite -return_precond => ->.
Qed.

Definition pre refund_table
           (xs : seq (data parameter_ty * (Datatypes.nat * (@proto_env (Some (parameter_ty, None)))))) :=
  let get := map.get address_constant tez.mutez address_compare in
  seq.map (fun x => match x.1 with
                 | inr (inr y) =>
                   match get y refund_table, contract_ None unit y with
                   | Some w, Some z =>
                     (* x.2.2 *)
                     Some (transfer_tokens x.2.2 unit tt w z)
                   | _, _ => None
                   end
                 | inr (inl y) =>
                   match contract_ None unit y with
                   | Some z =>
                     Some (transfer_tokens x.2.2 unit tt (balance x.2.2) z)
                   | _ => None
                   end
                 | inl y => None
                 end) xs.

Definition prefold t xs :=
  foldr (fun x y => match x with
                 | Some z => z :: y
                 | None => y
                 end) [::] (pre t xs).

Lemma prefold_cons t x xs :
  let get := map.get address_constant tez.mutez address_compare in
  prefold t (x :: xs) =
  match
  match x.1 with
  | inr (inr y) =>
    match get y t, contract_ None unit y with
    | Some w, Some z =>
      Some (transfer_tokens x.2.2 unit tt w z)
    | _, _ => None
    end
  | inr (inl y) =>
    match contract_ None unit y with
    | Some z =>
      Some (transfer_tokens x.2.2 unit tt (balance x.2.2) z)
    | _ => None
    end
  | inl y => None
  end
  with
  | None => prefold t xs
  | Some y => y :: prefold t xs
  end.
Proof. by []. Qed.

Lemma compN_operations xs storage :
(compN crowdfunding xs storage).1.1 = prefold storage.1.2 xs.
Proof.
  elim: xs storage => //= x xs IH.
  case => [][] raisers refund_table [][] withdrawn funding_start
           [] funding_end unconditional_refund_start.
  rewrite /= prefold_cons.
  case: x => x1 [] x2 x3.
  case: x1 => [|[]] x1.
  + rewrite /comp /=.
    move eq: (eval_seq _ _ _ _) => B.
    case: B eq => [??|]; first by apply/IH.
    case=> [][] a storage [] /=.
    rewrite IH /= return_precond.
    case x5 : (x2 > 5); last first.
     move/negP/negP: x5; rewrite -leqNgt => C.
     case: (compN crowdfunding xs (raisers, refund_table, (withdrawn, funding_start, (funding_end, unconditional_refund_start)))).1.2.
     move=> [] raisers' refund_table' [][] withdrawn' funding_start'
           [] funding_end' unconditional_refund_start' H.
     move: H (crowdfunding_fail_contribute x3 x1 raisers' refund_table' funding_start' funding_end' unconditional_refund_start' withdrawn' (eq^~ (a, storage, tt)) C).
     by rewrite -return_precond => ->.
    case: (compN crowdfunding xs (raisers, refund_table, (withdrawn, funding_start, (funding_end, unconditional_refund_start)))).1.2.
    move=> [] raisers' refund_table' [][] withdrawn' funding_start'
          [] funding_end' unconditional_refund_start'.
    rewrite crowdfunding_correct_contribute //=.
    case: (map.get _ _ _ _ _) => [?|].
     by case: (tez.of_Z _) => [] //= ? []?[]? []<-.
    by case: (tez.of_Z _) => [] //= ? []?[]? []<-.
  + rewrite /comp /=.
    move eq: (eval_seq _ _ _ _) => B.
    case: B eq => [? eq|].
     rewrite IH.
     rewrite /=.
    first by apply/IH.
     rewrite /=.
    rewrite

    rewrite /=.
  rewrite /prefold /pre /=.
  rewrite /=.
  rewrite /=.

Variable (env : @proto_env (Some (parameter_ty, None))).

Definition transfer_tokens' :=
fun x => transfer_tokens env unit x.1.1 x.1.2 x.2.

Axiom transfer_tokens_inj : injective transfer_tokens'.

Inductive transfer_tokens_proj3_ind :=
| Transfer_tokens_proj3 p :
    forall x y z, p (transfer_tokens' (x, y, z)) = Some z
             -> transfer_tokens_proj3_ind.

Axiom transfer_tokens_proj3 : transfer_tokens_proj3_ind.

Coercion transfer_tokens_proj3_morph
         (x : transfer_tokens_proj3_ind) :=
  match x with
  | Transfer_tokens_proj3 p _ _ _ _ => p
  end.

Lemma
data (contract unit)

Lemma refund_refund
      (xs : seq (data parameter_ty * Datatypes.nat))
      storage :
let (res, tt) := compN env crowdfunding xs storage in
@uniq [eqType of data operation] (seq.map (transfer_tokens_proj3_morph transfer_tokens_proj3) res.1).
Proof.
  elim: xs  => //= x xs.
  move eq: (compN _ _ _ _) => A.
  case: A eq => [][] /= res storage' []/= eqA IH.
  rewrite /comp.
  move eq: (eval_seq env crowdfunding x.2 (x.1, storage', tt)) => B.
  case: B eq => // [] a.
  rewrite return_precond eval_seq_precond_correct -eval_seq_precond_correct.
  case: storage' eqA => [][] raisers refund_table [][] withdrawn funding_start
                     [] funding_end unconditional_refund_start eqA.
  case: x => [][y|[|]y] z.
  + case z5 : (z > 5); last first.
     move/negP/negP: z5; rewrite -leqNgt => C H.
     move: H (crowdfunding_fail_contribute env y raisers refund_table funding_start funding_end unconditional_refund_start withdrawn (eq^~ a) C).
     by rewrite -return_precond => ->.
    rewrite crowdfunding_correct_contribute //=.
    case: (map.get _ _ _ _ _) => /= [a0|[]?[]? <-] //.
    case: (tez.of_Z _) => // a1 /= []?[]? <- //=.
  + case z7 : (z > 7); last first.
     move/negP/negP: z7; rewrite -leqNgt => C H.
     move: H (crowdfunding_fail_withdraw env y raisers refund_table funding_start funding_end unconditional_refund_start withdrawn (eq^~ a) C).
     by rewrite -return_precond => ->.
    rewrite crowdfunding_correct_withdraw //=.
    case=>[]? []? []? []C0 []? [] ? []? <-.
    rewrite uniq_catC cat_uniq IH /= orbF andbT.
    move: (f_equal (fun x => x.1.1) eqA) => /= {eqA} eqA.
    apply/negP => C {IH}.
    suff: withdrawn = true by rewrite C0.
    elim: res C xs storage eqA => //= a0 l IH.
    rewrite (@in_cons [eqType of data operation]).
    case/orP=> [/eqP <-|{}/IH // IH]; last first.
     elim => //= x xs IH0 storage.
     rewrite /comp /=.
     move eq: (eval_seq _ _ _ _) => B.
     case: B eq => [e + H|a1].
      by move: (IH0 storage H).
     case: a1 => [][]/= ++ [].
     move=> a1 b H.
     move: (size_crowdfunding_operations H).
     case: a1 H => [H ?|a1[]//]; last first.
      by move=> ?? []? /IH.
     by move/IH0.
    case=>//=.


     rewrite return_precond.

      case: xs H => //= a1 xs.
      rewrite /comp /=.
      move eq: (eval_seq _ _ _ _) => B.
      case: B eq => [e0 + H|].
      rewrite H.
      rewrite /=.
      move: (IH (x :: xs) storage) => /=.
      rewrite /comp /= => + C1.
      rewrite C1 /=.
      rewrite H.
     move eqA: (compN env crowdfunding xs storage) => A.
     case: A eqA => // A [].
     rewrite /=.
     rewrite /=.
     compN env crowdfunding xs storage
     rewrite /=.

  move eq: (eval_seq env crowdfunding x.2 (x.1, storage', tt)) => B.
  case: B eq => // [] a.
  rewrite return_precond eval_seq_precond_correct -eval_seq_precond_correct.
     move=> xs storage.
    Set Printing All.
    case.
    rewrite
    IH eq.
    Set Printing All.
    rewrite in_cons.
    case.
  rewrite /=.
  ((raisers, refund_table),
           ((withdrawn, funding_start),
            (funding_end, unconditional_refund_start)))
  rewrite /=.
  Search (_ = Return _).

  rewrite /=.
  set B :=
  eval_seq env crowdfunding x.2 (x.1, storage, tt)
   IH.
  rewrite /compN.
  rewrite /=.

  rewrite -/comp.
  Check foldl.
  rewrite
  rewrite /=.
  move=> storage.


all enough_fuel xs ->
About transfer_tokens.
Check contract_ None unit eligible_address

Lemma crowdfunding_correct_compN
      (env : @proto_env (Some (parameter_ty, None)))
      (xs : seq (data parameter_ty * Datatypes.nat))
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
let storage := ((raisers, refund_table),
                ((withdrawn, funding_start),
                 (funding_end, unconditional_refund_start))) in
precond (compN env crowdfunding xs storage) psi <->
all enough_fuel xs
/\
exists y, get eligible_address refund_table = Some y
/\ geq (now env) unconditional_refund_start
/\ withdrawn = false
/\ (exists y0, contract_ None unit eligible_address = Some y0
   /\ psi ([:: transfer_tokens env unit tt y y0],
           (raisers, remove eligible_address refund_table,
           (withdrawn, funding_start, (funding_end, unconditional_refund_start))), tt)).
Check precond (compN _ crowdfunding _ _).
Check bijective _.
Check precond.
collect_eligible_address
Variable (xs : seq (data parameter_ty * Datatypes.nat)).
Check undup xs.
Check [set x | x \in xs].
Check finset.
Check finset (mem (collect_eligible_address _)).
End crowdfunding.
