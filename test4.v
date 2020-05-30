From mathcomp Require Import all_ssreflect.
From Michocoq Require Import semantics util macros.
Import syntax comparable error.
Require Import ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import String.
Open Scope string_scope.
Import Notations.
Require Import Michocoq.main.

Definition contract := "{
  parameter (or (or unit unit) (or address (or nat nat)));
  storage (pair (pair (option mutez) address) (pair mutez (list (pair address mutez))));
  code { DUP;
         CAR;
         DIP 1 {CDR};
         IF_LEFT { IF_LEFT { DROP 1;
                             DUP;
                             {DUP; CAR; DIP 1 {CDR}};
                             {DUP; CAR; DIP 1 {CDR}};
                             DIP 1 {DROP 1};
                             IF_NONE {DROP 1; PUSH bool True}
                                     { DIP 1
                                           { {DUP; CAR; DIP 1 {CDR}};
                                             DIP 1 {DROP 1}
                                           };
                                       COMPARE;
                                       GT
                                     };
                             IF { AMOUNT;
                                  SENDER;
                                  DIP 2
                                      { {DUP; CAR; DIP 1 {CDR}};
                                        {DUP; CAR; DIP 1 {CDR}};
                                        DUP
                                      };
                                  DIP 3 {PAIR; PAIR};
                                  DIP 1 {SWAP};
                                  SWAP;
                                  DIP 1 {SWAP};
                                  DIP 2 {SWAP};
                                  IF_NONE {DIP 1 {NIL operation}}
                                          { DIP 2
                                                { DUP;
                                                  {DUP; CAR; DIP 1 {CDR}};
                                                  DROP 1;
                                                  {DUP; CAR; DIP 1 {CDR}};
                                                  DIP 1 {DROP 1}
                                                };
                                            DIP 1 {DUP};
                                            DIP 2 {ADD};
                                            SWAP;
                                            DIP 1 {DUP};
                                            DIP 2 {COMPARE; LT};
                                            DIP 1 {SWAP};
                                            SWAP;
                                            IF { DUP;
                                                 DIP 1 {SWAP};
                                                 DIP 1 {SUB};
                                                 DIP 1 {DUP};
                                                 SUB;
                                                 DIP 1
                                                     { {DIG 2; DUP; DIP 1 {DUG 2}};
                                                       CONTRACT unit;
                                                       IF_NONE { PUSH string
                                                                      ""handling error: cannot return exceeded fund"";
                                                                 FAILWITH
                                                               }
                                                               { SWAP;
                                                                 PUSH unit Unit;
                                                                 TRANSFER_TOKENS
                                                               }
                                                     };
                                                 DIP 2 {NIL operation};
                                                 DIP 1 {CONS}
                                               }
                                               { DIP 1 {DROP 1};
                                                 DIP 1 {NIL operation}
                                               }
                                          };
                                  DIP 2 {SWAP};
                                  DIP 1 {SWAP};
                                  SWAP;
                                  DIP 1 {DUP};
                                  PAIR;
                                  DIP 3 {{DUP; CAR; DIP 1 {CDR}}};
                                  DIP 4 {{DUP; CAR; DIP 1 {CDR}}};
                                  DIP 3 {SWAP};
                                  DIP 2 {SWAP};
                                  DIP 1 {ADD};
                                  DIP 3 {SWAP};
                                  DIP 2 {SWAP};
                                  DIP 1 {SWAP};
                                  CONS;
                                  SWAP;
                                  PAIR;
                                  SWAP;
                                  DIP 1 {SWAP; PAIR};
                                  PAIR
                                }
                                { PUSH string ""funding cap already reached"";
                                  FAILWITH
                                }
                           }
                           { DROP 1;
                             DUP;
                             CAR;
                             CDR;
                             SENDER;
                             COMPARE;
                             EQ;
                             IF { {DUP; CAR; DIP 1 {CDR}};
                                  DIP 1 {{DUP; CAR; DIP 1 {CDR}}};
                                  DIP 1 {SWAP};
                                  SWAP;
                                  DIP 3 {NIL (pair address mutez)};
                                  DIP 2 {PAIR};
                                  DIP 1 {PAIR};
                                  MAP { {DUP; CAR; DIP 1 {CDR}};
                                        CONTRACT unit;
                                        IF_NONE { PUSH string ""refund account invalid or of unsupported type"";
                                                  FAILWITH
                                                }
                                                { SWAP;
                                                  PUSH unit Unit;
                                                  TRANSFER_TOKENS
                                                }
                                      };
                                  PAIR
                                }
                                { PUSH string ""only contract owner can attempt a refund"";
                                  FAILWITH
                                }
                           }
                 }
                 { IF_LEFT { DIP 1 {DUP; CAR; CDR; SENDER; COMPARE; EQ};
                             SWAP;
                             IF { BALANCE;
                                  SWAP;
                                  DIP 2
                                      { {DUP; CAR; DIP 1 {CDR}};
                                        DIP 1 {{DUP; CAR; DIP 1 {CDR}}};
                                        DIP 1 {SWAP};
                                        SWAP;
                                        DIP 3
                                            {PUSH (list (pair address mutez)) {}};
                                        DIP 2 {PAIR};
                                        DIP 1 {PAIR}
                                      };
                                  CONTRACT unit;
                                  IF_NONE { PUSH string ""withdraw account invalid or of unsupported type"";
                                            FAILWITH
                                          }
                                          {SWAP; PUSH unit Unit; TRANSFER_TOKENS};
                                  DIP 1 {DROP 1};
                                  DIP 1 {NIL operation};
                                  CONS;
                                  PAIR
                                }
                                { PUSH string ""only contract owner can perform a withdraw"";
                                  FAILWITH
                                }
                           }
                           { IF_LEFT { DIP 1 {DUP; CAR; CDR; SENDER; COMPARE; EQ};
                                       SWAP;
                                       IF { DIP 1 {{DUP; CAR; DIP 1 {CDR}}};
                                            DIP 2 {{DUP; CAR; DIP 1 {CDR}}};
                                            DIP 2 {SWAP};
                                            DIP 1 {SWAP};
                                            SWAP;
                                            DIP 1
                                                { PUSH (pair nat (pair (option (pair address mutez)) (list (pair address mutez))))
                                                       (Pair 0 (Pair None {}))
                                                };
                                            ITER { DIP 1 {{DUP; CAR; DIP 1 {CDR}}};
                                                   {DIG 3; DUP; DIP 1 {DUG 3}};
                                                   {DIG 2; DUP; DIP 1 {DUG 2}};
                                                   SUB;
                                                   EQ;
                                                   IF { SWAP;
                                                        PUSH nat 1;
                                                        ADD;
                                                        DIP 2
                                                            { { DUP;
                                                                CAR;
                                                                DIP 1 {CDR}
                                                              }
                                                            };
                                                        DIP 2 {DROP 1};
                                                        DIP 1 {SOME; PAIR};
                                                        PAIR
                                                      }
                                                      { SWAP;
                                                        PUSH nat 1;
                                                        ADD;
                                                        DIP 2
                                                            { { DUP;
                                                                CAR;
                                                                DIP 1 {CDR}
                                                              }
                                                            };
                                                        DIP 1 {SWAP};
                                                        DIP 2 {CONS};
                                                        DIP 1 {PAIR};
                                                        PAIR
                                                      }
                                                 };
                                            {DUP; CAR; DIP 1 {CDR}};
                                            DROP 1;
                                            {DUP; CAR; DIP 1 {CDR}};
                                            DIP 2 {DROP 1};
                                            IF_NONE { PUSH string ""index out of range"";
                                                      FAILWITH
                                                    }
                                                    {PAIR};
                                            {DUP; CAR; DIP 1 {CDR}};
                                            DIP 1 {SWAP};
                                            DIP 2 {SWAP};
                                            DIP 2 {PAIR};
                                            DIP 1 {PAIR};
                                            {DUP; CAR; DIP 1 {CDR}};
                                            CONTRACT unit;
                                            IF_NONE { PUSH string ""refund account invalid or of unsupported type"";
                                                      FAILWITH
                                                    }
                                                    { SWAP;
                                                      PUSH unit Unit;
                                                      TRANSFER_TOKENS
                                                    };
                                            DIP 1 {NIL operation};
                                            CONS;
                                            PAIR
                                          }
                                          { PUSH string ""only contract owner can attempt a refund"";
                                            FAILWITH
                                          }
                                     }
                                     { DIP 1 {DUP; CAR; CDR; SENDER; COMPARE; EQ};
                                       SWAP;
                                       IF { DIP 1 {{DUP; CAR; DIP 1 {CDR}}};
                                            DIP 2 {{DUP; CAR; DIP 1 {CDR}}};
                                            DIP 2 {SWAP};
                                            DIP 1 {SWAP};
                                            SWAP;
                                            DIP 1
                                                { PUSH (pair nat (pair (option (pair address mutez)) (list (pair address mutez))))
                                                       (Pair 0 (Pair None {}))
                                                };
                                            ITER { DIP 1 {{DUP; CAR; DIP 1 {CDR}}};
                                                   {DIG 3; DUP; DIP 1 {DUG 3}};
                                                   {DIG 2; DUP; DIP 1 {DUG 2}};
                                                   SUB;
                                                   EQ;
                                                   IF { SWAP;
                                                        PUSH nat 1;
                                                        ADD;
                                                        DIP 2
                                                            { { DUP;
                                                                CAR;
                                                                DIP 1 {CDR}
                                                              }
                                                            };
                                                        DIP 2 {DROP 1};
                                                        DIP 1 {SOME; PAIR};
                                                        PAIR
                                                      }
                                                      { SWAP;
                                                        PUSH nat 1;
                                                        ADD;
                                                        DIP 2
                                                            { { DUP;
                                                                CAR;
                                                                DIP 1 {CDR}
                                                              }
                                                            };
                                                        DIP 1 {SWAP};
                                                        DIP 2 {CONS};
                                                        DIP 1 {PAIR};
                                                        PAIR
                                                      }
                                                 };
                                            {DUP; CAR; DIP 1 {CDR}};
                                            DROP 1;
                                            {DUP; CAR; DIP 1 {CDR}};
                                            DIP 2 {DROP 1};
                                            IF_NONE { PUSH string ""index out of range"";
                                                      FAILWITH
                                                    }
                                                    {PAIR};
                                            {DUP; CAR; DIP 1 {CDR}};
                                            DIP 1 {SWAP};
                                            DIP 2 {SWAP};
                                            DIP 2 {PAIR};
                                            DIP 1 {PAIR};
                                            DROP 1;
                                            NIL operation;
                                            PAIR
                                          }
                                          { PUSH string ""only contract owner can attempt a refund"";
                                            FAILWITH
                                          }
                                     }
                           }
                 }
       };
}".

Definition b2b (b : Datatypes.bool) : b -> is_true b.
  by case: b.
Defined.

Definition success_contract : success (contract_file_M contract 12).
by vm_compute.
Defined.

Definition fundme_file := @extract _ _ (b2b success_contract).

Definition parameter_ty :=
  Eval vm_compute in contract_file_parameter fundme_file.
Definition storage_ty :=
  Eval vm_compute in contract_file_storage fundme_file.
Module fundme (C : ContractContext).
Module semantics := Semantics C. Import semantics.

Definition transfer error {A S}
  : instruction_seq A false
    (address ::: mutez ::: S)
    (operation ::: S) :=
  {
    CONTRACT None unit;
    IF_NONE {PUSH syntax_type.string error; FAILWITH}
            {SWAP; PUSH unit Unit; TRANSFER_TOKENS}
  }.

Definition refundall {A S}
  : instruction_seq A false
    (storage_ty ::: S)
    ((pair (list operation) storage_ty) ::: S) :=
  {
    UNPAIR;
    DIP1 {UNPAIR};
    DIP1 {SWAP}; SWAP;
    DIIIP {NIL (pair address mutez)};
    DIIP {PAIR};
    DIP1 {PAIR};
    @MAP _ (list (pair address mutez)) _ (map_list _ _) _
         (UNPAIR;; transfer "refund account invalid or of unsupported type"); PAIR
  }.
Open Scope michelson.

Definition isolate {A S}
  : instruction_seq A false
    (nat ::: list (pair address mutez) ::: S)
    ((pair (pair address mutez) (list (pair address mutez))) ::: S) :=
  {
    SWAP; DIP1 {PUSH _ (Pair (Nat_constant 0) (Pair None_ (Concrete_list [::])))};
    ITER
      {DIP1 {UNPAIR}; DUUUUP; DUUUP; SUB; EQ;
       IF_TRUE {SWAP; PUSH nat (Nat_constant 1); ADD; DIIP {UNPAIR}; DIIP {DROP1}; DIP1 {SOME; PAIR}; PAIR}
               {SWAP; PUSH nat (Nat_constant 1); ADD; DIIP {UNPAIR}; DIP1 {SWAP}; DIIP {CONS}; DIP1 {PAIR}; PAIR}
       : instruction A false (_ ::: iter_elt_type (list (pair address mutez)) (iter_list (pair address mutez)) ::: _) _};
    UNPAIR; DROP1; UNPAIR; DIIP {DROP1}; IF_NONE {PUSH syntax_type.string "index out of range"; FAILWITH} {PAIR}
  }.

Definition refund1 {A S}
  : instruction_seq A false
    (nat ::: storage_ty ::: S)
    ((pair (list operation) storage_ty) ::: S) :=
  {
    DIP1 {UNPAIR}; DIIP {UNPAIR}; DIIP {SWAP}; DIP1 {SWAP}
  } ;;; isolate ;;;
  {
    UNPAIR;
    DIP1 {SWAP}; DIIP {SWAP}; DIIP {PAIR}; DIP1 {PAIR}; UNPAIR
  } ;;; transfer "refund account invalid or of unsupported type";;;
  {
    DIP1 {NIL operation}; CONS; PAIR
  }.

Definition droprefund1 {A S}
  : instruction_seq A false
    (nat ::: storage_ty ::: S)
    ((pair (list operation) storage_ty) ::: S) :=
  {
    DIP1 {UNPAIR}; DIIP {UNPAIR}; DIIP {SWAP}; DIP1 {SWAP}
  };;; isolate;;;
  {
    UNPAIR;
    DIP1 {SWAP}; DIIP {SWAP}; DIIP {PAIR}; DIP1 {PAIR};
    DROP1; NIL operation; PAIR
  }.

Definition withdraw {A S}
  : instruction_seq A false
    (address ::: mutez ::: storage_ty ::: S)
    ((pair (list operation) storage_ty) ::: S) :=
  DIIP {UNPAIR;
        DIP1 {UNPAIR};
        DIP1 {SWAP}; SWAP;
        DIIIP {PUSH (list (pair address mutez)) (Concrete_list nil)};
        DIIP {PAIR};
        DIP1 {PAIR}};;
  transfer "withdraw account invalid or of unsupported type";;;
  {
    DIP1 {DROP1}; DIP1 {NIL operation};
    CONS; PAIR
  }.

Definition fund {A S}
  : instruction_seq A false
    (address ::: mutez ::: storage_ty ::: S)
    ((pair (list operation) storage_ty) ::: S) :=
  {
    DIIP {UNPAIR; UNPAIR; DUP}; DIIIP {PAIR; PAIR}; DIP1 {SWAP}; SWAP; DIP1 {SWAP}; DIIP {SWAP};
    IF_NONE {DIP1 {NIL operation}}
            {DIIP {DUP; UNPAIR; DROP1; UNPAIR; DIP1 {DROP1}}; DIP1 {DUP}; DIIP {@ADD _ _ _ (Mk_add _ _ _ Add_variant_tez_tez) _}; SWAP; DIP1 {DUP}; DIIP {COMPARE; LT}; DIP1 {SWAP}; SWAP;
             IF_ IF_bool
                 {DUP; DIP1 {SWAP}; DIP1 {@SUB _ _ _ (Mk_sub _ _ _ Sub_variant_tez_tez) _}; DIP1 {DUP}; @SUB _ _ _ (Mk_sub _ _ _ Sub_variant_tez_tez) _; DIP1 (SEQ DUUUP (transfer "handling error: cannot return exceeded fund")); DIIP {NIL operation}; DIP1 {CONS}}
                 {DIP1 {DROP1}; DIP1 {NIL operation}}}; DIIP {SWAP};
    DIP1 {SWAP}; SWAP; DIP1 {DUP}; PAIR; DIIIP {UNPAIR}; DIIIIP {UNPAIR}; DIIIP {SWAP}; DIIP {SWAP}; DIP1 {@ADD _ _ _ (Mk_add _ _ _ Add_variant_tez_tez) _} ; DIIIP {SWAP}; DIIP {SWAP}; DIP1 {SWAP}; CONS; SWAP; PAIR; SWAP; DIP1 {SWAP; PAIR}; PAIR
  }.

Definition canfund {A S} :
    instruction_seq A false
    (storage_ty ::: S)
    (bool ::: S) :=
  {
    UNPAIR; UNPAIR; DIP1 {DROP1};
    IF_NONE {DROP1; PUSH _ True_}
            {DIP1 {UNPAIR; DIP1 {DROP1}};
             Instruction_opcode (@COMPARE _ mutez _);
             GT}
  }.

Definition valfund {A S} :
    instruction_seq A false
    (storage_ty ::: S)
    ((pair (list operation) storage_ty) ::: S) :=
  DUP;; canfund;;;
  {
    IF_ IF_bool ({AMOUNT; SENDER};;; fund)
        {PUSH syntax_type.string "funding cap already reached"; FAILWITH}
  }.

Definition fundme : full_contract false parameter_ty None storage_ty :=
  {
    DUP; CAR; DIP1 {CDR};
    IF_LEFT
      {IF_LEFT (DROP1;; valfund)
               {DROP1; DUP; CAR; CDR; SENDER; COMPARE; EQ;
                IF_TRUE refundall {PUSH syntax_type.string "only contract owner can attempt a refund"; FAILWITH}}}
      {IF_LEFT
         {DIP1 {DUP; CAR; CDR; SENDER; COMPARE; EQ}; SWAP;
          IF_TRUE ({BALANCE; SWAP};;; withdraw)
                  {PUSH syntax_type.string "only contract owner can perform a withdraw"; FAILWITH}}
         {IF_LEFT
            {DIP1 {DUP; CAR; CDR; SENDER; COMPARE; EQ}; SWAP;
              IF_TRUE refund1 {PUSH syntax_type.string "only contract owner can attempt a refund"; FAILWITH}}
            {DIP1 {DUP; CAR; CDR; SENDER; COMPARE; EQ}; SWAP;
             IF_TRUE droprefund1 {PUSH syntax_type.string "only contract owner can attempt a refund"; FAILWITH}}}}
  }.

Require Import util.

Compute pp fundme.


Lemma test : fundme = contract_file_code fundme_file.
Proof.
  vm_compute.
  apply erefl.


Compute micheline_pp (michelson2micheline_type storage_ty) 4 true true.
Compute micheline_pp (michelson2micheline_instruction (untype_data parameter_ty)) 4 true true.


Definition t :=
"{ DUP;
                 { {DUP; CAR; DIP 1 {CDR}};
                   {DUP; CAR; DIP 1 {CDR}};
                   DIP 1 {DROP 1};
                   IF_NONE {DROP 1; PUSH bool True}
                           { DIP 1
                                 { {DUP; CAR; DIP 1 {CDR}};
                                   DIP 1 {DROP 1}
                                 };
                             COMPARE;
                             GT }
                 };
                 IF { AMOUNT;
                      SENDER;
                      { { DIP 2
                              { {DUP; CAR; DIP 1 {CDR}};
                                {DUP; CAR; DIP 1 {CDR}};
                                DUP
                              };
                          DIP 3 {PAIR; PAIR};
                          DIP 1 {SWAP};
                          SWAP;
                          DIP 1 {SWAP};
                          DIP 2 {SWAP}
                        };
                        IF_NONE {DIP 1 {NIL operation}}
                                { DIP 2
                                      { DUP;
                                        {DUP; CAR; DIP 1 {CDR}};
                                        DROP 1;
                                        {DUP; CAR; DIP 1 {CDR}};
                                        DIP 1 {DROP 1}
                                      };
                                  DIP 1 {DUP};
                                  DIP 2 {ADD};
                                  SWAP;
                                  DIP 1 {DUP};
                                  DIP 2 {COMPARE; LT};
                                  DIP 1 {SWAP};
                                  SWAP;
                                  IF { DUP;
                                       DIP 1 {SWAP};
                                       DIP 1 {SUB};
                                       DIP 1 {DUP};
                                       SUB;
                                       DIP 1
                                           { { DIG 2;
                                               DUP;
                                               DIP 1 {DUG 2}
                                             };
                                             CONTRACT  unit;
                                             IF_NONE { PUSH string
                                                            ""handling error: cannot return exceeded fund"";
                                                       FAILWITH
                                                     }
                                                     { SWAP;
                                                       PUSH unit Unit;
                                                       TRANSFER_TOKENS
                                                     }
                                           };
                                       DIP 2 {NIL operation} ;
                                       DIP 1 {CONS}
                                     }
                                     { DIP 1 {DROP 1};
                                       DIP 1 {NIL operation}
                                     }
                                };
                        DIP 2 {SWAP};
                        DIP 1 {SWAP};
                        SWAP;
                        DIP 1 {DUP};
                        PAIR;
                        DIP 3 {{DUP; CAR; DIP 1 {CDR}}};
                        DIP 4 {{DUP; CAR; DIP 1 {CDR}}};
                        DIP 3 {SWAP};
                        DIP 2 {SWAP};
                        DIP 1 {ADD};
                        DIP 3 {SWAP};
                        DIP 2 {SWAP};
                        DIP 1 {SWAP};
                        CONS;
                        SWAP;
                        PAIR;
                        SWAP;
                        DIP 1 {SWAP; PAIR};
                        PAIR
                      }
                    }
                    { PUSH string ""funding cap already reached"";
                      FAILWITH
                    }
               }".
Definition t' :=
  let! y := parsed_M t 12 in
  let! z := list_map micheline2michelson.micheline2michelson_instruction y in
  @typer.type_check_instruction_seq None typer.type_instruction_seq (head untyped_syntax.NOOP z)
               (storage_ty ::: [::])
               (pair (list operation) storage_ty ::: [::]).

Definition success_t' : success t'.
by vm_compute.
Defined.
Definition t'' := Eval vm_compute in projT2 (@extract _ _ (b2b success_t')).
Lemma test : t'' = valfund.
  vm_compute.
  apply erefl.
Eval vm_compute in (erefl : t'' = valfund).
Eval vm_compute in contract_file_code fundme_file.

Lemma SEQA s x y z w tff
      (A : instruction s false x y)
      (B : instruction s false y z)
      (C : instruction_seq s tff z w) env fuel arg :
  eval_seq env (SEQ A (SEQ B C)) fuel arg
= eval_seq env (SEQ (Instruction_seq (SEQ A {B})) C) fuel arg.
Proof.
  (destruct fuel => //).
  (destruct fuel => //).
  rewrite /eval_seq.
  rewrite /=.
  rewrite /=.
  destruct A => //.
  destruct i => //.

  destruct B => //.

  destruct i => //.

  rewrite /=.
  rewrite /eval_seq_body.
  rewrite /=.
  move=> ?.
  rewrite /=.
  native_compute.

  done.
  destruct fuel.

  done.

  native_compute.
  rewrite /=.
  vm_compute.
  rewrite /=.

Lemma fundme_split env fuel arg :
  eval_seq env fundme fuel arg = eval_seq env (contract_file_code fundme_file) fuel arg.

Lemma fundme_split :
  fundme = contract_file_code fundme_file.
Proof.
  vm_compute.
  apply erefl.
  done.

Lemma fundme_split env fuel arg :
  eval_seq env fundme fuel arg = eval_seq env (contract_file_code fundme_file) fuel arg.
Proof.
  destruct fuel.
  vm_compute.
  done.
  more_fuel.
  simpl.
  vm_compute.
  done.

  rewrite /=.
  case: fuel.
  more_fuel.
  congr (SEQ _ _).
  apply erefl.
End fundme.
