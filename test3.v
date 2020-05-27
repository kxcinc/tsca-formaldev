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
Require Import Michocoq.main
        Michocoq.typer
        Michocoq.micheline2michelson
        Michocoq.michelson2micheline
        Michocoq.micheline_pp.

Definition contract :=
"parameter (or (or unit unit) (or address (or nat nat)));
storage (pair (pair (option mutez) address) (pair mutez (list (pair address mutez))));
code {
       {DUP; CAR; DIP 1 {CDR}};
       IF_LEFT
         { IF_LEFT
             { DROP 1;
               { DUP;
                 { {DUP; CAR; DIP 1 {CDR}};
                   {DUP; CAR; DIP 1 {CDR}};
                   DIP 1 {DROP 1};
                   IF_NONE {DROP 1; PUSH bool True}
                           { DIP 1
                                 { {DUP; CAR; DIP 1 {CDR}};
                                   DIP 1 {DROP 1}
                                 };
                             COMPARE;
                             GT
                           }
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
                    DIP 3 {PUSH (list (pair address mutez)) {}};
                    DIP 2 {PAIR};
                    DIP 1 {PAIR};
                    MAP { {DUP; CAR; DIP 1 {CDR}};
                          CONTRACT  unit;
                          IF_NONE { PUSH string
                                         ""refund account invalid or of unsupported type"";
                                    FAILWITH
                                  }
                                  { SWAP;
                                    PUSH unit Unit;
                                    TRANSFER_TOKENS
                                  }
                        };
                    PAIR
                  }
                  { PUSH string
                         ""only contract owner can attempt a refund"";
                    FAILWITH
                  }
             }
         }
         { IF_LEFT { DIP 1 {DUP; CAR; CDR; SENDER; COMPARE; EQ};
                     SWAP;
                     IF { BALANCE;
                          SWAP;
                          { DIP 2
                                { {DUP; CAR; DIP 1 {CDR}};
                                  DIP 1 {{DUP; CAR; DIP 1 {CDR}}};
                                  DIP 1 {SWAP};
                                  SWAP;
                                  DIP 3
                                      {PUSH (list (pair address mutez)) {}};
                                  DIP 2 {PAIR};
                                  DIP 1 {PAIR}
                                };
                            { CONTRACT  unit;
                              IF_NONE { PUSH string
                                             ""withdraw account invalid or of unsupported type"";
                                        FAILWITH
                                      }
                                      { SWAP;
                                        PUSH unit Unit;
                                        TRANSFER_TOKENS
                                      }
                            };
                            DIP 1 {DROP 1};
                            DIP 1 {NIL operation};
                            CONS;
                            PAIR
                          }
                        }
                        { PUSH string
                               ""only contract owner can perform a withdraw"";
                          FAILWITH
                        }
                   }
                   { IF_LEFT { DIP 1 {DUP; CAR; CDR; SENDER; COMPARE; EQ};
                               SWAP;
                               IF { DIP 1 {{DUP; CAR; DIP 1 {CDR}}};
                                    DIP 2 {{DUP; CAR; DIP 1 {CDR}}};
                                    DIP 2 {SWAP};
                                    DIP 1 {SWAP};
                                    { { SWAP;
                                        DIP 1
                                            { PUSH (pair nat (pair (option (pair address mutez)) (list (pair address mutez))))
                                                   (Pair 0 (Pair None {}))
                                            }
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
                                      IF_NONE { PUSH string
                                                     ""index out of range"";
                                                FAILWITH
                                              }
                                              {PAIR}
                                    };
                                    {DUP; CAR; DIP 1 {CDR}};
                                    DIP 1 {SWAP};
                                    DIP 2 {SWAP};
                                    DIP 2 {PAIR};
                                    DIP 1 {PAIR};
                                    {DUP; CAR; DIP 1 {CDR}};
                                    { CONTRACT  unit;
                                      IF_NONE { PUSH string
                                                     ""refund account invalid or of unsupported type"";
                                                FAILWITH
                                              }
                                              { SWAP;
                                                PUSH unit Unit;
                                                TRANSFER_TOKENS
                                              }
                                    };
                                    DIP 1 {NIL operation};
                                    CONS;
                                    PAIR
                                  }
                                  { PUSH string
                                         ""only contract owner can attempt a refund"";
                                    FAILWITH
                                  }
                             }
                             { DIP 1 {DUP; CAR; CDR; SENDER; COMPARE; EQ};
                               SWAP;
                               IF { DIP 1 {{DUP; CAR; DIP 1 {CDR}}};
                                    DIP 2 {{DUP; CAR; DIP 1 {CDR}}};
                                    DIP 2 {SWAP};
                                    DIP 1 {SWAP};
                                    { { SWAP;
                                        DIP 1
                                            { PUSH (pair nat (pair (option (pair address mutez)) (list (pair address mutez))))
                                                   (Pair 0 (Pair None {}))
                                            }
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
                                      IF_NONE { PUSH string ""index out of range""; FAILWITH }
                                              { PAIR }
                                    };
                                    {DUP; CAR; DIP 1 {CDR}};
                                    DIP 1 {SWAP};
                                    DIP 2 {SWAP};
                                    DIP 2 {PAIR};
                                    DIP 1 {PAIR};
                                    DROP 1;
                                    NIL operation;
                                    PAIR
                                  }
                                  { PUSH string
                                         ""only contract owner can attempt a refund"";
                                    FAILWITH
                                  }
                             }
                   }
         }
     };".

Definition b2b (b : Datatypes.bool) : b -> is_true b.
  by case: b.
Defined.

Definition success_contract : success (contract_file_M contract 12).
by vm_compute.
Defined.

Definition fundme_file := @extract _ _ (b2b success_contract).

Definition parameter_ty := contract_file_parameter fundme_file.
Definition storage_ty := contract_file_storage fundme_file.
Module fundme (C:ContractContext).
Module semantics := Semantics C. Import semantics.

Definition transfer error {A S}
  : instruction_seq A false
    (address ::: mutez ::: S)
    (operation ::: S) :=
  {
    CONTRACT (Some "") unit;
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
    DIIIP {PUSH (list (pair address mutez)) (Concrete_list nil)};
    DIIP {PAIR};
    DIP1 {PAIR};
    @MAP _ (list (pair address mutez)) _ (map_list _ _) _
         (UNPAIR;; transfer "refund account invalid or of unsupported type"); PAIR
  }.
Open Scope michelson.

Definition isolate {A S}
  : instruction_seq A false
    (nat ::: list (pair address mutez) ::: S)
    ((pair (pair address mutez) (list (pair address mutez))) ::: S).
apply: (SEQ (Instruction_seq {SWAP; DIP1 {PUSH _ (Pair (Nat_constant 0) (Pair None_ (Concrete_list nil)))}}) _).
apply:
({(@ITER _ (list (pair address mutez)) (iter_list _) _
{DIP1 {UNPAIR}; DUUUUP; DUUUP; SUB; EQ; (_ : instruction _ false _ _)});
UNPAIR; DROP1; UNPAIR; DIIP {DROP1};
IF_NONE {PUSH syntax_type.string "index out of range"; FAILWITH} {PAIR}}).
apply: (IF_ IF_bool
 {SWAP; PUSH nat (Nat_constant 1);
 @ADD _ _ _ (Mk_add _ _ _ Add_variant_nat_nat) _ ;
 DIIP {UNPAIR}; DIIP {DROP1}; DIP1 {SOME; PAIR}; PAIR}
 {SWAP; PUSH nat (Nat_constant 1);
 @ADD _ _ _ (Mk_add _ _ _ Add_variant_nat_nat) _;
 DIIP {UNPAIR}; DIP1 {SWAP}; DIIP {CONS}; DIP1 {PAIR}; PAIR}).
Defined.

Definition refund1 {A S}
  : instruction_seq A false
    (nat ::: storage_ty ::: S)
    ((pair (list operation) storage_ty) ::: S) :=
  {
    DIP1 {UNPAIR}; DIIP {UNPAIR}; DIIP {SWAP}; DIP1 {SWAP};
    Instruction_seq isolate; UNPAIR;
    DIP1 {SWAP}; DIIP {SWAP}; DIIP {PAIR}; DIP1 {PAIR}; UNPAIR;
    Instruction_seq (transfer "refund account invalid or of unsupported type");
    DIP1 {PUSH (list operation) (Concrete_list nil)}; CONS; PAIR
  }.

Definition droprefund1 {A S}
  : instruction_seq A false
    (nat ::: storage_ty ::: S)
    ((pair (list operation) storage_ty) ::: S) :=
  {
    DIP1 {UNPAIR}; DIIP {UNPAIR}; DIIP {SWAP}; DIP1 {SWAP};
    Instruction_seq isolate; UNPAIR;
    DIP1 {SWAP}; DIIP {SWAP}; DIIP {PAIR}; DIP1 {PAIR};
    DROP1; PUSH (list operation) (Concrete_list nil); PAIR
  }.

Definition withdraw {A S}
  : instruction_seq A false
    (address ::: mutez ::: storage_ty ::: S)
    ((pair (list operation) storage_ty) ::: S) :=
  {
    DIIP {UNPAIR;
          DIP1 {UNPAIR};
          DIP1 {SWAP}; SWAP;
          DIIIP {PUSH (list (pair address mutez)) (Concrete_list nil)};
          DIIP {PAIR};
          DIP1 {PAIR}};
    Instruction_seq (transfer "withdraw account invalid or of unsupported type");
    DIP1 {DROP1}; DIP1 {PUSH (list operation) (Concrete_list nil)};
    CONS; PAIR
  }.
(* 1:17:35 *)
Definition fund {A S}
  : instruction_seq A false
    (address ::: mutez ::: storage_ty ::: S)
    ((pair (list operation) storage_ty) ::: S).
  apply: (SEQ (Instruction_seq {DIIP {UNPAIR; UNPAIR; DUP}; DIIIP {PAIR; PAIR};
                                DIP1 {SWAP}; SWAP; DIP1 {SWAP}; DIIP {SWAP}}) _).
  (* sender funding_cap amount ... *)
  apply ({IF_NONE {DIP1 {PUSH (list operation) (Concrete_list nil)}}
  {DIIP {DUP; UNPAIR; DROP1; UNPAIR; DIP1 {DROP1}}; DIP1 {DUP}; DIIP {@ADD _ _ _ (Mk_add _ _ _ Add_variant_tez_tez) _}; SWAP; DIP1 {DUP}; DIIP {COMPARE; LT}; DIP1 {SWAP}; SWAP;
   IF_ IF_bool
       {DUP; DIP1 {SWAP}; DIP1 {@SUB _ _ _ (Mk_sub _ _ _ Sub_variant_tez_tez) _}; DIP1 {DUP}; @SUB _ _ _ (Mk_sub _ _ _ Sub_variant_tez_tez) _; DIP1 (SEQ DUUUP (transfer "handling error: cannot return exceeded fund")); DIIP {PUSH (list operation) (Concrete_list nil)}; DIP1 {CONS}}
       {DIP1 {DROP1}; DIP1 {PUSH (list operation) (Concrete_list nil)}}};
          DIIP {SWAP}; DIP1 {SWAP}; SWAP; DIP1 {DUP}; PAIR ; DIIIP {UNPAIR}; DIIIIP {UNPAIR}; DIIIP {SWAP}; DIIP {SWAP}; DIP1 {@ADD _ _ _ (Mk_add _ _ _ Add_variant_tez_tez) _}; DIIIP {SWAP}; DIIP {SWAP}; DIP1 {SWAP}; CONS; SWAP; PAIR; SWAP; DIP1 {SWAP; PAIR}; PAIR}).
Defined.

Definition canfund {A S} :
    instruction_seq A false
    (storage_ty ::: S)
    (bool ::: S) :=
  {
    UNPAIR; UNPAIR; DIP1 {DROP1}; IF_NONE {DROP1; PUSH _ True_} {DIP1 {UNPAIR; DIP1 {DROP1}}; COMPARE; GT}
  }.

Definition valfund {A S} :
    instruction_seq A false
    (storage_ty ::: S)
    ((pair (list operation) storage_ty) ::: S) :=
  {
    DUP;
    Instruction_seq canfund;
    IF_ IF_bool {AMOUNT; SENDER; Instruction_seq fund}
        {PUSH syntax_type.string "funding cap already reached"; FAILWITH}
  }.

Definition fundme: full_contract false parameter_ty (Some "fundme") storage_ty.
apply: ({Instruction_seq {DUP; CAR; DIP1 {CDR}}; (_ : instruction _ false _ _)}).
apply: (IF_LEFT (_ : instruction_seq _ false _ _) _).
+ apply: ({IF_LEFT {DROP1; Instruction_seq valfund} (_ : instruction_seq _ false _ _)}).
  apply: ({DROP1; DUP; CAR; CDR; SENDER; COMPARE; EQ; (_ : instruction _ false _ _)}).
  apply (IF_ IF_bool refundall
              {PUSH syntax_type.string "only contract owner can attempt a refund"; FAILWITH}).
+ apply: ({IF_LEFT (_ : instruction_seq _ false _ _) _}).
  - apply: ({DIP1 {DUP; CAR; CDR; SENDER; COMPARE; EQ}; SWAP; (_ : instruction _ false _ _)}).
    apply (IF_ IF_bool {BALANCE; SWAP; Instruction_seq withdraw}
                {PUSH syntax_type.string "only contract owner can perform a withdraw"; FAILWITH}).
+ apply: ({IF_LEFT (_ : instruction_seq _ false _ _) _}).
  - apply: ({DIP1 {DUP; CAR; CDR; SENDER; COMPARE; EQ}; SWAP; (_ : instruction _ false _ _)}).
    apply: (IF_ IF_bool refund1
                {PUSH syntax_type.string "only contract owner can attempt a refund"; FAILWITH}).
  - apply: ({DIP1 {DUP; CAR; CDR; SENDER; COMPARE; EQ}; SWAP; (_ : instruction _ false _ _)}).
    apply: (IF_ IF_bool droprefund1
                {PUSH syntax_type.string "only contract owner can attempt a refund"; FAILWITH}).
Defined.

      contract_file_code :


Definition dummy: contract_file.
  apply: Mk_contract_file => //.
  constructor.
Compute (let! x := parsed_M code 1000 in
         let! y := list_map micheline2michelson_instruction x in
         Return (seq.map type_instruction_seq y)).
Require Import Michocoq.untyper
        Michocoq.micheline2michelson
        Michocoq.michelson2micheline
        Michocoq.micheline_pp.

Check String.concat.
About Datatypes.concat.
Compute untype_instruction_seq fundme.
Compute String.concat ";" (seq.map (fun x => micheline_pp x 4 true true) (michelson2micheline_ins_seq (untype_instruction_seq fundme))).
Require Import Michocoq.main.
Require Import Michocoq.error.
Require Import Michocoq.typer.
Import Notations.
Check type_instruction.
Compute (let! x := parsed_M t 1000 in
         let! y := list_map micheline2michelson_instruction x in
         Return (seq.map type_instruction_seq y)).

Module U := Untyper C.
Check U.typer.instruction.
Check instruction.
Fail Check (erefl : U.typer.syntax.instruction = instruction).

Check fundme : U.typer.syntax.instruction _ _ _ _.
Set Printing All.
Check U.untype_instruction fundme.
Check U.typer.syntax.instruction.
Check IF_.

fundme.
Check michelson2micheline_instruction
Check micheline2michelson_file.
Check micheline_syntax.loc_micheline.


End tmp.
