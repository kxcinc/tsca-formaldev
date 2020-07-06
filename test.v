From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Sloppy.
Variable Program : Type.
Variable ChainId : Type.
Variable Timestamp : Type.
Variable RcLabel : eqType.
Variable AcLabel : eqType.
Variable MichelsonValue : Type.
Variable MichelsonType : Type.
Definition TokenMeasure := nat.
Definition TokenUpdate := int.
Variable ContractAddress : Type.
Definition Address := sum (Equality.sort RcLabel) (Equality.sort AcLabel).
Definition ProgramType := prod MichelsonType MichelsonType.
Variable rctype : RcLabel -> ProgramType.
Variable progtype : Program -> ProgramType.
Definition Delegation := option AcLabel.
Import intZmod.

Inductive effOp : Type :=
  | Transfer : forall (sender : Address) (destination : Address) (amount : TokenMeasure), effOp
  | Origination : forall (originator : Address) (rclabel : RcLabel) (code : Program) (storage : MichelsonType) (balance : TokenMeasure) (delegation : Delegation), effOp
  | DelegationUpdate : forall (subject : RcLabel) (delegation : Delegation), effOp.

Record RValue :=
  {
    program: Program;
    storage : MichelsonValue;
    balance : TokenMeasure;
    delegation : Delegation;
  }.

Record RelevantChainState :=
  {
    relevantContracts : RcLabel -> option RValue;
    affectedContracts : AcLabel -> option TokenUpdate;
  }.

Definition updateRCSr (x : RcLabel) (y : TokenMeasure) (G : RelevantChainState) :=
  {|
    relevantContracts := fun X =>
                           let Y := relevantContracts G X in
                           if X == x
                           then
                             match Y with
                             | Some Y =>
                               Some {|
                                 program := program Y;
                                 storage := storage Y;
                                 balance := balance Y - y;
                                 delegation := delegation Y;
                               |}
                             | None => None
                             end
                           else Y;
    affectedContracts := affectedContracts G;
  |}.

Definition updateRCSa (x : AcLabel) (y : TokenMeasure) (G : RelevantChainState) :=
  {|
    relevantContracts := relevantContracts G;
    affectedContracts := fun X =>
                           let Y := affectedContracts G X in
                           if X == x
                           then
                             match Y with
                             | Some Y => Some (addz Y (Negz y))
                             | None => Some (Negz y)
                             end
                           else Y;
  |}.

Definition act (G : RelevantChainState) (eop : effOp) :=
  match eop with
  | Transfer (inl sendor) (inl dest) am =>
    updateRCSr dest am (updateRCSr sendor am G)
  | Transfer (inr sendor) (inl dest) am =>
    updateRCSr dest am (updateRCSa sendor am G)
  | _ => G
  end.

End Sloppy.
