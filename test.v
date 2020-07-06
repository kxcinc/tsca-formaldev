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
| Origination : forall (originator : RcLabel) (rclabel : RcLabel) (code : Program) (storage : MichelsonValue) (balance : TokenMeasure) (delegation : Delegation), effOp
| DelegationUpdate : forall (subject : RcLabel) (delegation : Delegation), effOp.

Record RValue :=
  {
    program: Program;
    storage : MichelsonValue;
    balance : TokenMeasure;
    delegation : Delegation;
  }.

Record RelevantChainState :=
  mkRCS {
    relevantContracts : RcLabel -> option RValue;
    affectedContracts : AcLabel -> option TokenUpdate;
  }.

Definition updateRCSr (x : RcLabel) (y : TokenUpdate) (G : RelevantChainState) :=
  match relevantContracts G x with
  | Some _ =>
    Some (mkRCS (fun X =>
      let Y := relevantContracts G X in
      if X == x
      then
        match Y with
        | Some Y =>
          Some {|
              program := program Y;
              storage := storage Y;
              balance :=
                if intOrdered.lez 0 (sgz y)
                then balance Y + `|y|
                else balance Y - `|y|;
              delegation := delegation Y;
            |}
        | None => None
        end
      else Y) (affectedContracts G))
  | None => None
  end.

Definition updateRCSa (x : AcLabel) (y : TokenUpdate) (G : RelevantChainState) :=
  mkRCS (relevantContracts G)
  (fun X =>
    let Y := affectedContracts G X in
    if X == x
    then
      match Y with
      | Some Y => Some (addz Y y)
      | None => Some y
      end
    else Y).

Definition act (G : RelevantChainState) (eop : effOp) :=
  match eop with
  | Transfer (inl sendor) (inl dest) am => (* r/r *)
    obind (updateRCSr dest (Negz am)) (updateRCSr sendor (Posz am) G)
  | Transfer (inr sendor) (inl dest) am => (* a/r *)
    updateRCSr dest (Negz am) (updateRCSa sendor (Posz am) G)
  | Transfer (inl sendor) (inr dest) am => (* r/a *)
    omap (updateRCSa dest (Negz am)) (updateRCSr sendor (Posz am) G)
  | Transfer (inr _) (inr _) _ => None     (* a/a *)
  | Origination originator rclabel code storage balance delegation =>
    match relevantContracts G rclabel with
    | None =>
      omap (fun G =>
      mkRCS (fun X =>
               if X == rclabel
               then Some {|
                   program:=code;
                   storage:=storage;
                   balance:=balance;
                   delegation:=delegation;
                 |}
               else relevantContracts G X) (affectedContracts G))
      (updateRCSr originator (Posz balance) G)
    | Some _ => None
    end
  | DelegationUpdate subject delegation =>
    match relevantContracts G subject with
    | Some p =>
      Some (mkRCS (fun X =>
               if X == subject
               then Some {|
                   program:=program p;
                   storage:=storage p;
                   balance:=balance p;
                   delegation:=delegation;
                 |}
               else relevantContracts G X) (affectedContracts G))
    | None => None
    end
  end.
End Sloppy.
