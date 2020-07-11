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
Variable actype : AcLabel -> MichelsonType.
Variable progtype : Program -> ProgramType.
Definition Delegation := option AcLabel.
Definition StorageUpdate := MichelsonValue.
Variable michelsonTypeCheck : MichelsonValue -> MichelsonType -> bool.
Variable rcn : nat -> ProgramType -> RcLabel.
Variable inj_rcn : injective (fun '(a, b) => rcn a b).
Import intZmod.

Inductive effOp : Type :=
| TransferAc : forall (sender : Address) (destination : AcLabel) (amount : TokenMeasure), effOp
| TransferRc : forall (sender : Address) (destination : RcLabel) (amount : TokenMeasure) (storageUpdate : StorageUpdate), effOp
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

Definition updateRCSr (x : RcLabel) (y : TokenUpdate)
           (storageUpdate : option StorageUpdate)
           (G : RelevantChainState) :=
  if match storageUpdate with
    | Some storageUpdate =>
      michelsonTypeCheck storageUpdate (snd (rctype x))
    | None => true
     end
  then match relevantContracts G x with
  | Some _ =>
    Some (mkRCS (fun X =>
      let Y := relevantContracts G X in
      if X == x
      then
        match Y with
        | Some Y =>
          if intOrdered.lez 0 (sgz y)
          then Some {|
                   program := program Y;
                   storage :=
                     match storageUpdate with
                     | Some z => z
                     | None => storage Y
                     end;
                   balance := balance Y + `|y|;

                   delegation := delegation Y;
                 |}
          else if balance Y >= `|y|
          then Some {|
                   program := program Y;
                   storage :=
                     match storageUpdate with
                     | Some z => z
                     | None => storage Y
                     end;
                   balance := balance Y - `|y|;
                   delegation := delegation Y;
                 |}
          else None
        | None => None
        end
      else Y) (affectedContracts G))
  | None => None
  end
  else None.

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
  | TransferRc (inl sender) dest am su => (* r *)
    obind (updateRCSr dest (Posz am) (Some su)) (updateRCSr sender (Negz am) None G)
  | TransferRc (inr sender) dest am su => (* a *)
    updateRCSr dest (Posz am) (Some su) (updateRCSa sender (Negz am) G)
  | TransferAc (inl sender) dest am =>    (* r *)
    omap (updateRCSa dest (Posz am)) (updateRCSr sender (Negz am) None G)
  | TransferAc (inr _) _ _ => None        (* a *)
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
      (updateRCSr originator (Posz balance) None G)
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

Definition is_transfer (e : effOp) :=
  match e with
  | TransferAc _ _ _ | TransferRc _ _ _ _ => true
  | _ => false
  end.

Inductive eotree : Type :=
| Node : effOp -> list eotree -> eotree
| Leaf of effOp.

Inductive reotree : Type :=
| Root : forall e, is_transfer e -> eotree -> reotree.
End Sloppy.
