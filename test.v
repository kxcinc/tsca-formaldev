From mathcomp Require Import all_ssreflect all_algebra.
From Michocoq Require Import util macros syntax typer error.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Sloppy.
Variable Program : Type.
Variable ChainId : Type.
Variable Timestamp : Type.
Variable RcLabel : eqType.
Variable AcLabel : eqType.
Variable ContractAddress : Type.
Definition MichelsonValue := untyped_syntax.concrete_data.
Definition MichelsonType := type.
Definition ProgramType := prod MichelsonType MichelsonType.
Variable rctype : RcLabel -> ProgramType.
Variable actype : AcLabel -> MichelsonType.
Variable progtype : Program -> ProgramType.
Definition TokenMeasure := Datatypes.nat.
Definition TokenUpdate := ssrint.int.
Definition Address := sum (Equality.sort RcLabel) (Equality.sort AcLabel).
Definition Delegation := Datatypes.option AcLabel.
Definition StorageUpdate := MichelsonValue.
Definition michelsonTypeCheck : MichelsonValue -> MichelsonType -> Datatypes.bool :=
  fun a b => success (type_data Readable a b).
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
    relevantContracts : RcLabel -> Datatypes.option RValue;
    affectedContracts : AcLabel -> Datatypes.option TokenUpdate;
  }.

Definition updateRCSr (x : RcLabel) (y : TokenUpdate)
           (storageUpdate : Datatypes.option StorageUpdate)
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
| Node : effOp -> seq eotree -> eotree
| Leaf of effOp.

Inductive reotree : Type :=
| Root : forall e, is_transfer e -> ChainId -> Timestamp -> RcLabel -> eotree -> reotree.

Fixpoint insert (p : seq Datatypes.nat) (t : eotree) (v : eotree) :=
  match p with
  | [::] => v
  | n :: p' =>
    match t with
    | Node e cs =>
      let t' := nth t cs n in
      let cs' := set_nth t cs n (insert p' t' v) in
      Node e cs'
    | Leaf _ => v
    end
  end.

Record environment :=
  {
    chainid : ChainId;
    timestamp : Timestamp;
    self: RcLabel;
    src: RcLabel;
    sender: RcLabel;
  }.

Record rc_label_gen :=
  {
    rcn: Datatypes.nat -> ProgramType -> RcLabel;
    inj_rcn : injective (fun '(a, b) => rcn a b);
    cmp_rcn : forall k, rctype \o rcn k =1 id;
  }.

Inductive InternalOperation :=
| InternalTransfer : Address -> TokenMeasure -> InternalOperation
| InternalOrigination : RcLabel -> Program -> MichelsonValue -> TokenMeasure -> Delegation -> InternalOperation
| InternalDelegationUpdate : Delegation -> InternalOperation.

Variable mich_eval :
  environment -> rc_label_gen ->
  RelevantChainState -> Program -> MichelsonValue -> TokenMeasure
  -> MichelsonValue -> seq InternalOperation * MichelsonValue.

Fixpoint runriv (cid: ChainId) (ts: Timestamp) (adrs: Address) (rcn: rc_label_gen)
           (nse: seq Datatypes.nat * effOp) (G: Datatypes.option RelevantChainState) (k: Datatypes.nat)
           (reot: reotree) (queue: seq (seq Datatypes.nat * effOp)) : Datatypes.option RelevantChainState * reotree.
Check (
match nse with
| (_, TransferRc sender callee _ _ as eop) =>
  (act x )
  let code, storage,
  let '(iops, storage') :=
      mich_eval
        {|
          chainid:=cid;
          timestamp:=ts;
          self:=callee;
          src:=adrs;
          sender:=sender;
        |}
        rcn
        G


  let G' := obind (fun x => omap (updateRCSr callee 0 None) (act x eop)) G in


  in.

| (_, eop) =>
  match queue with
  | [::] => (obind (fun x => act x eop) G, reot)
  | head :: rest =>
    runriv cid ts adrs rcn head (obind (fun x => act x eop) G) k reot rest
  end
end).
move=> cid ts adrs rcn.

Definition eval

End Michelson.
End Sloppy.
