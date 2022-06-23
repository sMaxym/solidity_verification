(*
Contract provides a record to work with the smart contract representation
*)

Module Contract.

Record contract := build_contract
{
  balance : nat;
  program : SolidityFun.functions;
  storage : Storage.storage;
}.

Definition update_balance (c : contract) (b : nat) : contract :=
  build_contract b (program c) (storage c).
Definition update_program (c : contract) (p : SolidityFun.functions) : contract :=
  build_contract (balance c) p (storage c).
Definition update_storage (c : contract) (s : Storage.storage) : contract :=
  build_contract (balance c) (program c) s.

End Contract.

Module BlockchainInfo.

Definition info := SolidityVar.address -> Contract.contract.
Definition empty (def : Contract.contract) : info := (fun _ => def).
Definition update (i : info) (x : SolidityVar.address) (c : Contract.contract) :=
  fun x' => if SolidityVar.eqb_address x x' then c else i x'.

End BlockchainInfo.