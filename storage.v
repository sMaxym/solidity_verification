(*
Storage module provides the means to model a Solidity storage using the functional mapping.
SolifityFun module is implemneted the same way as a storage however it operates with
lambda functions that officiate the role of a solidity function's command.
*)

Module Storage.

Definition storage := string * string -> SolidityVar.var.
Definition empty (def : SolidityVar.var) : storage := (fun _ => def).
Definition update (s : storage) (a : string * string) (v : SolidityVar.var) :=
  (fun a' : string * string => if a =? a' then v else s a').

Definition Vdefault := SolidityVar.build_var SolidityVar.VTint 0.

Lemma apply_empty : forall (x : string * string) (v : SolidityVar.var),
  (empty v) x = v.
Proof.
  intros.
  trivial.
Qed.

End Storage.

Module SolidityFun.

Definition command := Storage.storage -> Storage.storage.

Definition functions := string -> list command.
Definition empty : functions := (fun _ => nil).
Definition new (fs : functions) (n : string) (cmds : list command) :=
  fun n' => if eqb n n' then cmds else fs n'.

End SolidityFun.
