(* main.v -- entry point of the system *)
(* Require Import String.
Local Open Scope string_scope.

Require Import PeanoNat.
Local Open Scope nat_scope. *)

(* Require Import List.
Import ListNotations. *)

(* Open Scope bool_scope.
 *)

Require Import Bool.
Require Import String.
Require Import Ascii.
Require Import PeanoNat.
Require Import List.
Require Import Arith.




Class Eq A :=
{
  eqb : A -> A -> bool;
}.

(* eqb definitions for all neccessary types *)

Definition eqb_pair {A B : Type} `{Eq A} `{Eq B} (p1 p2 : A * B) : bool :=
  let (a, b) := p1 in
  let (u, v) := p2 in
    if andb (eqb a u) (eqb b v) then true else false.


Local Instance eqNat : Eq nat := { eqb := Nat.eqb; }.
Local Instance eqBool : Eq bool := { eqb := Bool.eqb; }.
Local Instance eqString : Eq string := { eqb := String.eqb; }.
Local Instance eqPair {A B : Type} `{Eq A} `{Eq B} : Eq (A * B) :=
{
  eqb := eqb_pair;
}.

Notation "x =? y" := (eqb x y) (at level 70).

Example test_eqbNat : 1 =? 2 = false.
Proof. simpl. reflexivity. Qed.
Example test_eqbBool :true =? true = true.
Proof. simpl. reflexivity. Qed.
Example test_eqbString : "test"%string =? "test1"%string = false.
Proof. simpl. reflexivity. Qed.
Example test_eqbPair : ("xyz"%string, 2) =? ("ab"%string, 2) = false.
Proof. simpl. reflexivity. Qed.

(* ------------------------------------------- *)



Notation "v 'Of' t " := (SolidityVar.build_var t v) (at level 100, t at next level).

Notation "'_' '|>' def" := (Storage.empty def) (at level 100, right associativity).
Notation "a '|>' v ';' s" := (Storage.update s a v)
  (at level 100, v at next level, right associativity).

Notation "'c[' b ',' p ',' s ']'" := (Contract.build_contract b p s) (at level 100, left associativity).
Notation "c '<=b' b" := (Contract.update_balance c b) (at level 101, left associativity).
Notation "c '<=p' p" := (Contract.update_program c p) (at level 101, left associativity).
Notation "c '<=s' s" := (Contract.update_storage c s) (at level 101, left associativity).

Notation "def 'is' 'Null'" := (BlockchainInfo.empty def) (at level 100, right associativity).
Notation "v 'By' a ';' s" := (BlockchainInfo.update s a v)
  (at level 100, a at next level, right associativity). 


Fixpoint execute (prg : list SolidityFun.command) (s : Storage.storage)
    : option Storage.storage :=
  match prg with
    | nil => Some s
    | cmd :: cmds_left => execute cmds_left (cmd s) 
  end.





Definition srpc_storage := (
  ("purchaseValue"%string, "srpc"%string) |> 0 Of SolidityVar.VTint;
  ("sellerAddress"%string, "srpc"%string) |> 0 Of SolidityVar.VTaddress;
  ("buyerAddress"%string, "srpc"%string) |> 0 Of SolidityVar.VTaddress;
  ("purchaseState "%string, "srpc"%string) |> 0 Of SolidityVar.VTint;
  _ |> Storage.Vdefault
).



Definition cmd_divide_purchaseValue_by_half :=
  (fun s : Storage.storage =>
    let pv := SolidityVar.v_value (s ("purchaseValue"%string, "srpc"%string)) in
      let half_pv := Nat.div pv in
        (Storage.update s ("purchaseValue"%string, "srpc"%string) (half_pv Of SolidityVar.VTint))
  ).


Definition srpc_constructor :=
  cmd_divide_purchaseValue_by_half  
  :: nil.
Definition srpc_prgs :=
  SolidityFun.new SolidityFun.empty "srpc"%string srpc_constructor.
Definition srpc := c[12, srpc_prgs, srpc_storage].



(* Arbitrary address of the SRPC contract *)
Definition srpc_address := 71246.
Definition concrete_blockchain_info := (
  srpc By srpc_address;
  c[0, SolidityFun.empty, (Storage.empty Storage.Vdefault)] is Null
).









