(*
SolidityVar is the module that immitates variable data structure and provides
all the means to operate with it.
*)


Module SolidityVar.

Definition address := nat.

Definition eqb_address (x y : address) : bool :=
  if x =? y then true else false.

Inductive var_type :=
  | VTbool
  | VTint
  | VTaddress.

Definition get_type (v : var_type) : Type :=
match v with
  | VTbool => bool
  | VTint => nat
  | VTaddress => address
end.

Record var := build_var
{
  v_type : var_type;
  v_value : get_type v_type;
}.

End SolidityVar.