(* Require Import Coqlib Maps.
Require Import AST Integers Values Events Memory Globalenvs Smallstep.
Require Import Op Locations . *)

(* Require Import Op Locations Conventions. *)
Require Import Coqlib Maps.
Require Import Machregs LTL.


Definition boolTODO:= false.

Locate mreg.
Check mreg_eq.
Print mreg_eq.

Definition eqb_mreg (reg1 reg2: mreg) :=
    match reg1, reg2 with
    | AX, AX => true
    | _, _ => boolTODO
    end.

Fixpoint mregs_independ_mreg (args: list mreg) (reg: mreg):=
    match args with
    | nil => true
    | reg1 :: args' => if eqb_mreg reg reg1 then false 
                    else mregs_independ_mreg args' reg 
    end.

Definition independ_of (i1 i2: instruction) :=
    match i1 with 
    | Lop op1 args1 res1  => 
        match i2 with
        | Lop op2 args2 res2 => mregs_independ_mreg  args1 res2
        | _ => boolTODO
        end
    | _ => boolTODO
    end.

Require Import AST.
Require Import Errors.
Open Scope error_monad_scope.



(* Definition transf_program (p: LTL.program) : res LTL.program :=
    transform_partial_program transf_fundef p. *)







