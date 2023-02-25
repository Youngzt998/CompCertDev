Require Import Coqlib Maps.
Require Import AST Integers Values Events Memory Globalenvs Smallstep.
Require Import Op Locations Conventions Mach.

Import ListNotations.
Open Scope list_scope. 
(** * Mach with Bassic Block Structure *)

Definition node := positive.

Definition instruction := Mach.instruction.

Definition bblock := list instruction.

Definition code: Type := list bblock.

Record function: Type := mkfunction {
  fn_sig: signature;
  fn_stacksize: Z;
  fn_code: code;
  fn_link_ofs: ptrofs;
  fn_retaddr_ofs: ptrofs
}.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => fn_sig f
  | External ef => ef_sig ef
  end.

Definition genv := Genv.t fundef unit.
(** * Operational semantics *)

Section SEMANTICS.

Variable return_address_offset: function -> code -> ptrofs -> Prop.

Variable ge: genv.

Definition load_stack (m: mem) (sp: val) (ty: typ) (ofs: ptrofs) :=
  Mem.loadv (chunk_of_type ty) m (Val.offset_ptr sp ofs).

Definition store_stack (m: mem) (sp: val) (ty: typ) (ofs: ptrofs) (v: val) :=
  Mem.storev (chunk_of_type ty) m (Val.offset_ptr sp ofs) v.

Fixpoint find_label (lbl: label) (c: code) {struct c} : option code :=
  match c with
  | nil => None
  | nil :: ll => None
  | (i :: l) :: ll => if is_label lbl i then Some ((i :: l) :: ll) 
                      else find_label lbl ll
  end.

Print is_tail.
Lemma find_label_tail:
  forall lbl c c', find_label lbl c = Some c' -> is_tail c' c.
Proof. Admitted.

Print incl.
Lemma find_label_incl:
  forall lbl c c', find_label lbl c = Some c' -> incl c' c.
Proof. Admitted.

Definition find_function_ptr
        (ge: genv) (ros: mreg + ident) (rs: regset) : option block :=
  match ros with
  | inl r =>
      match rs r with
      | Vptr b ofs => if Ptrofs.eq ofs Ptrofs.zero then Some b else None
      | _ => None
      end
  | inr symb =>
      Genv.find_symbol ge symb
  end.


Inductive stackframe : Type :=
  | Stackframe:
      forall (f: block)         (**r calling function *)
             (sp: val)          (**r stack pointer in calling function *)
             (retaddr: val)     (**r Asm return address in calling function *)
             (bb: bblock)       (**remaining block *)
             (c: code),         (**remaining codes *)
      stackframe.

      Definition parent_sp (s: list stackframe) : val :=
        match s with
        | nil => Vnullptr
        | Stackframe f sp ra c bb :: s' => sp
        end.
      
      Definition parent_ra (s: list stackframe) : val :=
        match s with
        | nil => Vnullptr
        | Stackframe f sp ra c bb :: s' => ra
        end.

Inductive state: Type :=
  | State:
      forall (stack: list stackframe)  (**r call stack *)
             (f: block)                (**r pointer to current function *)
             (sp: val)                 (**r stack pointer *)
             (c: code)                 (**r current program point *)
             (rs: regset)              (**r register state *)
             (m: mem),                 (**r memory state *)
      state
  | Block:
      forall (stack: list stackframe) (**r call stack *)
             (f: block)            (**r function currently executing *)
             (sp: val)                (**r stack pointer *)
             (bb: bblock)             (**r current basic block *)
             (c: code)                (**remaining block *)
             (rs: regset)              (**r register state *)
             (m: mem),                (**r memory state *)
      state
  | Callstate:
      forall (stack: list stackframe)  (**r call stack *)
             (f: block)                (**r pointer to function to call *)
             (rs: regset)              (**r register state *)
             (m: mem),                 (**r memory state *)
      state
  | Returnstate:
      forall (stack: list stackframe)  (**r call stack *)
             (rs: regset)              (**r register state *)
             (m: mem),                 (**r memory state *)
      state.

Inductive step: state -> trace -> state -> Prop :=
  | exec_start_block: forall s fb sp c rs m bb,
      step (State s fb sp (bb::c) rs m)
        E0 (Block s fb sp bb c rs m)
  | exec_end_block:
      forall s fb sp c rs m,
      step (Block s fb sp nil c rs m)
        E0 (State s fb sp c rs m)
  | exec_Mgetstack:
      forall s f sp ofs ty dst bb c rs m v,
      load_stack m sp ty ofs = Some v ->
      step (Block s f sp (Mgetstack ofs ty dst :: bb) c rs m)
        E0 (Block s f sp bb c (rs#dst <- v) m)
  | exec_Msetstack:
      forall s f sp src ofs ty bb c rs m m' rs',
      store_stack m sp ty ofs (rs src) = Some m' ->
      rs' = undef_regs (destroyed_by_setstack ty) rs ->
      step (Block s f sp (Msetstack src ofs ty :: bb) c rs m)
        E0 (Block s f sp bb c rs' m')
  | exec_Mgetparam:
      forall s fb f sp ofs ty dst bb c rs m v rs',
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      load_stack m sp Tptr f.(fn_link_ofs) = Some (parent_sp s) ->
      load_stack m (parent_sp s) ty ofs = Some v ->
      rs' = (rs # temp_for_parent_frame <- Vundef # dst <- v) ->
      step (Block s fb sp (Mgetparam ofs ty dst :: bb) c rs m)
        E0 (Block s fb sp bb c rs' m)
  | exec_Mop:
      forall s f sp op args res bb c rs m v rs',
      eval_operation ge sp op rs##args m = Some v ->
      rs' = ((undef_regs (destroyed_by_op op) rs)#res <- v) ->
      step (Block s f sp (Mop op args res :: bb) c rs m)
        E0 (Block s f sp bb c rs' m)
  | exec_Mload:
      forall s f sp chunk addr args dst bb c rs m a v rs',
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      rs' = ((undef_regs (destroyed_by_load chunk addr) rs)#dst <- v) ->
      step (Block s f sp (Mload chunk addr args dst :: bb) c rs m)
        E0 (Block s f sp bb c rs' m)
  | exec_Mstore:
      forall s f sp chunk addr args src bb c rs m m' a rs',
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a (rs src) = Some m' ->
      rs' = undef_regs (destroyed_by_store chunk addr) rs ->
      step (Block s f sp (Mstore chunk addr args src :: bb) c rs m)
        E0 (Block s f sp bb c rs' m')
  | exec_Mcall:
      forall s fb sp sig ros bb c rs m f f' ra,
      find_function_ptr ge ros rs = Some f' ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      return_address_offset f c ra ->
      step (Block s fb sp (Mcall sig ros :: bb) c rs m)
        E0 (Callstate (Stackframe fb sp (Vptr fb ra) bb c :: s)
                        f' rs m)
  | exec_Mtailcall:
      forall s fb stk soff sig ros bb c rs m f f' m',
      find_function_ptr ge ros rs = Some f' ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      load_stack m (Vptr stk soff) Tptr f.(fn_link_ofs) = Some (parent_sp s) ->
      load_stack m (Vptr stk soff) Tptr f.(fn_retaddr_ofs) = Some (parent_ra s) ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step (Block s fb (Vptr stk soff) (Mtailcall sig ros :: bb) c rs m)
        E0 (Callstate s f' rs m')
  | exec_Mbuiltin:
      forall s f sp bb c rs m ef args res vargs t vres rs' m',
      eval_builtin_args ge rs sp m args vargs ->
      external_call ef ge vargs m t vres m' ->
      rs' = set_res res vres (undef_regs (destroyed_by_builtin ef) rs) ->
      step (Block s f sp (Mbuiltin ef args res :: bb) c rs m)
          t (Block s f sp bb c rs' m')
  | exec_Mgoto:
      forall s fb f sp lbl c rs m c' bb,
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      step (Block s fb sp (Mgoto lbl :: bb) c rs m)
        E0 (State s fb sp c' rs m)
  | exec_Mcond_true:
      forall s fb f sp cond args lbl bb c rs m c' rs',
      eval_condition cond rs##args m = Some true ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      step (Block s fb sp (Mcond cond args lbl :: bb) c rs m)
        E0 (State s fb sp c' rs' m)
  | exec_Mcond_false:
      forall s f sp cond args lbl bb c rs m rs',
      eval_condition cond rs##args m = Some false ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      step (Block s f sp (Mcond cond args lbl :: bb) c rs m)
        E0 (Block s f sp bb c rs' m)
  | exec_Mjumptable:
      forall s fb f sp arg tbl bb c rs m n lbl c' rs',
      rs arg = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some lbl ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      rs' = undef_regs destroyed_by_jumptable rs ->
      step (Block s fb sp (Mjumptable arg tbl :: bb) c rs m)
        E0 (State s fb sp c' rs' m)
  | exec_Mreturn:
      forall s fb stk soff bb c rs m f m',
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      load_stack m (Vptr stk soff) Tptr f.(fn_link_ofs) = Some (parent_sp s) ->
      load_stack m (Vptr stk soff) Tptr f.(fn_retaddr_ofs) = Some (parent_ra s) ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step (Block s fb (Vptr stk soff) (Mreturn :: bb) c rs m)
        E0 (Returnstate s rs m')
  | exec_function_internal:
      forall s fb rs m f m1 m2 m3 stk rs',
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      Mem.alloc m 0 f.(fn_stacksize) = (m1, stk) ->
      let sp := Vptr stk Ptrofs.zero in
      store_stack m1 sp Tptr f.(fn_link_ofs) (parent_sp s) = Some m2 ->
      store_stack m2 sp Tptr f.(fn_retaddr_ofs) (parent_ra s) = Some m3 ->
      rs' = undef_regs destroyed_at_function_entry rs ->
      step (Callstate s fb rs m)
        E0 (State s fb sp f.(fn_code) rs' m3)
  | exec_function_external:
      forall s fb rs m t rs' ef args res m',
      Genv.find_funct_ptr ge fb = Some (External ef) ->
      extcall_arguments rs m (parent_sp s) (ef_sig ef) args ->
      external_call ef ge args m t res m' ->
      rs' = set_pair (loc_result (ef_sig ef)) res (undef_caller_save_regs rs) ->
      step (Callstate s fb rs m)
          t (Returnstate s rs' m')
  | exec_return:
      forall s f sp ra c bb rs m,
      step (Returnstate (Stackframe f sp ra bb c :: s) rs m)
        E0 (Block s f sp bb c rs m)
  .

End SEMANTICS.

Inductive initial_state (p: program): state -> Prop :=
| initial_state_intro: forall fb m0,
    let ge := Genv.globalenv p in
    Genv.init_mem p = Some m0 ->
    Genv.find_symbol ge p.(prog_main) = Some fb ->
    initial_state p (Callstate nil fb (Regmap.init Vundef) m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r retcode,
      loc_result signature_main = One r ->
      rs r = Vint retcode ->
      final_state (Returnstate nil rs m) retcode.

Definition semantics (rao: function -> code -> ptrofs -> Prop) (p: program) :=
  Semantics (step rao) (initial_state p) final_state (Genv.globalenv p).

Require Import Errors.
Open Scope error_monad_scope.
Import ListNotations.
Open Scope list_scope. 


(* Fixpoint sep_block (l: list instruction): list instruction * list instruction:=
  match l with
  | Mlabel lb :: l' => ( Mlabel lb :: fst (sep_block l'), snd (sep_block l') )
  | _ => (nil, nil)
  end. *)

Fixpoint list2bbs (l: list instruction): list (list instruction) :=
  match l with
  (* termination *)
  | Mgoto lb :: l' =>  [Mgoto lb] :: list2bbs l'
  | Mcond con rs lb :: l' => [Mcond con rs lb] :: list2bbs l' 
  | Mjumptable r lbs :: l' => [Mjumptable r lbs] :: list2bbs l'
  | Mreturn :: l' => [Mreturn] :: list2bbs l' 
  (* non-termination *) 
  | inst :: l' => 
      match list2bbs l' with
      | (Mlabel lb :: l'') :: ll => [inst] :: (Mlabel lb :: l'') :: ll
      | l'' :: ll  => (inst :: l'') :: ll
      | nil => [ [inst] ]
      end 
  | nil => nil
  end. 

Fixpoint bbs2list (ll: list (list instruction)): list instruction :=
  match ll with 
  | l :: ll' => l ++ bbs2list ll'
  | nil => nil
  end.

Lemma list2bbs_correct: forall l, bbs2list (list2bbs l) = l.
Proof. 
  induction l. simpl; trivial.
Admitted.

Definition transf_code:= list2bbs.

Definition transf_function (f: Mach.function) : res function :=
  OK ( 
    let code' := transf_code(Mach.fn_code f) in
    (mkfunction (Mach.fn_sig f) (Mach.fn_stacksize f) 
      (code') (Mach.fn_link_ofs f) (Mach.fn_retaddr_ofs f) )
  ). 

Definition transf_fundef (f: Mach.fundef) : res fundef :=
    AST.transf_partial_fundef transf_function f.

Definition transf_program (p: Mach.program) : res program :=
    transform_partial_program transf_fundef p.





Require Import Linking.

(** Correctness Proof **)
Definition match_prog (p: Mach.program) (tp: MachBlock.program) :=
  match_program (fun _ f tf => transf_fundef f = OK tf) eq p tp.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. eapply match_transform_partial_program; eauto.
Qed.


Section PRESERVATION.

Variable return_address_offset: Mach.function -> Mach.code -> ptrofs -> Prop.

Variable treturn_address_offset: MachBlock.function -> MachBlock.code -> ptrofs -> Prop.

(* Hypothesis return_address_offset_exists:
  forall f sg ros c,
  is_tail (Mcall sg ros :: c) (fn_code f) ->
  exists ofs, return_address_offset f c ofs. *)

Let step := Mach.step return_address_offset.

Variable prog: Mach.program.
Variable tprog: MachBlock.program.
Hypothesis TRANSF: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.





Theorem transf_program_correct:
  forward_simulation (Mach.semantics return_address_offset prog) 
                     (MachBlock.semantics treturn_address_offset tprog).
Proof.
  
Admitted.

End PRESERVATION.