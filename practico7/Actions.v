(*******************************************************************
 * Este archivo especifica las acciones
 * (Como transformadores de estado)
 ******************************************************************)

Require Import State.

Section Actions.

Inductive Action : Set
:=   read : vadd -> Action
   | write : vadd -> value -> Action
   | chmod : Action.


Definition pre_read (s: state) (va: vadd): Prop
:= (ctxt_vadd_accessible ctxt va = true)
/\ aos_activity s = running
/\ (exists (ma: madd), va_mapped_to_ma s va ma 
    /\ is_RW (page_content ((memory s) ma))).

Definition post_read (s s':state): Prop
:= s = s'.

Definition pre_write (s: state) (va: vadd) (val: value)
:= (ctxt_vadd_accessible ctxt va = true)
/\ aos_activity s = running
/\ (exists (ma: madd), va_mapped_to_ma s va ma
                       /\ is_RW (page_content ((memory s) ma))).

Definition post_write (s s': state) (va: vadd) (val: value) : Prop
:= (exists (ma:madd), va_mapped_to_ma s va ma
/\ (memory s') = (update (memory s) ma (Page (RW val) (Os (active_os s))))
/\ active_os s = active_os s'
/\ aos_exec_mode s = aos_exec_mode s'
/\ aos_activity s = aos_activity s'
/\ oss s = oss s'
/\ hypervisor s = hypervisor s'
/\ forall (i:madd), (ma <> i) /\ ((memory s) i = (memory s') i)).

Definition pre_chmod (s: state): Prop
:= aos_activity s = waiting 
/\ hcall ((oss s) (active_os s)) = None.

Definition post_chmod (s s': state): Prop
:= ((ctxt_oss ctxt (active_os s) = true)
/\ active_os s' = active_os s
/\ aos_exec_mode s' = svc /\ aos_exec_mode s = usr
/\ aos_activity s' = running /\ aos_activity s = waiting
/\ oss s' = oss s
/\ hypervisor s' = hypervisor s
/\ memory s' = memory s)
\/ (ctxt_oss ctxt (active_os s) = false
   /\ active_os s' = active_os s
   /\ aos_exec_mode s' = usr /\ aos_exec_mode s = svc
   /\ aos_activity s' = running /\ aos_activity s = waiting
   /\ oss s' = oss s
   /\ hypervisor s' = hypervisor s
   /\ memory s' = memory s). 


Definition Pre (s:state) (a: Action) : Prop
:=  match a with
       read va      => pre_read s va
     | write va val => pre_write s va val
     | chmod        => pre_chmod s  
    end.

Definition Post (s: state) (a: Action) (s': state): Prop
:=  match a with
       read _       => post_read s s'
     | write va val => post_write s s' va val
     | chmod        => post_chmod s s'
    end.


Definition valid_state_prop_3 (s: state) : Prop
:= (ctxt_oss ctxt (active_os s) = true
/\ (aos_activity s) = running)
   \/ (aos_activity s = waiting) -> aos_exec_mode s = svc.

Definition valid_state_prop_5 (s:state) : Prop
:= (forall (o: os_ident) (pa: padd), page_owned_by ((memory s) ((hypervisor s) o pa)) = Os o)
/\ forall (o: os_ident) (pa pa': padd), (hypervisor s) o pa = (hypervisor s) o pa' -> pa = pa'.

Definition valid_state_prop_6 (s: state) : Prop
:= forall (o: os_ident) (pag: page) (va_to_ma: vadd -> madd), page_owned_by pag = Os o 
/\ page_content pag = PT va_to_ma ->
forall (va: vadd), (ctxt_vadd_accessible ctxt va = true -> 
                                       page_owned_by ((memory s) (va_to_ma va)) = Os o)
                                       /\ (ctxt_vadd_accessible ctxt va = false ->
                                           page_owned_by ((memory s) (va_to_ma va)) = Hyp).

Definition valid_state (s: state) : Prop
:= valid_state_prop_3 s /\ valid_state_prop_5 s /\ valid_state_prop_6 s.

Inductive one_step_execution : state -> Action -> state -> Prop
:= one_step_execution0 : forall (s s': state) (a: Action),
                         valid_state s -> Pre s a -> Post s a s' -> one_step_execution s a s'.


Theorem e76 (s s': state) (a: Action) : one_step_execution s a s' -> valid_state_prop_3 s'.
Proof.
  intros.
  inversion H.
  inversion H0.
  unfold valid_state_prop_3; intros.
  destruct a.
    (* read *)
    inversion H2.
    rewrite -> H9 in H6.
    apply H6; assumption.

    (* write *)
    elim H6; intros;

    inversion H2;
    elim H9; intros;
    elim H11; intros;
    elim H13; intros;
    elim H15; intros.

    symmetry; assumption.

    elim H17; intros.
    rewrite -> H14, H18; assumption.

    (* chmod *)
    inversion H2.
    
    elim H9; intros;
    elim H11; intros;
    elim H13; intros; assumption.

    elim H8; intros.

    elim H9; intros;
    elim H12; intros;
    elim H10; intros.
    rewrite <- H13 in H11.
    rewrite -> H15 in H11; discriminate.

    elim H9; intros;
    elim H12; intros;
    elim H14; intros;
    elim H16; intros;
    elim H18; intros.
    rewrite -> H19 in H10; discriminate.
Qed.

Lemma Read_isolation (s s': state) (va: vadd) :
one_step_execution s (read va) s' -> 
exists (ma: madd), va_mapped_to_ma s va ma
                   /\ exists (pg: page), pg = (memory s) ma /\ (page_owned_by pg) = Os (active_os s).
Proof.


Qed. 

End Actions.