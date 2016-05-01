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

Parameter ctxt : context.


Definition va_mapped_to_ma (s: state) (va: vadd) (ma: madd) : Prop
:= exists (o: os) (pm: padd -> option madd) (ma': madd) (pg: page) (vm: vadd -> option madd), 
           oss s (active_os s) = Some o 
        /\ hypervisor s (active_os s) = Some pm 
        /\ pm (curr_page o) = Some ma'
        /\ memory s ma' = Some pg
        /\ page_content pg = PT vm
        /\ vm va = Some ma.


Definition pre_read (s: state) (va: vadd): Prop
:= (ctxt_vadd_accessible ctxt va = true)
/\ aos_activity s = running
/\ (exists (ma: madd) (pg: page), va_mapped_to_ma s va ma 
               /\ memory s ma = Some pg
               /\ is_RW (page_content pg)).

Definition post_read (s s':state): Prop
:= s = s'.

Definition pre_write (s: state) (va: vadd) (val: value)
:= (ctxt_vadd_accessible ctxt va = true)
/\ aos_activity s = running
/\ (exists (ma: madd) (pg: page), va_mapped_to_ma s va ma
                       /\ memory s ma = Some pg
                       /\ is_RW (page_content pg)).

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
/\ exists (o: os), oss s (active_os s) = Some o 
                  /\ hcall o = None.

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
:= forall (o: os_ident) (pa: padd), 
      (forall (pm : padd -> option madd), exists (ma: madd) (pg: page),
           (hypervisor s) o = Some pm
          /\ pm pa = Some ma
          /\ memory s ma = Some pg /\
                   (page_owned_by pg = Os o
                /\ forall (pa pa': padd), pm pa = pm pa' -> pa = pa')).

Definition valid_state_prop_6 (s: state) : Prop
:= forall (o: os_ident) (pg: page) (vtm: vadd -> option madd),
          page_content pg = PT vtm 
          -> page_owned_by pg = Os o ->
          forall (va: vadd) (ma: madd), exists (pg': page),
                 vtm va = Some ma
              /\ memory s ma = Some pg' /\
                    ((ctxt_vadd_accessible ctxt va = true -> 
                      page_owned_by pg' = Os o)
                 /\ (ctxt_vadd_accessible ctxt va = false ->
                      page_owned_by pg' = Hyp)).

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
                   /\ exists (pg: page), Some pg = (memory s) ma /\ (page_owned_by pg) = Os (active_os s).
Proof.
  intros.
  inversion H.
  inversion H1.
  elim H7; clear H7; intros.
  elim H8; clear H8; intros ma H8.
  exists ma.
  split.

  elim H8; clear H8; intros.
  elim H8; intros; assumption.

  elim H8; clear H8; intros pg H8.
  exists pg.
  split.

  elim H8; clear H8; intros.
  elim H9; intros; symmetry; assumption.

  elim H8; clear H8; intros.
  elim H9; clear H9; intros.
  inversion H0.
  elim H12; clear H12; intros.

  elim H8; intros OS H14.
  elim H14; intros pm_HypervisorMap H15.
  elim H15; intros ma_ofPageTable H16.
  elim H16; intros pg_ofPageTable H17.
  elim H17; intros vm_ofPageTable H18.
  clear H14 H15 H16 H17.
  elim H18; clear H18; intros.
  elim H15; clear H15; intros.
  elim H16; clear H16; intros.
  elim H17; clear H17; intros.
  elim H18; clear H18; intros.

  elim (H12 (active_os s) (curr_page OS) pm_HypervisorMap); intros ma' H20.
  elim H20; clear H20; intros pg' H20.
  elim H20; clear H20; intros.
  elim H21; clear H21; intros.
  elim H22; clear H22; intros.
  elim H23; clear H23; intros.
  rewrite -> H16 in H21.
  injection H21; intros.
  rewrite <- H25 in H22.
  rewrite -> H17 in H22.
  injection H22; intros.
  rewrite <- H26 in H23.
 
  elim (H13 (active_os s) pg_ofPageTable vm_ofPageTable H18 H23 va ma); intros.
  elim H27; clear H27; intros.
  elim H28; clear H28; intros.
  elim H29; clear H29; intros.
  rewrite -> H9 in H28.
  injection H28; intros.
  rewrite <- H31 in H29.
  apply H29; assumption.
Qed. 

End Actions.