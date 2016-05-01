(*******************************************************************
 * Este archivo especifica el estado.
 * 
 ******************************************************************)

Require Export Maps.

Section State.

(** Identificadores de OSs e Hypercalls *)

Parameter os_ident : Set.
Parameter os_ident_eq : forall oi1 oi2 : os_ident, {oi1 = oi2} + {oi1 <> oi2}.

Parameter Hyperv_call: Set.


(* Memoria y direcciones *)

(* Direcciones Virtuales. *)
Parameter vadd: Set.
Parameter vadd_eq : forall va1 va2 : vadd, {va1 = va2} + {va1 <> va2}.

(** Direcciones de M\u00e1quina. *)
Parameter madd :  Set.
Parameter madd_eq : forall ma1 ma2 : madd, {ma1 = ma2} + {ma1 <> ma2}.

(** Direcciones F\u00edsicas : 
Los sitemas operativos utilizan este tipo de direcciones para ver regiones de memoria
contigua. Estos no ven direcciones de m\u00e1quina. *)
Parameter padd: Set.
Parameter padd_eq : forall pa1 pa2 : padd, {pa1 = pa2} + {pa1 <> pa2}.

(** Memory values. *)
Parameter value: Set.
Parameter value_eq:forall val1 val2 : value, {val1 = val2} + {val1 <> val2}.


(* Environment *)
Record context : Set :=
  Context
    {(** una direcci\u00f3n virtual es accesible, i.e. no est\u00e1 reserveda 
         por el Hypervisor *)
       ctxt_vadd_accessible: vadd -> bool; 
     (** guest Oss (Confiable/No Confiable) **)
       ctxt_oss : os_ident -> bool
    }.


Inductive exec_mode : Set := usr | svc.

Inductive os_activity : Set := running | waiting.

Record os : Set :=
  Os_
    {  curr_page : padd;
       hcall : option Hyperv_call
    }.

Definition oss_map : Set := os_ident -> option os.

Definition hypervisor_map : Set := os_ident -> option (padd -> option madd).

Inductive content : Set
:=     PT (va_to_ma : vadd -> option madd)
     | RW (v : value)
     | Other.

Definition is_RW (c:content) : Prop 
:=  match c with
       RW _ => True
     | _ => False
    end.

Inductive page_owner : Set
:=   Hyp
   | Os (osi : os_ident)
   | No_Owner.

Record page : Set :=
  Page
    {  page_content : content;
       page_owned_by : page_owner
    }.

Definition system_memory : Set := madd -> option page.

(* Estado de la m\u00e1quina *)
Record state : Set :=
  State
    { active_os : os_ident;
      aos_exec_mode : exec_mode;
      aos_activity : os_activity;
      oss : oss_map;
      hypervisor : hypervisor_map;
      memory : system_memory
    }.


Definition update (m:system_memory) (ma:madd) (p: page) : system_memory
:= fun (ma': madd) => if (madd_eq ma ma')
                      then Some p
                      else m ma.

End State.