Section Ejercicio1.

(* Definition ListN := list nat. *)

(* a *)

Require Import EqNat.

Fixpoint Elim (x:nat) (l: list nat) : list nat
:=   match l with
        nil => nil
      | cons y ys => if beq_nat x y
                    then Elim x ys
                    else cons y (Elim x ys)
     end.

(* b.1 *)

Theorem e11 : forall (x:nat) (l:list nat), Elim x (Elim x l) = Elim x l.
Proof.
  intros.
  induction l.
  
  simpl; auto.

  simpl.
  
  case_eq (beq_nat x a); intros.
  
  auto.

  simpl.
  case_eq (beq_nat x a); intros.
  
  rewrite -> H0 in H; discriminate H.  

  rewrite -> IHl; reflexivity.
Qed.

(* b.2 *)

Theorem e12 : forall (x:nat) (l:list nat), length (Elim x l) <= length l.
Proof.
  intros.
  induction l; simpl; auto.
  
  case_eq (beq_nat x a); intros.
  
  constructor; auto.

  simpl.
  elim IHl; intros; auto.
Qed.

End Ejercicio1.

Section Ejercicio2.
(* a *)

Inductive Prefijo (A:Set) : list A -> list A -> Prop
:=    prefijo0 : forall (l: list A), Prefijo A nil l
    | prefijoS : forall (x:A) (l1 l2: list A), Prefijo A l1 l2 -> Prefijo A (cons x l1) (cons x l2).

(* b.1 *)

Theorem e21 (A: Set) : forall (l1 l2: list A), Prefijo A l1 l2 -> Prefijo A l2 l1 -> l1 = l2.
Proof.
  induction l1, l2; intros.

  reflexivity.

  inversion H.
  inversion H0.

  inversion H.

  inversion H.
  inversion H0.
  
  rewrite (IHl1 l2 H2 H7).
  reflexivity.
Qed.

(* b.2 *)

Theorem e22 (A:Set): forall (l1 l2 l3: list A), Prefijo A l1 l2 -> Prefijo A l2 l3 -> Prefijo A l1 l3.
Proof.
  induction l1; intros.

  constructor.

  inversion H.
  
  rewrite <- H2 in H0.

  inversion H0.
  constructor.
  apply (IHl1 l4 l6); auto.
Qed.


End Ejercicio2.

Section Ejercicio3.

Definition Var := nat.
Definition Valor := nat.

Inductive Instr : Set
:=   Ass : Var -> Valor -> Instr
   | Seq : Instr -> Instr -> Instr
   | IfEq : Var -> Var -> Instr -> Instr
   | Repeat : nat -> Instr -> Instr.

Definition Memoria : Set := Var -> Valor.

Definition lookup (m:Memoria) (v:Var) := m v.

Definition update (m:Memoria) (v:Var) (val:Valor) : Memoria
:=  fun (v':Var) => if beq_nat v v' 
                   then val
                   else lookup m v'.

Inductive Execute : Instr -> Memoria -> Memoria -> Prop
:=   xAss  : forall (m:Memoria) (i:Instr) (v:Var) (val:Valor), Execute i m (update m v val)
   | xSeq  : forall (m1 m2 m3:Memoria) (i1 i2: Instr), Execute i1 m1 m2 -> Execute i2 m2 m3 -> Execute (Seq i1 i2) m1 m3
   | xIfF  : forall (m:Memoria) (i:Instr) (v1 v2:Var), ~(lookup m v1 = lookup m v2) -> Execute (IfEq v1 v2 i) m m
   | xIfT  : forall (m1 m2:Memoria) (i:Instr) (v1 v2:Var), lookup m1 v1 = lookup m1 v2 -> Execute i m1 m2 -> Execute (IfEq v1 v2 i) m1 m2
   | xRepO : forall (m:Memoria) (i:Instr), Execute (Repeat 0 i) m m
   | xRepS : forall (m1 m2 m3:Memoria) (i:Instr) (n:nat), Execute i m1 m2 -> Execute (Repeat n i) m2 m3 -> Execute (Repeat (n+1) i) m1 m3.


Theorem e31 : forall (m:Memoria) (v:Var) (val:Valor), lookup (update m v val) v = val.
Proof.
  intros.
  unfold lookup.
  unfold update.
  rewrite <- beq_nat_refl.
  reflexivity.
Qed.

Theorem e32 : forall (m:Memoria) (v1 v2:Var) (val:Valor), ~(v1 = v2) -> lookup (update m v1 val) v2 = lookup m v2.
Proof.
  intros.
  unfold lookup.
  unfold update.
  
  assert (beq_nat v1 v2 = false).
  apply beq_nat_false_iff; auto.
  
  rewrite -> H0.
  unfold lookup; auto.
Qed.

Theorem e33 : forall (m1 m2:Memoria) (v1 v2 : Var) (i:Instr),
lookup m1 v1 = lookup m1 v2 -> Execute (IfEq v1 v2 i) m1 m2 -> Execute (Repeat 1 i) m1 m2.
Proof.
  intros.
  
  apply (xRepS m1 m2 m2 i 0).

  inversion H0.

  constructor.

  rewrite <- H5 in H6.
  contradiction.

  assumption.

  constructor.
Qed.

Theorem e34 : forall (m1 m2:Memoria) (n:nat) (i:Instr),
Execute (Seq i (Repeat n i)) m1 m2 -> Execute (Repeat (n+1) i) m1 m2.
Proof.
  intros.
  
  inversion H.
  
  constructor.

  apply (xRepS m1 m3 m2 i n); auto.
Qed.

(*

Theorem e35 : forall (n1 n2 : nat) (m1 m2 m3: Memoria) (i : Instr),
Execute (Repeat n1 i) m1 m2 -> Execute (Repeat n2 i) m2 m3 -> Execute (Repeat (n1 + n2) i) m1 m3.
Proof.
  intros n1 n2.
  induction n1; intros.
  
  simpl.
  inversion H.

  
  
  
  

  
  

Qed.
*)
End Ejercicio3.

