Section Ejercicio1.

Inductive list (A:Set): Set :=
  | nil: list A
  | consl: A -> list A -> list A.

Inductive LE : nat -> nat -> Prop :=
  | Le_O : forall n : nat, LE 0 n
  | Le_S : forall n m : nat, LE n m -> LE (S n) (S m).

Inductive Mem (A : Set) (a : A) : list A -> Prop :=
  | here : forall x : list A, Mem A a (consl A a x)
  | there : forall x : list A, Mem A a x ->
              forall b : A, Mem A a (consl A b x).

Theorem not_sn_le_o: forall n:nat, ~ LE (S n) O.
Proof.
  unfold not; intros.
  inversion H.
Qed.

Theorem nil_empty (A:Set) : forall a:A, ~ Mem A a (nil A).
Proof.
  unfold not; intros.
  inversion H.
Qed.

Theorem e13: ~ LE 4 3.
Proof.
  unfold not; intros.
  inversion_clear H.
  inversion_clear H0.
  inversion_clear H.
  inversion_clear H0.
Qed.

Theorem e14 : forall n:nat, ~ LE (S n) n.
Proof.
  unfold not; intros.
  induction n.

  inversion H.

  apply IHn.
  inversion_clear H.
  assumption.
Qed.




Theorem LE_trans : forall (m n o:nat), LE m n -> LE n o -> LE m o.
Proof.
  induction m; intros; simpl.
  constructor.
  inversion H.

  rewrite <- H3 in H0.

  inversion H0.
  constructor.

  apply (IHm m0 m1); auto.
Qed.

Theorem e15 (A:Set) : forall (x y: A) (xs : list A), Mem A x xs -> Mem A x (consl A y xs).
Proof.
  intros.
  inversion H.
  apply there.
  apply here.

  apply there.
  rewrite -> H1.
  assumption.
Qed.

End Ejercicio1.

Section Ejercicio2.

Inductive bintree (A:Set):Set
:=   empty: bintree A
   | branch: bintree A -> A -> bintree A -> bintree A.

Inductive isomorfo (A:Set) : bintree A -> bintree A -> Prop
:=    isomorfo0 : isomorfo A (empty A) (empty A)
    | isomorfoS : forall (x y: A) (a b c d: bintree A), isomorfo A a c ->
                  isomorfo A b d -> isomorfo A (branch A a x b) (branch A c y d).


Fixpoint inverse (A:Set) (t:bintree A): bintree A
:=   match t with
        empty => empty A
      | branch t1 x t2 => branch A (inverse A t2) x (inverse A t1)
     end.

Theorem e21 (A:Set): forall (l r: bintree A) (x:A), ~ (isomorfo A (empty A) (branch A l x r)).
Proof.
  unfold not; intros.
  inversion H.
Qed.

Theorem e22 (A:Set) : forall (a b l r: bintree A) (x y: A), isomorfo A (branch A a x b) (branch A l y r) -> (isomorfo A a l) /\ (isomorfo A b r).
Proof.
  intros.
  split; inversion H; auto.
Qed.

Theorem e23 (A:Set) : forall (a b c: bintree A), isomorfo A a b -> isomorfo A b c -> isomorfo A a c.
Proof.
  induction a; intros.
  inversion H.
  rewrite -> H2; auto.

  inversion H.
  rewrite <- H3 in H0.
  inversion H0.
  constructor.

  apply (IHa1 c0 c1); auto.
  apply (IHa2 d d0); auto.   
Qed.

Theorem e24 (A:Set) :  forall (a b: bintree A), isomorfo A a b -> isomorfo A (inverse A a) (inverse A b).
Proof.
  induction a; intros; simpl.

  inversion H.
  simpl; constructor.

  inversion H; simpl.
  constructor.

  apply (IHa2 d); auto.
  apply (IHa1 c); auto.
Qed. 

End Ejercicio2.

Section Ejercicio3.

Variable A : Set.
Parameter equal : A -> A -> bool.

Axiom equal1 : forall x y : A, equal x y = true -> x = y.

Axiom equal2 : forall x : A, equal x x <> false.

Inductive List : Set :=
  | nullL : List
  | consL : A -> List -> List.

Inductive MemL (a : A) : List -> Prop :=
  | hereL : forall x : List, MemL a (consL a x)
  | thereL : forall x : List, MemL a x -> forall b : A, MemL a (consL b x).

Inductive isSet : List -> Prop := 
    emptyS : isSet nullL
  | setS : forall (x:A) (xs:List), isSet xs -> ~MemL x xs -> isSet (consL x xs).

Fixpoint deleteAll (x:A) (xs : List) : List
:=   match xs with
        nullL => nullL
      | consL y ys => if (equal x y) then deleteAll x ys
                                     else consL y (deleteAll x ys)
     end.

Lemma DeleteAllNotMember : forall (l : List) (x : A),
~ MemL x (deleteAll x l).
Proof.
  intros.
  induction l; unfold not; intros.
  inversion H.

  simpl in H.

  case_eq (equal x a); intros.

  rewrite -> H0 in H.
  contradiction.

  rewrite -> H0 in H.

  inversion H.
  rewrite H2 in H0.
  elim (equal2 a); auto.

  apply IHl; auto.
Qed.

Fixpoint delete (x:A) (xs : List) : List
:=   match xs with
        nullL => nullL
      | consL y ys => if (equal x y) then ys
                                     else consL y (delete x ys)
     end.

Lemma DeleteNotMember : forall (l : List) (x : A), isSet l ->
~ MemL x (delete x l).
Proof.
  unfold not; intros.
  induction H.
  inversion H0.
  apply IHisSet.
  simpl in H0.
  case_eq (equal x x0); intros.

  rewrite -> H2 in H0.
  assert (x = x0).
  apply equal1; auto.

  rewrite -> H3 in H0.
  contradiction.
  
  rewrite -> H2 in H0.

  inversion H0.
  rewrite -> H4 in H2.
  elim (equal2 x0); auto.

  auto.
Qed.

End Ejercicio3.

Section Ejercicio4.

Variable A : Set.
Inductive AB: Set :=
    null : AB
  | cons: A -> AB-> AB -> AB.

Inductive Pertenece : A -> AB -> Prop :=
    Pertenece0 : forall (x: A)(a b: AB), Pertenece x (cons x a b)
  | Pertenecel : forall (x: A)(a b: AB), Pertenece x a -> Pertenece x (cons x a b)
  | Pertenecer : forall (x: A)(a b: AB), Pertenece x b -> Pertenece x (cons x a b).

Parameter eqGen: A->A->bool.

Fixpoint Borrar (a:A) (ab:AB) : AB
:=   match ab with
        null => null
      | cons x l r => if eqGen x a 
                      then null
                      else cons x (Borrar a l ) (Borrar a r )
     end.

Axiom eqGen1 : forall (x:A), ~(eqGen x x)=false.

Lemma BorrarNoPertenece: forall (x:AB) (a:A), ~(Pertenece a (Borrar a x)).
Proof.
  
  (*unfold not; intros.*)
  induction x.
  unfold not; intros.
 
  inversion H.
  
  unfold not; intros.

  simpl in H.

  case_eq (eqGen a a0); intros.
  

  rewrite -> H0 in H.
  inversion H.

  rewrite -> H0 in H.

  inversion H.

  rewrite <- H3 in H0.

  elim (eqGen1 a0); auto.

  rewrite <- H1 in H0.

  elim (eqGen1 a0); auto.

  rewrite <- H1 in H0.
  elim (eqGen1 a0); auto.
  
Qed.

Inductive SinRepetidos : AB -> Prop
:=   NullSR : SinRepetidos null
   | ConsSR : forall (x:A) (l r: AB), ~(Pertenece x l) -> ~(Pertenece x r) -> SinRepetidos (cons x l r).

End Ejercicio4.

Section Ejercicio5.

Definition Var := nat.

Inductive BoolExpr
:=   VAR : Var -> BoolExpr
   | BOOL : bool -> BoolExpr
   | OR : BoolExpr -> BoolExpr -> BoolExpr
   | R  : BoolExpr -> BoolExpr.

Definition Valor := bool.

Definition Memoria : Set := Var -> Valor.

Definition lookup (m:Memoria) (v:Var) : Valor := m v.

Inductive BEval : BoolExpr -> Memoria-> Valor -> Prop
:=    Eevar : forall (v:Var) (m:Memoria), BEval (VAR v) m (lookup m v)
    | Eeboolt : forall (m:Memoria), BEval (BOOL true) m true
    | Eeboolf : forall (m:Memoria), BEval (BOOL false) m false
    | Eeorl : forall (e1 e2:BoolExpr)(m:Memoria), BEval e1 m true -> BEval (OR e1 e2) m true
    | Eeorr : forall (e1 e2:BoolExpr)(m:Memoria), BEval e2 m true -> BEval (OR e1 e2) m true
    | Eeorrl : forall (e1 e2:BoolExpr)(m:Memoria), BEval e1 m false -> BEval e2 m false -> BEval (OR e1 e2) m false
    | Eenott : forall (e:BoolExpr)(m:Memoria), BEval e m true -> BEval (R e) m false
    | Eenotf : forall (e:BoolExpr)(m:Memoria), BEval e m false -> BEval (R e) m true.

Theorem e51: forall (m:Memoria), ~ BEval (BOOL true) m false.
Proof.
  unfold not; intros.
  inversion H.
Qed.

Theorem e52: forall (m:Memoria) (e1 e2:BoolExpr) (w: bool), BEval e1 m false -> BEval e2 m w -> BEval (OR e1 e2) m w.
Proof.
  intros.
  destruct w.
  apply (Eeorr e1 e2 m).
  assumption.

  constructor; assumption.
Qed.



Theorem e53: forall (m:Memoria) (e:BoolExpr) (w1 w2:bool), BEval e m w1 -> BEval e m w2 -> w1 = w2.
Proof.
  intros.
 
  induction e.
 
  inversion H.
 
  inversion H0; reflexivity.
 
  inversion H.
  rewrite <- H2 in H0.
  inversion H0; auto.
 
  rewrite <- H2 in H0.
  inversion H0; auto.
 
  inversion H.
  inversion H0; auto.
 
  rewrite -> H4, H10.
  apply IHe1.
 
  rewrite -> H4 in H5; auto.
 
  rewrite -> H10 in H8; auto.
 
  rewrite -> H4.
 
  apply IHe2.
 
  rewrite -> H4 in H5; auto.
 
  inversion H0; auto.

  inversion H0.

  rewrite -> H5, H10.
  apply IHe1.

  rewrite -> H5 in H3; auto.
  rewrite -> H10 in H11; auto.
  
  rewrite -> H5, H10.
  apply IHe2.

  rewrite -> H5 in H6; auto.
  rewrite -> H10 in H11; auto.
  
  reflexivity.

  inversion H; auto.
  inversion H0; auto.

  rewrite -> H4, H8.
  
  apply IHe.
  rewrite -> H4 in H6; auto.
  rewrite -> H8 in H2; auto.

  inversion H0.

  rewrite -> H4, H8.
  apply IHe.
  
  rewrite -> H4 in H6; auto.
  rewrite -> H8 in H2; auto.

  reflexivity.
Qed.



Theorem e54: forall (m:Memoria) (e1 e2:BoolExpr), BEval e1 m true -> ~BEval (R (OR e1 e2)) m true.
Proof.
  unfold not; intros.

  inversion H0.
  inversion H2.

  assert (true = false); intros.
  apply (e53 m e1 true false); auto.
  discriminate H9.  
Qed.


Fixpoint beval (m:Memoria) (b:BoolExpr): Valor
:=   match b with
        VAR v => lookup m v
      | BOOL b1 => b1
      | OR e1 e2 => if beval m e1
                    then true
                    else beval m e2
      | R e1 => if beval m e1
                then false
                else true
      end.

Theorem e55: forall (m:Memoria) (e:BoolExpr) (b:bool), BEval e m (beval m e).
Proof.
  intros.
  induction e; simpl; auto.
  constructor.
  
  destruct b0; constructor.

  destruct (beval m e1).
  constructor; assumption.
  
  destruct (beval m e2). 
  apply (Eeorr e1 e2 m); assumption.

  apply (Eeorrl e1 e2 m); assumption.

  destruct (beval m e); constructor; auto.
Qed.

End Ejercicio5.

Section Ejercicio6.

Inductive Instr
:=    SKIP : Instr
    | ASSIGN : Var -> BoolExpr -> Instr
    | IFF : BoolExpr -> Instr -> Instr -> Instr
    | WHILE : BoolExpr -> Instr -> Instr
    | BEGIN : LInstr -> Instr
    with LInstr :=   EMPTY : LInstr
                   | SEQ : Instr -> LInstr -> LInstr.

Infix ";" := SEQ (right associativity, at level 80).

Definition PP: Instr
:=  BEGIN 
    ( (ASSIGN 1 (BOOL true)); 
      (ASSIGN 2 (R (VAR 1)));
      EMPTY).


Definition swap : Instr
:=  BEGIN
    ( (ASSIGN 1 (VAR 2));
      (ASSIGN 2 (VAR 3));
      (ASSIGN 3 (VAR 1));
      EMPTY).

Require Import Coq.Arith.EqNat.


Definition update (m:Memoria) (n:Var) (b:Valor) : Memoria
:= fun (n':Var) => if beq_nat n n' 
                   then b
                   else lookup m n'.

End Ejercicio6.

Section Ejercicio7.

Inductive Execute : Instr -> Memoria -> Memoria ->  Prop
:=    xAss : forall (m:Memoria) (e:BoolExpr) (w:bool) (v:Var), BEval e m w -> Execute (ASSIGN v e) m (update m v w)
    | xSkip : forall (m:Memoria), Execute SKIP m m
    | xIFthen : forall (m m1:Memoria) (e:BoolExpr) (p1 p2: Instr), BEval e m true -> Execute p1 m m1 -> Execute (IFF e p1 p2) m m1
    | xIFelse : forall (m m1:Memoria) (e:BoolExpr) (p1 p2: Instr), BEval e m false -> Execute p2 m m1 -> Execute (IFF e p1 p2) m m1
    | xWhileTrue : forall (m m1 m2:Memoria) (e:BoolExpr) (p:Instr), BEval e m true -> Execute p m m1 -> Execute (WHILE e p) m1 m2 -> Execute (WHILE e p) m m2
    | xWhileFalse : forall (m:Memoria) (e:BoolExpr) (p:Instr), BEval e m false -> Execute (WHILE e p) m m
    | xBeginEnd : forall (m m1:Memoria) (p:LInstr), ExecuteL p m m1 -> Execute (BEGIN p) m m1
    with ExecuteL : LInstr -> Memoria -> Memoria -> Prop 
         :=   xEmptyBlock : forall (m:Memoria), ExecuteL EMPTY m m
            | xNext : forall (m m1 m2:Memoria) (i:Instr) (li:LInstr), Execute i m m1 -> ExecuteL li m1 m2 -> ExecuteL (SEQ i li) m m2.


Theorem e71 : forall (m m' : Memoria) (e1 e2 : Instr), Execute (IFF (R (BOOL true)) e1 e2) m m' -> Execute (IFF (BOOL true) e2 e1) m m'.
Proof.
  intros.
  inversion H.
  inversion H5.
  inversion H8.
  inversion H5.
  inversion H8.
  constructor; auto.
Qed.

Theorem e72 : forall (m m' : Memoria) (p1 p2 : Instr) (c:bool) , Execute (IFF (R (BOOL c)) p1 p2) m m' -> Execute (IFF (BOOL c) p2 p1) m m'.
Proof.
  intros.
  destruct c.

  apply e71; auto.

  apply xIFelse.
 
  constructor.

  inversion H; auto.
  inversion H5.
  inversion H8.
Qed.

Theorem e73 : forall (m m' : Memoria) (p:Instr), Execute (WHILE (BOOL false) p) m m' -> m=m'.
Proof.
  intros.
  inversion H.
  inversion H2.

  reflexivity.
Qed.

Infix ";" := SEQ (right associativity, at level 80).

Theorem e74 : forall (m m':Memoria) (p:Instr) (c:BoolExpr), Execute (BEGIN ((IFF c p SKIP) ; (WHILE c p); EMPTY)) m m' -> Execute (WHILE c p) m m'.
Proof.
  intros.

  inversion_clear H.
  inversion H0.
  inversion H2.

  inversion H5.
  inversion H18.
  rewrite -> H21 in H15.
  apply (xWhileTrue m m1 m' c p); auto.

  inversion H5.
  inversion H12. 
  inversion H18.
  rewrite -> H23 in H15; auto.
Qed.

Theorem e75 : forall (m m':Memoria), Execute PP m m' -> BEval (VAR 2) m' false /\ BEval (VAR 1) m' true.
Proof.
  intros.

  inversion H.
  inversion H1.
  
  inversion H6. (* 1 := true *)
  inversion H14.
  rewrite <- H17 in H13.
  rewrite <- H13 in H9.
  inversion H9.
  inversion H19. (* 2 := ~1 *)
  inversion H27.


  rewrite <- H31 in H26.
  rewrite <- H26 in H22.
  inversion H22. (* nil *)

  split; inversion H29; constructor.

  split; inversion H29.
Qed.

End Ejercicio7.
