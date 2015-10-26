Section Ej1.
Require Import Classical.

Variables P R : Prop.

Lemma lema1_1 : (P -> R) \/ (R -> P).
Proof.
  elim (classic P); intros.
  
  right; intros; assumption.
  left; intros; contradiction.
Qed.

End Ej1.

Section Ej2.

Variables Cuad Nad Herv Vuel BebLec: Prop.

Hypothesis Regla1: Cuad -> ~Vuel.
Hypothesis Regla2: Herv -> Vuel.
Hypothesis Regla3: ~BebLec -> Herv.
Hypothesis Regla4: Vuel \/ ~BebLec.
Hypothesis Regla5: Vuel -> Herv /\ Cuad.
Hypothesis Regla6: Nad <-> Herv.

Theorem Ninguno: False.
Proof.
  elim Regla4; intros.
  
  apply Regla1;
  elim Regla5; intros; assumption.
  
  unfold iff in Regla6.
  elim Regla6; intros.
  apply Regla1; elim Regla5; intros;
 [assumption | idtac | idtac | idtac];
  apply Regla2;
  apply Regla3; assumption.
Qed.

End Ej2.

Section Ej3.

Variable C : Set.

Variables T U: C -> C -> Prop.

Lemma Ej3:
(forall (x y:C), (U x y -> ~ (T x y))) /\ (exists z:C, T z z) -> exists w:C, ~U w w.
Proof.
  intros.
  elim H; intros.
  elim H1; intros.
  exists x.
  unfold not; intro.
  apply (H0 x x); assumption.
Qed.


End Ej3.

Section Ej4.
Variable Bool: Set.
Variable TRUE : Bool.
Variable FALSE : Bool.
Variable Not : Bool -> Bool.
Variable Or : Bool -> Bool -> Bool.
Variable And : Bool -> Bool -> Bool.
Axiom BoolVal : forall b : Bool, b = TRUE \/ b = FALSE.
Axiom NotTrue : Not TRUE = FALSE.
Axiom NotFalse : Not FALSE = TRUE.
Axiom AndTrue : forall b : Bool, And TRUE b = b.
Axiom AndFalse : forall b : Bool, And FALSE b = FALSE.
Axiom OrTrue : forall b : Bool, Or TRUE b = TRUE.
Axiom OrFalse : forall b : Bool, Or FALSE b = b.

Lemma lema4_1 : forall b : Bool, Not (Not b) = b.
Proof.
  intro b.
  elim (BoolVal b); intros; rewrite -> H.

  rewrite -> NotTrue.
  rewrite -> NotFalse; reflexivity.

  rewrite -> NotFalse.
  rewrite -> NotTrue; reflexivity.
Qed.

Lemma lema4_2 : forall b1 b2 : Bool, Not (Or b1 b2) = And (Not b1) (Not b2).
Proof.
  intros b1 b2.
  elim (BoolVal b1); intros; rewrite -> H;
  elim (BoolVal b2); intros; rewrite -> H0.

  rewrite -> OrTrue;
  rewrite -> NotTrue;
  rewrite -> AndFalse; reflexivity.

  rewrite -> OrTrue;
  rewrite -> NotTrue;
  rewrite -> AndFalse; reflexivity.

  rewrite -> OrFalse;
  rewrite -> NotTrue;
  rewrite -> NotFalse;
  rewrite -> AndTrue; reflexivity.

  rewrite -> OrFalse;
  rewrite -> NotFalse;
  rewrite -> AndTrue; reflexivity.
Qed.

Lemma lema4_3 : forall b1 : Bool, exists b2 : Bool, Or b1 b2 = Or (Not b1) (Not b2).
Proof.
  intros.
  elim (BoolVal b1); intros; rewrite -> H; 
  [exists FALSE | exists TRUE].
  
  rewrite -> NotTrue;
  rewrite -> OrTrue;
  rewrite -> OrFalse;
  rewrite -> NotFalse; reflexivity.

  rewrite -> NotTrue;
  rewrite -> NotFalse;
  rewrite -> OrFalse;
  rewrite -> OrTrue; reflexivity.
Qed.


End Ej4.

Section Ej5.

Parameter Array : Set -> nat -> Set.
Parameter emptyA : forall X : Set, Array X 0.
Parameter addA : forall (X : Set) (n : nat), X -> Array X n -> Array X (S n).

Parameter Matrix : Set -> nat -> Set.

(* 1 *)
Parameter emptyM : forall A:Set, Matrix A 0.
(* 2 *)
Parameter addM : forall (A:Set) (n:nat), Matrix A n ->Array A (n + 1) -> Matrix A (n + 1). 

(* 3 *)

Definition Column1 := addA nat 0 1 (emptyA nat).
Definition Column2 := addA nat 1 2 (addA nat 0 2 (emptyA nat)).
Definition Column3 := addA nat 2 3 (addA nat 1 3 (addA nat 0 3 (emptyA nat))).

Definition Matr3:= addM nat 2 (addM nat 1 (addM nat 0 (emptyM nat) Column1) Column2) Column3.

End Ej5.
