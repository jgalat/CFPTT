Section Ejercicio1.


Variable U  : Set.
Variable A B: U -> Prop.
Variable P Q: Prop.
Variable R S: U -> U -> Prop.

Theorem e11 : (forall x:U, A(x)) -> forall y:U, A(y).
Proof.
  intros H.
  assumption.
  
Qed.

Theorem e12 : (forall x y:U, (R x y)) -> forall x y:U, (R y x).
Proof.
  intros.
  apply (H y x).
Qed.


Theorem e13 : (forall x: U, ((A x)->(B x)))
                        -> (forall y:U, (A y))
                          -> (forall z:U, (B z)).
Proof.
  intros H H' z.
  apply H.
  apply H'.
Qed.


End Ejercicio1.



Section Ejercicio2.

Variable U  : Set.
Variable A B: U -> Prop.
Variable P Q: Prop.
Variable R S: U -> U -> Prop.


Theorem e21 : (forall x:U, ((A x)-> ~(forall x:U, ~ (A x)))).
Proof.
  intro x0.
  intro H.
  intro H'.
  apply (H' x0).
  assumption.  
Qed.

Theorem e22 : (forall x y:U, ((R x y)))-> (forall x:U, (R x x)).
Proof.
  intros H z.
  apply (H z z).
  
Qed.

Theorem e23 : (forall x:U, ((P -> (A x))))
                        -> (P -> (forall x: U, (A x))).
Proof.
  intros H H' y.
  apply (H y).
  assumption.
  
Qed.


Theorem e24 : (forall x:U, ((A x) /\ (B x)))
                        -> (forall x:U, (A x))
                          -> (forall x:U, (B x)).
Proof.
  intros H H' y.
  elim (H y).
  intros.
  assumption.
  
Qed.

End Ejercicio2.



Section Ejercicio3.

Variable U   : Set.
Variable A B : U -> Prop.
Variable P Q : Prop.
Variable R S : U -> U -> Prop.

Hypothesis H1: forall x:U, (R x x).
Hypothesis H2: forall x y z:U, (R x y) /\ (R x z) -> (R y z).

Theorem simm: forall x y:U, (R x y) -> (R y x).
Proof.
  intros x0 y0 H.
  apply (H2 x0 y0 x0).
  split.

  assumption.
  apply (H1 x0).
Qed.

Theorem reflex: forall x:U, (R x x).
Proof.
  assumption.
Qed.

Theorem trans: forall x y z:U, (R x y) /\ (R y z) -> (R x z).
Proof.
  intros x0 y0 z0 H.
  apply (H2 y0 x0 z0).

  split.
  elim H.
  intros.
  apply (H2 x0 y0 x0).
  
  split.
  assumption.
  apply (H1 x0).
  
  elim H.
  intros.
  assumption. 
Qed.


End Ejercicio3.



Section Ejercicio4.

Variable U : Set.
Variable A : U->Prop.
Variable R : U->U->Prop.

Theorem e41: (exists x:U, exists y:U, (R x y)) -> exists y:U, exists x:U, (R x y).
Proof.
  intro H.
  elim H; intros x H'.
  elim H'; intros y H''.

  exists y.
  exists x.
  assumption.
  
Qed.

Theorem e42: (forall x:U, A(x)) -> ~ exists x:U, ~ A(x).
Proof.
  intro H.
  intro H'.
  elim H'; intros x H''.
  apply H''.
  apply H.
  
Qed.

Theorem e43: (exists x:U, ~(A x)) -> ~(forall x:U, (A x)).
Proof.
  intros H H'.
  elim H; intros y H''.
  absurd (A y).
   assumption.
   apply H'.
  
Qed.

End Ejercicio4.



Section Ejercicio5.

Variable nat      : Set.
Variable S        : nat -> nat.
Variable a b c    : nat.
Variable odd even : nat -> Prop.
Variable P Q      : nat -> Prop.
Variable f        : nat -> nat.

Theorem e51: forall x:nat, exists y:nat, (P(x)->P(y)).
Proof.
  intros x0.
  exists x0.
  intro.
  assumption.
Qed.

Theorem e52: exists x:nat, (P x)
                            -> (forall y:nat, (P y)->(Q y))
                               -> (exists z:nat, (Q z)).
Proof.
  exists a.
  intro.
  intro.
  exists a.
  apply (H0 a).
  assumption.
Qed.


Theorem e53: even(a) -> (forall x:nat, (even(x)->odd (S(x)))) -> exists y: nat, odd(y).
Proof.
  intros.
  exists (S a).
  apply (H0).
  assumption.
Qed.


Theorem e54: (forall x:nat, P(x) /\ odd(x) ->even(f(x)))
                            -> (forall x:nat, even(x)->odd(S(x)))
                            -> even(a)
                            -> P(S(a))
                            -> exists z:nat, even(f(z)).
Proof.
  intros.
  exists (S a).
  apply (H (S a)).
  split.
  assumption.
  apply (H0 a).
  assumption.
Qed.

End Ejercicio5.



Section Ejercicio6.

Variable nat : Set.
Variable S   : nat -> nat.
Variable le  : nat -> nat -> Prop.
Variable f   : nat -> nat.
Variable P   : nat -> Prop.

Axiom le_n: forall n:nat, (le n n).
Axiom le_S: forall n m:nat, (le n m) -> (le n (S m)).
Axiom monoticity: forall n m:nat, (le n m) -> (le (f n) (f m)).


Lemma le_x_Sx: forall x:nat, (le x (S x)).
Proof.
  intro x0.
  apply (le_S x0 x0).
  apply (le_n x0).
Qed.

Lemma le_x_SSx: forall x:nat, (le x (S (S x))).
Proof.
  intro x0.
  apply (le_S x0 (S x0)).
  apply (le_S x0 x0).
  apply (le_n x0).
Qed.

Theorem T11: forall a:nat, exists b:nat, (le (f a) b).
Proof.
  intro x0.
  exists (f x0).
  apply (monoticity x0 x0).
  apply (le_n x0).
Qed.

Theorem T12: forall a:nat, exists b:nat, (le (f a) b).
Proof.
  intro x0.
  exists (S (f x0)).
  apply (le_S (f x0) (f x0)).
  apply (le_n (f x0)).
Qed.

Theorem T13: forall a:nat, exists b:nat, (le (f a) b).
Proof.
  intro x0.
  exists (S (S (f x0))).
  apply (le_S (f x0) (S (f x0))).
  apply (le_S (f x0) (f x0)).
  apply (le_n (f x0)).
Qed.

Theorem T1a: forall a:nat, exists b:nat, (le (f a) b).
Proof.
  intro x0.
  exists (S (S (S (S (S (f x0)))))).
  repeat apply le_S.
  apply (le_n (f x0)).
Qed.

Theorem T1b: forall a:nat, exists b:nat, (le (f a) b).
Proof.
  intro x0.
  exists (S (S (S (S (S (f x0)))))).
  do 5 (apply le_S).
  apply (le_n (f x0)).
Qed.

End Ejercicio6.



Section Ejercicio7.

Variable U   : Set.
Variable A B : U -> Prop.

Theorem e71: (forall x:U, ((A x) /\ (B x)))
                       -> (forall x:U, (A x)) /\ (forall x:U, (B x)).
Proof.
  intro;split; intro; apply (H x).
Qed.

Theorem e72: (exists x:U, (A x \/ B x))->(exists x:U, A x )\/(exists x:U, B x).
Proof.
  intro; elim H; intros x0 H'; elim H'; intros; [left | right]; exists x0; assumption.
Qed.

End Ejercicio7.

Section Ejercicio8.


Variable U: Set.
Variable R: U -> U -> Prop.
Variable T V: U -> Prop.

Theorem T281: (exists y:U, forall x:U, (R x y)) ->
              (forall x:U, exists y:U, (R x y)).
Proof.
  intros H.
  elim H.
  intros.
  exists x.
  apply H0.
Qed.

Theorem T282: (exists y:U, True) /\ (forall x:U, (T x) \/ (V x)) ->
              (exists z:U, (T z)) \/ (exists w:U, (V w)). 
Proof.
  intros.
  elim H; intros; clear H.
  elim H0; intros.

  elim (H1 x); intros; 
  [left | right];
  exists x; assumption.
Qed.

(* 8)3) Si, ya que nos provee de una instancia de la variable
        x para poder eliminar el cuantificador universal.
*)


End Ejercicio8.


Section Ejercicio9.
Require Import Classical.
Variables U : Set.
Variables A : U -> Prop.

Lemma not_ex_not_forall: (~exists x :U, ~A x) -> (forall x:U, A x).
Proof.
  intros.
  elim (classic (A x)).
  
  intro.
  assumption.
  
  intro.
  elim H.
  exists x.
  assumption.
Qed.

Lemma not_forall_ex_not: (~forall x :U, A x) -> (exists x:U,  ~A x).
Proof.
  intro.

  elim (classic (exists x:U, ~A x)).
  intro. assumption.

  intro.
  elim H.
  apply (not_ex_not_forall H0).
Qed.

End Ejercicio9.



Section Sec_Peano.

Variable nat : Set.
Variable  O  : nat.
Variable  S  : nat -> nat.

Axiom disc   : forall n:nat, ~O=(S n).
Axiom inj    : forall n m:nat, (S n)=(S m) -> n=m.

Variable sum prod : nat->nat->nat.
Axiom sum0   : forall n :nat, (sum n O)=n.
Axiom sumS   : forall n m :nat, (sum n (S m))=(S (sum n m)).
Axiom prod0  : forall n :nat, (prod n O)=O.
Axiom prodS  : forall n m :nat, (prod n (S m))=(sum n (prod n m)).


Lemma L10_1: (sum (S O) (S O)) = (S (S O)).
Proof.
  replace (sum (S O) (S O)) with (S (sum (S O) O)).
  replace (sum (S O) O) with (S O).
  reflexivity.
  symmetry.
  apply (sum0 (S O)).
  symmetry.
  apply (sumS (S O) O). 
Qed.

Lemma L10_2: forall n :nat, ~(O=n /\ (exists m :nat, n = (S m))).
Proof.
  intros.
  intro.
  elim H; intros; clear H.
  elim H1.
  intros.
  replace n with O in H.
  apply (disc x).
  assumption.
Qed.

Lemma prod_neutro: forall n :nat, (prod n (S O)) = n.
Proof.
  intros.
  replace (prod n (S O)) with (sum n (prod n O)).
  replace (prod n O) with O.
  apply (sum0 n).
  symmetry.
  apply (prod0 n).
  symmetry.
  apply (prodS n O).
Qed.

Lemma diff: forall n:nat, ~(S (S n))=(S O).
Proof.
  intros.
  intro.
  symmetry in H.
  apply (inj O (S n)) in H.
  apply (disc n).
  assumption.
Qed.



Variable le : nat->nat->Prop.
Axiom leinv: forall n m:nat, (le n m) -> n=O \/
      (exists p:nat, (exists q:nat, n=(S p)/\ m=(S q) /\ (le p q))).

Lemma notle_s_o: forall n:nat, ~(le (S n) O).
Proof.
  intros.
  intro.
  apply (leinv (S n) O) in H.
  elim H; intros.
  apply (disc n).
  symmetry.
  assumption.
  elim H0; intros.
  elim H1; intros.
  elim H2; intros; clear H2.
  elim H4; intros; clear H4.
  apply (disc x0).
  assumption.
Qed.

End Sec_Peano.

