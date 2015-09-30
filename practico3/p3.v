Section Ejercicio1.
Variable A B C: Set.

Definition hab1: (A->A->A)->A->A := 
fun (f:A->A->A) (x:A) => (f x) x.

Definition hab2: (A->B)->(B->C)->A->B->C :=
fun (f:A->B) (g:B->C) (a:A) (b:B) => g (f a).

Definition hab3: (A->B)->(A->B->C)->A->C :=
fun (f:A->B) (g:A->B->C) (a:A) => g a (f a).

Definition hab4: (A->B)->((A->B)->C)->C :=
fun (f:A->B) (g:(A->B)->C) => g f.

Theorem e11: (A->A->A)->A->A.
Proof.
  intros.
  exact (H H0 H0).
Qed.

Theorem e12: (A->B)->(B->C)->A->B->C.
Proof.
  intros.
  exact (H0 (H H1)).
Qed.

Theorem e13:(A->B)->(A->B->C)->A->C.
Proof.
  intros.
  exact (H0 H1 (H H1)).
Qed.

Theorem e14:(A->B)->((A->B)->C)->C.
Proof.
  intros.
  exact (H0 H).
Qed.

End Ejercicio1.

Section Ejercicio2.
Variable A B C: Set.


(* 
??????? 
[x:A->B->C][y:A][z:B]((x y) z).

[x:B->C][y:A->B][z:A](x (y z)).

[z:B] ([x:A->B->C][y:A](x y) z).

([x:(A->B)->C]x [y:A->B]y).

*)

End Ejercicio2.


Section Ejercicio3.
Variable A B C: Set.

Set implicit arguments.

Definition apply: (A->B)->A->B :=
fun (f:A->B) (x:A) => f x.

Definition o: (A->B)->(B->C)->(A->C) :=
fun (f:A->B) (g:B->C) => (fun (x:A) => g (f x)).

Definition twice: (A->A) -> A -> A :=
fun (f:A->A) (x:A) => f (f x).

Definition g_apply: forall A B: Set, (A->B)->A->B :=
fun (A B:Set) (f:A->B) (x:A) => f x.

Definition g_o: forall A B C: Set, (A->B)->(B->C)->(A->C) :=
fun (A B C: Set) (f:A->B) (g:B->C) => (fun (x:A) => g (f x)).

Definition g_twice: forall A: Set, (A->A) -> A -> A :=
fun (A: Set) (f:A->A) (x:A) => f (f x).

End Ejercicio3.


Section Ejercicio4.
Variable A: Set.

Definition id := fun (x: A) => x.




Theorem e4_a : forall x:A, (o A A A id id) x = id x.
Proof.
  intros.
  compute.
  reflexivity.
Qed.

Theorem e4_b : forall x:A, (o A A A id id) x = id x.
Proof.
  intros.
  unfold o.
  cbv delta.
  cbv beta.
  reflexivity.
Qed.

Theorem e4_c : forall x:A, (o A A A id id) x = id x.
Proof.
  intros.
  unfold o.
  cbv beta delta.
  reflexivity.
Qed.

End Ejercicio4.


Section Ejercicio5.
Variable A B C: Set.

(* 5.1 *)
Definition opI: forall A:Set, A -> A
 := fun (A:Set) (x: A) => x.

Definition opK: forall A B:Set, A -> B -> A
 := fun (A B:Set) (x:A) (y:B) => x.

Definition opS: forall A B C:Set, (A->B->C)->(A->B)->A->C
 := fun (A B C:Set) (f:A->B->C) (g:A->B) (x:A) => ((f x) (g x)).


(* 5.2 *)
Lemma e52 : opS A (B->A) A (opK A (B->A)) (opK A B)= opI A.
Proof.
  cbv delta beta.
  reflexivity.
Qed.

End Ejercicio5.


Section Ejercicio6.
Definition N := forall X : Set, X -> (X -> X) -> X.
Definition Zero (X : Set) (o : X) (f : X -> X) := o.
Definition Uno  (X : Set) (o : X) (f : X -> X) := f (Zero X o f).

(* 6.1 *)
Definition Dos (X: Set) (o: X) (f: X->X) := f (Uno X o f). 

(* 6.2 *)
Definition Succ := fun (n:N) (X: Set) (o : X) (f: X->X) => f (n X o f).

Lemma succUno : Succ Uno = Dos.
Proof.
  unfold Succ.
  cbv delta beta.
  reflexivity.
Qed.

(* 6.3 *)
Definition Plus (n m : N) : N
                := fun (X : Set) (o : X) (f : X -> X) => n X (m X o f) f.


Infix "+++" := Plus (left associativity, at level 94).

Lemma suma1: (Uno +++ Zero) = Uno.
Proof.
  cbv delta beta.
  reflexivity.
Qed.

Lemma suma2: (Uno +++ Uno) = Dos.
Proof.
  cbv delta beta.
  reflexivity.
Qed.
 
(* 6.4 *)
Definition Prod (n m : N) : N
                := fun (X:Set) (o:X) (f:X->X) => m X o (fun y:X => n X y f).


Infix "**" := Prod (left associativity, at level 93).

(* 6.5 *)
Lemma prod1 : (Uno ** Zero) = Zero.
Proof.
  cbv delta beta.
  reflexivity.
Qed.

Lemma prod2: (Uno ** Dos) = Dos.
Proof.
  cbv delta beta.
  reflexivity.
Qed.

End Ejercicio6.


Section Ejercicio7.
(* 7.1 *)
Definition Bool := forall X:Set, X->X->X. 
Definition t    := fun (X:Set) (x y:X) => x.
Definition f    := fun (X:Set) (x y:X) => y.

(* 7.2 *)
Definition If: Bool -> Bool -> Bool -> Bool
 := fun b then' else' => (fun (X: Set) (x y: X) => b X (then' X x y) (else' X x y)).

(* 7.3 *)
Definition Not: Bool -> Bool
 := fun b => fun (X:Set) (x y:X) => b X y x.

Lemma CorrecNot : (Not t) = f /\ (Not f) = t.
Proof.
  split; cbv delta beta; reflexivity.
Qed.

(* 7.4 *)
Definition And: Bool -> Bool -> Bool
 := fun p q => If p q f.

Definition And': Bool -> Bool -> Bool
 := fun p q => If (Not p) f q.

(* 7.5 *)
Infix "&" := And (right associativity, at level 80).

Lemma CorrecAnd : (t & t) = t /\ (f & t) = f /\ (t & f) = f.
Proof.
  split; [idtac | split]; cbv delta beta; reflexivity.
Qed.

End Ejercicio7.



(* Ejercicio8 *)

Section ArrayNat.

Parameter ArrayNat : forall n:nat, Set.
Parameter empty    : ArrayNat 0.
Parameter add      : forall n:nat, nat -> ArrayNat n -> ArrayNat (n + 1).

(* 8.1 *)
Definition v : ArrayNat (S 0)
 := (add 0 (S 0) empty).
(* 8.2 *)
Definition v1 : ArrayNat 2
 := add 1 0 (add 0 0 empty).
Definition v2 : ArrayNat 4
 := add 3 0 (add 2 1 (add 1 0 (add 0 1 empty))).


(* 8.3 *)
Parameter Concat : forall m n:nat, ArrayNat m -> ArrayNat n -> ArrayNat (m + n).

(* 8.4 *)
Parameter Zip : forall n:nat, ArrayNat n -> ArrayNat n -> (nat -> nat -> nat) -> ArrayNat n.

(* 8.5 *)
Check ArrayNat.

(* 8.6 *)
Parameter Array  : forall (T:Type) (n:nat), Set.
Parameter empty' : forall T:Set, Array T 0.
Parameter add'   : forall (T:Type) (n:nat), T -> Array T n -> Array T (n + 1). 
Parameter Zip'   : forall (T:Type) (n:nat), Array T n -> Array T n -> (T->T->T) -> Array T n.

(* 8.7 *)
Parameter ArrayBool : forall n:nat, Array Bool n.

End ArrayNat.

Section Ejercicio9.
Parameter MatrizNat: forall (m n:nat), Set.

Parameter prod: forall (m n p:nat), MatrizNat m n -> MatrizNat n p -> MatrizNat m p.
 
Parameter es_id: forall n:nat, MatrizNat n n -> Bool.

Parameter ins_fila: forall (n m:nat), MatrizNat n m -> ArrayNat m -> MatrizNat (n + 1) m.

Parameter ins_columna: forall (n m:nat), MatrizNat n m -> ArrayNat n -> MatrizNat n (m + 1).

Check MatrizNat.

Parameter Matriz: forall (T:Type) (m n:nat), Set.

End Ejercicio9.



Section Ejercicio10.
Parameter ABNat : forall n : nat, Set.
Parameter emptyAB: ABNat 0.
Parameter addAB: forall n:nat, ABNat n -> nat -> ABNat n -> ABNat (n + 1).

Definition AB2 : ABNat 2
 := addAB 1 (addAB 0 emptyAB 7 emptyAB) 3 (addAB 0 emptyAB 7 emptyAB).

Parameter AB: forall (T:Type) (n:nat), Set.
Parameter emptyAB': forall (T:Type), AB T 0.
Parameter addAB': forall (T:Type) (n:nat), AB T n -> T -> AB T n -> AB T (n + 1).

End Ejercicio10.


Section Ejercicio11.

Parameter AVLNat : forall n : nat, Set.

(* 11.1 *) 
Parameter emptyAVL: AVLNat 0.

(* 11.2 *)
Parameter addAVL0: forall (n:nat), AVLNat n -> nat -> AVLNat n -> AVLNat (n + 1).
Parameter addAVL1: forall (n:nat), AVLNat (n + 1) -> nat -> AVLNat n -> AVLNat (n + 1).
Parameter addAVL2: forall (n:nat), AVLNat n -> nat -> AVLNat (n + 1) -> AVLNat (n + 1).

(* 11.3 *)
Definition AVL2: AVLNat 2
 := addAVL0 1 (addAVL0 0 emptyAVL 1 emptyAVL) 0 (addAVL0 0 emptyAVL 2 emptyAVL).

(* 11.4 *)
Parameter AVL : forall (T:Type) (n:nat), Set.
Parameter emptyAVL' : forall (T:Type), AVL T 0.
Parameter addAVL0': forall (T:Type) (n:nat), AVL T n -> T -> AVL T n -> AVL T (n + 1).
Parameter addAVL1': forall (T:Type) (n:nat), AVL T (n + 1) -> T -> AVL T n -> AVL T (n + 1).
Parameter addAVL2': forall (T:Type) (n:nat), AVL T n -> T -> AVL T (n + 1) -> AVL T (n + 1).

End Ejercicio11.


Section Ejercicio12.
Variable A B C: Set.

Lemma e12_1 : (A -> B -> C) -> B -> A -> C.
Proof.
  exact (fun f x y => f y x).
Qed.

Lemma e12_2 : (A -> B) -> (B -> C) -> A -> C.
Proof.
  exact (fun f g x => g (f x)).
Qed.

Lemma e12_3 : (A -> B -> C) -> (B -> A) -> B -> C.
Proof.
  exact (fun f g x => f (g x) x).
Qed.

End Ejercicio12.



Section Ejercicio13.
Variable A B C: Prop.

Lemma Ej313_1 : (A -> B -> C) -> A -> (A -> C) -> B -> C.
Proof.
  intros f a g b.
  exact (g a).
Qed.

Lemma Ej313_2 : A -> ~ ~ A.
Proof.
  unfold not.
  intros.
  exact (H0 H).
Qed.

Lemma Ej313_3 : (A -> B -> C) -> A -> B -> C.
Proof.
  exact (fun f x y => f x y).
Qed.

Lemma Ej313_4 : (A -> B) -> ~ (A /\ ~ B).
Proof.
  unfold not.
  intros.
  elim H0; intros.
  exact (H2 (H H1)).
Qed.

End Ejercicio13.



Section Ejercicio14.

Variable U : Set.
Variable e : U.
Variable A B : U -> Prop.
Variable P : Prop.
Variable R : U -> U -> Prop.

Lemma Ej314_1 : (forall x : U, A x -> B x) -> (forall x : U, A x) ->
forall x : U, B x.
Proof.
  intros.
  exact (H x (H0 x)).
Qed.

Lemma Ej314_2 : forall x : U, A x -> ~ (forall x : U, ~ A x).
Proof.
  unfold not.
  intros.
  exact (H0 x H).
Qed.

Lemma Ej314_3 : (forall x : U, P -> A x) -> P -> forall x : U, A x.
Proof.
  intros.
  exact (H x H0).
Qed.

Lemma Ej314_4 : (forall x y : U, R x y) -> forall x : U, R x x.
Proof.
     exact (fun f => fun x => f x x).
Qed.

Lemma Ej314_5 : (forall x y: U, R x y -> R y x) ->
                 forall z : U, R e z -> R z e.
Proof.
     exact (fun f => fun z => f e z).
Qed.

End Ejercicio14.

