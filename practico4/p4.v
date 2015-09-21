Section Ejercicio1.


(* 1.1 *)
Inductive list (A:Set): Set
:=   emptyl: list A
   | consl: A -> list A -> list A.

Inductive bintree (A:Set):Set
:=   emptyt: bintree A
   | addt: bintree A -> A -> bintree A -> bintree A.

(* 1.2 *)
Inductive Array (A:Set) : nat -> Set
:=    emptyA: Array A 0
    | consA: forall n:nat, A -> Array A n -> Array A (n + 1).

Inductive Matrix (A:Set) : nat -> nat -> Set
:=    emptyM: Matrix A 0 0
    | addR : forall (m n: nat), Array A n -> Matrix A m n -> Matrix A (m + 1) n
    | addC : forall (m n: nat), Array A m -> Matrix A m n -> Matrix A m (n + 1).

(* 1.3 *)
Inductive leq : nat -> nat -> Prop
:=    leq0 : forall n:nat, leq 0 n
    | leqS : forall (m n: nat), leq m n -> leq (S m) (S n).

(* 1.4 *)
Inductive eq_list (A:Set) : list A -> list A -> Prop
:=    eq_list0 : eq_list A (emptyl A) (emptyl A)
    | eq_listS : forall (x:A) (xs ys: list A), eq_list A xs ys -> 
                 eq_list A (consl A x xs) (consl A x ys).

(* 1.5 *)
Inductive sorted (A:Set) (R:A -> A -> Prop) : list A -> Prop
:=    sorted0 : sorted A R (emptyl A)
    | sorted1 : forall (x:A), sorted A R (consl A x (emptyl A))
    | sortedS : forall (x y:A) (xs:list A), R x y -> sorted A R (consl A y xs) ->
                sorted A R (consl A x (consl A y xs)).

(* 1.6 *)
Inductive mirror (A:Set) : bintree A -> bintree A -> Prop
:=    mirror0 : mirror A (emptyt A) (emptyt A)
    | mirrorS : forall (x:A) (a b c d: bintree A), mirror A a d -> mirror A b c ->
                mirror A (addt A a x b) (addt A c x d).


(* 1.7 *)
Inductive isomorfo (A:Set) : bintree A -> bintree A -> Prop
:=    isomorfo0 : isomorfo A (emptyt A) (emptyt A)
    | isomorfoS : forall (x y: A) (a b c d: bintree A), isomorfo A a c ->
                  isomorfo A b d -> isomorfo A (addt A a x b) (addt A c y d).

(* 1.8 *)
Inductive Gtree (A B:Set): Set
:=    emptyG : Gtree A B
    | leafG  : A -> Gtree A B
    | nodeG  : B -> Gforest A B -> Gtree A B
with Gforest (A B:Set) : Set
:=    addG   : Gtree A B -> Gforest A B -> Gforest A B.


End Ejercicio1.


Section Ejercicio2.

Definition Or : bool -> bool -> bool
:=   fun (x y: bool) => match x with
                           true  => true
                         | _ => y
                        end.

Definition And : bool -> bool -> bool
:=   fun (x y: bool) => match x with
                           true => y
                         | _ => false
                        end.

Definition Not : bool -> bool
:=   fun x: bool => match x with 
                       true => false
                     | _    => true
                    end.

Definition Xor : bool -> bool -> bool
:=   fun (x y: bool) => match x with
                           true => Not y
                         | _    => y
                        end.

Definition is_nil (A:Set) : list A -> bool
:=   fun (x: list A) => match x with
                           emptyl => true
                         | _      => false
                        end.

End Ejercicio2.

Section Ejercicio3.

Fixpoint sum (x y:nat) : nat
:=   match x with
        0 => y
      | S n => sum n (S y)
     end.

Fixpoint prod (x y:nat) : nat
:=   match x with
        0 => 0
      | S n => prod n (sum y y)
     end.

Fixpoint pot (x y: nat) : nat
:=   match y with
        0 => 1
      | S n => pot (prod x x) n
     end.

Fixpoint leBool (x y:nat) : bool
:=   match x, y with
        0, _ => true
      | (S m), (S n) => leBool m n
      | _,  0 => false
     end.

End Ejercicio3.

Section Ejercicio4.

Fixpoint length (A:Set) (xs: list A) : nat
:=   match xs with
        emptyl => 0
      | (consl y ys) => 1 + length A ys
     end.

Fixpoint append (A:Set) (xs ys: list A) : list A
:=   match xs with
        emptyl => ys
      | consl x zs => consl A x (append A zs ys)
     end.


Fixpoint reverse' (A:Set) (xs ys:list A): list A
:=   match xs with
        emptyl => ys
      | consl x zs => reverse' A zs (consl A x ys)
     end.

Fixpoint reverse (A:Set) (xs:list A) : list A
:=   reverse' A xs (emptyl A).

Fixpoint filter (A:Set) (f: A -> bool) (xs:list A) : list A
:=   match xs with
        emptyl => emptyl A
      | consl y ys => if (f y)
                      then (consl A y (filter A f ys))
                      else (filter A f ys)
     end.

Fixpoint map (A B:Set) (f:A->B) (xs:list A): list B
:=   match xs with
        emptyl => emptyl B
      | consl y ys => consl B (f y) (map A B f ys)
     end.

Fixpoint exists_ (A:Set) (p:A->bool) (xs:list A) : bool
:=   match xs with
        emptyl => false
      | consl y ys => if (p y)
                      then true
                      else exists_ A p ys
     end.


End Ejercicio4.