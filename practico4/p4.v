Section Ejercicio1.


(* 1.1 *)
Inductive list (A:Set): Set
:=   nil: list A
   | cons: A -> list A -> list A.

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
:=    eq_list0 : eq_list A (nil A) (nil A)
    | eq_listS : forall (x:A) (xs ys: list A), eq_list A xs ys -> 
                 eq_list A (cons A x xs) (cons A x ys).

(* 1.5 *)
Inductive sorted (A:Set) (R:A -> A -> Prop) : list A -> Prop
:=    sorted0 : sorted A R (nil A)
    | sorted1 : forall (x:A), sorted A R (cons A x (nil A))
    | sortedS : forall (x y:A) (xs:list A), R x y -> sorted A R (cons A y xs) ->
                sorted A R (cons A x (cons A y xs)).

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
                           nil => true
                         | _      => false
                        end.

End Ejercicio2.

Section Ejercicio3.

Fixpoint sum (x y:nat) : nat
:=   match x with
        0 => y
      | S n => S (sum n y)
     end.

Fixpoint prod (x y:nat) : nat
:=   match x with
        0 => 0
      | S n => sum y (prod n y) 
     end.

Fixpoint pot (x y: nat) : nat
:=   match y with
        0 => 1
      | S n => prod x (pot x n)
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
        nil => 0
      | (cons y ys) => 1 + length A ys
     end.

Fixpoint append (A:Set) (xs ys: list A) : list A
:=   match xs with
        nil => ys
      | cons x zs => cons A x (append A zs ys)
     end.

(*
Fixpoint reverse' (A:Set) (xs ys:list A): list A
:=   match xs with
        nil => ys
      | cons x zs => reverse' A zs (cons A x ys)
     end.

Fixpoint reverse (A:Set) (xs:list A) : list A
:=   reverse' A xs (nil A).

*)

Fixpoint reverse (A:Set) (xs:list A) : list A
:=   match xs with
        nil => nil A
      | cons x zs => append A (reverse A zs) (cons A x (nil A))
     end.


Fixpoint filter (A:Set) (f: A -> bool) (xs:list A) : list A
:=   match xs with
        nil => nil A
      | cons y ys => if (f y)
                      then (cons A y (filter A f ys))
                      else (filter A f ys)
     end.

Fixpoint map (A B:Set) (f:A->B) (xs:list A): list B
:=   match xs with
        nil => nil B
      | cons y ys => cons B (f y) (map A B f ys)
     end.

Fixpoint exists_ (A:Set) (p:A->bool) (xs:list A) : bool
:=   match xs with
        nil => false
      | cons y ys => if (p y)
                      then true
                      else exists_ A p ys
     end.


End Ejercicio4.

Section Ejercicio5.

Fixpoint inverse (A:Set) (t:bintree A): bintree A
:=   match t with
        emptyt => emptyt A
      | addt t1 x t2 => addt A (inverse A t2) x (inverse A t1)
     end.

Fixpoint countExternbt (A:Set) (t:bintree A) : nat
:=   match t with
        emptyt => 0
      | addt t1 _ t2 => match t1, t2 with
                           emptyt, emptyt => 1
                         | _, _  => countExternbt A t1 + countExternbt A t2
                        end
     end.

Fixpoint countInternbt (A:Set) (t:bintree A) : nat
:=   match t with
        emptyt => 0
      | addt t1 _ t2 => match t1,t2 with
                           emptyt, emptyt => 0
                         | _, _         => 1 + countInternbt A t1 + countInternbt A t2
                        end
     end.

Definition InternGTExternbt (A:Set) (t:bintree A) : bool
:= leBool (countExternbt A t) (countInternbt A t).


End Ejercicio5.

Section Ejercicio6.

Fixpoint eq_nat (m n: nat) : bool
:=   match m, n with
        0, 0 => true
      | S _, 0 => false
      | 0, S _ => false
      | S x, S y => eq_nat x y
     end.

Definition ListN := list nat.

Fixpoint member (n:nat) (l:ListN) : bool
:=   match l with
        nil => false
      | cons x xs => if (eq_nat x n)
                      then true
                      else member n xs
     end.

Fixpoint delete (l:ListN) (x:nat) : ListN
:=   match l with
        nil => nil nat
      | cons n ns => if (eq_nat x n)
                      then delete ns x
                      else cons nat n (delete ns x)
     end.

Fixpoint ordered_insert (n:nat) (l:ListN) : ListN
:=   match l with
        nil => cons nat n l
      | cons x xs => if leBool n x
                      then cons nat n l
                      else cons nat x (ordered_insert n xs)
     end.


Fixpoint insert_sort' (l o:ListN) : ListN
:=   match l with
        nil => o
      | cons x xs => insert_sort' xs (ordered_insert x o)
     end.


Definition insert_sort (l:ListN) : ListN
:=  insert_sort' l (nil nat).

Fixpoint member' (A:Set) (eq:A->A->bool) (n:A) (l:list A) : bool
:=   match l with
        nil => false
      | cons x xs => if (eq x n)
                      then true
                      else member' A eq n xs
     end.

Fixpoint delete' (A:Set) (eq:A->A->bool) (l:list A) (x:A) : list A
:=   match l with
        nil => nil A
      | cons n ns => if (eq x n)
                      then delete' A eq ns x
                      else cons A n (delete' A eq ns x)
     end.

Fixpoint ordered_insert' (A:Set) (le:A->A->bool) (n:A) (l:list A) : list A
:=   match l with
        nil => cons A n l
      | cons x xs => if le n x
                      then cons A n l
                      else cons A x (ordered_insert' A le n xs)
     end.


Fixpoint insert_sort_aux (A:Set) (le:A->A->bool) (l o:list A) : list A
:=   match l with
        nil => o
      | cons x xs => insert_sort_aux A le xs (ordered_insert' A le x o)
     end.


Definition insert_sort'' (A:Set) (le:A->A->bool) (l:list A) : list A
:=  insert_sort_aux A le l (nil A).

End Ejercicio6.

Section Ejercicio7.

Inductive Exp (A:Set) : Set := Atomo : A -> Exp A
                             | Add : Exp A -> Exp A -> Exp A
                             | Mul : Exp A -> Exp A -> Exp A
                             | Neg : Exp A -> Exp A.

Fixpoint EvalNat (e: Exp nat) : nat
:=   match e with
        Atomo n => n
      | Add m n => (EvalNat m) + (EvalNat n)
      | Mul m n => (EvalNat m) * (EvalNat n)
      | Neg m   => (EvalNat m)
     end.

Fixpoint EvalBool (e: Exp bool) : bool
:=   match e with
        Atomo b => b
      | Add m n => Or (EvalBool m) (EvalBool n)
      | Mul m n => And (EvalBool m) (EvalBool n)
      | Neg m   => Not (EvalBool m)
     end.

End Ejercicio7.

Section Ejercicio8.

(* 1 *)
Lemma Or_Conm: forall a b : bool, Or a b = Or b a.
Proof.
  intros a b.

  destruct a; simpl.
  destruct b; simpl; reflexivity.
  destruct b; reflexivity.
Qed.

Lemma Or_Assoc: forall a b c: bool, Or (Or a b) c = Or a (Or b c).
Proof.
  intros a b c.
  destruct a; simpl; reflexivity.
Qed.

Lemma And_Conm: forall a b: bool, And a b = And b a.
Proof.
  intros a b.
  destruct a; simpl.
  destruct b; simpl; reflexivity.
  destruct b; reflexivity.
Qed.

Lemma And_Assoc: forall a b c: bool, And (And a b) c = And a (And b c).
Proof.
  intros a b c.
  destruct a; simpl; reflexivity.
Qed.

Lemma LAnd : forall a b : bool, And a b = true <-> a = true /\ b = true.
Proof.
  intros a b;unfold iff; split; intros.
  destruct a; destruct b; auto.
  destruct a; destruct b; auto; elim H; intros; discriminate.
Qed.

Lemma LOr1 : forall a b : bool, Or a b = false <-> a = false /\ b = false.
Proof.
  intros a b; unfold iff; split; intros.
  destruct a; destruct b; auto.
  destruct a; destruct b; auto; elim H; intros; discriminate.
Qed.

Lemma LOr2 : forall a b : bool, Or a b = true <-> a = true \/ b = true.
Proof.
  intros a b; unfold iff; split; intros.
  destruct a; destruct b; auto.
  destruct a; destruct b; auto; elim H; intros; discriminate.
Qed.

Lemma LXor : forall a b : bool, Xor a b = true <-> a <> b.
Proof.
  intros a b; unfold iff; split; intros.
  destruct a; destruct b; auto; elim H; intros; discriminate.
  destruct a; destruct b; auto; elim H; intros; auto.
Qed.

Lemma LNot : forall b : bool, Not (Not b) = b.
Proof.
  intro b.
  destruct b; simpl; reflexivity.
Qed. 

End Ejercicio8.

Section Ejercicio9.

Lemma SumO : forall n : nat, sum n 0 = n.
Proof.
  intro.
  induction n; simpl.

  reflexivity.

  rewrite -> IHn. reflexivity.
Qed.

Lemma SumS : forall n m : nat, sum n (S m) = sum (S n) m.
Proof.
  intros.

  induction n.
  simpl; reflexivity.
  
  simpl.
  rewrite -> IHn; simpl; reflexivity.
Qed.

Lemma SumConm : forall n m : nat, sum n m = sum m n.
Proof.
  intros.
  induction n.
  rewrite SumO.
  simpl; reflexivity.
  
  simpl.
  rewrite -> IHn.
  rewrite SumS; simpl;reflexivity.
Qed.

Lemma SumAsoc : forall n m p : nat, sum n (sum m p) = sum (sum n m) p.
Proof.
  intros n m p.
  induction n.
  simpl; reflexivity.
  
  simpl. rewrite -> IHn.
  reflexivity.
Qed.

Lemma ProdO : forall n : nat, prod n 0 = 0.
Proof.
  intro.
  induction n; auto.
Qed.

Lemma ProdS: forall n m : nat, prod n (S m) = sum n (prod n m).
Proof.
  intros.
  induction n; simpl.
  reflexivity.
  rewrite -> IHn.
 
  induction m; simpl; auto.
  rewrite -> SumS; simpl.

  rewrite -> SumAsoc.
  rewrite -> (SumConm m n).
  rewrite -> SumAsoc.
  reflexivity.
Qed.

Lemma ProdConm : forall n m : nat, prod n m = prod m n.
Proof.
  intros n m.
  induction n; simpl.
  
  induction m; simpl.

  reflexivity.
  assumption.
  
  rewrite -> IHn.
  induction m; simpl.
  reflexivity.

  rewrite -> ProdS, SumAsoc.
  rewrite -> (SumConm m n).
  rewrite -> SumAsoc.
  reflexivity.  
Qed.

Lemma ProdDistr : forall n m p : nat,
prod n (sum m p) = sum (prod n m) (prod n p).
Proof.
  intros n m p.
  induction n; simpl; auto.

  rewrite -> IHn.
  rewrite -> SumAsoc.
  rewrite <- (SumAsoc m p (prod n m)).
  rewrite -> (SumConm p (prod n m)). 
  rewrite -> SumAsoc.
  rewrite <- (SumAsoc (sum m (prod n m)) p (prod n p)).
  reflexivity.
Qed.

Lemma ProdAsoc : forall n m p : nat, prod n (prod m p) = prod (prod n m) p.
Proof.
  intros n m p.
  induction n; auto.

  simpl.
  rewrite -> IHn.
  rewrite -> (ProdConm (sum m (prod n m)) p).
  rewrite -> ProdDistr.
  rewrite -> (ProdConm m p).
  rewrite -> (ProdConm p (prod n m)).
  auto.
Qed.

End Ejercicio9.

Section Ejercicio10.

Lemma L1 : forall (A : Set) (l : list A), append A l (nil A) = l.
Proof.
  intros.
  induction l; simpl; auto.
  
  rewrite -> IHl; auto.
Qed.

Lemma L2 : forall (A : Set) (l : list A) (a : A), ~(cons A a l) = nil A.
Proof.
  intros.
  induction l; simpl;
  discriminate.
Qed.

Lemma L3 : forall (A : Set) (l m : list A) (a : A),
cons A a (append A l m) = append A (cons A a l) m.
Proof.
  intros.
  induction l; simpl; auto.
Qed.

Lemma L4 : forall (A : Set) (l m : list A),
length A (append A l m) = sum (length A l) (length A m).
Proof.
  intros.
  induction l; simpl; auto.
Qed.

Lemma L5_1: forall (n:nat), sum n 1 = S n.
Proof.
  intro.
  induction n; simpl;auto.
Qed.

Lemma L5 : forall (A : Set) (l : list A), length A (reverse A l) = length A l.
Proof.
  intros.
  induction l; simpl; auto.
  rewrite -> L4.
  rewrite -> IHl; simpl. (* induction en length A l ??? *)
  rewrite -> L5_1; reflexivity.
Qed.

Lemma L6_1: forall (A:Set) (j k l : list A),
append A (append A j k) l = append A j (append A k l).
Proof.
  intros.
  induction j; simpl; auto.
  rewrite -> IHj; reflexivity.
Qed. 

Lemma L6 : forall (A : Set) (l m : list A),
reverse A (append A l m) = append A (reverse A m) (reverse A l).
Proof.
  intros.
  induction l; simpl; auto.
  rewrite -> L1; reflexivity.
  rewrite -> IHl.
  rewrite -> L6_1; reflexivity.
Qed.

End Ejercicio10.

Section Ejercicio11.

Lemma L7 : forall (A B : Set) (l m : list A) (f : A -> B),
map A B f (append A l m) = append B (map A B f l) (map A B f m).
Proof.
  intros.
  induction l; simpl; auto.
  rewrite -> IHl; reflexivity.
Qed.



Lemma L8 : forall (A : Set) (l m : list A) (P : A -> bool),
filter A P (append A l m) = append A (filter A P l) (filter A P m).
Proof.
  intros.
  induction l; simpl; auto.
  case (P a).
  
  rewrite -> IHl; induction l; auto.
  induction l; auto.
Qed.

Lemma L9 : forall (A : Set) (l m n : list A),
append A l (append A m n) = append A (append A l m) n.
Proof.
  intros.
  induction l; simpl; auto.
  rewrite -> IHl; reflexivity.
Qed.

Lemma L10_1 : forall (A :Set) (l : list A) (a: A),
reverse A (append A l (cons A a (nil A))) = cons A a (reverse A l).
Proof.
  intros.
  induction l; simpl; auto.
  rewrite -> IHl; simpl; auto.
Qed.

Lemma L10 : forall (A : Set) (l : list A), reverse A (reverse A l) = l.
Proof.
  intros.
  induction l; simpl; auto.
  rewrite -> L10_1, IHl; reflexivity.
Qed.

End Ejercicio11.

Section Ejercicio12.

Fixpoint filterMap (A B : Set) (P : B -> bool) (f : A -> B)
(l : list A) {struct l} : list B :=
match l with
   | nil => nil B
   | cons a l1 =>
                match P (f a) with
                   | true => cons B (f a) (filterMap A B P f l1)
                   | false => filterMap A B P f l1
                end
end.

Lemma FusionFilterMap :
forall (A B : Set) (P : B -> bool) (f : A -> B) (l : list A),
filter B P (map A B f l) = filterMap A B P f l.
Proof.
  intros.
  induction l; simpl; auto.
  case (P (f a)).

  rewrite -> IHl; auto.
  
  assumption.
Qed.

End Ejercicio12.

Section Ejercicio13.

Theorem e13 : forall (A : Set) (t : bintree A), mirror A (inverse A t) t.
Proof.
  intros.
  induction t; simpl.

  apply mirror0.

  apply mirrorS; assumption.  
Qed.

End Ejercicio13.

Section Ejercicio14.


Theorem e141 : forall (A : Set) (t : bintree A), isomorfo A (id t) t.
Proof.
  intros.
  induction t; simpl.
  
  apply isomorfo0.

  apply isomorfoS; assumption.
Qed.

Theorem isom_reflex : forall (A : Set) (a b: bintree A), 
isomorfo A a b -> isomorfo A b a.
Proof.
  intros.
  induction b.
  
  induction a.
  apply isomorfo0.
  
  elim H.
  apply isomorfo0.
  
  intros.
  apply isomorfoS; assumption.

  elim H.
  apply isomorfo0.
  
  intros.
  apply isomorfoS; assumption.
Qed.

End Ejercicio14.

Section Ejercicio15.

Inductive Tree (A:Set) : Set
:=   nodeleaf : A -> Tree A
   | branch : Tree A -> Tree A -> Tree A.

Fixpoint mapTree (A B:Set) (f: A->B) (t: Tree A) : Tree B
:=   match t with
        nodeleaf a => nodeleaf B (f a)
      | branch l r => branch B (mapTree A B f l) (mapTree A B f r)
     end.

Fixpoint countLeaves (A:Set) (t: Tree A) : nat
:=    match t with
         nodeleaf _ => 1
       | branch l r => countLeaves A l + countLeaves A r
      end.

Theorem e151 : forall (A B : Set) (f : A -> B) (t : Tree A),
countLeaves A t = countLeaves B (mapTree A B f t).
Proof.
  intros.
  induction t; simpl; auto.
Qed.

Fixpoint hojas (A:Set) (t : Tree A) : list A
:=   match t with
        nodeleaf a => cons A a (nil A)
      | branch l r => append A (hojas A l) (hojas A r)
     end.

Theorem e152 : forall (A:Set) (t:Tree A), countLeaves A t = length A (hojas A t).
Proof.
  intros.
  induction t; simpl; auto.
  rewrite -> L4.
  rewrite -> IHt1, IHt2.
  auto.
Qed.

End Ejercicio15.



Section Ejercicio16.


Inductive posfijo (A:Set) : list A -> list A -> Prop 
:=   posfijo0 : forall l:list A,  posfijo A l l
   | posfijoS : forall (l l':list A) (a:A), posfijo A l l' -> posfijo A l (cons A a l').



Theorem e162a : forall (A:Set) (l1 l2 l3 : list A), l2 = append A l3 l1 -> posfijo A l1 l2.
Proof.
  intros.

  rewrite H.
  clear H.

  induction l3; simpl; auto.
  apply posfijo0.

  apply posfijoS.
  assumption.
Qed.

Theorem e162b : forall (A:Set) (l1 l2 :list A), posfijo A l1 l2 -> (exists l3 : list A, l2 = append A l3 l1).
Proof.
  intros.
  
  induction H.

  exists (nil A); simpl; auto.

  elim IHposfijo; intros.  
  
  rewrite -> H0.
  rewrite -> L3.

  exists (cons A a x).
  auto.
Qed.



Fixpoint ultimo (A:Set) (l:list A) : list A
:=   match l with
        nil => nil A
      | cons x xs => match xs with
                        nil => cons A x (nil A)
                      | _   => ultimo A xs
                     end
     end.

Fixpoint init (A:Set) (l:list A) : list A
:=   match l with
        nil => nil A
      | cons x xs => match xs with
                        nil => nil A
                      | cons y ys => cons A x (init A xs)
                     end
     end.

Theorem e164 : forall (A : Set) (l : list A), posfijo A (ultimo A l) l.
Proof.
  intros.
  induction l.

  simpl; apply posfijo0.
  
  simpl; destruct l.
  apply posfijo0.
  intros.
  apply posfijoS.
  assumption.
Qed.



End Ejercicio16.


Section Ejercicio17.

Inductive ABin (A B:Set)
:=    leafAB : B -> ABin A B
    | branchAB : ABin A B -> A -> ABin A B -> ABin A B.

Fixpoint countExternAB (A B:Set) (t : ABin A B) : nat
:=   match t with
        leafAB _ => 1
      | branchAB l _ r => countExternAB A B l + countExternAB A B r
     end.

Fixpoint countInternAB (A B:Set) (t : ABin A B) : nat
:=   match t with
        leafAB _ => 0
      | branchAB l _ r => countInternAB A B l + 1 + countInternAB A B r
     end.

Require Import Coq.Arith.Plus. (* plus_assoc... *)

Theorem e171 : forall (A B: Set) (t:ABin A B), countExternAB A B t = countInternAB A B t + 1.
Proof.
  intros.
  induction t.

  simpl; auto.

  simpl countExternAB.
  simpl countInternAB.
  rewrite -> IHt1, IHt2.
  rewrite -> plus_assoc.
  reflexivity.
Qed.

End Ejercicio17.

Section Ejercicio18.

Variable A : Set.
Inductive Tree_ : Set :=
  | nullT : Tree_
  | consT : A -> Tree_ -> Tree_ -> Tree_.

Inductive isSubTree : Tree_ -> Tree_ -> Prop
:=    isSubTree0 : forall (t:Tree_), isSubTree t t
    | isSubTreeL : forall (a b c:Tree_) (x:A), isSubTree a b -> isSubTree a (consT x b c)
    | isSubTreeR : forall (a b c:Tree_) (x:A), isSubTree a c -> isSubTree a (consT x b c).


Theorem isSubTree_reflex : forall (t: Tree_), isSubTree t t.
Proof.
  intros.
  apply isSubTree0.
Qed.

Theorem isSubTree_trans : forall (a b c:Tree_), isSubTree a b -> isSubTree b c -> isSubTree a c.
Proof.
  intros.
  induction H0.

  assumption.

  apply isSubTreeL.
  apply IHisSubTree; assumption.

  apply isSubTreeR.
  apply IHisSubTree; assumption.
Qed.

End Ejercicio18.

Section Ejercicio19.

Inductive ACom (A:Set) : nat -> Set
:=   leafAC : A -> ACom A 0
   | branchAC : forall n:nat, ACom A n -> A ->  ACom A n -> ACom A (n+1).

Fixpoint h (A:Set) (n:nat) (t:ACom A n) : nat
:=   match t with
        leafAC  _ => 1
      | branchAC n l _ r => (h A n l + h A n r)
     end.

Axiom potO : forall n : nat, pot (S n) 0 = 1.
Axiom potS : forall m: nat, pot 2 (m + 1) = sum (pot 2 m) (pot 2 m).

Theorem e191: forall (A:Set) (n:nat) (t : ACom A n), h A n t = pot 2 n.
Proof.
  intros.
  induction t; simpl; auto.
  rewrite -> IHt1, IHt2.
  symmetry.
  exact (potS n).
Qed.

End Ejercicio19.

Section Ejercicio20.

Definition max_n (m n: nat) : nat
:= if leBool m n
   then n
   else m.

Inductive AB (A:Set) : nat -> Set
:=   emptyAB : AB A 0
   | leAB : A -> AB A 1
   | brAB : forall m n : nat, AB A m -> A -> AB A n -> AB A (S(max_n m n)).

Fixpoint camino (A:Set) (n:nat) (t: AB A n) : list A
:=   match t with
        emptyAB => nil A
      | leAB a  => cons A a (nil A)
      | brAB ml mr l x r => cons A x (if leBool ml mr then (camino A mr r) else (camino A ml l))
     end.

Theorem e201: forall (A:Set) (n:nat) (t:AB A n), length A (camino A n t) = n.
Proof.
  intros.
  induction t; simpl; auto.
  unfold max_n.
  destruct (leBool m n).

  rewrite -> IHt2; auto.
  rewrite -> IHt1; auto.

Qed.

End Ejercicio20.
