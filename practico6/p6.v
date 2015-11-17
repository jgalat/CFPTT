Section Ejercicio1.

Lemma predspec : forall n : nat, {m : nat | n = 0 /\ m = 0 \/ n = S m}.
Proof.
  intros. induction n.
  exists 0; left; split; reflexivity.
  elim IHn.
  intros.
  exists n.
  right; reflexivity.
Qed.

End Ejercicio1.

Extraction Language Haskell.
Extraction "predecesor" predspec.

Section Ejercicio2.


Inductive bintree (A:Set):Set
:=   Leaf: bintree A
   | Branch: bintree A -> A -> bintree A -> bintree A.

Inductive mirror (A:Set) : bintree A -> bintree A -> Prop
:=    mirror0 : mirror A (Leaf A) (Leaf A)
    | mirrorS : forall (x:A) (a b c d: bintree A), mirror A a d -> mirror A b c ->
                mirror A (Branch A a x b) (Branch A c x d).

Lemma MirrorC: forall (A:Set) (t:bintree A),
{t':bintree A|(mirror A t t')} .
Proof.
  intros.
  induction t.
  exists (Leaf A).
  constructor.
  elim IHt1; intros. elim IHt2; intros.
  exists (Branch A x0 a x).
  constructor; assumption.
Qed.

Fixpoint inverse (A:Set) (t:bintree A): bintree A
:=   match t with
        Leaf => Leaf A
      | Branch t1 x t2 => Branch A (inverse A t2) x (inverse A t1)
     end.

Hint Constructors mirror.

Lemma MirrorC2: forall (A:Set) (t: bintree A),
{t': bintree A | mirror A t t'}.
Proof.
  intros.
  exists (inverse A t).
  induction t; simpl.
  constructor.
  auto.
Qed.

End Ejercicio2.

Extraction Language Haskell.
Extraction "mirror_function" MirrorC2.

Section Ejercicio3.

Definition Value := bool.

Inductive BoolExpr : Set :=
| bbool : bool -> BoolExpr
| or : BoolExpr -> BoolExpr -> BoolExpr
| bnot : BoolExpr -> BoolExpr.

Inductive BEval : BoolExpr -> Value -> Prop :=
| ebool : forall b : bool, BEval (bbool b) (b:Value)
| eorl : forall e1 e2 : BoolExpr, BEval e1 true -> BEval (or e1 e2) true
| eorr : forall e1 e2 : BoolExpr, BEval e2 true -> BEval (or e1 e2) true
| eorrl : forall e1 e2 : BoolExpr, BEval e1 false -> BEval e2 false -> BEval (or e1 e2) false
| enott : forall e : BoolExpr, BEval e true -> BEval (bnot e) false
| enotf : forall e : BoolExpr, BEval e false -> BEval (bnot e) true.

Fixpoint beval (e : BoolExpr) : Value :=
  match e with
    | bbool b => b
    | or e1 e2 => match beval e1, beval e2 with
                    | false, false => false
                    | _, _ => true
                  end
    | bnot e1 => if beval e1 then false else true
  end.

Fixpoint sbeval (e : BoolExpr) : Value :=
  match e with
    | bbool b => b
    | or e1 e2 => match sbeval e1 with
                    | true => true
                    | _ => sbeval e2
                  end
    | bnot e1 => if sbeval e1 then false else true
  end.

Lemma bevalC: forall (e:BoolExpr), {b:Value | (BEval e b)}.
Proof.
  intros.
  exists (beval e).
  induction e.

  simpl; constructor.

  simpl.
  destruct (beval e1).

  apply eorl; assumption.

  destruct (beval e2).
  apply eorr; assumption.
  apply eorrl; assumption.

  simpl.
  destruct (beval e); constructor; assumption.
Qed.

Lemma sbevalC: forall (e:BoolExpr), {b:Value | (BEval e b)}.
Proof.
  intros.
  exists (sbeval e).
  induction e.

  simpl; constructor.
  
  simpl.
  destruct (sbeval e1).

  constructor; assumption.

  destruct (sbeval e2).
  
  apply eorr; assumption.
  
  apply eorrl; assumption.

  simpl.
  destruct (sbeval e); constructor; assumption.
Qed.

Hint Constructors BEval.

Lemma bevalC2: forall (e:BoolExpr), {b:Value | (BEval e b)}.
Proof.
  intros.
  exists (beval e).
  induction e; simpl; auto.

  destruct (beval e1); auto.
  destruct (beval e2); auto.

  destruct (beval e); auto.
Qed.

Lemma sbevalC2: forall (e:BoolExpr), {b:Value | (BEval e b)}.
Proof.
  intros.
  exists (beval e).
  induction e; simpl; auto.

  destruct (beval e1); auto.
  destruct (beval e2); auto.

  destruct (beval e); auto.
Qed.

End Ejercicio3.

Extraction Language Haskell.
Extraction "beval" bevalC2.
Extraction "sbeval" sbevalC2.

Extract Inductive bool => "Bool" [ "true" "false" ].
Extraction "beval" bevalC2.
Extraction "sbeval" sbevalC2.

Section Ejercicio4.

Variable A:Set.

Inductive list : Set :=
  | nil : list
  | cons : A -> list -> list.


Fixpoint append (l1 l2 : list) {struct l1} : list :=
  match l1 with
    | nil => l2
    | cons a l => cons a (append l l2)
  end.

Inductive perm : list -> list ->Prop:=
  |perm_refl: forall l, perm l l
  |perm_cons: forall a l0 l1, perm l0 l1-> perm (cons a l0)(cons a l1)
  |perm_app: forall a l, perm (cons a l) (append l (cons a nil))
  |perm_trans: forall l1 l2 l3, perm l1 l2 -> perm l2 l3 -> perm l1 l3.

Hint Constructors perm.

Fixpoint reverse (l : list) : list :=
  match l with
    | nil => nil
    | cons a l1 => append (reverse l1) (cons a nil) 
  end.

Lemma Ej6_4: forall l: list, {l2: list | perm l l2}.
Proof.
  intros.
  exists (reverse l).
  induction l; simpl.

  constructor.

  apply (perm_trans (cons a l) (cons a (reverse l)) (append (reverse l) (cons a nil))). 

  constructor; assumption.

  constructor.
Qed.

End Ejercicio4.

Section Ejercicio5.

Inductive Le:nat -> nat -> Prop 
:=   Le0 : forall (n:nat), Le 0 n
   | LeS : forall (m n: nat), Le m n -> Le (S m) (S n).

Inductive Gt:nat -> nat -> Prop
:=   Gt0 : forall (n:nat), Gt (S n) 0
   | GtS : forall (m n:nat), Gt m n -> Gt (S m) (S n).

Function leBool (m n: nat): bool
:=   match m, n with
         0, _ => true
       | S x, 0 => false
       | S x, S y => leBool x y
     end.

Lemma Le_Gt_dec: forall n m:nat, {(Le n m)}+{(Gt n m)}.
Proof.
  intros.
  functional induction (leBool n m).
  
  left; constructor.
  right; constructor.
  
  elim IHb; intros;

  [left | right]; constructor; assumption.
Qed.

Require Import Omega.

Lemma le_gt_dec: forall n m:nat, {(le n m)}+{(gt n m)}.
Proof.
  intros.
  functional induction (leBool n m).
  left; omega.
  right; omega.
  
  elim IHb; intros.
  
  left; omega.

  right; omega.
Qed.

End Ejercicio5.

Section Ejercicio6.

Require Import Omega.
Require Import DecBool.
Require Import Compare_dec.
Require Import Plus.
Require Import Mult.

Definition spec_res_nat_div_mod (a b:nat) (qr:nat*nat) :=
  match qr with
    (q,r) => (a = b*q + r) /\ r < b
  end.

Definition nat_div_mod :
forall a b:nat, not(b=0) -> {qr:nat*nat | spec_res_nat_div_mod a b qr}.
Proof.
  intros.
  unfold spec_res_nat_div_mod.  
  induction a.

  exists (0, 0); split; omega.

  elim IHa; intros.
  destruct x.
  case (lt_dec n0 (b-1)); intros.

  exists (n, n0 + 1).
  split; omega.

  exists (n+1, 0).

  split; [idtac |omega].
  elim p; intros; clear p.
  
  assert (n0 = b-1). omega.
  rewrite -> H0.
  rewrite -> H2.
  rewrite -> mult_plus_distr_l.
  omega.
Qed.

End Ejercicio6.

Section Ejercicio7.

Inductive tree (A:Set) : Set :=
  | leaf : tree A
  | node : A -> tree A -> tree A -> tree A.

Inductive tree_sub (A:Set) (t:tree A) : tree A -> Prop :=
  | tree_sub1 : forall (t':tree A) (x:A), tree_sub A t (node A x t t')
  | tree_sub2 : forall (t':tree A) (x:A), tree_sub A t (node A x t' t).

Theorem well_founded_tree_sub : forall A:Set, well_founded (tree_sub A).
Proof.
  intros.
  unfold well_founded; intros.

  induction a.
  apply Acc_intro; intros.
  inversion H.
  
  apply Acc_intro; intros.
  inversion H; assumption.
Qed.

End Ejercicio7.

Section Ejercicio8.

Function size (e: BoolExpr) : nat
:=    match e with
         bbool _ => 0
       | or e1 e2 => 1 + size e1 + size e2
       | bnot e1 => 1 + size e1
      end.

Definition elt (e1 e2 : BoolExpr) := size e1 < size e2.

Require Import Wf_nat.
Require Import Inverse_Image.

Theorem well_founded_elt : well_founded elt.
Proof.
  apply (wf_inverse_image BoolExpr nat lt size);
  apply lt_wf.
Qed.

End Ejercicio8.

Section Ejercicio9.

Check Acc_inv.




Require Import Recdef.

Function lBool (a b: nat): bool
:= match a, b with
      _, 0 => false
    | 0, S x => true
    | S x, S y => lBool x y
   end.

Function divmod (a b : nat) (t : b > 0) {wf lt a} : nat*nat
:= match lBool a b with
         true => (0, a)
       | false => let (q,r) := divmod (a-b) b t 
                  in (S q, r)
   end.
Proof.
  intros.
  assert (a >= b).

  clear t.
  functional induction (lBool a b).

  omega.

  inversion teq.

  apply IHb0 in teq.

  omega.

  omega.

  apply lt_wf.
Qed.
    
End Ejercicio9.

Section Ejercicio10.

Fixpoint ordered_insert (n:nat) (l:list nat) : list nat
:=   match l with
        nil => cons nat n l
      | cons x xs => if leBool n x
                      then cons nat n l
                      else cons nat x (ordered_insert n xs)
     end.

Fixpoint insert_sort' (l o:list nat) : list nat
:=   match l with
        nil => o
      | cons x xs => insert_sort' xs (ordered_insert x o)
     end.


Definition insert_sort (l: list nat) : list nat
:=  insert_sort' l (nil nat).

Inductive sorted (A:Set) (R:A -> A -> Prop) : list A -> Prop
:=    sorted0 : sorted A R (nil A)
    | sorted1 : forall (x:A), sorted A R (cons A x (nil A))
    | sortedS : forall (x y:A) (xs:list A), R x y -> sorted A R (cons A y xs) ->
                sorted A R (cons A x (cons A y xs)).


Inductive perm_10 (A:Set) : list A -> list A -> Prop:=
  |perm_refl_10: forall l, perm_10 A l l
  |perm_cons_10: forall a l0 l1, perm_10 A l0 l1-> perm_10 A (cons A a l0)(cons A a l1)
  |p_ccons_10: forall a b l, (perm_10 A (cons A a (cons A b l)) (cons A b (cons A a l)))
  |perm_trans_10: forall l1 l2 l3, perm_10 A l1 l2 -> perm_10 A l2 l3 -> perm_10 A l1 l3.

End Ejercicio10.



