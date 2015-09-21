(* Practica 1 *)

Section P1.
Variables A B C:Prop.

(* Ej 1.1 *)
Theorem e11: A->A.
Proof.
  intro.
  assumption.
Qed.

(* Ej 1.2 *)
Theorem e12: A->B->A.
Proof.
  intros.
  assumption.
Qed.

(* Ej 1.3 *)
Theorem e13: (A->(B->C))->(A->B)->(A->C).
Proof.
  intros.
  apply H.
  assumption.
  apply H0.
  assumption.
Qed.



(*Ej 2.1 *)
Theorem e21: (A->B)->(B->C)->A->C.
Proof.
  intros.
  apply H0.
  apply H.
  assumption.
Qed.


(*Ej 2.2 *)
Theorem e22: (A->B->C)->B->A->C.
Proof.
  intros.
  apply H.
  assumption.
  assumption.

Qed.


(*Ej 3.1 *)
Theorem e31: A->A->A.
Proof.
  intros.
  assumption.

Qed.

Theorem e31b: A->A->A.
Proof.
  intro H.
  intro G.
  assumption.
Qed.

(* Ej 3.2 *)
Theorem e32: (A->B->C)->A->(A->C)->B->C.
Proof.
  intros.
  apply H1.
  assumption.
Qed.

Theorem e32b: (A->B->C)->A->(A->C)->B->C.
Proof.
  intro G.
  intro H.
  intro I.
  apply G.
  assumption.
Qed.


(* Ej 4.1 *)
Theorem e41: A -> ~~A.
Proof.
  intro H.
  intro G.
  absurd A.
  assumption.
  assumption.
Qed.


(* Ej 4.2 *)
Theorem e42: A -> B -> (A /\ B).
Proof.
  intro G.
  intro H.
  split.
  assumption.
  assumption.
Qed.

(* Ej 4.3 *)
Theorem e43: (A->B->C) -> (A/\B->C).
Proof.
  intro G.
  intro H.
  apply G.
  elim H.
  intros.
  assumption.
  elim H.
  intros.
  assumption.
Qed.

(* Ej 4.4 *)
Theorem e44: A->(A\/B).
Proof.
  intro G.
  left.
  assumption.
Qed.

(* Ej 4.5 *)
Theorem e45: B->(A\/B).
Proof.
  intro G.
  right.
  assumption.
Qed.

(* Ej 4.6 *)
Theorem e46: (A \/ B) -> (B \/ A).
Proof.
  intro G.
  elim G.
  intro H.
  right.
  assumption.
  intro H.
  left.
  assumption.
Qed.

(* Ej 4.7 *)
Theorem e47: (A->C)->(B->C)->A\/B->C.
Proof.
  intro G.
  intro H.
  intro I.
  elim I.
  assumption.
  assumption.
Qed.

(* Ej 4.8 *)
Theorem e48: False->A.
Proof.
  intro H.
  elim H.
Qed.



(* Ej 5.1 *)
Theorem e51: (A->B)-> ~B-> ~A.
Proof.
  intro G.
  intro H.
  intro I.
  absurd B.
  assumption.
  apply G.
  assumption.
Qed.

(* Ej 5.2 *)
Theorem e52: ~(A/\~A).
Proof.
  intro G.
  elim G.
  intro H.
  intro I.
  absurd A.
  assumption.
  assumption.
Qed.

(* Ej 5.3 *)
Theorem e53: (A->B)-> ~(A/\~B).
Proof.
  intro G.
  intro I.
  elim I.
  intros.
  absurd B.
  assumption.
  apply G.
  assumption.
Qed.

(* Ej 5.4 *)
Theorem e54: (A/\B)->~(A->~B).
Proof.
  intro G.
  intro H.
  elim G.
  intros.
  absurd B.
  apply H.
  assumption.
  assumption.
Qed.

(* Ej 5.5 *)
Theorem e55: (~A /\ ~~A) -> False.
Proof.
  intro G.
  elim G.
  intros.
  absurd A.
  assumption.
  elim H0.
  assumption.
Qed.



(* Ej 6.1 *)
Theorem e61: (A\/B) -> ~(~A/\~B).
Proof.
  intro G.
  intro H.
  elim H.
  intros.
  elim G.
  apply H0.
  apply H1.
Qed.

(* Ej 6.2 *)
Theorem e62: A\/B <-> B\/A.
Proof.
  unfold iff.
  split.
  intro G.
  elim G.
  intro H.
  right.
  assumption.
  intro H.
  left.
  assumption.
  intro G.
  elim G.
  intro H.
  right.
  assumption.
  intro H.
  left.
  assumption.
Qed.

(* Ej 6.3 *)
Theorem e63: A\/B -> ((A->B)->B).
Proof.
  intro G.
  intros.
  elim G.
  assumption.
  intro.
  assumption.
Qed.

End P1.



Section Logica_Clasica.
Variables A B C: Prop.

(* Ej 7.1 *)
Theorem e71: A \/ ~A -> ~~A->A.
Proof.
  intros.
  elim H.
  intro I.
  assumption.
  intro I.
  elim H0.
  assumption.
Qed.

(* Ej 7.2 *)
Theorem e72: A\/~A -> ((A->B) \/ (B->A)).
Proof.
  intros.
  elim H.
  intros.
  right.
  intro I.
  assumption.
  intro I.
  left.
  intro J.
  absurd A.
  assumption.
  assumption.
Qed.


(* Ej 7.3 *)
Theorem e73: (A \/ ~A) -> ~(A /\ B) -> ~A \/ ~B.
Proof.
  intros.
  elim H.
  intro.
  right.
  intro.
  unfold not in H0.
  apply H0.
  split.
  assumption.
  assumption.
  intro.
  left.
  assumption.
 
Qed.



Require Import Classical.
Check classic.

(* Ej 8.1 *)
Theorem e81: ~~A->A.
Proof.
  intro.
  elim (classic (A)).
  intro.
  assumption.
  intro.
  elim H.
  assumption.
Qed.

(* Ej 8.2 *)
Theorem e82: (A->B)\/(B ->A).
Proof.
  elim (classic (A)).
  intros.
  right.
  intro.
  assumption.
  intro.
  left.
  intro.
  absurd A.
  assumption.
  assumption.
Qed.

(* Ej 8.3 *)
Theorem e83: ~(A/\B)-> ~A \/ ~B.
Proof.
  intro.
  elim (classic (A)).
  intro.
  right.
  intro.
  unfold not in H.
  apply H.
  split.
  assumption.
  assumption.
  intro.
  left.
  assumption.
Qed.


End Logica_Clasica.

Section ejercicio10.
(* Ej 10 *)
(* Definicion *)
Variable E:Prop.   (* Es escoces *)
Variable MR:Prop.  (* Usa medias rojas *)
Variable K: Prop.  (* Usa kilt *)
Variable C: Prop.  (* Esta casado *)
Variable SD: Prop. (* Sale los domingos *)

Hypothesis Regla1: ~E -> MR.
Hypothesis Regla2: K \/ ~MR.
Hypothesis Regla3: C -> ~SD.
Hypothesis Regla4: SD <-> E.
Hypothesis Regla5: K -> E /\ C.
Hypothesis Regla6: E -> K.

Theorem ej10: False.
Proof.
  unfold iff in Regla4.

  elim Regla2.
  intro.
  apply Regla3.

  elim Regla5.
  intros.
  assumption.
  assumption.
  
  elim Regla4.
  intros.
  apply H1.

  elim Regla5.
  intros.

  assumption.

  assumption.

  intro.
  apply H.
  apply Regla1.
  intro.
  elim Regla4.
  intros.
  apply Regla3.

  elim Regla5.
  
  intros.
  assumption.
  
  apply Regla6.
  assumption.

  apply H2.
  assumption.  
Qed.


End ejercicio10.


Section ejercicio11.

(* Ej 11 *)
(* Definiciones *)
Variable PF:Prop. (*el paciente tiene fiebre*)
Variable PA:Prop. (*el paciente tiene piel amarillenta*)
Variable PH:Prop. (*el paciente tiene hepatitis*)
Variable PR:Prop. (*el paciente tiene rubeola*)

Hypothesis Regla1: PF \/ PA -> PH \/ PR.
Hypothesis Regla2: PR -> PF.
Hypothesis Regla3: PH /\ ~PR -> PA.


Theorem ej11: (~PA /\ PF) -> PR.
Proof.
  intro.
  elim H.
  intros.

  assert (~ (PH /\ ~ PR)).
  intro.
  elim H2.
  intros.
  apply H0.
  apply Regla3.
  split.
  assumption.
  assumption.

  apply e83 in H2.
  
  elim H2.
  intro.

  elim Regla1.

  intro.
  contradiction.
  
  intro.
  assumption.
  
  left.
  assumption.
  
  intro.
  apply e81 in H3.
  assumption.
Qed.

End ejercicio11.




