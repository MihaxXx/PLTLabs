From LF Require Export Basics.
From LF Require Export Logic.
Require Import PeanoNat.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
Notation "~ x" := (not x) : type_scope.

Lemma lma (P:Prop) : ~(P /\ ~P).
Proof.
  unfold not.
  intros H.
  destruct H as [p].
  apply H.
  apply p.
Qed.

Lemma lma' (P Q:Prop) : ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  unfold not.
  intros H.
  constructor.
  - intro p.
    apply H.
    left.
    apply p.
  - intro q.
    apply H.
    right.
    apply q.
Qed.

(*1 - 1 балл*)
Theorem excluded_middle_irrefutableKR: forall (P : Prop), ~~(P \/ ~ P).
Proof.
intros P H.
  apply lma' in H.
  apply lma in H.
  apply H.
Qed.

(*2 - 0.5 баллов*)
Theorem all_imp_ist A (P Q: A -> Prop): 
  (forall x: A, P x -> Q x) -> (forall y, P y) -> forall z, Q z. 
Proof.
Admitted.

(*3 - 1 балл*)
Theorem or_distributes_over_and_2 P Q R :
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
    intros. inversion H as [[HP|HQ] [HP2|HR]].
    apply or_introl. apply HP.
    apply or_introl. apply HP.
    apply or_introl. apply HP2.
    apply or_intror. split. apply HQ. apply HR.
Qed.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(*4 - 0.5 баллов*)
(*В примерах (Example) заменить "A" на функцию, которая позволит из данного (короткого)
списка получить итоговый (длинный) список)*)
Fixpoint map {X Y: Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.
Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X)
                   : (list Y):=
  match l with
  | []     => []
  | h :: t =>  (f h) ++  (flat_map f t)
  end.

Example test_flat_map':
  flat_map (fun n => [n;n;n;n]) [1;5;4]
  = [1; 1; 1; 1; 5; 5; 5; 5; 4; 4; 4; 4].
Proof. reflexivity. Qed.

Example test_flat_map'':
  flat_map (fun n => [n;n]) [8;10;15;2]
  = [8; 8; 10; 10; 15; 15; 2; 2].
Proof. reflexivity. Qed.

Require Import Classical_Prop.

Definition peirce_law := forall P Q: Prop, ((P -> Q) -> P) -> P.
Definition classic := forall P:Prop,   ~~P  ->  P.
Definition peirce := peirce_law.
Definition double_neg := forall P: Prop, ~ ~ P -> P.
Definition excluded_middle := forall P: Prop, P \/ ~P.
Definition de_morgan_not_and_not := forall P Q: Prop, ~ ( ~P /\ ~Q) -> P \/ Q.
Definition implies_to_or := forall P Q: Prop, (P -> Q) -> (~P \/ Q).

(*5 - 2 балла*)
(*Используя приведенные выше определения доказать теорему*)
Theorem classic_implies_demorgan : classic -> de_morgan_not_and_not.
Proof.
unfold classic, de_morgan_not_and_not.
intro Classic. intros P Q. unfold not.
intro nan. apply Classic. unfold not.
intro double_neg. apply nan. 
split.
 intro. apply double_neg. left. assumption.
 intro. apply double_neg. right. assumption.
Qed.

(*6 - 2 балла*)
(*Используя приведенные выше определения доказать теорему*)
Theorem demorgan_implies_exclude : de_morgan_not_and_not -> excluded_middle.
Proof.
unfold de_morgan_not_and_not, excluded_middle.
intros Demogran P. apply Demogran. unfold not. intro.
inversion H. contradiction.
Qed.






