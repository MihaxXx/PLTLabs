From LF Require Export Basics.
From LF Require Export Induction.
From LF Require Export Lists.

(*1 балл*)
Theorem mult_comm : forall n m : nat,
  n * m = m * n.
Proof.
  intros. induction n as [|m'].
  - simpl. rewrite mult_0_r. reflexivity. 
  - simpl. rewrite IHm'. 
    assert (H: forall x y, x + x * y = x * S y).
    { intros. induction x as [|x']. 
      - reflexivity. 
      - simpl. rewrite <- IHx'. rewrite plus_swap. reflexivity. }
    rewrite H. reflexivity. 
Qed.

(*2 балл*)
Theorem mult_plus_distr_l : forall n m p : nat,
 p* (n + m)  = (p* n) + (p * m).
Proof.
intros n m p.
induction p.
reflexivity.
simpl.
rewrite IHp.
rewrite<- plus_assoc.
pattern (m + (p * n + p * m)).
rewrite plus_assoc.
pattern (m + p * n).
rewrite plus_comm.
rewrite plus_assoc.
rewrite plus_assoc.
rewrite plus_assoc.
reflexivity.
Qed.


(*3 балла*)
Lemma plusCrazy : forall m n p q : nat,
                  plus m (plus n (plus p q)) = plus n (plus (plus q m) p).
Proof.
  intros m n p q.
  + rewrite plus_swap. replace (m+(p+q)) with (q+m+p). {reflexivity. } rewrite plus_comm.
    replace (q+m) with (m+q). { rewrite plus_swap. reflexivity. } rewrite plus_comm.
    reflexivity.
Qed.

(*4 балла*)
Theorem mult_S_1 : forall n m : nat,   m = S n -> mult m (plus 1 n) = mult m m.
Proof.
  intros n m.
  intros H.
  rewrite -> plus_1_l.
  rewrite <- H.
  reflexivity. Qed.

(*Дополнительно*)
Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
    | [] => []
    | h :: t =>
        match h with
          | 0 => nonzeros t
          | nz => nz :: (nonzeros t)
        end
  end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof.
  reflexivity. Qed.



