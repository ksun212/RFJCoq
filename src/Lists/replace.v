Require Import List.
Require Import ZArith.
Require Import Tactics.

Fixpoint replace {A : Type} (l : list A)  (i : nat) (v : A) := 
  match l with 
  | nil => nil
  | a :: l1 => match i with 
               |    0 => v :: l1 
               | S i1 => a :: replace l1 i1 v 
               end 
  end.

Lemma replace_just_replace: forall {A:Type} Ts i (Ti':A),
i < length Ts -> 
nth_error (replace Ts i Ti') i = Some Ti'/\(forall j : nat, j <> i -> nth_error Ts j = nth_error (replace Ts i Ti') j).
Proof.
  intros.
  generalize dependent i.
  induction Ts.
  -
    intros.
    destruct i.
    +
      simpl in H.
      apply lt_0_neq in H.
      contradiction.
    +
      simpl in H.
      unfold lt in H.
      forwards: (le_n_0_eq (S (S i)) H).
      discriminate.
  -
    intros.
    destruct i.
    +
      simpl.
      constructor.
      reflexivity.
      intros.
      destruct j.
      contradiction.
      simpl.
      reflexivity.
    +
      simpl.
      simpl in H.
      lets: (lt_S_n i (length Ts) H).
      forwards: (IHTs i H0).
      destruct H1.
      constructor;auto.
      intros.
      destruct j.
      simpl.
      reflexivity.
      simpl.
      apply H2.
      unfold not.
      intros.
      rewrite H4 in H3.
      unfold not in H3.
      crush.
Qed.
Lemma replace_length_eq: forall (A:Type) (es:list A) i ei', length es = length (replace es i ei').
Proof.
  intros. generalize dependent i. induction es;intros.
  -
    auto.
  -
    simpl. destruct i. simpl. f_equal.
    simpl. rewrite IHes with i. auto.
Qed. 