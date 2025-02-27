
Require Import List.
Require Import Lists.Nth_error.
Require Import RelationClasses.
Require Import Tactics.
(** Forall for two-fold relations **)

#[export] Hint Constructors Forall2.
Section Two_predicate.


Variables A B: Type.
Variable P: A -> B -> Prop.

Lemma Forall2_len: forall xs ys,
  Forall2 P xs ys -> length xs = length ys.
Proof.
  intros.
  induction H. auto.
  simpl. rewrite IHForall2; auto.
Qed.

Lemma Forall2_nth_error(l:list A)(l': list B): forall n x,
  Forall2 P l l' -> 
  nth_error l n = Some x ->
  exists y, nth_error l' n = Some y.
Proof.
  intros. generalize dependent n.
  induction H.
  intros.
  rewrite nth_error_nil in H0; inversion H0.
  intros.
  case n in *.
  simpl; exists y; auto.
  simpl in *.
  apply IHForall2; auto.
Qed.

Lemma Forall2_nth_error'(l:list A)(l': list B): forall n x,
  Forall2 P l l' -> 
  nth_error l' n = Some x ->
  exists y, nth_error l n = Some y.
Proof.
  intros. generalize dependent n.
  induction H.
  intros.
  rewrite nth_error_nil in H0; inversion H0.
  intros.
  case n in *.
  simpl. exists x0; auto.
  simpl in *.
  apply IHForall2; auto.
Qed.

Lemma Forall2_forall (l:list A)(l': list B): forall n x y,
  Forall2 P l l' -> 
    nth_error l  n = Some x ->
    nth_error l' n = Some y -> P x y.
Proof.
  intros n x y H.
  generalize dependent n.
  induction H.
  intros.
  rewrite nth_error_nil in H. inversion H.
  intros.
  case n in *; simpl in H1, H2. inversion H1. inversion H2. rewrite <- H4, <- H5; auto.
  apply IHForall2 with n; auto.
Qed.

Lemma Forall2_exi: forall (Q: B -> B -> Prop) xs ys,
  Forall2 (fun x y => exists y', Q y' y /\ P x y') xs ys ->
  exists ys', Forall2 Q ys' ys /\ Forall2 P xs ys'.
Proof.
  intros. induction H. exists (@nil B); split; constructor.
  destruct H as [z]. destruct H. destruct IHForall2 as [zs]. destruct H2.
  exists (z :: zs). split; constructor; auto.
Qed.

Lemma Forall2_map: forall (f: A -> A) xs ys,  
  Forall2 (fun x => P (f x)) xs ys ->
  Forall2 P (map f xs) ys.
Proof.
  intros. induction H. simpl; auto.
  simpl in *. constructor; auto.
Qed.


End Two_predicate.


Lemma Forall2_trans: forall (A: Type) (P: A -> A -> Prop) xs ys zs,
  Transitive P ->
  Forall2 P xs ys ->
  Forall2 P ys zs ->
  Forall2 P xs zs.
Proof.
  induction xs, ys, zs; intros; 
  match goal with
  | [ |- Forall2 _ nil nil ] => apply Forall2_nil
  | [ H : Forall2 _ nil (?a :: ?b) |- _] => inversion H
  | [ H : Forall2 _ (?a :: ?b) nil |- _] => inversion H
  | [ |- _ ] => idtac
  end.
  constructor; inverts H0; inverts H1. transitivity a0; auto.
  eapply IHxs; eauto.
Qed.


Lemma forall2_corres: forall (A:Type) (B:Type) (es: list A) (Cs: list B) i ei Ci P, nth_error es i = Some ei -> nth_error Cs i = Some Ci -> Forall2 P es Cs -> P ei Ci.
Proof.
  intros.
  generalize dependent i.
  induction H1.
  -
    intros.
    induction i;simpl in H;inversion H.
  -
    intros.
    induction i.
    +
      simpl in H;simpl in H0.
      crush.
    +
      simpl in H;simpl in H0.
      eapply IHForall2;eauto.
Qed.

Lemma forall2_exists2: forall (A:Type) (B:Type) (es: list A) (Cs: list B) i ei P, nth_error es i = Some ei -> Forall2 P es Cs -> (exists Ci, nth_error Cs i = Some Ci).
Proof.
  intros.
  generalize dependent i.
  induction H0.
  -
    intros.
    induction i;simpl in H;inversion H.
  -
    intros.
    induction i.
    +
      simpl in *.
      exists y.
      reflexivity.
    +
      simpl in *.
      eapply IHForall2;eauto.
Qed.

Lemma forall2_exists1: forall (A:Type) (B:Type) (es: list A) (Cs: list B) i Ci P, nth_error Cs i = Some Ci -> Forall2 P es Cs -> (exists ei, nth_error es i = Some ei).
Proof.
  intros.
  generalize dependent i.
  induction H0.
  -
    intros.
    induction i;simpl in H;inversion H.
  -
    intros.
    induction i.
    +
      simpl in *.
      exists x.
      reflexivity.
    +
      simpl in *.
      eapply IHForall2;eauto.
Qed.

Lemma forall_corres: forall (A:Type) (es: list A) i ei P, nth_error es i = Some ei -> Forall P es -> P ei.
Proof.
  intros.
  generalize dependent i.
  induction H0.
  -
    intros.
    induction i;simpl in H;inversion H.
  -
    intros.
    induction i.
    +
      simpl in H;simpl in H0.
      crush.
    +
      simpl in H;simpl in H0.
      eapply IHForall;eauto.
Qed.


Lemma Forall_fun: forall (A:Type) P l, (Forall P l) <-> (fix f (es' : list A) : Prop :=
match es' with
| nil => True
| e :: es'' => P e /\ f es''
end) l.
Proof.
  constructor;
  intros;
  induction l;auto;
  inversion H;
  constructor;
  auto;
  apply IHl;auto.
Qed.