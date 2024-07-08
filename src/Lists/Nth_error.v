Require Import List.
Require Import Tactics.
Require Import Lists.snoc.

Import ListNotations.

Lemma none_ex_Some: forall {A: Type} x,
  x <> @None A ->
  exists x', x = Some x'.
Proof.
  intros. induction x.
  exists a; auto.
  exfalso; auto.
Qed.

Lemma nth_error_nil : forall (A: Type) n,
  nth_error [] n = @None A.
Proof.
  intros; induction n; auto.
Qed.
#[export] Hint Rewrite nth_error_nil.

Lemma nth_error_Some' : forall {A: Type} (l: list A)  n,
  n < List.length l ->
  exists x, nth_error l n = Some x.
Proof.
  intros.
  apply <- nth_error_Some in H.
  apply none_ex_Some; auto.
Qed.

Lemma nth_error_In': forall {A:Type} (l: list A) x,
  In x l ->
  exists n, nth_error l n = Some x.
Proof.
  intros.
  induction l. simpl in H; contradiction.
  simpl in *. destruct H.
  rewrite H; simpl. exists 0; auto.
  destruct IHl as [n]; auto.
  exists (S n); auto.
Qed.


Lemma nth_error_app_app : forall A (l l': list A) n x,
  nth_error l n = Some x ->
  nth_error (l ++ l') n = Some x.
Proof.
  intros. rewrite nth_error_app1; auto. 
  apply nth_error_Some. intro.
  rewrite H in H0; inversion H0.
Qed.

Lemma nth_error_same_len : forall {A B:Type} (l:list A) (l': list B) n x,
  length l = length l' ->
  nth_error l n = Some x ->
  exists y, nth_error l' n = Some y.
Proof.
  induction l, l'; intros.
  rewrite nth_error_nil in H0; inversion H0.
  simpl in H; inversion H.
  simpl in H; inversion H.
  intros; simpl in *.
  case n in *. exists b; auto.
  simpl in *.
  eapply IHl; eauto.
Qed.

Lemma nth_error_dec : forall {A: Type} l n,
  {x | nth_error l n = Some x} + {nth_error l n = @None A}.
Proof.
  intros; generalize dependent n.
  induction l.
  right; apply nth_error_nil. intro.
  case n in *. left; exists a; auto.
  simpl. apply IHl.
Defined.

Lemma nth_error_fst: forall {A: Type} {a: A} l i,
  NoDup (a::l) ->
  nth_error (a::l) i = Some a ->
  i = 0.
Proof.
  intros.
  induction i. auto.
  inversion H. subst. simpl in H0.
  apply nth_error_In in H0. contradiction.
Qed.

Lemma nth_error_same: forall {A: Type} (xs xs': list A),
  (forall i, nth_error xs i = nth_error xs' i) ->
  xs = xs'.
Proof.
  induction xs, xs'; crush. 
  lets ?H: H 0; inversion H0.
  lets ?H: H 0; inversion H0.
  lets ?H: H 0. crush. apply f_equal. apply IHxs. intro i.
  lets ?H: H (S i). crush.
Qed.

Lemma nth_error_split: forall {A: Type} (xs: list A) i x,  
  nth_error xs i = Some x ->
  xs = firstn i xs ++ x :: skipn (S i) xs.
Proof.
  induction xs; intros. rewrite nth_error_nil in H; inversion H.
  destruct i; simpl in *. inversion H. reflexivity.
  apply f_equal.
  eapply IHxs; eauto.
Qed.



Lemma env_extend: forall (T:Type) (Fi:T) fs i x, nth_error fs i = Some Fi -> nth_error (fs :> x) i = Some Fi.
Proof.
  intros.
  generalize dependent fs.
  induction i.
  -
    intros.
    destruct fs.
    +
      simpl in H.
      inversion H.
    +
      simpl in H.
      simpl.
      assumption.
  -
    intros.
    (*We need to figure out the approach to use "i", so we must reduce S i to i*)
    destruct fs.
    +
      simpl in H.
      inversion H.
    +
      simpl in H.
      simpl. auto.
Qed.

Lemma env_weaken: forall (T:Type) (Fi:T) fs i x, nth_error fs i = Some Fi -> nth_error (fs ++ x) i = Some Fi.
Proof.
  intros.
  generalize dependent fs.
  induction x.
  -
    intros.
    simpl in *.
    (* rewrite nth_nil in H.
    inversion H. *)
    rewrite app_nil_r.
    assumption.
  -
    intros.
    simpl.
    rewrite snoc_app. 
    (* crush. *)
    apply IHx.
    apply env_extend;auto.
Qed.

Lemma nth_error_app {X:Type} (l r:list X) (i:nat) (x:X) :
  nth_error (l ++ r) i = Some x ->
  nth_error l i = Some x \/ exists j, i = length l + j /\ nth_error r j = Some x.
revert i. induction l as [|y l IH].
- simpl. intros i H1. right. exists i. tauto.
- intros [|i]; simpl.
  + intros H1. now left.
  + intros H1. destruct (IH i H1) as [H2|[j [H2 H3]]].
    * now left.
    * { right. exists j. split.
        - congruence.
        - exact H3.
      }
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
      simpl in H1.
      crush.
    +
      simpl in H;simpl in H0.
      eapply IHForall;eauto.
Qed.

Lemma f_morp: forall (A:Type) (B:Type) L (l:A) i (f:A->B), nth_error L i = Some l -> nth_error (map f L) i = Some (f l).
Proof.
  intros.
  generalize dependent i.
  induction L;crush;
  induction i;crush.
Qed.

Lemma nth_eq: forall (A:Type) (l1:list A) l2, length l1 = length l2 -> (forall i, nth_error l1 i = nth_error l2 i) -> l1 = l2.
Proof.
  intros. generalize dependent l2. induction l1;intros.
  - destruct l2. auto. simpl in H. inversion H.
  - destruct l2. inversion H. simpl in H. inversion H. f_equal. 
    + pose proof (H0 0) as HH. simpl in HH. inversion HH. auto.
    + assert (forall i : nat, nth_error l1 i = nth_error l2 i). intros. pose proof (H0 (S i)) as HH. simpl in HH. auto. apply IHl1 in H2;auto.
Qed.

Lemma forall_nth_error: forall (A:Type) P es n (x:A),
(Forall P es) -> nth_error es n = Some x -> P x.
Proof.
    intros.
    generalize dependent n.
    induction es.
    -
    intros.
    induction n.
    +
    simpl in H0.
    discriminate.
    +
    simpl in H0.
    discriminate.
    -
    intros.
    induction n.
    simpl in H0.
    inversion H0.
    inversion H.
    crush.
    eapply IHes.
    inversion H.
    auto.
    simpl in H0.
    apply H0.
Qed.