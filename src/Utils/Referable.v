Require Import List.
Require Import Tactics.
Require Import Lists.
Require Import Nat.
Require Import ZArith.
Import ListNotations.
#[export] Hint Constructors NoDup.


Definition var := nat.

Fixpoint find_w (n: nat) (key: var) (l: list var) :=
  match l with
    | [] => None
    | (x :: xs) => if key =? x then Some n else find_w (S n) key xs
  end.

Definition find_where := (find_w 0).



Section Ref.

  Class Referable (A: Type) :={
                               ref : A -> var;
                               find: var -> list A -> option A := 
                                 let fix f (key: var) (l: list A) :=
                                     match l with
                                     | [] => None
                                     | (x :: xs) => if key =? (ref x) 
                                                   then Some x
                                                   else f key xs
                                     end in f;
                             }.



  Lemma find_deterministic: forall `{R: Referable} d (k1: var) x1 x2,
      find k1 d = x1 ->
      find k1 d = x2 ->
      x1 = x2.
  Proof with eauto.
    intros.
    destruct x1, x2; destruct (@find A) in *; auto with rewrite; crush.
  Qed.
End Ref.

Module Refs.

  Definition refs {A: Type} {R: Referable A} (x: list A) := (map ref x).

  #[export] Hint Rewrite map_length.
  Lemma refs_lenght: forall  (A: Type) (R: @Referable A) xs,
      length (refs xs) = length xs.
  Proof. unfold refs; crush. Qed.
  #[export] Hint Rewrite refs_lenght.

End Refs.
Export Refs.


Lemma find_ref_inv: forall `{R: Referable} d (k: var) x,
    find k d = Some x ->
    ref x = k.
Proof.
  intros. induction d.
  -
    simpl in H. inversion H.
  -
    simpl in H. 
    case_eq  (k =? ref a);intros. 
    +
      rewrite H0 in H. 
      apply Nat.eqb_eq in H0. subst k.
      f_equal.
      inversion H. auto.
    +
      rewrite H0 in H.
      apply IHd;auto.
Qed.


Lemma find_in: forall `{R: Referable} var xs x,
    find var xs = Some x ->
    In x xs.
Proof.
  intros. induction xs.
  -
    simpl in H. inversion H.
  -
    simpl in H. 
    case_eq (var0 =? ref a);intros.
    +
      rewrite H0 in H.
      simpl. left.
      inversion H. auto.
    +   
      rewrite H0 in H.
      simpl. right.
      apply IHxs. auto.
Qed.

Lemma Forall_find: forall `{R: Referable} P xs var x,
    Forall P xs ->
    find var xs = Some x ->
    P x.
Proof.
  intros. 
  eapply Forall_forall in H; eauto. 
  eapply find_in; eauto.
Qed.

Lemma in_imp_inref: forall {T} {H: Referable T} (xs:list T) x,
    In x xs ->
    In (ref x) (refs xs).
Proof.
  induction xs; crush.
Qed.

Lemma ref_noDup_nth_error: forall {T} {H: Referable T} (xs:list T) i i1 x x1,
    nth_error xs i = Some x ->
    nth_error xs i1 = Some x1 ->
    NoDup (refs xs) ->
    ref x = ref x1 ->
    x = x1.
Proof.
  induction xs; crush.
  destruct i; destruct i1; simpl in *; crush.
  rewrite H3 in H2. inversion H2. subst. clear H3.
  false. apply H5. apply nth_error_In in H1. apply in_imp_inref; eauto.
  rewrite <- H3 in H2. inversion H2. subst. false.
  apply H5. apply nth_error_In in H0. apply in_imp_inref; eauto.
  inversion H2.
  eapply IHxs; eauto.
Qed.