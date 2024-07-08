(*This file largely follows the file with the same name in Michael H. Borkowski's mechanization of refinement types*)

Require Import Arith.
Require Import Crush.
Require Import Lists.
Require Import Lia.

Require Import Definitions.Syntax.
Require Import Definitions.Names.



(*---------------Basic Properties of the Syntax---------------*)

Lemma islc_at_weaken : (forall  (e : expr) (j j' : index),
    j <= j' -> isLC_at j e -> isLC_at j' e ) /\ ((
  forall (t : type) (j j' : index),
    j <= j' -> isLCT_at j t -> isLCT_at j' t ) /\ (
  forall (ps : preds) (j j' : index),
    j <= j' -> isLCP_at j ps -> isLCP_at j' ps ))%type.
Proof. 
  apply (syntax_mutind'
  (fun e : expr => forall (j j' : index),
       j <= j' -> isLC_at j e -> isLC_at j' e)
  (fun t : type => forall (j j' : index),
       j <= j' -> isLCT_at j t -> isLCT_at j' t)   
  (fun ps : preds => forall (j j' : index),
       j <= j' -> isLCP_at j ps -> isLCP_at j' ps));
  simpl; try reflexivity.
  
  - (* BV i *) simpl. intros i j j' j_le Hjk. 
      apply Nat.lt_le_trans with j. all : assumption.
  - intros. apply H with j; auto.
  - intros. destruct H2. constructor;eauto.
  -
    intros. destruct H2. constructor;eauto.
  - intros. eauto.
  - intros. induction l. auto. inversion H1. inversion H. constructor. eapply H6;eauto. apply IHl;auto.
  - intros. destruct H2. constructor;eauto. apply H0 with (j+1);auto. lia.
  -
    intros.
    apply H with (j + 1). lia. auto.
  -
    intros. destruct H2. constructor;eauto.
Qed.

Lemma aux1: forall l j x v_x, Forall (fun e => (isLC_at j (subFV x v_x e))) l -> (fix f (es' : [expr]) : Prop :=
match es' with
| nil => True
| (e :: es'')%list => isLC_at j e /\ f es''
end)
((fix f (es' : [expr]) : [expr] :=
   match es' with
   | nil => nil
   | (e :: es'')%list => (subFV x v_x e :: f es'')%list
   end) l).
Proof.
  intros.
  induction l;auto.
  inversion H.
  constructor.
  auto.
  apply IHl;auto.
Qed.


Lemma aux2:  forall l j v_x x, Forall (fun e : expr =>
isLC v_x /\ isLC_at j e) l  -> 
Forall (fun e : expr =>
isLC v_x -> isLC_at j e -> isLC_at j (subFV x v_x e)) l -> Forall (fun e : expr => isLC_at j (subFV x v_x e)) l.
Proof.
  intros.
  induction l.
  apply Forall_nil.

  inversion H.
  inversion H0.
  apply Forall_cons. 
  apply H7. apply H3. apply H3.
  apply IHl. apply H4. apply H8.
Qed.
Lemma forall_conj1: forall v_x j l, isLC v_x -> Forall (isLC_at j) l -> Forall (fun e : expr => isLC v_x /\ isLC_at j e) l.
Proof.
  intros.
  induction l.
  apply Forall_nil.
  inversion H0.
  apply Forall_cons.
  constructor;auto.
  apply IHl;auto.
Qed.
Lemma islc_at_subFV : (forall  (e : expr) (j : index) (x : vname) (v_x : expr),
    isLC v_x -> isLC_at j e -> isLC_at j (subFV x v_x e )) /\ ((
  forall (t : type) (j : index) (x : vname) (v_x : expr),
    isLC v_x -> isLCT_at j t -> isLCT_at j (tsubFV x v_x t ) ) /\ (
  forall (ps : preds) (j : index) (x : vname) (v_x : expr),
    isLC v_x -> isLCP_at j ps -> isLCP_at j (psubFV x v_x ps ) ))%type.
Proof. 
  apply (syntax_mutind'
  (fun e : expr => forall (j : index) (x : vname) (v_x : expr),
    isLC v_x -> isLC_at j e -> isLC_at j (subFV x v_x e ))
  (fun t : type => forall (j : index) (x : vname) (v_x : expr),
    isLC v_x -> isLCT_at j t -> isLCT_at j (tsubFV x v_x t ))   
  (fun ps : preds => forall (j : index) (x : vname) (v_x : expr),
    isLC v_x -> isLCP_at j ps -> isLCP_at j (psubFV x v_x ps )));
  simpl; try reflexivity. 
  - intros. assumption.
  - intros. destruct (x0 =? x). 
      { apply islc_at_weaken with 0; try apply Nat.le_0_l. assumption. }
      { reflexivity. }
  - intros. apply H. all : assumption.
  - intros. 
      destruct H2 as [He1 He2]. split.
      { apply H.  all : assumption. } 
      { apply H0. all : assumption. }
  - 
      intros. destruct H2 as [He1 He2]. split.
      { apply H.  all : assumption. } 
      { apply H0. all : assumption. }
  - intros. eauto.

  -  intros.
      apply aux1.
      apply aux2.
      apply forall_conj1;auto. apply Forall_fun. auto.
      induction l. apply Forall_nil. inversion H. apply Forall_cons. apply H4. apply IHl. apply H5. destruct H1. apply H6.
  - intros. destruct H2. constructor; eauto.
  - intros. destruct b; apply H. all : assumption. 

  - intros.  destruct H2 as [Hp Hps]. split.
      { apply H . all : assumption. }
      { apply H0. all : assumption. }
Qed.

Lemma islcp_at_strengthen : forall (j : index) (ps : preds) (ts : preds),
    j >= 1 -> isLCP_at j ps -> isLCP_at 1 ts -> isLCP_at j (strengthen ps ts ).
Proof. intros j. induction ps. all : simpl.
  - intros. apply islc_at_weaken with 1. 
      { assumption. } { assumption. }
  - intros. destruct H0 as [Hp Hps]. split.
      { assumption. } { apply IHps. all : assumption. }
  Qed.



Lemma lt_S : forall (j : index), j < j + 1.
Proof. intro j. rewrite <- Nat.add_0_r at 1. apply Nat.add_lt_mono_l. 
  unfold lt. trivial. Qed.

Lemma tighten_lt : forall (i j : index),
    i < j + 1  ->  j <> i  ->  i < j.
Proof. intros i j Hlt Hneq. rewrite Nat.add_comm in Hlt. simpl in Hlt.  
  unfold lt in Hlt. unfold lt.
  apply not_eq_S in Hneq. apply Nat.le_succ_r in Hlt. 
  destruct Hlt. { assumption. } 
                { symmetry in H; contradiction. } 
  Qed.

Lemma loosen_lt : forall (i j : index),
    i < j -> i < j + 1. 
Proof. intros i j Hlt. assert (j < j + 1). apply lt_S. 
  apply Nat.lt_trans with j; assumption. Qed. 

Lemma beq_lt_S : forall ( i j : index ),
  (j =? i) = true  ->  i < j + 1.
Proof. intros. apply Nat.eqb_eq in H. rewrite H. apply lt_S. Qed.

Lemma islc_at_before_open_at : (forall (e : expr) (j : index) (y : vname),
    isLC_at (j+1) e -> isLC_at j (open_at j y e) ) /\ ((
  forall (t : type) (j : index) (y : vname),
    isLCT_at (j+1) t -> isLCT_at j (openT_at j y t)  ) /\ (
  forall (ps : preds) (j : index) (y : vname),
    isLCP_at (j+1) ps -> isLCP_at j (openP_at j y ps))).
Proof.
apply (syntax_mutind'
  (fun e : expr => forall (j : index) (y : vname),
    isLC_at (j+1) e -> isLC_at j (open_at j y e))
  (fun t : type => forall (j : index) (y : vname),
    isLCT_at (j+1) t -> isLCT_at j (openT_at j y t))   
  (fun ps : preds => forall  (j : index) (y : vname),
    isLCP_at (j+1) ps -> isLCP_at j (openP_at j y ps))); 
  simpl; try reflexivity;
  (* one IH *)  try (intros; apply H; assumption);
  (* two IHs *) try (intros; destruct H1; split;
    apply H || apply H0; assumption).
  - (* BV i *) intros i j k y. destruct (j =? i) eqn:E; simpl.
        { reflexivity. } 
        { apply Nat.eqb_neq in E. apply tighten_lt; assumption. }
  -
   (* If e0 e1 e2 *) intros.
    apply Forall_fun.
    induction l.
    + apply Forall_nil.
    + inversion H. destruct H0. apply Forall_cons. apply H3. apply H0. apply IHl. apply H4. apply H5.
Qed.
Lemma l3: forall j l y, Forall (fun e : expr => isLC_at j (open_at j y e)) l ->
Forall (fun e : expr => isLC_at j (open_at j y e) -> isLC_at (j + 1) e) l -> Forall (isLC_at (j + 1)) l.
Proof.
  intros.
  induction l.
  apply Forall_nil.
  inversion H. inversion H0.
  apply Forall_cons.
  eapply H7. apply H3.
  apply IHl. apply H4. apply H8.
Qed.
(* -- In particular, isLC (unbind y e) => isLC_at 1 0 e *)
Lemma islc_at_after_open_at : (forall (e : expr) (j : index) (y : vname),
  isLC_at j (open_at j y e) -> isLC_at (j+1) e ) /\ ((
forall (t : type) (j : index) (y : vname),
  isLCT_at j (openT_at j y t) -> isLCT_at (j+1) t ) /\ (
forall (ps : preds) (j : index) (y : vname),
  isLCP_at j (openP_at j y ps) -> isLCP_at (j+1) ps )).
Proof.
apply (syntax_mutind'
  (fun e : expr => forall (j : index) (y : vname),
    isLC_at j (open_at j y e) -> isLC_at (j+1) e)
  (fun t : type => forall (j : index) (y : vname),
    isLCT_at j (openT_at j y t) -> isLCT_at (j+1) t)   
  (fun ps : preds => forall  (j : index) (y : vname),
    isLCP_at j (openP_at j y ps) -> isLCP_at (j+1) ps)); 
  simpl; try reflexivity;
  (* one IH *)  try (intros; apply H with y; assumption);
  (* two IHs *) try (intros; destruct H1; split;
    apply H with y || apply H0 with y; assumption).
  - (* BV i *) intros. destruct (j =? i) eqn:E.
      { apply beq_lt_S. assumption. }
      { simpl in H. apply loosen_lt. assumption. }
  - (* If e0 e1 e2 *) intros.
    apply Forall_fun.
    apply l3 with y.
    induction l.
    +
      apply Forall_nil.
    +
      destruct H0.
      inversion H. 
      apply Forall_cons.
      apply H0.
      apply IHl. apply H5. apply H1.
    +
      induction l. apply Forall_nil. inversion H. apply Forall_cons. apply H3. apply IHl. apply H4. destruct H0. apply H5.
Qed.


Lemma value_lc: forall v_y, isValue v_y -> isLC v_y.
Proof.
  intros.
  induction v_y using expr_ind'; intros; simpl;auto;intros;try contradiction.
  unfold isLC.
  simpl.
  induction l. auto.
  inversion H0. simpl in H. destruct H. 
  constructor. 
  apply H3. apply H.
  apply IHl. apply H4.
  apply H5.
Qed. 

Lemma value_closed: forall v_y, isValue v_y -> fv v_y = empty.
Proof.
  intros.
  induction v_y using expr_ind'; intros; simpl;auto;intros;try contradiction.
  induction l. auto.
  inversion H0. simpl in H. destruct H.
  assert (fv a = empty). apply H3. apply H.
  assert (((fix f (es' : [expr]) : ListSet.set vname :=
  match es' with
  | nil => empty
  | e :: es'' => union (fv e) (f es'')
  end) l) = empty). apply IHl. apply H4. simpl. auto.
  rewrite H6. rewrite H7. simpl. auto.
Qed. 

Lemma value_lc_at: forall v_y n, isValue v_y -> isLC_at n v_y.
Proof.
  intros.
  apply islc_at_weaken with 0. crush. 
  apply value_lc;auto.
Qed. 
Lemma value_lc_forall: forall es, Forall isValue es -> Forall isLC es.
Proof.
  intros.
  induction es.
  apply Forall_nil.
  inversion H.
  apply Forall_cons.
  apply value_lc;auto.
  apply IHes;auto. 
Qed. 


