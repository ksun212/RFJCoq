(*This file largely follows the file with the same name in Michael H. Borkowski's mechanization of refinement types*)

Require Import Arith.
Require Import Crush.
Require Import List.
Require Import Lia.

Require Import Definitions.Syntax.
Require Import Definitions.Names.


Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasSyntax.


(*---------------Properties of the Substitution Operations---------------*)

(* Lemmas. The set of lc terms is closed under substitution. *)
Lemma subFV_lc : forall (y:vname) (v_y v: expr) (i:nat),
    isLC v_y -> isLC_at i v -> isLC_at i (subFV y v_y v).
Proof.
  intros y v_y v i val_vy val_v.
  generalize dependent i.
  induction v using expr_ind'; intros;simpl in val_v; try contradiction;
  simpl; try (destruct (Nat.eqb y x)); simpl; try assumption.
  apply islc_at_weaken with 0. apply le_0_n. 
  auto.
  apply IHv;auto.
  destruct val_v. constructor. apply IHv1. auto. apply IHv2. auto.
  destruct val_v. constructor. apply IHv1. auto. apply IHv2. auto.
  apply IHv. auto. 
  unfold isLC in *. simpl in *.
  induction l.
  auto.
  inversion H.
  destruct val_v.
  constructor.
  auto.
  apply IHl;auto.
  destruct val_v. constructor. apply IHv1. auto. apply IHv2. auto.
  Qed.
Lemma subFV_lc_forall: forall (y:vname) (v_y : expr) vs (i:nat),
isLC v_y -> Forall (isLC_at i) vs -> Forall (isLC_at i) (map (subFV y v_y) vs).
Proof.
  intros. induction vs.
  apply Forall_nil.
  inversion H0. apply Forall_cons. 
  apply subFV_lc;auto.
  apply IHvs;auto.
Qed.

(* Lemmas. The set of values is closed under substitution. *)
Lemma subFV_value : forall (y:vname) (v_y v: expr),
    isValue v_y -> isValue v -> isValue (subFV y v_y v).
Proof.
  intros y v_y v val_vy val_v. 
  induction v using expr_ind'; simpl in val_v; try contradiction;
  simpl; try (destruct (Nat.eqb y x)); simpl; try assumption.
  induction l.
  auto.
  inversion H.
  destruct val_v.
  constructor.
  auto.
  apply IHl;auto.
  Qed.


Lemma subFV_value_forall : forall (y:vname) (v_y: expr) vs,
  isValue v_y -> Forall isValue vs -> Forall isValue (map (subFV y v_y) vs).
Proof. intros y v_y vs val_vy val_v.
  induction  vs.
  apply Forall_nil.
  inversion val_v.
  apply Forall_cons. apply subFV_value;auto.
  apply IHvs; auto.
Qed.



Lemma subFV_notin : ( forall (e:expr) (x:vname) (v:expr) ,
    (*isValue v ->*) ~ Elem x (fv e) -> subFV x v e = e ) /\ ((
  forall (t:type) (x:vname) (v:expr),
    (*isValue v ->*) ~ Elem x (free t) -> tsubFV x v t = t ) /\ (
  forall (ps:preds) (x:vname) (v:expr),
    (*isValue v ->*) ~ Elem x (fvP ps) -> psubFV x v ps = ps )).
Proof.  
    apply ( syntax_mutind'
  ( fun e:expr => forall (x:vname) (v:expr) ,
      (*isValue v ->*) ~ Elem x (fv e) -> subFV x v e = e )
  ( fun t:type => forall (x:vname) (v:expr),
      (*isValue v ->*) ~ Elem x (free t) -> tsubFV x v t = t)
  ( fun ps:preds => forall (x:vname) (v:expr),
      (*isValue v ->*) ~ Elem x (fvP ps) -> psubFV x v ps = ps) )
      ; simpl; try reflexivity; intros
      ; (* 1 IH *) try ( apply f_equal; apply H )
      ; (* 2 IH *) try ( apply f_equal2; apply H || apply H0;
          apply not_elem_union_elim in H1; destruct H1; assumption )
      ; (* FV *) try (intuition; destruct (Nat.eqb x0 x) eqn:Eq;
          (apply Nat.eqb_eq in Eq; symmetry in Eq; contradiction) 
          || reflexivity )
      ; try (rewrite H;auto).
      -
        apply not_elem_union_elim in H1; destruct H1.
        rewrite H0;auto.
      -
        apply not_elem_union_elim in H1; destruct H1;assumption.
      -
      induction l.
      reflexivity.
      inversion H.
      f_equal.
      f_equal.
      apply H3;auto;notin_solve_one.
      apply IHl in H4.
      inversion H4.
      rewrite H6.
      rewrite H6.
      reflexivity.
      notin_solve_one.
  Qed.

Lemma subFV_notin' : forall (e:expr) (x:vname) (v:expr) ,
    ~ Elem x (fv e) -> subFV x v e = e.
Proof. intros; apply subFV_notin; apply H.  Qed.    

Lemma tsubFV_notin : forall (t:type) (x:vname) (v:expr),
    ~ Elem x (free t) -> tsubFV x v t = t.
Proof. intros; apply subFV_notin; apply H.  Qed.

Lemma psubFV_notin : forall (ps:preds) (x:vname) (v:expr),
    ~ Elem x (fvP ps) -> psubFV x v ps = ps.
Proof. intros; apply subFV_notin; apply H.  Qed.


Lemma open_at_is_subBV_at :(forall (e:expr) (j:index) (y:vname),
    open_at j y e = subBV_at j (FV y) e ) /\ ((
  forall (t:type) (j:index) (y:vname),
    openT_at j y t = tsubBV_at j (FV y) t ) /\ (
  forall (ps:preds) (j:index) (y:vname),
    openP_at j y ps = psubBV_at j (FV y) ps )).
Proof. 
  apply ( syntax_mutind'
  (fun e : expr => forall (j:index) (y:vname),
      open_at j y e = subBV_at j (FV y) e )
  (fun t : type => forall (j:index) (y:vname),
      openT_at j y t = tsubBV_at j (FV y) t )
  (fun ps : preds => forall (j:index) (y:vname),
      openP_at j y ps = psubBV_at j (FV y) ps ))
  ; intros; simpl; try reflexivity
  ; (* 1 IH *) try ( apply f_equal; apply H )
  ; (* 2 IH *) try ( apply f_equal2; apply H || apply H0 )
  ; try (rewrite H;auto).
  -  rewrite H0. auto.
  -
  apply f_equal.
  induction l. reflexivity. inversion H. f_equal. 
  apply H2. apply IHl. apply H3.
  (* - (* 3 IH *) apply f_equal3; intuition. *)
Qed. 

Lemma unbind_is_subBV : forall (y:vname) (e:expr),
    unbind y e = subBV (FV y) e. 
Proof. intros; apply open_at_is_subBV_at. Qed.

Lemma unbindT_is_tsubBV : forall (y:vname) (t:type),
    unbindT y t = tsubBV (FV y) t. 
Proof. intros; apply open_at_is_subBV_at. Qed.

Lemma unbindP_is_psubBV : forall (y:vname) (ps:preds),
    unbindP y ps = psubBV (FV y) ps. 
Proof. intros; apply open_at_is_subBV_at. Qed.

Lemma subBV_at_lc_at : (forall (e:expr) (j:index) (v:expr) (kx:index),
    (*isValue v ->*) kx <= j -> isLC_at kx  e -> subBV_at j v e = e ) /\ ((
  forall (t:type) (j:index) (v:expr) (kx:index) ,
    (*isValue v ->*) kx <= j -> isLCT_at kx  t -> tsubBV_at j v t = t ) /\ (
  forall (ps:preds) (j:index) (v:expr) (kx:index) ,
    (*isValue v ->*) kx <= j -> isLCP_at kx  ps -> psubBV_at j v ps = ps )).
Proof. 

  apply ( syntax_mutind'
  (fun e:expr => forall (j:index) (v:expr) (kx:index) ,
     (*isValue v ->*) kx <= j -> isLC_at kx  e -> subBV_at j v e = e  )
  (fun t:type => forall (j:index) (v:expr) (kx:index) ,
     (*isValue v ->*) kx <= j -> isLCT_at kx  t -> tsubBV_at j v t = t  )
  (fun ps:preds => forall (j:index) (v:expr) (kx:index) ,
     (*isValue v ->*) kx <= j -> isLCP_at kx  ps -> psubBV_at j v ps = ps  ))
  ; intros; simpl; try reflexivity
  ; (* 1 IH *) try ( apply f_equal; revert H1; simpl; 
                     apply H; try apply Nat.add_le_mono_r; assumption)
  ; (* 2 IH *) try ( apply f_equal2; simpl in H2; destruct H2; 
                     (revert H2; apply H) || (revert H3; apply H0); 
                     try apply Nat.add_le_mono_r; assumption ).
  - (* BV *) destruct (j =? i) eqn:J; simpl in H0.
      * apply Nat.lt_le_trans with i kx j in H0; try assumption.
        apply Nat.lt_neq in H0; apply Nat.neq_sym in H0;
        apply Nat.eqb_neq in H0. rewrite J in H0. discriminate.
      * reflexivity.
  - simpl in H2. destruct H2. f_equal. apply H with kx;auto. apply H0 with kx;auto.
  - f_equal. apply H with kx;auto. 
  
  - f_equal. induction l. reflexivity.
    inversion H. simpl in H1. destruct H1. f_equal. apply H4 with kx;auto. apply IHl. apply H5. simpl. apply H6.  
  Qed. 
Lemma subBV_at_j: (forall (e:expr) (j:index) (v:expr) (kx:index),
(*isValue v ->*) kx <= j -> isLC_at kx  e -> subBV_at j v e = e ).
Proof.
  apply subBV_at_lc_at.
Qed.
Lemma subBV_lc : forall (v:expr) (e:expr),
    (*isValue v ->*) isLC e -> subBV v e = e.
Proof. intros; apply subBV_at_lc_at with 0; intuition. Qed.

Lemma tsubBV_lct : forall (v:expr) (t:type),
    (*isValue v ->*) isLCT t -> tsubBV v t = t.
Proof. intros; apply subBV_at_lc_at with 0; intuition. Qed.    

Lemma open_at_lc_at : (forall (e:expr) (j:index) (x:vname),
    isLC_at j e -> open_at j x e = e ) * ((
  forall (t:type) (j:index) (x:vname),
    isLCT_at j t -> openT_at j x t = t ) * (
  forall (ps:preds) (j:index) (x:vname),
    isLCP_at j ps -> openP_at j x ps = ps  )).
    
Proof. repeat split; intros; pose proof open_at_is_subBV_at; 
  destruct H0 as [He Ht]; destruct Ht as [Ht Hps];
  rewrite He || rewrite Ht || rewrite Hps;
  apply subBV_at_lc_at with j; simpl; intuition. Qed.

Lemma unbind_lc : forall (x:vname) (e:expr),
    isLC e -> unbind x e = e.
Proof. intros; rewrite unbind_is_subBV; apply subBV_lc; 
  simpl; trivial. Qed.

Lemma unbindT_lct : forall (x:vname) (t:type),
    isLCT t -> unbindT x t = t.
Proof. intros; rewrite unbindT_is_tsubBV; apply tsubBV_lct; 
  simpl; trivial. Qed.

Lemma subFV_open_at : (forall (e:expr) (j:index) (y:vname) (v:expr),
    (*isValue v ->*) ~ Elem y (fv e) -> subBV_at j v e = subFV y v (open_at j y e) ) /\ ((
  forall (t:type) (j:index) (y:vname) (v:expr),
    (*isValue v ->*) ~ Elem y (free t) -> tsubBV_at j v t = tsubFV y v (openT_at j y t) ) /\ (
  forall (ps:preds) (j:index) (y:vname) (v:expr),
    (*isValue v ->*) ~ Elem y (fvP ps) -> psubBV_at j v ps = psubFV y v (openP_at j y ps) )).
Proof. 
  apply ( syntax_mutind'
  (fun e : expr => forall (j:index) (y:vname) (v:expr),
      (*isValue v ->*) ~ Elem y (fv e) -> subBV_at j v e = subFV y v (open_at j y e) )
  (fun t : type => forall (j:index) (y:vname) (v:expr),
      (*isValue v ->*) ~ Elem y (free t) -> tsubBV_at j v t = tsubFV y v (openT_at j y t) )
  (fun ps : preds => forall (j:index) (y:vname) (v:expr),
      (*isValue v ->*) ~ Elem y (fvP ps) -> psubBV_at j v ps = psubFV y v (openP_at j y ps) ))
  ; intros; simpl; try reflexivity
  ; (* 1 IH *) try ( apply f_equal; apply H; assumption)
  ; (* 2 IH *) try ( apply f_equal2; apply H || apply H0;
    apply not_elem_union_elim in H1; destruct H1; assumption )
  ;   try (erewrite H;eauto).
  - (* BV *) destruct (j =? i); simpl; 
    assert (y =? y = true) by (apply Nat.eqb_eq; reflexivity); try rewrite H0;
    reflexivity.
  - (* FV *) simpl in H; intuition; apply Nat.neq_sym in H0; 
    apply Nat.eqb_neq in H0; rewrite H0; reflexivity.
  - simpl in H1. apply not_elem_union_elim in H1. destruct H1. rewrite <- H0;eauto.
  - simpl in H1. apply not_elem_union_elim in H1. destruct H1. eauto.
  -
    f_equal. induction l. reflexivity.
    inversion H. simpl in H0. 
    f_equal. apply H3. notin_solve_one. apply IHl. apply H4. simpl. notin_solve_one. 
Qed.  

Lemma subFV_unbind : forall (y:vname) (v:expr) (e:expr),
    (*isValue v ->*) ~ Elem y (fv e) -> subBV v e = subFV y v (unbind y e).
Proof. intros; apply subFV_open_at; assumption. Qed.

Lemma tsubFV_unbindT : forall (y:vname) (v:expr) (t:type),
    (*isValue v ->*) ~ Elem y (free t) -> tsubBV v t = tsubFV y v (unbindT y t).
Proof. intros; apply subFV_open_at; assumption. Qed.

Lemma tsubFV_unbindT_forall : forall (y:vname) (v:expr) (ts:[type]),
    (*isValue v ->*) ~ Elem y ((frees) ts)-> map (tsubBV v) ts = map (tsubFV y v) (map (unbindT y) ts).
Proof. intros.
  induction ts.
  - 
    simpl. reflexivity.
  -
    simpl in H. apply not_elem_union_elim in H. destruct H. 
    simpl. f_equal. apply tsubFV_unbindT;auto.
    apply IHts;auto.
Qed.
Lemma psubFV_unbindP : forall (y:vname) (v:expr) (ps:preds),
    (*isValue v ->*) ~ Elem y (fvP ps) -> psubBV v ps = psubFV y v (unbindP y ps).
Proof. intros; apply subFV_open_at; assumption. Qed.

Lemma commute_subFV_subBV_at : (forall (e:expr) (j:index) (v:expr) (y:vname) (v_y:expr),
    (*isValue v -> isValue v_y ->*) isLC v_y 
      -> subFV y v_y (subBV_at j v e) = subBV_at j (subFV y v_y v) (subFV y v_y e) )  /\ ((
  forall (t:type) (j:index) (v:expr) (y:vname) (v_y:expr),
    (*isValue v -> isValue v_y ->*) isLC v_y 
      -> tsubFV y v_y (tsubBV_at j v t) = tsubBV_at j (subFV y v_y v) (tsubFV y v_y t) )  /\ (
  forall (ps:preds) (j:index) (v:expr) (y:vname) (v_y:expr),
    (*isValue v -> isValue v_y ->*) isLC v_y 
      -> psubFV y v_y (psubBV_at j v ps) = psubBV_at j (subFV y v_y v) (psubFV y v_y ps) )).
Proof.
  apply ( syntax_mutind'
  (fun e : expr => forall (j:index) (v:expr) (y:vname) (v_y:expr),
    (*isValue v -> isValue v_y ->*) isLC v_y 
      -> subFV y v_y (subBV_at j v e) = subBV_at j (subFV y v_y v) (subFV y v_y e) )
  (fun t : type => forall (j:index) (v:expr) (y:vname) (v_y:expr),
    (*isValue v -> isValue v_y ->*) isLC v_y 
      -> tsubFV y v_y (tsubBV_at j v t) = tsubBV_at j (subFV y v_y v) (tsubFV y v_y t) )
  (fun ps : preds => forall (j:index) (v:expr) (y:vname) (v_y:expr),
    (*isValue v -> isValue v_y ->*) isLC v_y 
      -> psubFV y v_y (psubBV_at j v ps) = psubBV_at j (subFV y v_y v) (psubFV y v_y ps) ))
  ; intros; simpl; try reflexivity
  ; (* 1 IH *) try ( apply f_equal; apply H; assumption)
  ; (* 2 IH *) try ( apply f_equal2; apply H || apply H0; assumption ).
  - (* BV *) destruct (j =? i); simpl; reflexivity.
  - (* FV *) destruct (y =? x); try reflexivity; symmetry.
    apply subBV_at_lc_at with 0; auto with *.
  -  rewrite H;auto. rewrite H0;auto.
  - rewrite H. reflexivity. auto. 
  -
    f_equal. induction l. reflexivity.
    inversion H. f_equal. apply H3. auto.
    apply IHl. apply H4.
Qed.  
Lemma commute_subFV_subBV_at' : forall (v:expr) (y:vname) (v_y:expr) (e:expr) j,
(*isValue v -> isValue v_y ->*) isLC v_y 
  -> subFV y v_y (subBV_at j v e) = subBV_at j (subFV y v_y v) (subFV y v_y e).
Proof. intros. apply commute_subFV_subBV_at; assumption. Qed.
Lemma commute_subFV_subBV : forall (v:expr) (y:vname) (v_y:expr) (e:expr),
    (*isValue v -> isValue v_y ->*) isLC v_y 
      -> subFV y v_y (subBV v e) = subBV (subFV y v_y v) (subFV y v_y e).
Proof. intros. apply commute_subFV_subBV_at; assumption. Qed.
      
Lemma commute_tsubFV_tsubBV : forall (v:expr) (y:vname) (v_y:expr) (t:type),
    (*isValue v -> isValue v_y ->*) isLC v_y 
      -> tsubFV y v_y (tsubBV v t) = tsubBV (subFV y v_y v) (tsubFV y v_y t).
Proof. intros. apply commute_subFV_subBV_at; assumption. Qed.
Lemma commute_tsubFV_tsubBV' : forall (v:expr) (y:vname) (v_y:expr) (t:type),
    (*isValue v -> isValue v_y ->*) isLC v_y 
      -> tsubFV y v_y (tsubBV_at 1 v t) = tsubBV_at 1 (subFV y v_y v) (tsubFV y v_y t).
Proof. intros. apply commute_subFV_subBV_at; assumption. Qed.

Lemma commute_psubFV_psubBV : forall (v:expr) (y:vname) (v_y:expr) (ps:preds),
    (*isValue v -> isValue v_y ->*) isLC v_y 
      -> psubFV y v_y (psubBV v ps) = psubBV (subFV y v_y v) (psubFV y v_y ps).
Proof. intros. apply commute_subFV_subBV_at; assumption. Qed.

Lemma commute_subFV_unbind : forall (y:vname) (x:vname) (v:expr) (e:expr),
    x <> y (*-> isValue v*) -> isLC v 
      -> subFV x v (unbind y e) = unbind y (subFV x v e).
Proof. intros; repeat rewrite unbind_is_subBV.
  apply Nat.eqb_neq in H.
  assert (subFV x v (FV y) = FV y) as H2 by (simpl; rewrite H; reflexivity).
  rewrite commute_subFV_subBV; try rewrite H2; simpl; trivial.
  Qed.

Lemma commute_tsubFV_unbindT : forall (y:vname) (x:vname) (v:expr) (t:type),
  x <> y (*-> isValue v*) -> isLC v 
    -> tsubFV x v (unbindT y t) = unbindT y (tsubFV x v t).
Proof. intros; repeat rewrite unbindT_is_tsubBV.
  apply Nat.eqb_neq in H.
  assert (subFV x v (FV y) = FV y) as H2 by (simpl; rewrite H; reflexivity).
  rewrite commute_tsubFV_tsubBV; try rewrite H2; simpl; trivial.
  Qed.

Lemma commute_tsubFV_unbindT' : forall (y:vname) (x:vname) (v:expr) (t:type),
  x <> y (*-> isValue v*) -> isLC v 
    -> tsubFV x v (openT_at 1 y t) = openT_at 1 y (tsubFV x v t).
Proof. intros. assert (openT_at 1 y t = tsubBV_at 1 (FV y) t). apply open_at_is_subBV_at. rewrite H1. assert (openT_at 1 y (tsubFV x v t) = tsubBV_at 1 (FV y) (tsubFV x v t)). apply open_at_is_subBV_at. rewrite H2.
  apply Nat.eqb_neq in H.
  assert (subFV x v (FV y) = FV y) as H3 by (simpl; rewrite H; reflexivity).
  rewrite <- H3 at 2.
  apply commute_subFV_subBV_at;auto. 
  Qed.

Lemma commute_tsubFV_subFV' : forall (y:vname) (x:vname) (v:expr) (t:expr),
  x <> y (*-> isValue v*) -> isLC v 
    -> subFV x v (open_at 1 y t) = open_at 1 y (subFV x v t).
Proof. intros.
  assert (open_at 1 y t = subBV_at 1 (FV y) t). apply open_at_is_subBV_at. rewrite H1. assert (open_at 1 y (subFV x v t) = subBV_at 1 (FV y) (subFV x v t)). apply open_at_is_subBV_at. rewrite H2.
  apply Nat.eqb_neq in H.
  assert (subFV x v (FV y) = FV y) as H3 by (simpl; rewrite H; reflexivity).
  rewrite <- H3 at 2.
  apply commute_subFV_subBV_at;auto. 
  Qed.
Lemma commute_psubFV_unbindP : forall (y:vname) (x:vname) (v:expr) (ps:preds),
  x <> y (*-> isValue v*) -> isLC v 
    -> psubFV x v (unbindP y ps) = unbindP y (psubFV x v ps).
Proof. intros; repeat rewrite unbindP_is_psubBV.
  apply Nat.eqb_neq in H.
  assert (subFV x v (FV y) = FV y) as H2 by (simpl; rewrite H; reflexivity).
  rewrite commute_psubFV_psubBV; try rewrite H2; simpl; trivial.
  Qed.



  Lemma commute_subFV' : (forall (e:expr) (x:vname) (v:expr) (y:vname) (v_y:expr),
  y <> x -> ~ Elem x (fv v_y) 
    -> subFV y v_y (subFV x v e) = subFV x (subFV y v_y v) (subFV y v_y e) ) /\ ((
forall (t:type) (x:vname) (v:expr) (y:vname) (v_y:expr),
  y <> x -> ~ Elem x (fv v_y)
    -> tsubFV y v_y (tsubFV x v t) = tsubFV x (subFV y v_y v) (tsubFV y v_y t) ) /\ (
forall (ps:preds) (x:vname) (v:expr) (y:vname) (v_y:expr),
  y <> x -> ~ Elem x (fv v_y)
    -> psubFV y v_y (psubFV x v ps) = psubFV x (subFV y v_y v) (psubFV y v_y ps) )).
Proof. apply ( syntax_mutind'
(fun e : expr => forall (x:vname) (v:expr) (y:vname) (v_y:expr),
  y <> x -> ~ Elem x (fv v_y) 
    -> subFV y v_y (subFV x v e) = subFV x (subFV y v_y v) (subFV y v_y e) )
(fun t : type => forall (x:vname) (v:expr) (y:vname) (v_y:expr),
  y <> x -> ~ Elem x (fv v_y) 
    -> tsubFV y v_y (tsubFV x v t) = tsubFV x (subFV y v_y v) (tsubFV y v_y t) )
(fun ps : preds => forall (x:vname) (v:expr) (y:vname) (v_y:expr),
  y <> x -> ~ Elem x (fv v_y) 
    -> psubFV y v_y (psubFV x v ps) = psubFV x (subFV y v_y v) (psubFV y v_y ps) ))
; intros; simpl; try reflexivity
; (* 1 IH *) try ( apply f_equal; apply H; assumption)
; (* 2 IH *) try ( apply f_equal2; apply H || apply H0; assumption ).
- (* FV *) destruct (Nat.eqb x0 x) eqn:E0; 
  destruct (Nat.eqb y x) eqn:E; simpl;
  try rewrite E0; try rewrite E; try reflexivity;
  (* both E0 and E cannot be true *)
  try apply Nat.eqb_eq in E0; try apply Nat.eqb_eq in E;
  try rewrite E0 in H; try rewrite E in H; try contradiction;
  apply subFV_notin || (symmetry; apply subFV_notin); assumption.
- rewrite H;auto. rewrite H0;auto.
- rewrite H;auto. 
-
  induction l. reflexivity.
  inversion H. f_equal. f_equal. apply H4;auto.    
  apply IHl in H5. inversion H5. rewrite H7. auto. 
Qed.  

Lemma commute_subFV_general : 
forall (e:expr) (x:vname) (v:expr) (y:vname) (v_y:expr),
  y <> x -> ~ Elem x (fv v_y) 
    -> subFV y v_y (subFV x v e) = subFV x (subFV y v_y v) (subFV y v_y e).
Proof. intros; apply commute_subFV'; assumption. Qed.

Lemma commute_tsubFV_general : 
forall (t:type) (x:vname) (v:expr) (y:vname) (v_y:expr),
  y <> x -> ~ Elem x (fv v_y) 
    -> tsubFV y v_y (tsubFV x v t) = tsubFV x (subFV y v_y v) (tsubFV y v_y t).
Proof. intros; apply commute_subFV'; assumption. Qed.  

Lemma commute_psubFV_general : 
forall (ps:preds) (x:vname) (v:expr) (y:vname) (v_y:expr),
  y <> x -> ~ Elem x (fv v_y) 
    -> psubFV y v_y (psubFV x v ps) = psubFV x (subFV y v_y v) (psubFV y v_y ps).
Proof. intros; apply commute_subFV'; assumption. Qed.  

Lemma commute_subFV : forall (e:expr) (x:vname) (v:expr) (y:vname) (v_y:expr),
  y <> x -> ~ Elem x (fv v_y) -> ~ Elem y (fv v)
    -> subFV y v_y (subFV x v e) = subFV x v (subFV y v_y e).
Proof. intros; rewrite <- (subFV_notin' v y v_y) at 2;
 try apply commute_subFV_general; assumption. Qed.

Lemma commute_tsubFV : forall (t:type) (x:vname) (v:expr) (y:vname) (v_y:expr),
  y <> x -> ~ Elem x (fv v_y) -> ~ Elem y (fv v)
    -> tsubFV y v_y (tsubFV x v t) = tsubFV x v (tsubFV y v_y t).
Proof. intros; rewrite <- (subFV_notin' v y v_y) at 2;
 try apply commute_tsubFV_general; assumption. Qed.

Lemma commute_psubFV : forall (ps:preds) (x:vname) (v:expr) (y:vname) (v_y:expr),
  y <> x -> ~ Elem x (fv v_y) -> ~ Elem y (fv v)
    -> psubFV y v_y (psubFV x v ps) = psubFV x v (psubFV y v_y ps).
Proof. intros; rewrite <- (subFV_notin' v y v_y) at 2;
 try apply commute_psubFV_general; assumption. Qed.


Lemma commute_subBV_subBV: forall e j k e1 e2, j <> k -> isLC e1 -> isLC e2 -> subBV_at j e1 (subBV_at k e2 e) = subBV_at k e2 (subBV_at j e1 e).
Proof.
  intro. induction e using expr_ind';simpl;auto;intros.
  - 
    case_eq (k=?i);intros.
    +
      assert (j=?i = false). apply Nat.eqb_eq in H2. subst k. apply Nat.eqb_neq. auto. rewrite H3. 
      simpl. rewrite H2. apply subBV_at_j with 0;auto.
      lia. 
    +
      case_eq (j=?i);intros.
      ++
        simpl. rewrite H3.
        assert (subBV_at k e2 e1 = e1). apply subBV_at_j with 0;auto. lia. rewrite <- H4 at 1.
        auto.
      ++
        simpl. rewrite H2. rewrite H3.
        auto.
  -
    f_equal;auto.
  -
    f_equal;auto.
  -
    f_equal;auto.
  -
    f_equal;auto.
  -
    f_equal;auto.
    induction l.
    +
      auto.
    +
      inversion H.
      f_equal.
      apply H5;auto.
      apply IHl;auto.
  -
    f_equal;auto.
    rewrite IHe2;auto.
    lia.
Qed.

Lemma commute_open_at_subBV: forall j k e1 e2 e, j <> k -> isLC e2 -> open_at j e1 (subBV_at k e2 e) = subBV_at k e2 (open_at j e1 e).
Proof.
  intros. 
  assert (open_at j e1 e = subBV_at j (FV e1) e). apply open_at_is_subBV_at. rewrite H1.
  rewrite commute_subBV_subBV;simpl;auto.
  assert (open_at j e1 (subBV_at k e2 e) = subBV_at j (FV e1) (subBV_at k e2 e)). apply open_at_is_subBV_at. rewrite H2.
  rewrite commute_subBV_subBV;simpl;auto.
  unfold isLC. simpl;auto. 
  unfold isLC. simpl;auto. 
Qed.

Lemma commute_open_at_open_at: forall j k e1 e2 e, j <> k -> open_at j e1 (open_at k e2 e) = open_at k e2 (open_at j e1 e).
Proof.
  intros. 
  assert (open_at j e1 e = subBV_at j (FV e1) e). apply open_at_is_subBV_at. rewrite H0.
  assert (open_at k e2 e = subBV_at k (FV e2) e). apply open_at_is_subBV_at. rewrite H1.
  assert (open_at j e1 (subBV_at k (FV e2) e) = subBV_at j (FV e1) (subBV_at k (FV e2) e)). apply open_at_is_subBV_at. rewrite H2.
  assert (open_at k e2 (subBV_at j (FV e1) e) = subBV_at k (FV e2) (subBV_at j (FV e1) e)). apply open_at_is_subBV_at. rewrite H3.
  rewrite commute_subBV_subBV;simpl;auto.
  unfold isLC. simpl;auto. 
  unfold isLC. simpl;auto. 
Qed.
Lemma commute_psubBV_psubBV: forall ps j k e1 e2, j <> k -> isLC e1 -> isLC e2 -> psubBV_at j e1 (psubBV_at k e2 ps) = psubBV_at k e2 (psubBV_at j e1 ps).
Proof.
  intros. induction ps.
  -
    auto.
  -
    simpl. rewrite IHps. 
    rewrite commute_subBV_subBV;auto.
Qed.
Lemma commute_tsubBV_tsubBV: forall t j k e1 e2, j <> k -> isLC e1 -> isLC e2 -> tsubBV_at j e1 (tsubBV_at k e2 t) = tsubBV_at k e2 (tsubBV_at j e1 t).
Proof.
  intros. destruct t.
  simpl.
  rewrite commute_psubBV_psubBV;auto.
  lia.
Qed.

Lemma fv_subBV_intro : ( forall (e1:expr) (e2:expr) j,
Subset (fv e1) (fv (subBV_at j e2 e1)) ).
Proof.
  intros. generalize dependent j.
  induction e1 using expr_ind';intros;simpl;auto; try apply subset_refl;try apply subset_empty_l.
  -
    apply subset_union_both;auto.
  - 
    apply subset_union_both;auto.
  -
    induction l.
    +
      apply subset_refl.
    +
      inversion H. 
      apply subset_union_both;auto.
  -
    apply subset_union_both;auto.
Qed.

Lemma fv_psubBV_intro : ( forall (ps:preds) (e2:expr) j,
Subset (fvP ps) (fvP (psubBV_at j e2 ps)) ).
Proof.
  intros. generalize dependent j. induction ps;intros.
  -
    simpl. apply subset_empty_l.
  -
    simpl. apply subset_union_both;auto.
    apply fv_subBV_intro.
Qed.

Lemma fv_tsubBV_intro : ( forall (t:type) (e2:expr) j,
Subset (free t) (free (tsubBV_at j e2 t)) ).
Proof.
  intros. destruct t. simpl.
  apply fv_psubBV_intro.
Qed.


Lemma fv_subBV_elim : ( forall (e1:expr) (e2:expr) j,
Subset (fv (subBV_at j e2 e1)) (union (fv e1) (fv e2))  ).
Proof.
  intros.
  pick_fresh zz. remember (fresh zz ) as y. assert (~Elem y zz). rewrite Heqy. apply fresh_not_elem. rewrite Heqzz in H. 
  assert (subBV_at j e2 e1 = subFV y e2 (open_at j y e1)). apply subFV_open_at. notin_solve_one. rewrite H0.
  apply subset_trans with ((union (diff (fv (open_at j y e1)) (singleton y)) (fv e2))). apply fv_subFV_elim.
  apply subset_union_both. apply subset_add_to_diff. apply fv_open_at_elim.
  apply subset_refl.
Qed.

Lemma fv_subBV_elim' : ( forall (e1:expr) (e2:expr) j,
Subset (fv (subBV_at j e2 e1)) (union (fv e2) (fv e1))  ).
Proof.
  intros.
  pick_fresh zz. remember (fresh zz ) as y. assert (~Elem y zz). rewrite Heqy. apply fresh_not_elem. rewrite Heqzz in H. 
  assert (subBV_at j e2 e1 = subFV y e2 (open_at j y e1)). apply subFV_open_at. notin_solve_one. rewrite H0.
  apply subset_trans with ((union (diff (fv (open_at j y e1)) (singleton y)) (fv e2))). apply fv_subFV_elim.
  apply subset_union_both'. apply subset_add_to_diff. apply fv_open_at_elim.
  apply subset_refl.
Qed.
  
Lemma fv_tsubBV_elim : ( forall (t:type) (e2:expr),
Subset (free (tsubBV e2 t)) (union (free t) (fv e2))  ).
Proof.
  intros.
  pick_fresh zz. remember (fresh zz ) as y. assert (~Elem y zz). rewrite Heqy. apply fresh_not_elem. rewrite Heqzz in H. 
  assert (tsubBV e2 t = tsubFV y e2 (unbindT y t)). apply tsubFV_unbindT. notin_solve_one. rewrite H0.
  apply subset_trans with ((union (diff (free (unbindT y t)) (singleton y)) (fv e2))). apply fv_subFV_elim.
  apply subset_union_both. apply subset_add_to_diff. apply fv_unbind_elim.
  apply subset_refl.
Qed.
Require Import Lists.ListSet.
Lemma fv_tsubBV_elim'' : forall x y,
Subset (union y x) (union x y)  .
Proof.
  intros.
  unfold Subset. intros.
  apply set_union_intro.
  apply set_union_elim in H. destruct H.
  right;auto. left;auto.
Qed.
Lemma fv_tsubBV_elim' : ( forall (t:type) (e2:expr),
Subset (free (tsubBV e2 t)) (union (fv e2) (free t))).
Proof.
  intros.
  apply subset_trans with (union (free t) (fv e2)).
  apply fv_tsubBV_elim.
  apply fv_tsubBV_elim''.
Qed.

  

Lemma psubFV_strengthen : forall (x:vname) (v:expr) (ps rs:preds),
    psubFV x v (strengthen ps rs) = strengthen (psubFV x v ps) (psubFV x v rs).
Proof. intros x v. induction ps. all : simpl.
  - (* PEmpty *) reflexivity.
  - (* PCons p ps *) intros rs. rewrite -> IHps. reflexivity. Qed.


Lemma openP_at_strengthen : forall (j:index) (y:vname) (ps:preds) (rs:preds),
    openP_at j y (strengthen ps rs) = strengthen (openP_at j y ps) (openP_at j y rs).
Proof. intros j y. induction ps. all : simpl.
- (* PEmpty *) reflexivity.
- (* PCons p ps *) intros rs. rewrite -> IHps. reflexivity. Qed.






Lemma self_islct_at : forall (t:type) (e:expr) (j:index),
    isLCT_at j t -> isLC e -> isLCT_at j (self t e).
Proof. induction t; intros;  unfold self; try assumption.
  - (* TRefn b ps, Base *) destruct b eqn:B; simpl in H;
     try (destruct H; unfold lt in H; apply Nat.le_0_r in H; discriminate);
    simpl; repeat split;
    try auto with *;apply islc_at_weaken with 0;auto with *.
    Qed.

Lemma self_islct : forall (t : type) (e : expr),
    isLCT t -> isLC e -> isLCT (self t e).
Proof. intros t e; apply self_islct_at. Qed. 

Lemma openT_at_self : forall (j:index) (y:vname) (t:type) (e:expr),
    isLC e ->  openT_at j y (self t e) = self (openT_at j y t) e.
Proof. intros j y t; generalize dependent j; induction t; intros.
  - (* TRefn *)  simpl; unfold eqlPred. destruct b; simpl;
  pose proof open_at_lc_at; destruct H0;
  try rewrite (e0 e (j+1) y); try destruct (j + 1 =? 0) eqn:J; 
  rewrite Nat.add_comm in J; simpl in J; try discriminate J;
  try apply islc_at_weaken with 0; auto with *.
  Qed.

Lemma unbindT_self : forall (y:vname) (t:type) (e:expr),
    isLC e ->  unbindT y (self t e) = self (unbindT y t) e.
Proof. intros; unfold unbindT; apply openT_at_self; apply H. Qed. 

Lemma tsubFV_self : forall (z:vname) (v_z:expr) (t:type) (e:expr) ,
    tsubFV z v_z (self t e) = self (tsubFV z v_z t) (subFV z v_z e).
Proof. intros; induction t; simpl;f_equal.
  Qed.
Lemma tsubBV_at_self : forall (j:index) (v_z:expr) (t:type) (e:expr),
    isValue v_z -> isLC e -> tsubBV_at j v_z (self t e) = self (tsubBV_at j v_z t) e.
Proof. intros j v_z t; generalize dependent j; induction t; intros.
  - (* TRefn *) simpl; pose proof subBV_at_lc_at; destruct H1. destruct H2. 
    destruct b;simpl;
    rewrite H1 with e (j+1) v_z 0; try destruct (j + 1 =? 0) eqn:J;
    rewrite Nat.add_comm in J; simpl in J; try discriminate J; auto with *.
  Qed.
  
Lemma tsubBV_self : forall (v_z:expr) (t:type) (e:expr),
    isValue v_z -> isLC e -> tsubBV v_z (self t e) = self (tsubBV v_z t) e.
Proof. intros; apply tsubBV_at_self; apply H || apply H0. Qed.

Lemma erase_self : forall (t:type) (e:expr),
    erase (self t e) = erase t.
Proof. intros; induction t; simpl; try apply IHt2; reflexivity. Qed.

Lemma free_self: forall t e, Subset (free (self t e)) (union (fv e)  (free t)).
Proof.
  intros. destruct t. unfold self. simpl. apply subset_refl.
Qed. 

