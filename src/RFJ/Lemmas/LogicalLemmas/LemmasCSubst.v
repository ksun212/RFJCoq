Require Import Arith.
Require Import ZArith.
Require Import Lists.ListSet.
Require Import Lists.

Require Import Definitions.Syntax.
Require Import Definitions.Names.
Require Import Definitions.FJTyping.
Require Import Definitions.Typing.


Require Import Definitions.Semantics.
Require Import Definitions.SubDenotation.


Require Import Lemmas.BasicLemmas.LemmasFJTyping.
Require Import Lemmas.BasicLemmas.LemmasSubstitution.
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasEnvironments.





(*---------------Basic Properties of the Closing Substitution Operations---------------*)

Lemma ctsubst_self_noFTV : forall (th:csub) (t:type) (v:expr),
   ctsubst th (self t v) = self (ctsubst th t) (csubst th v).
Proof. induction th; simpl; intros; try reflexivity.
  - rewrite tsubFV_self; apply IHth.
  Qed.
Lemma csubst_lc : forall (th:csub) (v:expr),
    isLC v -> substitutable th -> isLC (csubst th v).
Proof. induction th; simpl; intros; try apply H; 
  destruct H0; try destruct H1.
  apply IHth.
  apply subFV_lc;auto. 
  apply value_lc;auto.
  auto.
Qed.
Lemma csubst_lc_forall: forall (th:csub) vs,
  Forall isLC vs -> substitutable th -> Forall isLC (map (csubst th) vs).
Proof.
  induction vs;intros.
  - simpl. apply Forall_nil.
  - inversion H. apply Forall_cons. apply csubst_lc;auto.
    apply IHvs;auto.
Qed.
Lemma csubst_value : forall (th:csub) (v:expr),
    isValue v -> substitutable th -> isValue (csubst th v).
Proof. induction th; simpl; intros; try apply H; 
  destruct H0; try destruct H1;
  try apply subFV_value with x v_x v in H as H';
  try apply subFTV_value with a t_a v in H as H';
  try apply IHth; assumption. Qed.


Lemma value_after_csubst : forall (th:csub) (v:expr),
  isValue v -> substitutable th -> Subset (fv v) (bindsC th) -> isValue (csubst th v).
Proof. intros. generalize dependent v. induction th.
-
  intros. simpl in *. 
  induction v using expr_ind';try contradiction;try auto.
-
  intros. simpl in *. destruct H0. apply IHth;auto. apply subFV_value;auto. 
  pose proof fv_subFV_elim as [Hfv _].
  apply subset_trans with (union (diff (fv v) (singleton x)) (fv v_x)).
  apply Hfv. apply subset_union_intro_l. apply subset_add_to_diff;auto. rewrite value_closed;auto. apply subset_empty_l.
Qed.



Lemma value_after_csubst_forall : forall (th:csub) (vs:[expr]),
  Forall isValue vs -> substitutable th -> Subset (fvs vs) (bindsC th) -> Forall isValue (map (csubst th) vs).
Proof. intros. induction vs.
  - simpl. apply Forall_nil.
  - inversion H. simpl in H1. apply subset_union_elim in H1. destruct H1.
    apply Forall_cons. apply value_after_csubst;auto.
    apply IHvs;auto.
Qed.



Lemma unroll_csubst_left : forall (th:csub) (x:vname) (v_x e:expr),
    ~ in_csubst x th -> fv v_x = empty (*-> isValue v_x*)
        -> closed th -> substitutable th
        -> csubst (CCons x v_x th) e = subFV x v_x (csubst th e).
Proof. induction th; intros; simpl; try reflexivity;
  unfold in_csubst in H; simpl in H; 
  apply not_elem_names_add_elim in H; destruct H.
  - (* CCons *) rewrite <- IHth. simpl. try apply f_equal.
    try apply commute_subFV;auto.
    simpl in H2; simpl in H1. destruct H1. destruct H2. rewrite H1. apply empty_no_elem. reflexivity.
    rewrite H0. apply empty_no_elem. reflexivity. unfold in_csubst. auto. auto. simpl in H1. destruct H1. auto.
    simpl in H2. destruct H2. auto. 
  Qed.
   
   
Lemma unroll_ctsubst_left : forall (th:csub) (x:vname) (v_x:expr) (t:type),
    ~ in_csubst x th -> fv v_x = empty (*-> isValue v_x*)
        -> closed th -> substitutable th
        -> ctsubst (CCons x v_x th) t = tsubFV x v_x (ctsubst th t).
Proof. induction th; intros; simpl; try reflexivity;
  unfold in_csubst in H; simpl in H; 
  apply not_elem_names_add_elim in H; destruct H.
  - (* CCons *) rewrite <- IHth; simpl; try apply f_equal;
    try apply commute_tsubFV. auto.
    simpl in H1; simpl in H2. destruct H1. destruct H2. rewrite H1.  apply empty_no_elem. reflexivity.
    rewrite H0. apply empty_no_elem. reflexivity. unfold in_csubst. auto. auto.
    simpl in H1. destruct H1. auto. simpl in H2. destruct H2. auto.
  Qed.       

Lemma unroll_cpsubst_left : forall (th:csub) (x:vname) (v_x:expr) (ps:preds),
  ~ in_csubst x th -> fv v_x = empty (*-> isValue v_x*)
      -> closed th -> substitutable th
      -> cpsubst (CCons x v_x th) ps = psubFV x v_x (cpsubst th ps).
Proof.
induction th; intros; simpl; try reflexivity;
unfold in_csubst in H; simpl in H; 
apply not_elem_names_add_elim in H; destruct H.
- (* CCons *) rewrite <- IHth; simpl; try apply f_equal;
  try apply commute_psubFV. auto.
  simpl in H1; simpl in H2. destruct H1. destruct H2. rewrite H1.  apply empty_no_elem. reflexivity.
  rewrite H0. apply empty_no_elem. reflexivity. unfold in_csubst. auto. auto.
  simpl in H1. destruct H1. auto. simpl in H2. destruct H2. auto.
Qed.        



  (* --- Various properties of csubst/ctsubst and free/bound variables *)

Lemma csubst_nofv : forall (th:csub) (e:expr),
    fv e = empty -> csubst th e = e.
Proof. induction th; intros; simpl; try reflexivity;
  rewrite IHth; try rewrite subFV_notin';
  try rewrite subFTV_notin'; 
  try apply empty_no_elem; trivial. Qed.
Lemma csubst_nofv' : forall (th:csub) (e:expr),
  intersect (bindsC th) (fv e) = empty -> csubst th e = e.
Proof. induction th; intros; simpl; try reflexivity;
simpl in H. apply intersect_names_add_elim_l in H. destruct H. 
assert ((subFV x v_x e) = e). apply subFV_notin. auto. rewrite H1.
apply IHth;auto.
Qed.
Lemma csubst_nofv_forall : forall (th:csub) (es:[expr]),
    Forall (fun e => fv e = empty) es -> map (csubst th) es = es.
Proof. 
  induction es;intros.
  - simpl. auto.
  - inversion H. 
    simpl. f_equal.
    apply csubst_nofv;auto.
    apply IHes;auto.
Qed.

Lemma ctsubst_nofree : forall (th:csub) (t:type),
    free t = empty -> ctsubst th t = t.
Proof. induction th; intros; simpl; try reflexivity;
  rewrite IHth; try rewrite tsubFV_notin; 
  try rewrite tsubFTV_notin; 
  try apply empty_no_elem; trivial. Qed.

Lemma ctsubst_nofree_forall: forall (th:csub) (ts:[type]),
  Forall (fun t => free t = empty) ts -> map (ctsubst th) ts = ts.
Proof.
  induction ts;intros.
  - simpl. auto.
  - inversion H. 
    simpl. f_equal.
    apply ctsubst_nofree;auto.
    apply IHts;auto.
Qed.

Lemma ctsubst_nofree' : forall (th:csub) (t:type),
  intersect (bindsC th) (free t) = empty-> ctsubst th t = t.
Proof. induction th; intros; simpl; try reflexivity.
simpl in H. apply intersect_names_add_elim_l in H. destruct H. 
assert ((tsubFV x v_x t) = t). apply tsubFV_notin. auto. rewrite H1.
apply IHth;auto.
Qed.
  (* --- various distributive properties of csubst and ctsubst *)

Lemma csubst_bc : forall (th:csub) (b:bool) ,
    csubst th (Bc b) = Bc b.
Proof. induction th; simpl; apply IHth || reflexivity. Qed.

Lemma csubst_ic : forall (th:csub) (n:Z),
    csubst th (Ic n) = Ic n.
Proof. induction th; simpl; apply IHth || reflexivity. Qed.

(* Lemma csubst_prim : forall (th:csub) (c:prim),
    csubst th (Prim c) = Prim c.
Proof. induction th; simpl; apply IHth || reflexivity. Qed. *)

Lemma csubst_bv : forall (th:csub) (y:vname),
    csubst th (BV y) = BV y.
Proof. induction th; simpl; apply IHth || reflexivity. Qed.

Lemma csubst_fv : forall (th:csub) (y:vname),
    ~ in_csubst y th -> csubst th (FV y) = FV y.
Proof. induction th; unfold in_csubst; intros; simpl; 
  simpl in H; try apply not_elem_names_add_elim in H; 
  try destruct (x =? y) eqn:E;
  try apply Nat.eqb_eq in E; try rewrite E in H;
  try apply IHth; intuition. Qed.

(* Lemma csubst_lambda : forall (th:csub) (e:expr),
    csubst th (Lambda e) = Lambda (csubst th e).
Proof. induction th; simpl; intro e; apply IHth || reflexivity. Qed.

Lemma csubst_app : forall (th:csub) (e e':expr),
    csubst th (App e e') = App (csubst th e) (csubst th e').
Proof. induction th; simpl; intros e e'; apply IHth || reflexivity. Qed. *)

Lemma csubst_access : forall (th:csub) (e:expr) f,
    csubst th (ExpFieldAccess e f) = ExpFieldAccess (csubst th e) f. 
Proof. induction th; simpl; intros e e'; apply IHth || reflexivity. Qed.
Lemma csubst_invok : forall (th:csub) (e1:expr) (es:expr) m,
    csubst th (ExpMethodInvoc e1 m es) = ExpMethodInvoc (csubst th e1) m ((csubst th) es). 
  Proof. induction th; simpl; intros e e'; apply IHth || reflexivity. Qed.

Lemma csubst_new : forall (th:csub) (es:[expr]) C,
    csubst th (ExpNew C es) = ExpNew C (map (csubst th) es). 
Proof. 

induction th.
- intros. simpl. f_equal. induction es;simpl;auto. f_equal. apply IHes. 
- intros. simpl. rewrite IHth. f_equal. induction es;simpl;auto.   f_equal. apply IHes. 
Qed.

Lemma csubst_unop : forall (th:csub) (e:expr) op,
    csubst th (ExpUnOp op e) = ExpUnOp op (csubst th e). 
Proof. 

induction th; simpl; intros e e'. reflexivity. apply IHth || reflexivity. Qed.

Lemma csubst_binop : forall (th:csub) (e1 e2:expr) op,
    csubst th (ExpBinOp op e1 e2) = ExpBinOp op (csubst th e1) (csubst th e2). 
Proof. 

induction th; simpl; intros e e'. reflexivity. apply IHth || reflexivity. Qed.

Lemma csubst_let : forall (th:csub) (e_x e:expr), 
    csubst th (ExpLet e_x e) = ExpLet (csubst th e_x) (csubst th e).
Proof. induction th; simpl; intros; apply IHth || reflexivity. Qed.

Lemma cpsubst_pempty : forall (th:csub), cpsubst th PEmpty = PEmpty.
Proof. induction th; simpl; apply IHth || reflexivity. Qed.

Lemma cpsubst_pcons : forall (th:csub) (p:expr) (ps:preds),
    cpsubst th (PCons p ps) = PCons (csubst th p) (cpsubst th ps).
Proof. induction th; simpl; intros; apply IHth || reflexivity. Qed.
 
Lemma cpsubst_strengthen : forall (th:csub) (ps qs:preds),
    cpsubst th (strengthen ps qs) = strengthen (cpsubst th ps) (cpsubst th qs).
Proof. induction th; simpl; intros; 
  try rewrite psubFV_strengthen; try rewrite psubFTV_strengthen; 
  try apply IHth || reflexivity. Qed.

Lemma ctsubst_refn : forall (th:csub) (b:fjtype) (ps:preds),
    ctsubst th (TRefn b ps) = TRefn b (cpsubst th ps).
Proof. induction th; intros b ps; simpl;
  destruct b; try rewrite IHth; intuition. Qed.

(* Lemma ctsubst_func : forall (th:csub) (t_x t:type),
    ctsubst th (TFunc t_x t) = TFunc (ctsubst th t_x) (ctsubst th t).
Proof. induction th; simpl; intros; apply IHth || reflexivity. Qed. *)

Lemma ctsubst_erase_basic : forall (th:csub) (t:type) (b:fjtype), 
    erase t = b -> 
        erase (ctsubst th t) = b.
Proof. intro th; induction t; simpl; intros; try discriminate;
  try injection H as H; try subst b0;
  rewrite ctsubst_refn || rewrite ctsubst_exis;
  simpl; try apply IHt2; trivial. Qed.
Lemma erase_ctsubst: forall th0 t,  erase (ctsubst th0 t) = erase t.
Proof.
  induction th0.
  intros. simpl. reflexivity.
  intros. simpl. assert (erase (ctsubst th0 (tsubFV x v_x t)) = erase (tsubFV x v_x t)). 
  apply IHth0. rewrite H. apply erase_tsubFV.
Qed.
  (* --- Commutative laws relating csubst/ctsubst and substitution operations *)
Lemma csubst_subBV_at : forall (th:csub) (v e:expr) j,
  loc_closed th -> substitutable th
      -> csubst th (subBV_at j v e) = subBV_at j (csubst th v) (csubst th e).
  Proof. induction th; intros; try reflexivity.
  simpl in *. destruct H. destruct H0.
  rewrite commute_subFV_subBV_at';auto.
  Qed.
Lemma csubst_subBV : forall (th:csub) (v e:expr),
    loc_closed th -> substitutable th
        -> csubst th (subBV v e) = subBV (csubst th v) (csubst th e).
Proof. induction th; intros; try reflexivity.
  simpl in *. destruct H. destruct H0.
  rewrite commute_subFV_subBV;auto.
Qed.

Lemma csubst_unbind : forall (th:csub) (e:expr) y,
    loc_closed th -> substitutable th -> ~in_csubst y th
        -> csubst th (unbind y e) = unbind y (csubst th e).
Proof. induction th; intros. try reflexivity.
  simpl in *. destruct H. destruct H0.

  unfold in_csubst in *. simpl in H1. apply not_elem_names_add_elim in H1. destruct H1.
  rewrite commute_subFV_unbind. rewrite IHth;auto.
  unfold not. intros. rewrite H5 in H1. contradiction.
  auto.
Qed.

Lemma ctsubst_unbindT : forall (th:csub) (t:type) y,
    loc_closed th -> substitutable th -> ~in_csubst y th
        -> ctsubst th (unbindT y t) = unbindT y (ctsubst th t).
Proof.
  induction th; intros. try reflexivity.
  simpl in *. destruct H. destruct H0.

  unfold in_csubst in *. simpl in H1. apply not_elem_names_add_elim in H1. destruct H1.
  rewrite commute_tsubFV_unbindT. rewrite IHth;auto.
  unfold not. intros. rewrite H5 in H1. contradiction.
  auto.
  Qed.

Lemma ctsubst_unbindP : forall (th:csub) (ps:preds) y,
  loc_closed th -> substitutable th -> ~in_csubst y th
      -> cpsubst th (unbindP y ps) = unbindP y (cpsubst th ps).
Proof.
  induction th; intros. try reflexivity.
  simpl in *. destruct H. destruct H0.

  unfold in_csubst in *. simpl in H1. apply not_elem_names_add_elim in H1. destruct H1.
  rewrite commute_psubFV_unbindP. rewrite IHth;auto.
  unfold not. intros. rewrite H5 in H1. contradiction.
  auto.
Qed.

Lemma ctsubst_tsubBV : forall (th:csub) (v:expr) (t:type),
    loc_closed th -> substitutable th 
        -> ctsubst th (tsubBV v t) = tsubBV (csubst th v) (ctsubst th t).
Proof. induction th; simpl; intros; try reflexivity;
  try rewrite commute_tsubFV_tsubBV;
  try rewrite commute_tsubFTV_tsubBV;
  try apply IHth; destruct H; destruct H0; 
  try destruct H2; try assumption. Qed.

Lemma ctsubst_tsubBV_forall : forall (th:csub) (v:expr) (ts:[type]),
loc_closed th -> substitutable th 
    -> map (ctsubst th) (map (tsubBV v) ts) = map (tsubBV (csubst th v)) (map (ctsubst th) ts).
Proof. 
  intros. induction ts.
  -
    simpl. reflexivity.
  -
    simpl. f_equal.
    apply ctsubst_tsubBV;auto.
    apply IHts.
Qed.
Lemma ctsubst_tsubBV' : forall (th:csub) (v:expr) (t:type),
  loc_closed th -> substitutable th 
      -> ctsubst th (tsubBV_at 1 v t) = tsubBV_at 1 (csubst th v) (ctsubst th t).
Proof.
induction th; simpl; intros; try reflexivity.
try rewrite commute_tsubFV_tsubBV';
try apply IHth; destruct H; destruct H0; 
try destruct H2; try assumption. Qed.


Lemma cpsubst_psubBV : forall (th:csub) (v:expr) (ps:preds),
    loc_closed th -> substitutable th 
        -> cpsubst th (psubBV v ps) = psubBV (csubst th v) (cpsubst th ps).
Proof. induction th; simpl; intros; try reflexivity;
  try rewrite commute_psubFV_psubBV;
  try rewrite commute_psubFTV_psubBV;
  try apply IHth; destruct H; destruct H0; 
  try destruct H2; try assumption. Qed.

Lemma cpsubst_psubFV : forall (th:csub) (v:expr) (ps:preds) y,
  loc_closed th -> substitutable th -> ~in_csubst y th -> isValue v
      -> cpsubst th (psubFV y v ps) = psubFV y v (cpsubst th ps).
Proof.
intros. generalize dependent ps. induction th;intros.
- simpl. auto.
- simpl. simpl in H. inversion H. simpl in H0. inversion H0. unfold in_csubst in H1. simpl in H1. apply not_elem_names_add_elim in H1. destruct H1.
  rewrite <-IHth;auto.
  rewrite commute_psubFV;auto.
  rewrite value_closed;simpl;auto.
  rewrite value_closed;simpl;auto.
Qed.


Lemma csubst_subFV : forall (th:csub) (v:expr) (ps:expr) y,
  loc_closed th -> substitutable th -> ~in_csubst y th -> isValue v
      -> csubst th (subFV y v ps) = subFV y v (csubst th ps).
Proof.
intros. generalize dependent ps. induction th;intros.
- simpl. auto.
- simpl. simpl in H. inversion H. simpl in H0. inversion H0. unfold in_csubst in H1. simpl in H1. apply not_elem_names_add_elim in H1. destruct H1.
  rewrite <-IHth;auto.
  rewrite commute_subFV;auto.
  rewrite value_closed;simpl;auto.
  rewrite value_closed;simpl;auto.
Qed.

  (* --- After applying a closing substitution there are no more free variables remaining *)

Lemma csubst_no_more_fv : forall (th:csub) (v_x:expr),
    Subset (fv v_x) (bindsC th)
        -> closed th -> substitutable th
        -> fv (csubst th v_x) = empty.
Proof. induction th; simpl; intros.
  - (* CEmpty *) apply no_elem_empty. intros.
    apply not_elem_subset with empty; auto.
  -
    apply IHth.
    assert (Subset (fv (subFV x v_x v_x0)) (union (diff (fv v_x0) (singleton x)) (fv v_x))).
    apply fv_subFV_elim.
    destruct H0.
    rewrite H0 in H2.
    assert (Subset (union (diff (fv v_x0) (singleton x)) empty) (diff (fv v_x0) (singleton x))).
    apply union_empty_r.
    assert (Subset (fv (subFV x v_x v_x0)) (diff (fv v_x0) (singleton x))).
    apply subset_trans with ((union (diff (fv v_x0) (singleton x)) empty));auto.
    apply subset_add_to_diff in H.
    eapply subset_trans;eauto.
    destruct H0. destruct H1. auto.
    destruct H0. destruct H1. auto.

Qed.

Lemma ctsubst_no_more_fv : forall (th:csub) (t:type),
    Subset (free t) (bindsC th)
        -> closed th -> substitutable th
        -> free (ctsubst th t) = empty.
Proof. induction th; simpl; intros.
  - (* CEmpty *) apply no_elem_empty; intros;
    apply not_elem_subset with empty; auto.
  - (* CCons  *) apply IHth.
    assert (Subset (free (tsubFV x v_x t)) (union (diff (free t) (singleton x)) (fv v_x))).
    apply fv_subFV_elim.
    destruct H0.
    rewrite H0 in H2.
    assert (Subset (union (diff (free t) (singleton x)) empty) (diff (free t) (singleton x))).
    apply union_empty_r.
    assert (Subset (free (tsubFV x v_x t)) (diff (free t) (singleton x))).
    apply subset_trans with ((union (diff (free t) (singleton x)) empty));auto.
    apply subset_add_to_diff in H.
    eapply subset_trans;eauto.
    destruct H0. destruct H1. auto.
    destruct H0. destruct H1. auto.
Qed.
    

Lemma csubst_isLC : forall (th:csub) (v:expr),
    loc_closed th -> substitutable th -> isLC v -> isLC (csubst th v).
Proof. induction th; simpl; trivial; intros; destruct H; destruct H0.
  - (* CCons *) apply IHth; try apply islc_at_subFV; trivial.
  Qed. 

Lemma ctsubst_isLCT : forall (th:csub) (t:type),
    loc_closed th -> substitutable th -> isLCT t -> isLCT (ctsubst th t).
Proof. induction th; simpl; trivial; intros; destruct H; destruct H0.
  - (* CCons *) apply IHth; try apply islc_at_subFV; trivial. 
  Qed.  


Lemma csubst_subFV_extract : forall (th:csub) (y:vname) (v_y e:expr), 
    ~ (in_csubst y th) -> closed th -> substitutable th -> uniqueC th
        -> Subset (fv v_y) (bindsC th) ->
        csubst th (subFV y (csubst th v_y) e) = csubst th (subFV y v_y e).
Proof. induction th as [|y v_y th]; simpl; intros x v_x; intros.
  - (* CEmpty *) reflexivity.
  - (* CCons  *) apply not_elem_names_add_elim in H; destruct H;
    destruct H0; destruct H1; destruct H2. fold bindsC in H4. 
    rewrite commute_subFV; try rewrite IHth;
    try rewrite <- (commute_subFV_general e x v_x y v_y);
    try (apply empty_no_elem; apply H0);
    pose proof fv_subFV_elim as [Hfv _];
    assert (Subset (fv (subFV y v_y v_x)) (bindsC th))
      by (apply subset_trans with (union (diff (fv v_x) (singleton y)) (fv v_y));
          try apply Hfv; rewrite H0; apply subset_union_intro_l;
          try apply subset_empty_l; apply subset_add_to_diff; auto);
    pose proof (csubst_no_more_fv th (subFV y v_y v_x)). reflexivity. auto. unfold in_csubst. auto.
    auto. auto. auto. auto. auto.  rewrite H9;auto.
  Qed.
   
Lemma ctsubst_tsubFV_extract : forall (th:csub) (x:vname) (v_x:expr) (t:type), 
    ~ (in_csubst x th) -> closed th -> substitutable th -> uniqueC th
        -> Subset (fv v_x) (bindsC th)
        -> ctsubst th (tsubFV x (csubst th v_x) t) = ctsubst th (tsubFV x v_x t).
Proof. induction th as [|y v_y th]; simpl; intros x v_x; intros.
  - (* CEmpty *) reflexivity.
  - (* CCons  *) apply not_elem_names_add_elim in H; destruct H;
    destruct H0; destruct H1; destruct H2. fold bindsC in H5. 
    rewrite commute_tsubFV; try rewrite IHth;
    try rewrite <- (commute_tsubFV_general t x v_x y v_y);
    try (apply empty_no_elem; apply H0);
    pose proof fv_subFV_elim as [Hfv _];
    assert (Subset (fv (subFV y v_y v_x)) (bindsC th))
      by (apply subset_trans with (union (diff (fv v_x) (singleton y)) (fv v_y));
          try apply Hfv; rewrite H0; apply subset_union_intro_l;
          try apply subset_empty_l; apply subset_add_to_diff; auto);
    pose proof (csubst_no_more_fv th (subFV y v_y v_x)); auto.
    rewrite H9;auto.
  Qed.        

Lemma cpsubst_psubFV_extract : forall (th:csub) (x:vname) (v_x:expr) (ps:preds), 
    ~ (in_csubst x th) -> closed th -> substitutable th -> uniqueC th
        -> Subset (fv v_x) (bindsC th)
        -> cpsubst th (psubFV x (csubst th v_x) ps) = cpsubst th (psubFV x v_x ps).
Proof. induction th as [|y v_y th]; simpl; intros x v_x; intros.
  - (* CEmpty *) reflexivity.
  - (* CCons  *) apply not_elem_names_add_elim in H; destruct H;
    destruct H0; destruct H1; destruct H2. fold bindsC in H5. 
    rewrite commute_psubFV; try rewrite IHth;
    try rewrite <- (commute_psubFV_general ps x v_x y v_y);
    try (apply empty_no_elem; apply H0);
    pose proof fv_subFV_elim as [Hfv _];
    assert (Subset (fv (subFV y v_y v_x)) (bindsC th))
      by (apply subset_trans with (union (diff (fv v_x) (singleton y)) (fv v_y));
          try apply Hfv; rewrite H0; apply subset_union_intro_l;
          try apply subset_empty_l; apply subset_add_to_diff; auto);
    pose proof (csubst_no_more_fv th (subFV y v_y v_x)); auto.
    rewrite H9;auto.
  Qed.        


    
(*  --- Closing Substitutions and Technical Operations *)

Lemma remove_not_incsubst : forall (th:csub) (x:vname),
    ~ in_csubst x th -> remove_fromCS th x = th.
Proof. induction th; unfold in_csubst; simpl; intros; 
  try reflexivity; apply not_elem_names_add_elim in H;
  destruct H; apply Nat.eqb_neq in H; rewrite H;
  f_equal; apply IHth; trivial. Qed.

Lemma remove_ctsubst : forall (th:csub) (x:vname) (t:type),
    Elem x (bindsC th) -> ~ Elem x (free t)
        -> closed th -> uniqueC th -> substitutable th
        -> ctsubst th t = ctsubst (remove_fromCS th x) t.
Proof. induction th; intros; simpl.
  - (* CEmpty *) reflexivity.
  - (* CCons  *) destruct (x0 =? x) eqn:X.
    * apply Nat.eqb_eq in X; subst x0; 
      rewrite tsubFV_notin; trivial.
    * simpl; apply IHth;auto.
      simpl in H. apply set_add_elim in H; destruct H;auto. apply Nat.eqb_neq in X. rewrite H in X. contradiction.
      simpl in *; destruct H2 as [H2  Hcl];
      destruct H3;
      pose proof fv_subFV_elim as [_ [H' _]];
      unfold not; intros. apply H' in H5. destruct H1. rewrite H1 in H5. simpl in H5. 
      apply (set_diff_elim1 Nat.eq_dec) in H5. contradiction.
      inversion H1. auto.
      inversion H2. auto.
      inversion H3. auto.
Qed.

Lemma remove_cpsubst : forall (th:csub) (x:vname) (ps:preds),
    Elem x (bindsC th) -> ~ Elem x (fvP ps)
        -> closed th -> uniqueC th -> substitutable th
        -> cpsubst th ps = cpsubst (remove_fromCS th x) ps.
Proof. induction th; intros; simpl.
  - (* CEmpty *) reflexivity.
  - (* CCons  *) destruct (x0 =? x) eqn:X.
    * apply Nat.eqb_eq in X; subst x0; 
      rewrite psubFV_notin; trivial.
    * simpl; apply IHth; simpl in H;
      apply set_add_elim in H; destruct H;
      try (apply Nat.eqb_neq in X; contradiction);
      simpl in *; destruct H1 as [H1 Hcl];
      destruct H3; 
      pose proof fv_subFV_elim as [_ [_ H' ]];
      unfold not; intros;
      try apply H' in H5; try apply H'' in H5;
      try rewrite H1 in H5; try rewrite H1' in H5;
      try revert H5;
      try apply not_elem_union_intro; unfold not; intros;
      try apply (set_diff_elim1 Nat.eq_dec) in H5; 
      try contradiction; auto.
      destruct H2. auto.
Qed.


Lemma ctsubst_concat': forall th th1 t0, 
ctsubst th (ctsubst th1 t0) = ctsubst (CconcatE th th1) t0.
Proof.
  intros. generalize dependent t0. induction th1;intros.
  -
    simpl. auto. 
  -
    simpl.
    rewrite <- IHth1. auto. 
Qed.
Lemma ctsubst_tsubFV_commute: forall th x v t, ~Elem x (bindsC th) -> isValue v -> substitutable th -> 
  ctsubst th (tsubFV x v t) = tsubFV x v (ctsubst th t) .
Proof.
  intros. generalize dependent t. induction th;intros.
  - 
    simpl. auto.
  - 
    simpl. simpl in H1. destruct H1. simpl in H. apply not_elem_names_add_elim in H. destruct H.
    rewrite <- IHth;auto. rewrite commute_tsubFV;auto;auto.
    rewrite value_closed;simpl;auto.
    rewrite value_closed;simpl;auto.
Qed.
Lemma ctsubst_commute: forall th th1 t0, intersect (bindsC th) (bindsC th1) = empty -> substitutable th1 -> substitutable th -> 
ctsubst th (ctsubst th1 t0) = ctsubst th1 (ctsubst th t0).
Proof.
  intros. generalize dependent t0. induction th;intros.
  -
    simpl. auto.
  -
    simpl. simpl in H. apply intersect_names_add_elim_l in H. destruct H. simpl in H1. destruct H1.
    rewrite <- IHth;auto.  
    assert (tsubFV x v_x (ctsubst th1 t0) = ctsubst th1 (tsubFV x v_x t0)).  rewrite ctsubst_tsubFV_commute;auto.
    rewrite H4. auto.
Qed.
Lemma ctsubst_concat: forall th th1 t0, intersect (bindsC th1) (bindsC th) = empty -> substitutable th1 -> substitutable th -> 
ctsubst th1 (ctsubst th t0) = ctsubst (CconcatE th th1) t0.
Proof.
  intros. rewrite ctsubst_commute;auto. rewrite ctsubst_concat';auto.
Qed.


Lemma cpsubst_concat': forall th th1 t0, 
cpsubst th (cpsubst th1 t0) = cpsubst (CconcatE th th1) t0.
Proof.
  intros. generalize dependent t0. induction th1;intros.
  -
    simpl. auto. 
  -
    simpl.
    rewrite <- IHth1. auto. 
Qed.
Lemma cpsubst_psubFV_commute: forall th x v t, ~Elem x (bindsC th) -> isValue v -> substitutable th -> 
  cpsubst th (psubFV x v t) = psubFV x v (cpsubst th t) .
Proof.
  intros. generalize dependent t. induction th;intros.
  - 
    simpl. auto.
  - 
    simpl. simpl in H1. destruct H1. simpl in H. apply not_elem_names_add_elim in H. destruct H.
    rewrite <- IHth;auto. rewrite commute_psubFV;auto;auto.
    rewrite value_closed;simpl;auto.
    rewrite value_closed;simpl;auto.
Qed.
Lemma cpsubst_commute: forall th th1 t0, intersect (bindsC th) (bindsC th1) = empty -> substitutable th1 -> substitutable th -> 
cpsubst th (cpsubst th1 t0) = cpsubst th1 (cpsubst th t0).
Proof.
  intros. generalize dependent t0. induction th;intros.
  -
    simpl. auto.
  -
    simpl. simpl in H. apply intersect_names_add_elim_l in H. destruct H. simpl in H1. destruct H1.
    rewrite <- IHth;auto.  
    assert (psubFV x v_x (cpsubst th1 t0) = cpsubst th1 (psubFV x v_x t0)).  rewrite cpsubst_psubFV_commute;auto.
    rewrite H4. auto.
Qed.
Lemma cpsubst_concat: forall th th1 t0, intersect (bindsC th1) (bindsC th) = empty -> substitutable th1 -> substitutable th -> 
cpsubst th1 (cpsubst th t0) = cpsubst (CconcatE th th1) t0.
Proof.
  intros. rewrite cpsubst_commute;auto. rewrite cpsubst_concat';auto.
Qed.

Lemma csubFV_unop: forall x v_x e c w', isValue v_x -> subFV x v_x e = ExpUnOp c w' -> exists w' : expr, e = ExpUnOp c w'.
Proof.
  intros. destruct e;simpl in H0;try inversion H0.
  case_eq (x=?x0); intros. rewrite H1 in H0. subst v_x. simpl in H. contradiction. rewrite H1 in H0. inversion H0.
  subst o. exists e. auto.
Qed. 
Lemma csubst_reverse_unop: forall c w th e, substitutable th -> ExpUnOp c w = csubst th e -> exists w', e = ExpUnOp c w'.
Proof.
  intros. generalize dependent e. induction th;intros.
  - simpl in H0. exists w. auto.
  - simpl in H0. simpl in H. destruct H. apply IHth in H0;auto. destruct H0 as [w']. eapply csubFV_unop;eauto. 
Qed. 


Lemma csubFV_binop: forall x v_x e c v1 v2, isValue v_x -> subFV x v_x e = ExpBinOp c v1 v2 -> exists v1' v2' : expr, e = ExpBinOp c v1' v2'.
Proof.
  intros. destruct e;simpl in H0;try inversion H0.
  case_eq (x=?x0); intros. rewrite H1 in H0. subst v_x. simpl in H. contradiction. rewrite H1 in H0. inversion H0.
  subst o. exists e1. exists e2. auto.
Qed. 
Lemma csubst_reverse_binop: forall c v1 v2 th e, substitutable th -> ExpBinOp c v1 v2 = csubst th e -> exists v1' v2' : expr, e = ExpBinOp c v1' v2'.
Proof.
  intros. generalize dependent e. induction th;intros.
  - simpl in H0. exists v1. exists v2. auto.
  - simpl in H0. simpl in H. destruct H. apply IHth in H0;auto. destruct H0 as [v1'[v2']]. eapply csubFV_binop;eauto. 
Qed. 

Lemma csubFV_invok: forall x v_x e e1 e2  m, isValue v_x -> subFV x v_x e = ExpMethodInvoc e1 m e2 -> exists e1' e2' : expr, e = ExpMethodInvoc e1' m e2'.
Proof.
  intros. destruct e;simpl in H0;try inversion H0.
  case_eq (x=?x0); intros. rewrite H1 in H0. subst v_x. simpl in H. contradiction. rewrite H1 in H0. inversion H0.
  exists e3. exists e4. auto.
Qed. 
Lemma csubst_reverse_invok: forall e1 e2 th e m, substitutable th -> ExpMethodInvoc e1 m e2 = csubst th e -> exists e1' e2' : expr, e = ExpMethodInvoc e1' m e2'.
Proof.
  intros. generalize dependent e. induction th;intros.
  - simpl in H0. exists e1. exists e2. auto.
  - simpl in H0. simpl in H. destruct H. apply IHth in H0;auto. destruct H0 as [e1'[e2']]. eapply csubFV_invok;eauto. 
Qed.

Lemma csubFV_access: forall x v_x e e1 f, isValue v_x -> subFV x v_x e = ExpFieldAccess e1 f -> exists e1' : expr, e = ExpFieldAccess e1' f.
Proof.
  intros. destruct e;simpl in H0;try inversion H0.
  case_eq (x=?x0); intros. rewrite H1 in H0. subst v_x. simpl in H. contradiction. rewrite H1 in H0. inversion H0.
  exists e. auto.
Qed. 
Lemma csubst_reverse_access: forall e1 th e f, substitutable th -> ExpFieldAccess e1 f = csubst th e -> exists e1' : expr, e = ExpFieldAccess e1' f.
Proof.
  intros. generalize dependent e. induction th;intros.
  - simpl in H0. exists e1. auto.
  - simpl in H0. simpl in H. destruct H. apply IHth in H0;auto. destruct H0 as [e1']. eapply csubFV_access;eauto. 
Qed.

Lemma csubFV_new: forall x v_x e C es, isValue v_x -> subFV x v_x e = ExpNew C es -> (exists es' : [expr], e = ExpNew C es') \/ (e = FV x).
Proof.
  intros. destruct e;simpl in H0;try inversion H0.
  case_eq (x=?x0); intros. rewrite H1 in H0. subst v_x. apply Nat.eqb_eq in H1. subst x. right. auto. rewrite H1 in H0. inversion H0.
  left. exists l. auto.
Qed. 

Lemma csubFV_FV: forall x v_x e x0, isValue v_x -> subFV x v_x e = FV x0 -> e = FV x0.
Proof.
  intros. destruct e;simpl in H0;try inversion H0.
  case_eq (x=?x1); intros. rewrite H1 in H0. subst v_x. simpl in H. contradiction.
  auto.
Qed.
Lemma csubst_reverse_new: forall es th e C, substitutable th -> ExpNew C es = csubst th e -> (exists es' : [expr], e = ExpNew C es') \/ (exists x, e = FV x /\ in_csubst x th).
Proof.
  intros. generalize dependent e. induction th;intros.
  - simpl in H0. left. exists es. auto.
  - simpl in H0. simpl in H. destruct H. apply IHth in H0;auto.
    destruct H0.
      + destruct H0 as [es']. apply csubFV_new in H0;auto. destruct H0. destruct H0 as [es'']. left. exists es''. auto. right. exists x. constructor;simpl;auto. unfold in_csubst. simpl. apply elem_names_add_intro. left. auto.  
      + destruct H0 as [x0]. destruct H0. assert (e = FV x0). eapply csubFV_FV;eauto. right. exists x0. constructor;auto. unfold in_csubst. simpl. apply elem_names_add_intro. right. auto.  
Qed.

Lemma csubFV_let: forall x v_x e v1 v2, isValue v_x -> subFV x v_x e = ExpLet v1 v2 -> exists v1' v2' : expr, e = ExpLet v1' v2'.
Proof.
  intros. destruct e;simpl in H0;try inversion H0.
  case_eq (x=?x0); intros. rewrite H1 in H0. subst v_x. simpl in H. contradiction. rewrite H1 in H0. inversion H0.
  exists e1. exists e2. auto.
Qed. 
Lemma csubst_reverse_let: forall v1 v2 th e, substitutable th -> ExpLet v1 v2 = csubst th e -> exists v1' v2' : expr, e = ExpLet v1' v2'.
Proof.
  intros. generalize dependent e. induction th;intros.
  - simpl in H0. exists v1. exists v2. auto.
  - simpl in H0. simpl in H. destruct H. apply IHth in H0;auto. destruct H0 as [v1'[v2']]. eapply csubFV_let;eauto. 
Qed. 


Lemma csubst_sub_isValue: forall th x, substitutable th -> in_csubst x th -> isValue (csubst th (FV x)).
Proof.
  induction th;intros.
  - simpl;auto.
  - simpl in H. destruct H. unfold in_csubst in H0. simpl in H0. simpl.
    assert (x0 = x \/ in_csubst x0 th). apply elem_names_add_elem;auto. destruct H2.
    case_eq (x =? x0);intros. apply Nat.eqb_eq in H3. apply csubst_value;auto. apply Nat.eqb_neq in H3. subst x0. contradiction.
    case_eq (x =? x0);intros. apply Nat.eqb_eq in H3. apply csubst_value;auto. apply Nat.eqb_neq in H3. apply IHth;auto.
Qed.


(*Closing Substitution of Primitive Signatures*)

Lemma csubst_ty': forall th op, (ctsubst th (ty' op)) = ty' op.
Proof.
  intros. destruct op. simpl. rewrite ctsubst_refn. 
  rewrite cpsubst_pcons. rewrite csubst_binop. 
  rewrite csubst_unop. 
  repeat rewrite csubst_bv. 
  rewrite cpsubst_pempty.
  auto.
Qed. 

Lemma csubst_intype: forall th op, (ctsubst th (intype op)) = intype op.
Proof.
  intros. destruct op. simpl. rewrite ctsubst_refn.
  rewrite cpsubst_pempty.
  auto.
Qed. 

Lemma csubst_ty'2: forall th op, (ctsubst th (ty'2 op)) = ty'2 op.
Proof.
  intros. destruct op; simpl; rewrite ctsubst_refn;
  rewrite cpsubst_pcons;rewrite csubst_binop;
  rewrite csubst_binop;
  repeat rewrite csubst_bv;
  rewrite cpsubst_pempty;
  auto.
Qed. 

Lemma csubst_intype2: forall th op, (ctsubst th (fst (intype2 op))) = (fst (intype2 op)).
Proof.
  intros. destruct op;simpl;rewrite ctsubst_refn;
  rewrite cpsubst_pempty;
  auto.
Qed.

Lemma csubst_intype2': forall th op, (ctsubst th (snd (intype2 op))) = (snd (intype2 op)).
Proof.
  intros. destruct op;simpl;rewrite ctsubst_refn;
  rewrite cpsubst_pempty;
  auto.
Qed.



