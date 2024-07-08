Require Import Definitions.Syntax.
Require Import Definitions.Names.


Require Import Definitions.Semantics.
Require Import Definitions.FJTyping.
Require Import Lemmas.BasicLemmas.LemmasFJTyping.
Require Import Definitions.WellFormedness.
Require Import Lemmas.BasicLemmas.LemmasSubstitution.
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasEnvironments.
Require Import Lemmas.BasicLemmas.LemmasWellFormedness.
Require Import Definitions.Typing.
Require Import Definitions.ClosingSubstitutions.
Require Import Definitions.Denotations.
Require Import Lemmas.LogicalLemmas.LemmasDenotations.
Require Import Lemmas.BasicLemmas.LemmasSemantics.
Require Import Lemmas.LogicalLemmas.LemmasCSubst.

Require Import Arith.
Require Import Lists.ListSet.

Lemma denotesenv_loc_closed : forall (g:env) (th:csub), 
    DenotesEnv g th -> loc_closed th.
Proof. intros; induction H; simpl; try split; trivial.
  - (* CCons *) apply den_hasfjtype in H1; 
    apply fjtyp_islc in H1; assumption.
  Qed.

Lemma denotesenv_closed : forall (g:env) (th:csub), 
    DenotesEnv g th -> closed th.
Proof. intros; induction H; simpl; trivial.
  - (* CCons *) apply den_hasfjtype in H1;
    apply fv_subset_bindsFJ in H1; repeat split;
    try apply IHDenotesEnv; apply no_elem_empty; intuition.
  Qed.

Lemma denotesenv_substitutable : forall (g:env) (th:csub), 
    DenotesEnv g th -> substitutable th.
Proof. intros; induction H; simpl; repeat split; trivial.
  apply den_isvalue with (ctsubst th t); apply H1. Qed.

Lemma denotesenv_unique : forall (g:env) (th:csub),
    DenotesEnv g th -> unique g.
Proof. intros g th den_g_th; induction den_g_th; simpl; 
  try split; trivial; unfold in_csubst;
  rewrite <- binds_env_th with g th; trivial. Qed.

Lemma denotesenv_uniqueC : forall (g:env) (th:csub),
    DenotesEnv g th -> uniqueC th.
Proof. intros g th den_g_th; induction den_g_th; simpl; 
  try split; trivial; unfold in_csubst;
  rewrite <- binds_env_th with g th; trivial. Qed.

Lemma bound_in_denotesenv : 
  forall (x:vname) (t:type) (g:env) (th:csub),
    DenotesEnv g th -> bound_in x t g -> WFEnv g
        -> Denotes (ctsubst th t) (csubst th (FV x)).
Proof. intros x t; induction g.
  - simpl; intuition.
  - intros; inversion H;   subst x1 t1 g0;
    try apply H1;  simpl in H0. destruct H0.
    * (* x = x0 *) destruct H0; subst x0 t0;
      inversion H1; subst x0 t0 g0.
      simpl; destruct (x =? x) eqn:X;
      try apply Nat.eqb_neq in X; try unfold not in X; 
      try contradiction.
      assert (~Elem x (free t)). apply free_bound_in_env with g;auto.
      rewrite tsubFV_notin;auto.
      rewrite csubst_nofv. auto. eapply den_nofv;eauto.
    * 
      simpl. destruct (x0 =? x) eqn:X. assert (x0 = x). apply Nat.eqb_eq. auto. subst x0. apply boundin_inenv in H0.  unfold in_env in H7. contradiction. 
      assert (x0 <> x). apply Nat.eqb_neq. auto.  
      inversion H1. apply boundin_wfenv_wftype in H0 as p_g_t;auto. assert (~Elem x0 (free t)).  apply free_bound_in_env with g;auto.
      rewrite tsubFV_notin;auto.
Qed.

(*left-distributive of ctsubst over self*)
Lemma denotes_ctsubst_self : 
  forall (th:csub) (t:type) (v v':expr),
    closed th -> loc_closed th -> substitutable th -> uniqueC th 
        -> isLC v
        -> Denotes (self (ctsubst th t) (csubst th v)) v'
        -> Denotes (ctsubst th (self t v)) v'.
Proof.
  induction th.
  intros. simpl in *. auto.
  intros. simpl. rewrite tsubFV_self. inversion H. inversion H0. inversion H1. inversion H2. apply IHth;auto.
  apply islc_at_subFV; auto.
Qed.
