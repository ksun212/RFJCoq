Require Import Arith.
Require Import Lists.ListSet.
Require Import Coq.Program.Equality.
Require Import Lists.

Require Import RFJ.Utils.Referable.
Require Import RFJ.Lists.

Require Import Definitions.Syntax.
Require Import Definitions.Names.
Require Import Definitions.FJTyping.
Require Import Definitions.Semantics.

Require Import Definitions.Typing.
Require Import Definitions.CTSanity.
Require Import Definitions.SubDenotation.

Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasFJTyping.
Require Import Lemmas.BasicLemmas.LemmasSubstitution.
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasEnvironments.
Require Import Lemmas.BasicLemmas.LemmasFJWeaken.
Require Import Lemmas.BasicLemmas.LemmasEnvironments.
Require Import Lemmas.BasicLemmas.LemmasWFWeaken.



(*---------------Basic Properties of WF---------------*)

Lemma truncate_wfenv : forall (g g':env),
    WFEnv (concatE g g') -> WFEnv g.
Proof. intro g; induction g'; intro p_wf_g'g.
  - simpl in p_wf_g'g; assumption.
  - simpl in p_wf_g'g. inversion p_wf_g'g. intuition.
Qed.

Lemma free_subset_binds : forall (g:env) (t:type),
    WFtype g t -> Subset (free t) (binds g).
Proof. intros g t p_g_t; induction p_g_t. 
  - (* WFBase *) destruct b; try apply subset_empty_l; simpl in H; try contradiction.
  - (* WFRefn *) 
    pose proof (fresh_varT_not_elem nms g (TRefn b ps)) as Hfv.
    set (z := (fresh_varT nms g (TRefn b ps))) in Hfv;
    destruct Hfv as [Hfv Hnms]; destruct Hnms as [Hnms Hg];
    simpl in Hfv;
    pose proof (fvp_subset_bindsFJ (FCons z (b) (erase_env g))
                                      (unbindP z ps) (H0 z Hnms)).
    simpl in H1.
    * (* free *) rewrite binds_erase_env; destruct b eqn:B; simpl;
      apply subset_add_elim with z; try apply Hfv;
      apply subset_trans with (fvP (unbindP z ps));
      try apply fv_unbind_intro; apply H1.
  Qed.
  
Lemma free_bound_in_env : forall (g:env) (t:type) (x:vname),
    WFtype g t -> ~ in_env x g -> ~ Elem x (free t).
Proof. unfold in_env; intros; apply free_subset_binds in H; 
  pose proof (binds_subset g); pose proof (binds_subset g); intuition. Qed. 

Lemma wftype_islct : forall (g:env) (t:type),
    WFtype g t -> isLCT t.
Proof. intros; induction H; unfold isLCT; simpl; intuition.
  (* - WFBase destruct b; simpl in H; intuition. *)
  - (* WFRefn *) pose proof (fresh_not_elem nms);
    set (y := fresh nms) in H2; apply H1 in H2;  
    apply pbool_islcp in H2; revert H2;
    destruct b; try apply islc_at_after_open_at.
  Qed.


Lemma wftype_closedtype : forall (t:type),
  WFtype Empty t -> free t = empty.
Proof.
  intros. apply free_subset_binds in H.
  simpl in H. apply subset_empty_r in H. auto.
Qed.


Lemma eqlPred_fjtyping : forall (g:env) (b bb:fjtype) (ps:preds) (e:expr) (y:vname),
    WFtype g (TRefn b ps) -> ~ in_env y g -> HasFJtype (erase_env g) e (bb) (*-> isValue e *)
        -> HasFJtype (FCons y (b) (erase_env g)) 
                    (unbind y (eqlPred e)) (TBool).
Proof. intros.
  (* destruct b. *)
  - (*TAny*)
    unfold unbind. simpl.
    assert (open_at 0 y e = e). apply open_at_lc_at. apply fjtyp_islc with (erase_env g) (TAny);auto. apply FTSub with bb;auto. rewrite H2.
    assert ((erase (ty'2 Eq)) = TBool). reflexivity. rewrite <- H3. 
    apply FTBinOP;simpl;auto. simpl. apply weaken_fjtyp_top;auto. apply FTSub with bb;auto. unfold in_envFJ. unfold in_env in H0. rewrite <- binds_erase_env. auto.
    apply FTSub with b;auto.
    simpl. apply FTVar. try (simpl; right; left; constructor; reflexivity).  try (simpl; left; constructor; reflexivity).
Qed.

Lemma strengthen_fjtyping : forall (g:fjenv) (ps:preds) (rs:preds),
    PIsBool g ps -> PIsBool g rs -> PIsBool g (strengthen ps rs).
Proof. intros g ps rs p_ps_bl p_rs_bl; induction p_ps_bl; simpl.
  - (* PFTEmp  *) apply p_rs_bl.
  - (* PFTCons *) apply PFTCons; 
      ( apply H || apply IHp_ps_bl; apply p_rs_bl). Qed.

Lemma selfify_wf' : forall (g:env) (t:type) (e:expr),
  WFtype g (self t e)  (*-> FJSubtype (erase s) (erase t) *)(*-> isValue e *)
                -> WFtype g t. (* in LH this was induction on tsize *)
Proof. intros. dependent induction H. simpl in *;intros.
- (* WFBase *) 
  destruct t. unfold self in x. simpl in x. inversion x.
-
  destruct t. unfold self in x. simpl in x. inversion x.
  case_eq ps0.
  intros. apply WFBase.
  intros.
  pick_fresh zz.
  apply WFRefn with zz.
  apply WFBase.
  discriminate.
  intros.
  rewrite Heqzz in H5.

  rewrite H4 in H1. rewrite H2 in H1.
  assert (~Elem y nms). notin_solve_one. apply H1 in H6.
  unfold unbindP in H6. simpl in H6. inversion H6.
  inversion H11. subst b0. auto.
Qed.

Lemma selfify_wf : forall (g:env) (s t:type) (e:expr),
    WFtype g t  -> HasFJtype (erase_env g) e (erase s) (*-> FJSubtype (erase s) (erase t) *)(*-> isValue e *)
                  -> WFtype g (self t e). (* in LH this was induction on tsize *)
Proof. intros g s t k p_g_t sub. induction p_g_t; simpl in *;intros.
  - (* WFBase *) 
    eapply WFRefn.
    apply WFBase.
    discriminate.
    intros.
    apply PFTCons.
    fold open_at.
    apply eqlPred_fjtyping with (erase s) PEmpty;eauto.
    apply PFTEmp.
  -
    pick_fresh zz.
    apply WFRefn with zz.
    apply WFBase.
    discriminate.
    intros.
    rewrite Heqzz in H1.
    apply PFTCons.
    fold open_at.
    apply eqlPred_fjtyping with (erase s) ps;eauto.
    unfold in_env.
    notin_solve_one.
    apply H0.
    notin_solve_one.
  Qed.


Lemma boundin_wfenv_wftype : forall (x:vname) (t:type) (g:env),
  bound_in x t g -> WFEnv g -> WFtype g t.
Proof. intros x t g H p_wf_g; induction p_wf_g. simpl in H.
  - contradiction.
  - simpl in H; destruct H; apply weaken_wf_top;
    try (destruct H; subst t0; (apply H1 || apply WFKind; apply H1));
    try apply IHp_wf_g; intuition.
Qed.
