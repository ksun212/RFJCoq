Require Import Arith.
Require Import Coq.Program.Equality.
Require Import List.

Require Import Definitions.Syntax.
Require Import Definitions.Names.
Require Import Definitions.FJTyping.

Require Import Lemmas.BasicLemmas.LemmasFJTyping.
Require Import Lemmas.BasicLemmas.LemmasSubstitution.
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasEnvironments.
Require Import Lemmas.BasicLemmas.LemmasFJWeaken.

(*---------------Substitution Lemmas of FJ Typing---------------*)

Lemma subst_fjtyp' : forall (g'xg : fjenv) (e : expr) (t : fjtype),
    HasFJtype g'xg e t -> ( forall (g g':fjenv) (x:vname) (v_x:expr) (t_x:fjtype),
       g'xg = concatF (FCons x t_x g) g' 
                     -> uniqueF g -> uniqueF g'
                     -> intersect (bindsFJ g) (bindsFJ g') = empty
                     -> ~ (in_envFJ x g) -> ~ (in_envFJ x g') 
                     -> isLC v_x -> HasFJtype g v_x t_x
                     -> HasFJtype (concatF g g') (subFV x v_x e) t ).
Proof. apply ( HasFJtype_ind'
 (fun (g'xg : fjenv) (e : expr) (t : fjtype) => 
   forall (g g':fjenv) (x:vname) (v_x:expr) (t_x:fjtype),
       g'xg = concatF (FCons x t_x g) g' 
             -> uniqueF g -> uniqueF g'
             -> intersect (bindsFJ g) (bindsFJ g') = empty
             -> ~ (in_envFJ x g) -> ~ (in_envFJ x g') 
             -> isLC v_x -> HasFJtype g v_x t_x
             -> HasFJtype (concatF g g') (subFV x v_x e) t  ));
  intros env; intros; subst env.
  - (* FTBC *) apply FTBC.
  - (* FTIC *) apply FTIC.
  - (* FTVar *) apply boundinF_concatF in H; simpl in H; destruct H. destruct H.
    * (* x = x0 *) destruct H; subst x0; subst b; simpl.
      assert (x = x) by reflexivity; apply Nat.eqb_eq in H; rewrite H.
      apply weaken_many_fjtyp; assumption.       
    * (* x0 in g *) apply boundin_inenvFJ in H as H'.
      pose proof bindsFJ_subset as Htv; unfold Subset in Htv; apply Htv in H';
      assert (x0 <> x) by (unfold not; intro; subst x0; contradiction).
      apply Nat.eqb_neq in H0; simpl; rewrite H0.
      apply FTVar. apply boundinF_concatF; intuition.
    * (* x0 in g' *) apply boundin_inenvFJ in H as H'.
      pose proof bindsFJ_subset as Htv; unfold Subset in Htv; apply Htv in H';
      assert (x0 <> x) by (unfold not; intro; subst x0; contradiction).
      apply Nat.eqb_neq in H0; simpl; rewrite H0.
      apply FTVar; apply boundinF_concatF; intuition.
  - (* FTPrm *) apply FTUnOP. apply H0 with t_x;intuition. (*apply subFV_value;auto.*)
  - (* FTPrm *) apply FTBinOP; try apply subFV_value;auto. apply H0 with t_x || apply H2 with t_x;intuition. apply H2 with t_x; intuition.
  - (* FTApp *) 
    apply FTInvok with t C ps;auto. 
    apply H0 with t_x;intuition.
    apply H3 with t_x;intuition.
  -
    apply FTInvokI with t C ps;auto. 
    apply H0 with t_x;intuition.
    apply H3 with t_x;intuition.
  - 
    eapply FTField;eauto. (*apply subFV_value;auto. *)
  -
    apply FTNew with Fs Us fs.
    apply H. apply H0. apply H1.
    clear H.
    generalize dependent Us. 
    induction es.
    + intros. induction Us. apply Forall2_nil. inversion H3.
    + intros. destruct Us. inversion H3. inversion H3. inversion H2. apply Forall2_cons. apply H13 with t_x;auto.
    eapply IHes. apply H15. apply H21. 
  -
    apply FTLet with b (names_add x (union nms (union (bindsFJ g') (bindsFJ g)))).
    apply H0 with t_x;auto.
    intros. assert (FCons y b (concatF g g') = concatF g (FCons y b g')) by reflexivity. rewrite H11. 
    apply not_elem_names_add_elim in H3; destruct H3.
    apply not_elem_union_elim in H12; destruct H12.
    apply not_elem_union_elim in H13; destruct H13.
    rewrite <- commute_subFV_unbind; auto. try apply value_lc;auto. apply H2 with t_x;auto.
    simpl. constructor;auto. 
    try apply intersect_names_add_intro_r;auto.
    try apply not_elem_names_add_intro; intuition.
  -
    apply FTSub with s;eauto. 
Qed.

Lemma subst_fjtyp : 
  forall (g g':fjenv) (e : expr) (t : fjtype) (x:vname) (v_x:expr) (t_x:fjtype),
    HasFJtype (concatF (FCons x t_x g) g') e t
                     -> uniqueF g -> uniqueF g'
                     -> intersect (bindsFJ g) (bindsFJ g') = empty
                     -> ~ (in_envFJ x g) -> ~ (in_envFJ x g') 
                     -> isLC v_x -> HasFJtype g v_x t_x
                     -> HasFJtype (concatF g g') (subFV x v_x e) t.
Proof. intros; apply subst_fjtyp' with (concatF (FCons x t_x g) g') t_x;
  trivial. Qed.

Lemma subst_pbool' : forall (g'xg : fjenv) (ps : preds),
    PIsBool g'xg ps -> ( forall (g g':fjenv) (x:vname) (v_x:expr) (t_x:fjtype),
       g'xg = concatF (FCons x t_x g) g' 
                     -> uniqueF g -> uniqueF g'
                     -> intersect (bindsFJ g) (bindsFJ g') = empty
                     -> ~ (in_envFJ x g) -> ~ (in_envFJ x g') 
                     -> isLC v_x -> HasFJtype g v_x t_x
                     -> PIsBool (concatF g g') (psubFV x v_x ps) ).
Proof. apply ( PIsBool_ind 
 (fun (g'xg : fjenv) (ps : preds) => 
   forall (g g':fjenv) (x:vname) (v_x:expr) (t_x:fjtype),
       g'xg = concatF (FCons x t_x g) g' 
             -> uniqueF g -> uniqueF g'
             -> intersect (bindsFJ g) (bindsFJ g') = empty
             -> ~ (in_envFJ x g) -> ~ (in_envFJ x g') 
             -> isLC v_x -> HasFJtype g v_x t_x
             -> PIsBool (concatF g g') (psubFV x v_x ps)  ));
  intros env; intros; subst env; simpl.
  - apply PFTEmp.
  - apply PFTCons; try apply subst_fjtyp with t_x;
    try apply H1 with t_x; trivial. Qed.

Lemma subst_pbool : forall (g g' : fjenv) (ps : preds) (x:vname) (v_x:expr) (t_x:fjtype),
    PIsBool (concatF (FCons x t_x g) g') ps 
                     -> uniqueF g -> uniqueF g'
                     -> intersect (bindsFJ g) (bindsFJ g') = empty
                     -> ~ (in_envFJ x g) -> ~ (in_envFJ x g') 
                     -> isLC v_x -> HasFJtype g v_x t_x
                     -> PIsBool (concatF g g') (psubFV x v_x ps).
Proof. intros; apply subst_pbool' with (concatF (FCons x t_x g) g') t_x; 
  trivial. Qed.



Lemma substbv_fjtyp' : forall (g'xg : fjenv) (e : expr) (t : fjtype) (x:vname),
  HasFJtype g'xg (open_at 1 x e) t -> ~ Elem x (fv e) -> ( forall (g g':fjenv) (v_x:expr) (t_x:fjtype),
     g'xg = concatF (FCons x t_x g) g'
                   -> uniqueF g -> uniqueF g'
                   -> intersect (bindsFJ g) (bindsFJ g') = empty
                   -> ~ (in_envFJ x g) -> ~ (in_envFJ x g') 
                   -> isLC v_x -> HasFJtype g v_x t_x
                   -> HasFJtype (concatF g g') (subBV_at 1 v_x e) t ).
Proof.
  intros.
  assert ((subBV_at 1 v_x e) = subFV x v_x (open_at 1 x e) ).
  apply subFV_open_at.
  apply H0.
  rewrite H9.
  rewrite H1 in H.
  apply subst_fjtyp with t_x;auto.

Qed.

Lemma substbv_fjtyp : 
forall (g g':fjenv) (e : expr) (t : fjtype) (x:vname) (v_x:expr) (t_x:fjtype),
HasFJtype (concatF (FCons x t_x g) g') (open_at 1 x e) t -> ~ Elem x (fv e)
                -> uniqueF g -> uniqueF g'
                -> intersect (bindsFJ g) (bindsFJ g') = empty
                -> ~ (in_envFJ x g) -> ~ (in_envFJ x g') 
                -> isLC v_x -> HasFJtype g v_x t_x
                -> HasFJtype (concatF g g') (subBV_at 1 v_x e) t.
Proof. intros; apply substbv_fjtyp' with (concatF (FCons x t_x g) g') x t_x;
trivial. Qed.

Lemma aux1: forall x0 ps,  PEmpty = openP_at 1 x0 ps -> ps = PEmpty.
Proof.
  intros.
  induction ps.
  simpl in *.
  reflexivity.
  simpl in H.
  inversion H.
Qed.

Lemma aux2: forall p ps0 x0 ps,  PCons p ps0 = openP_at 1 x0 ps -> exists p' ps', ps = PCons p' ps' /\ p = open_at 1 x0 p' /\ ps0 = openP_at 1 x0 ps'.
Proof.
  intros.
  induction ps.
  simpl in *.
  inversion H.
  simpl in H.
  inversion H.
  exists p0. exists ps.
  constructor. constructor.
  constructor. constructor.
  reflexivity.
Qed.


Lemma substbv_pbool' : forall (g'xg : fjenv) (ps : preds) (x:vname),
  PIsBool g'xg (openP_at 1 x ps) -> ~Elem x (fvP ps)-> ( forall (g g':fjenv) (v_x:expr) (t_x:fjtype),
     g'xg = concatF (FCons x t_x g) g' 
                   -> uniqueF g -> uniqueF g'
                   -> intersect (bindsFJ g) (bindsFJ g') = empty
                   -> ~ (in_envFJ x g) -> ~ (in_envFJ x g') 
                   -> isLC v_x -> HasFJtype g v_x t_x
                   -> PIsBool (concatF g g') (psubBV_at 1 v_x ps) ).
Proof. 
intros env; intros. dependent induction H.
- apply aux1 in x. rewrite x. simpl. apply PFTEmp.
- apply aux2 in x. destruct x as [p' [ps']]. destruct H10. destruct H11. rewrite H10.
  simpl. apply PFTCons. rewrite H10 in H1. simpl in H1. apply substbv_fjtyp with x0 t_x;auto.
  subst g. subst p. apply H.
  notin_solve_one.
  subst g. subst p. eapply IHPIsBool;eauto.
  rewrite H10 in H1. simpl in H1. notin_solve_one.
Qed.
