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



(*---------------Narrowing Lemmas of WF---------------*)

Lemma narrow_fjtyp: forall (g'xg : fjenv) e (t : fjtype),
    HasFJtype g'xg e t -> forall (g g' : fjenv) (x : vname) (s_x:fjtype) (t_x:fjtype),
    g'xg = concatF (FCons x t_x g) g' 
                -> uniqueF g -> uniqueF g'
                -> intersect (bindsFJ g) (bindsFJ g') = empty
                -> ~ (in_envFJ x g) -> ~ (in_envFJ x g') 
                -> FJSubtype s_x t_x
                -> HasFJtype (concatF (FCons x s_x g) g') e t.
Proof.
apply ( HasFJtype_ind'
(fun (g'xg : fjenv) (e : expr) (t : fjtype) => 
    forall (g g' : fjenv) (x : vname) (s_x:fjtype) (t_x:fjtype),
    g'xg = concatF (FCons x t_x g) g' 
    -> uniqueF g -> uniqueF g'
    -> intersect (bindsFJ g) (bindsFJ g') = empty
    -> ~ (in_envFJ x g) -> ~ (in_envFJ x g') 
    -> FJSubtype s_x t_x
    -> HasFJtype (concatF (FCons x s_x g) g') e t));
  intros env; intros; subst env.
  - apply FTBC.
  - apply FTIC.
  - apply boundinF_concatF in H; simpl in H; destruct H. destruct H.
  * (* x = x0 *) destruct H; subst x0; subst b; simpl.
    apply FTSub with s_x;auto.
    apply FTVar. apply boundinF_concatF; intuition. left. simpl. left. constructor;auto.
  * (* x0 in g *) apply boundin_inenvFJ in H as H'.
    pose proof bindsFJ_subset as Htv; unfold Subset in Htv; apply Htv in H';
    assert (x0 <> x) by (unfold not; intro; subst x0; contradiction).
    apply FTVar. apply boundinF_concatF; intuition. left. simpl. right. auto.
  * (* x0 in g' *) apply boundin_inenvFJ in H as H'.
    pose proof bindsFJ_subset as Htv; unfold Subset in Htv; apply Htv in H';
    assert (x0 <> x) by (unfold not; intro; subst x0; contradiction).
    apply FTVar; apply boundinF_concatF; intuition.
  - apply FTUnOP;eauto.      
  - apply FTBinOP;eauto.
  - eapply FTInvok;eauto.
  - eapply FTInvokI;eauto.
  - eapply FTField;eauto.
  - eapply FTNew;eauto. 
    clear H.
    generalize dependent Us.
    induction es. intros. destruct Us. apply Forall2_nil. inversion H2.
    intros. destruct Us. inversion H2. inversion H3. inversion H2. apply Forall2_cons. eapply H12;eauto. apply IHes;auto. 
  - eapply FTLet;eauto. intros. assert ((FCons y b (concatF (FCons x s_x g) g')) = (concatF (FCons x s_x g) (FCons y b g' ))). reflexivity. rewrite H10.
    assert (~Elem y (union (singleton x) (union (bindsFJ g') (union (bindsFJ g) nms)))). apply H3.  
    apply H2 with t_x;eauto. notin_solve_one. simpl. constructor;auto. unfold in_envFJ. notin_solve_one.
    simpl. apply intersect_names_add_intro_r;auto. notin_solve_one. unfold in_envFJ. simpl. apply not_elem_names_add_intro. constructor;auto. 
    assert (y<>x). apply not_elem_singleton. notin_solve_one. auto.
  - apply FTSub with s;eauto. 
Qed.
Lemma narrow_pbool: forall (g'xg : fjenv) e,
    PIsBool g'xg e -> forall (g g' : fjenv) (x : vname) (s_x:fjtype) (t_x:fjtype),
    g'xg = concatF (FCons x t_x g) g' 
                -> uniqueF g -> uniqueF g'
                -> intersect (bindsFJ g) (bindsFJ g') = empty
                -> ~ (in_envFJ x g) -> ~ (in_envFJ x g') 
                -> FJSubtype s_x t_x
                -> PIsBool (concatF (FCons x s_x g) g') e.
Proof.
  intros. induction H.
  -
    apply PFTEmp.
  -
    apply PFTCons.
    eapply narrow_fjtyp;eauto.
    apply IHPIsBool;auto.
Qed.



Lemma narrow_wf' : forall (g'xg : env) (t : type),
    WFtype g'xg t -> forall (g g' : env) (x : vname) (s_x:type) (t_x:type),
        g'xg = concatE (Cons x t_x g) g' 
                    -> unique g -> unique g'
                    -> intersect (binds g) (binds g') = empty
                    -> ~ (in_env x g) -> ~ (in_env x g') 
                    -> Subtype g s_x t_x
                    -> WFtype (concatE (Cons x s_x g) g') t.
Proof. apply ( WFtype_ind
  (fun (g'xg : env) (t : type) =>
    forall (g g' : env) (x : vname) (s_x:type) (t_x:type),
        g'xg = concatE (Cons x t_x g) g' 
                    -> unique g -> unique g'
                    -> intersect (binds g) (binds g') = empty
                    -> ~ (in_env x g) -> ~ (in_env x g') 
                    -> Subtype g s_x t_x
                    -> WFtype (concatE (Cons x s_x g) g') t) );
  intro env; intros; subst env.
  - (* WFBase *) apply WFBase; apply H.
  - (* WFRefn *) apply WFRefn with (union (singleton x) (union (binds g') (union (binds g) nms))); try apply H0 with t_x; intros;
    rewrite erase_concat in H2; simpl in H2;
    try rewrite erase_concat; simpl;
    try apply erase_subtype in H9 as Hsx; try rewrite Hsx; try apply H2;auto. 
    assert (FCons y b (concatF (FCons x (erase s_x) (erase_env g)) (erase_env g')) = concatF (FCons x (erase s_x) (erase_env g)) (FCons y b (erase_env g'))) by reflexivity. rewrite H10.
    eapply narrow_pbool. apply H2;auto. notin_solve_one. reflexivity. auto. apply unique_erase_env. auto. simpl. constructor. unfold in_envFJ. rewrite <- binds_erase_env. notin_solve_one. apply unique_erase_env. auto.
    simpl. apply intersect_names_add_intro_r. rewrite <- binds_erase_env. rewrite <- binds_erase_env. auto. rewrite <- binds_erase_env. notin_solve_one. unfold in_envFJ. rewrite <- binds_erase_env. unfold in_env in H7. notin_solve_one.
    unfold in_envFJ. simpl. apply not_elem_names_add_intro. constructor. unfold not. intros. assert (y<>x). apply not_elem_singleton. notin_solve_one. rewrite H11 in H12. contradiction. rewrite <- binds_erase_env. auto. 
    eapply subtype_fsubtype;eauto.
  Qed.
Lemma narrow_wf'_forall : forall (g'xg : env) (ts : [type]),
Forall (WFtype g'xg) ts -> forall (g g' : env) (x : vname) (s_x:type) (t_x:type),
    g'xg = concatE (Cons x t_x g) g' 
                -> unique g -> unique g'
                -> intersect (binds g) (binds g') = empty
                -> ~ (in_env x g) -> ~ (in_env x g') 
                -> Subtype g s_x t_x
                -> Forall (WFtype (concatE (Cons x s_x g) g')) ts.
Proof.
  intros.
  induction ts.
  apply Forall_nil.
  inversion H.
  apply Forall_cons;auto.
  subst g'xg. eapply narrow_wf';eauto.
Qed.

Lemma narrow_wf : forall (g g':env) (x:vname) (s_x:type) (t_x:type) (t:type),
    WFtype (concatE (Cons x t_x g) g') t 
                    -> unique g -> unique g'
                    -> intersect (binds g) (binds g') = empty
                    -> ~ (in_env x g) -> ~ (in_env x g') 
                    -> Subtype g s_x t_x
                    -> WFtype (concatE (Cons x s_x g) g') t.
Proof. intros; apply narrow_wf' with (concatE (Cons x t_x g) g') t_x; trivial. Qed.

Lemma narrow_wf_top : forall (g:env) (x:vname) (s_x:type) (t_x:type) (t:type),
    WFtype (Cons x t_x g) t -> unique g 
                              -> ~ (in_env x g) 
                              -> Subtype g s_x t_x
                              -> WFtype (Cons x s_x g) t.
Proof. intros; assert (Cons x s_x g = concatE (Cons x s_x g) Empty) by reflexivity;
  rewrite H3; apply narrow_wf with t_x; try apply intersect_empty_r;
  simpl; intuition. Qed. 
Lemma narrow_wf_under: forall ps ps' b2 b3 t, Subtype Empty (TRefn (TNom b2) ps') (TRefn (TNom b3) ps) -> wf_under (TRefn (TNom b3) ps) t -> wf_under (TRefn (TNom b2) ps') t.
Proof.
  intros.
  unfold wf_under in *.
  intros.
  apply narrow_wf_top with (TRefn (TNom b3) ps);simpl;auto.
  (* apply SBase with nms;auto. intros. apply IRefl. *)
Qed.