Require Import Coq.Program.Equality.
Require Import Relations Decidable.
Require Import Forall2.
Require Import Lists.
Require Import ZArith.

Require Import RFJ.Utils.
Require Import Tactics.
Require Import RFJ.Utils.Referable.

Require Export Definitions.Syntax.
Require Export Definitions.Names.
Require Import Definitions.FJTyping.

Require Import Definitions.SubDenotation.

Require Import Definitions.Typing.
Require Import Definitions.CTSanity.
Require Export Definitions.Semantics.

Require Import Lemmas.BasicLemmas.LemmasFJTyping.
Require Import Lemmas.BasicLemmas.LemmasEnvironments.
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasSubstitution. 
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasWF.
Require Import Lemmas.BasicLemmas.LemmasWFNarrow.
Require Import Lemmas.BasicLemmas.LemmasWFNarrow.
Require Import Lemmas.BasicLemmas.LemmasWFSubstitution.
Require Import Lemmas.BasicLemmas.LemmasWFWeaken.
Require Import Lemmas.LogicalLemmas.LemmasSImp.
Require Import Lemmas.LogicalLemmas.LemmasCSubst.



(*---------------Basic Properties of Class Table---------------*)


(*---------------Lemmas Concerning MDefns in Class Table---------------*)
Lemma methodDecl_OK :forall C D0 Fs noDupfs K Ms noDupMds C0 m fargs ret ps Is,
  find m Ms = Some (MDefn (MDecl C0 m ps fargs) ret) ->
  find C RefCT = Some (RefCDecl C D0 Is Fs noDupfs K Ms noDupMds) ->
  MType_OK C (MDefn (MDecl C0 m ps fargs) ret).
Proof.
  intros.
  assert (CType_OK (RefCDecl C D0 Is Fs noDupfs K Ms noDupMds)). apply cok;auto.
  inversion H1.
  eapply Forall_find. 
  apply H11.
  apply H.
Qed.

Lemma methodDecl_OK_override: forall C D Fs noDupfs K Ms Is noDupMds m t t0 e ps,
              find C RefCT = Some (RefCDecl C D Is Fs noDupfs K Ms noDupMds) ->
              MType_OK C (MDefn (MDecl t m ps t0) e) -> override m C D ps t0 t.
Proof.
  intros. inversion H0. rewrite H in H6. inversion H6. subst D0. auto.
Qed.
Lemma methods_sub_exists: forall C D Is Fs noDupfs K Ms noDupMds Ds D0 m ps,
    find C RefCT = Some (RefCDecl C D Is Fs noDupfs K Ms noDupMds) ->
    mtype(m, D) = ps ~> Ds ~> D0 ->
    (exists ps' Ds' D0', mtype(m, C) = ps' ~> Ds' ~> D0').
Proof.
  intros.
  case_eq (find m Ms);intros. (*only case_eq works here*)
  -
    intros.
    assert (ref m0 = m).
    apply find_ref_inv with Ms;auto.
    destruct m0. (*destruct vs inversion here*)
    simpl in H2. destruct m0.
    assert (MType_OK C (MDefn (MDecl t m0 p t0) e)).
    
    eapply methodDecl_OK.
    rewrite <- H2 in H1.
    apply H1.
    apply H.
    rewrite H2 in H3.

    assert (override m C D p t0 t). eapply methodDecl_OK_override;eauto.
    unfold override in H4.
    assert (mtype( m, D)= ps ~> Ds ~> D0) by auto. 
    apply H4 in H5. destruct H5. destruct H6. subst m0. exists p. exists t0. exists t.
    eapply mty_ok;eauto.
  -
    intros. exists ps. exists Ds. exists D0.
    eapply mty_no_override;eauto.
Qed.
Lemma mbody_det: forall m C e e0, mbody( m, C)= e -> mbody( m, C)= e0 -> e = e0.
Proof.
  intros. induction H.
  -
    inversion H0;rewrite H in H2;inversion H2;subst Ms0;rewrite H1 in H3. 
    inversion H3. auto.
    inversion H3.
  -
    inversion H0; rewrite H in H3;inversion H3;subst Ms0; rewrite H1 in H4. 
    inversion H4.  
    subst D0. apply IHm_body;auto.
Qed.
Lemma class_sub_type': forall C0 ps C m t rt, FJSubtype (TNom (TClass C0)) (TNom (TClass C)) -> mtype(m, C) = ps ~> t ~> rt -> (exists ps' t' rt', mtype(m, C0) = ps' ~> t' ~> rt').
Proof.
  intros.
  inversion H.
  subst C1. subst D.
  generalize dependent t. generalize dependent rt. generalize dependent ps.
  dependent induction H3.
  -
  intros. exists ps. exists t. exists rt. auto. 
  -
  rename C0 into b1. rename C into b3.
  assert (exists xx, b2 = TClass xx). eapply subclass_class;eauto. destruct H0 as [xx]. subst b2. rename xx into b2.

  intros.
  assert (FJSubtype (TNom (TClass b2)) (TNom (TClass b3))). apply SubBClass. auto. eapply IHSubClass2 in H1;eauto. destruct H1 as [ps' [t' [rt']]].
  assert (FJSubtype (TNom (TClass b1)) (TNom (TClass b2))). apply SubBClass. auto. eapply IHSubClass1 in H2;auto.
  apply H1.
  -
  intros.
  apply cok in H0. inversion H0. eapply methods_sub_exists in H13. Focus 2. apply H1.
  destruct H13 as [ps'[Ds'[D0']]]. exists ps'.  exists Ds'. exists D0'. auto.
Qed. 


Lemma reffields_NoDup : forall C fs,
  Reffields C fs ->
  NoDup (refs fs).
Proof.
  intros.
  induction H.
  -
    simpl.
    crush.
  -
    assumption.
Qed.

Lemma fields_i_eq: forall (A:Type) L1 i i0 (l1:A) (l2:A), 
                  nth_error L1 i = Some l1 ->
                  NoDup L1 -> 
                  nth_error L1 i0 = Some l2 ->
                  l1 = l2 -> i = i0. 
Proof.
  intros.
  generalize dependent i0. generalize dependent i.
  induction L1.
  -
    intros.
    destruct i.
    simpl in H. inversion H.
    simpl in H. inversion H.
  -
    intros.
    destruct i.
    destruct i0.
    reflexivity.
    simpl in H. simpl in H1. rewrite <- H2 in H1. rewrite <-H in H1. 
    inversion H0. apply nth_error_In in H1. contradiction.
    destruct i0.
    simpl in H. simpl in H1. rewrite <- H2 in H1. rewrite <-H1 in H. 
    inversion H0. apply nth_error_In in H. contradiction.

    simpl in H. simpl in H1. inversion H0.
    f_equal.
    apply IHL1;auto.
Qed.
Lemma subtype_fields: forall C D fs ,
  SubClass (TClass C)  (TClass D) ->
  Reffields D fs ->
  exists fs', Reffields C (fs ++ fs').
Proof.
  intros. generalize dependent H0. generalize dependent fs.
  (dependent induction H); intros.
  -
    exists (@nil RefFieldDecl). rewrite app_nil_r.  simpl; auto. 
  -
    assert (exists bb, b2 = TClass bb). eapply subclass_class;eauto. destruct H2 as [bb]. subst b2.
    assert (exists fs', Reffields bb (fs ++ fs')). eapply IHSubClass2;auto. destruct H2 as [fs'].
    eapply IHSubClass1 in H2;eauto. destruct H2 as [fs'0]. exists (fs' ++ fs'0).  rewrite app_assoc. auto.
  -
    exists fs. eapply RefF_Decl;eauto.
    assert (CType_OK (RefCDecl C D Is fs noDupfs K mds noDupMds)). apply cok;auto. inversion H1.
    assert (fs0 = fdecl). eapply reffields_det;eauto. subst fdecl. auto.
Qed.

Lemma subtype_field_nth_same: forall c C Fs Fs1 i fi, 
    SubClass (TClass c) (TClass C) -> Reffields C Fs -> Reffields c Fs1 -> nth_error Fs i = Some fi -> nth_error Fs1 i = Some fi.
Proof.
  intros. assert (exists fs', Reffields c (Fs ++ fs')). apply subtype_fields with C;auto.
  destruct H3 as [fs']. assert (Fs1 = (Fs ++ fs')). apply reffields_det with c;auto.
  rewrite H4. apply env_weaken. auto.
Qed.

(*---------------Lemmas Linking mtype with mbody---------------*)

Lemma mtype_mbody': forall m C ps t rt, mtype( m, C)= ps ~> t ~> rt ->  exists mb, mbody( m, C)= mb.
Proof.
  intros.
  induction H. exists e. eapply mbdy_ok;eauto. destruct IHm_type as [mb]. exists mb. eapply mbdy_no_override;eauto.
Qed.
Lemma mbody_mtype': forall m C mb, mbody( m, C)= mb ->  exists ps t rt, mtype( m, C)= ps ~> t ~> rt.
Proof.
  intros.
  induction H. exists ps. exists t. exists rt. eapply mty_ok;eauto. destruct IHm_body as [ps[t[rt]]]. exists ps. exists t. exists rt. eapply mty_no_override;eauto.
Qed.

Lemma find_method_name: forall m mds m0 e ps rt t, find m mds = Some (MDefn (MDecl rt m0 ps t) e) -> m0 = m.
Proof.
  intros.
  assert (m0 = ref (MDefn (MDecl rt m0 ps t) e)). simpl. reflexivity.
  rewrite H0. apply find_ref_inv with mds;auto.
Qed.
Lemma mtype_mbody: forall m C c t rt ps, SubClass (TClass c) (TClass C) -> mtype( m, C)= ps ~> t ~> rt ->  exists mb, mbody( m, c)= mb.
Proof.
  intros.
  generalize dependent t. generalize dependent rt. generalize dependent ps.
  dependent induction H.
  intros. eapply mtype_mbody';eauto. 
  intros. assert (exists bb, b2 = TClass bb). eapply subclass_class;eauto. destruct H2 as [bb]. subst b2. rename bb into b2. assert (exists ps' t' rt', mtype(m, b2) = ps' ~> t' ~> rt'). apply class_sub_type' with ps C t rt. apply SubBClass. auto. auto. destruct H2 as [ps'[t'[rt']]]. eapply IHSubClass1;eauto. 
  intros. assert (exists mb, mbody( m, C)= mb). apply mtype_mbody' with ps t rt;auto. destruct H1 as [mb].
  case_eq (find m mds). intros. destruct m0. exists e. destruct m0. apply mbdy_ok with C Is p t0 t1 fs K mds noDupfs noDupMds;auto. assert (m0 = m).  apply find_method_name with mds e p t0 t1;auto. subst m0. auto.
  intros. exists mb. apply mbdy_no_override with C Is fs K mds noDupfs noDupMds;auto.
Qed.  
Lemma mbody_mbody: forall m C c t rt ps, SubClass (TClass c) (TClass C) -> mtype( m, C)= ps ~> t ~> rt ->  exists mb, mbody( m, c)= mb.
Proof.
  intros.
  generalize dependent t. generalize dependent rt. generalize dependent ps.
  dependent induction H.
  intros. eapply mtype_mbody';eauto. 
  intros. assert (exists bb, b2 = TClass bb). eapply subclass_class;eauto. destruct H2 as [bb]. subst b2. rename bb into b2. assert (exists ps' t' rt', mtype(m, b2) = ps' ~> t' ~> rt'). apply class_sub_type' with ps C t rt. apply SubBClass. auto. auto. destruct H2 as [ps'[t'[rt']]]. eapply IHSubClass1;eauto. 
  intros. assert (exists mb, mbody( m, C)= mb). apply mtype_mbody' with ps t rt;auto. destruct H1 as [mb].
  case_eq (find m mds). intros. destruct m0. exists e. destruct m0. apply mbdy_ok with C Is p t0 t1 fs K mds noDupfs noDupMds;auto. assert (m0 = m).  apply find_method_name with mds e p t0 t1;auto. subst m0. auto.
  intros. exists mb. apply mbdy_no_override with C Is fs K mds noDupfs noDupMds;auto.
Qed.  
Lemma mtypei_mbody: forall m C c t rt ps, SubClass (TClass c) (TInterface C) -> mtypei( m, C)= ps ~> t ~> rt ->  exists mb, mbody( m, c)= mb.
Proof.
  intros.
  generalize dependent t. generalize dependent rt. generalize dependent ps.
  dependent induction H.
  -
  intros.
  apply subclass_class' in H0 as HH. destruct HH. subst b2.
  eapply IHSubClass1 in H1;eauto.
  destruct H2 as [bb]. subst b2.
  assert (exists mb, mbody( m, bb)= mb). apply IHSubClass2 with C ps rt t;auto.

  destruct H2 as [mb].
  apply mbody_mtype' in H2. destruct H2 as [ps'[t'[rt']]].
  eapply mbody_mbody;eauto.
  -
  intros.
  apply cok in H. inversion H.
  inversion H1.
  eapply H14 in H0;eauto.
  inversion H0.
  rewrite H22 in H15. inversion H15. subst Ms0.
  apply H23 in H16. 
  unfold implement in H16.
  destruct H16 as [tt[tt0[ps']]].
  destruct H16.
  eapply mtype_mbody';eauto.
Qed.  





(*---------------Basic Properties of mtype and mbody---------------*)
Lemma mtypei_rt_no_fv: forall m C ps t rt, mtypei(m, C) = ps ~> t ~> rt -> free rt = empty.
Proof.
  intros.
  induction H.
  apply iok in H. inversion H.
  assert (MType_OK_I I (MDecl rt m ps t)). eapply Forall_find;eauto. inversion H5.
  apply H15.
Qed.
Lemma mtypei_t_no_fv: forall m C ps t rt, mtypei(m, C) = ps ~> t ~> rt -> free t = empty.
Proof.
  intros.
  induction H.
  apply iok in H. inversion H.
  assert (MType_OK_I I (MDecl rt m ps t)). eapply Forall_find;eauto. inversion H5.
  apply H14.
Qed.
Lemma mtypei_t_no_fvP: forall m C ps t rt, mtypei(m, C) = ps ~> t ~> rt -> fvP ps = empty.
Proof.
  intros.
  induction H.
  apply iok in H. inversion H.
  assert (MType_OK_I I (MDecl rt m ps t)). eapply Forall_find;eauto. inversion H5.
  assert (free ((TRefn (TNom (TInterface I)) ps)) = empty). apply wftype_closedtype;auto.  simpl in H16. auto.
Qed.

Lemma mtype_rt_no_fv: forall m C ps t rt, mtype(m, C) = ps ~> t ~> rt -> free rt = empty.
Proof.
  intros.
  induction H.
  apply cok in H. inversion H.
  assert (MType_OK C (MDefn (MDecl rt m ps t) e)). eapply Forall_find;eauto. inversion H14. auto. 
  auto. 
Qed.
Lemma mtype_t_no_fv: forall m C ps t rt, mtype(m, C) = ps ~> t ~> rt -> free t = empty.
Proof.
  intros.
  induction H.
  apply cok in H. inversion H.
  assert (MType_OK C (MDefn (MDecl rt m ps t) e)). eapply Forall_find;eauto. inversion H14. auto. 
  auto.
Qed.
Lemma mtype_t_no_fvP: forall m C ps t rt, mtype(m, C) = ps ~> t ~> rt -> fvP ps = empty.
Proof.
  intros.
  induction H.
  apply cok in H. inversion H.
  assert (MType_OK C (MDefn (MDecl rt m ps t) e)). eapply Forall_find;eauto. inversion H14. auto.
  assert (free ((TRefn (TNom (TClass C)) ps)) = empty). apply wftype_closedtype;auto. simpl in H30. auto.
  auto.
Qed.

Lemma mbody_no_fv: forall m C e, mbody(m, C) = e -> fv e = empty.
Proof.
  intros.
  induction H.
  -
  apply cok in H. inversion H.
  assert (MType_OK C (MDefn (MDecl rt m ps t) e)). eapply Forall_find;eauto. inversion H14.
  auto.
  -
  auto.
Qed.

Lemma mbody_subBv_no_fv: forall m C e v1 v2, mbody(m, C) = e -> isValue v1 -> isValue v2 -> fv (subBV_at 1 v1 (subBV v2 e)) = empty.
Proof.
  intros.
  apply subset_empty_intro with (union (fv v1) (fv (subBV v2 e))). apply fv_subBV_elim'. 
  apply subset_empty_intro with (union (fv v1) (union (fv v2) (fv e))). apply subset_union_both. apply subset_refl. apply fv_subBV_elim'. 
  apply union_eq_empty_intro. constructor. apply value_closed. auto.
  apply union_eq_empty_intro. constructor. apply value_closed. auto. eapply mbody_no_fv;eauto.
Qed.





Lemma fieldtype_no_fv: forall C Fs fi i, Reffields C Fs -> nth_error Fs i = Some fi -> free (ReffieldType fi) = empty.
Proof.
  intros.
  generalize dependent i.
  induction H.
  intros. destruct i; simpl in H0; inversion H0.
  apply cok in H. inversion H.
  intros. apply nth_error_app in H15. destruct H15. eapply IHReffields;eauto. 
  destruct H15 as [j]. destruct H15.  assert (FType_OK C fi). apply forall_nth_error with fs j;auto. inversion H17. auto.
Qed.
Lemma aux1: forall C fs, Forall (FType_OK C) fs -> Forall (fun t : type => free t = empty) (map ReffieldType fs).
Proof.
  intros.
  induction fs.
  apply Forall_nil.
  inversion H.
  apply Forall_cons. inversion H2. auto.
  apply IHfs. auto.
Qed.
Lemma fieldtype_no_fv_forall: forall C Fs Us, Reffields C Fs -> Us = map ReffieldType Fs -> Forall (fun t => free t = empty) Us.
Proof.
  intros.
  generalize dependent Us.
  induction H.
  intros. simpl in H0; inversion H0. apply Forall_nil.
  apply cok in H. inversion H.
  intros. rewrite map_app in H15. rewrite H15.
  apply Forall_app. constructor. apply IHReffields. auto.
  apply aux1 in H12. auto.
Qed.






(*---------------WF Properties of mtype and mbody---------------*)

Lemma wf_narrow_subclass: forall C D ps, SubClass D C -> WFtype Empty (TRefn (TNom C) ps) -> WFtype Empty (TRefn (TNom D) ps).
Proof.
  intros.
  inversion H0. apply WFBase.
  apply WFRefn with nms. apply WFBase. auto. intros.
  assert (FCons y (TNom D) (erase_env Empty) = concatF (FCons y (TNom D) (erase_env Empty)) FEmpty). reflexivity. rewrite H8.
  assert (FCons y (TNom C) (erase_env Empty) = concatF (FCons y (TNom  C) (erase_env Empty)) FEmpty). reflexivity.
  apply narrow_pbool with (concatF (FCons y (TNom C) (erase_env Empty)) FEmpty) (TNom C); simpl; auto.
Qed.
Lemma wf_narrow_fsubtype: forall C D ps, FJSubtype D C -> WFtype Empty (TRefn C ps) -> WFtype Empty (TRefn D ps).
Proof.
  intros.
  inversion H; subst C; subst D;auto.
  inversion H0. apply WFBase.
  apply WFRefn with nms;auto. intros. apply H6 in H7.
  assert ((FCons y t (erase_env Empty)) = concatF ((FCons y t (erase_env Empty))) FEmpty). auto. rewrite H8.
  apply narrow_pbool with (concatF ((FCons y TAny (erase_env Empty))) FEmpty) TAny;simpl;auto.
  eapply wf_narrow_subclass;eauto. 
Qed.
Lemma wf_narrow_subclass': forall C D ps g, SubClass D C -> WFtype g (TRefn (TNom C) ps) -> WFEnv g ->  WFtype g (TRefn (TNom D) ps).
Proof.
  intros.
  inversion H0. apply WFBase.
  apply WFRefn with (union (binds g)nms). apply WFBase. auto. intros.
  assert (FCons y (TNom D) (erase_env g) = concatF (FCons y (TNom D) (erase_env g)) FEmpty). reflexivity. rewrite H9.
  assert (FCons y (TNom C) (erase_env g) = concatF (FCons y (TNom C) (erase_env g)) FEmpty). reflexivity.
  apply narrow_pbool with (concatF (FCons y (TNom  C) (erase_env g)) FEmpty) (TNom  C); simpl; auto. apply H7. notin_solve_one.
  apply unique_erase_env. apply wfenv_unique. auto. apply intersect_empty_r. unfold in_envFJ. rewrite <- binds_erase_env. notin_solve_one.

Qed.

Lemma mtype_t_wf: forall m C ps t rt, mtype(m, C) = ps ~> t ~> rt ->wf_under (TRefn (TNom (TClass C)) ps) t.
Proof.
  intros.
  unfold wf_under. intros.
  induction H.
  apply cok in H. inversion H.
  assert (MType_OK C (MDefn (MDecl rt m ps t) e)). eapply Forall_find;eauto. inversion H14. apply H24.
  eapply narrow_wf_top;simpl;eauto. 
  apply SBase with empty. apply SubBClass. eapply SubCInh;eauto.
  intros. apply IRefl. 
Qed.

Lemma mtype_rt_wf: forall m C ps t rt, mtype(m, C) = ps ~> t ~> rt ->wf_under2 (TRefn (TNom (TClass C)) ps) t rt.
Proof.
  intros.
  unfold wf_under2. intros.
  induction H.
  apply cok in H. inversion H.
  assert (MType_OK C (MDefn (MDecl rt m ps t) e)). eapply Forall_find;eauto. inversion H15. apply H27.
  auto.
  assert ((Cons y' (openT_at 0 y t) (Cons y (TRefn (TNom (TClass C)) ps) Empty)) = concatE (Cons y (TRefn (TNom (TClass C)) ps) Empty) (Cons y' (openT_at 0 y t) Empty)). reflexivity. rewrite H3. 
  
  assert ((Cons y' (openT_at 0 y t) (Cons y (TRefn (TNom (TClass D)) ps) Empty)) = concatE (Cons y (TRefn (TNom (TClass D)) ps) Empty) (Cons y' (openT_at 0 y t) Empty)). reflexivity.
  apply narrow_wf' with (concatE (Cons y (TRefn (TNom (TClass D)) ps) Empty) (Cons y' (openT_at 0 y t) Empty)) (TRefn (TNom (TClass D)) ps);simpl;eauto.
  unfold in_env. simpl. unfold not. intros. destruct H5. assert (y'<>y). auto. auto. auto.
  apply SBase with empty. apply SubBClass. eapply SubCInh;eauto.
  intros. apply IRefl. 
Qed.

Lemma mtype_ps_wf: forall m C ps t rt, mtype(m, C) = ps ~> t ~> rt ->WFtype Empty (TRefn (TNom (TClass C)) ps).
Proof.
  intros.
  induction H.
  apply cok in H. inversion H.
  assert (MType_OK C (MDefn (MDecl rt m ps t) e)). eapply Forall_find;eauto. inversion H14. apply H23.
  apply wf_narrow_subclass with (TClass D);auto. eapply SubCInh;eauto.
Qed.

Lemma mtype_ps_wf_g: forall m C ps t rt g, mtype(m, C) = ps ~> t ~> rt -> unique g -> WFtype g (TRefn (TNom (TClass C)) ps).
Proof.
  intros.
  assert (g = concatE g Empty). auto. rewrite H1. apply weaken_many_wf_r;simpl;auto. eapply mtype_ps_wf;eauto. apply intersect_empty_r;auto.
Qed.
Lemma mtypei_t_wf: forall m C ps t rt, mtypei(m, C) = ps ~> t ~> rt -> wf_under (TRefn (TNom (TInterface C)) ps) t.
Proof.
  intros.
  induction H.
  apply iok in H. inversion H.
  assert (MType_OK_I I (MDecl rt m ps t)). eapply Forall_find;eauto. inversion H5.
  apply H12.
Qed. 
Lemma mtypei_rt_wf: forall m C ps t rt, mtypei(m, C) = ps ~> t ~> rt ->wf_under2 (TRefn (TNom (TInterface C)) ps) t rt.
Proof.
  intros.
  induction H.
  apply iok in H. inversion H.
  assert (MType_OK_I I (MDecl rt m ps t)). eapply Forall_find;eauto. inversion H5.
  apply H13.
Qed.

Lemma mtypei_ps_wf: forall m C ps t rt, mtypei(m, C) = ps ~> t ~> rt ->WFtype Empty (TRefn (TNom (TInterface C)) ps).
Proof.
  intros.
  induction H.
  apply iok in H. inversion H.
  assert (MType_OK_I I (MDecl rt m ps t)). eapply Forall_find;eauto. inversion H5.
  apply H10.
Qed.
Lemma mtypei_ps_wf_g: forall m C ps t rt g, mtypei(m, C) = ps ~> t ~> rt -> unique g -> WFtype g (TRefn (TNom (TInterface C)) ps).
Proof.
  intros.
  assert (g = concatE g Empty). auto. rewrite H1. apply weaken_many_wf_r;simpl;auto. eapply mtypei_ps_wf;eauto. apply intersect_empty_r;auto.
Qed.
Lemma fieldtype_wf: forall C Fs fi i, Reffields C Fs -> nth_error Fs i = Some fi ->wf_under (TRefn (TNom (TClass C)) PEmpty) (ReffieldType fi).
Proof.
  intros.
  generalize dependent i.
  induction H.
  intros. destruct i; simpl in H0; inversion H0.
  apply cok in H. inversion H.
  intros. apply nth_error_app in H15. destruct H15. apply IHReffields in H15. apply narrow_wf_under with PEmpty (TClass D). apply SBase with empty. apply SubBClass. eapply SubCInh;eauto. intros. apply IRefl. auto.
  destruct H15 as [j]. destruct H15.  assert (FType_OK C fi). apply forall_nth_error with fs j;auto. inversion H17. auto.
Qed.
Lemma nth_length: forall (A:Type) Fs' (a:A) Fs, nth_error (Fs' ++ a :: Fs) (length Fs') = Some a.
Proof.
  intros. 
  induction Fs'. simpl. auto.
  simpl. auto.
Qed.
Lemma fieldtype_wf_forall: forall C Fs Fs', Reffields C (Fs' ++ Fs) ->  Forall (wf_under (TRefn (TNom (TClass C)) PEmpty)) (map ReffieldType Fs).
Proof.
  intros. generalize dependent Fs'. induction Fs.
  intros. apply Forall_nil.
  intros. apply Forall_cons. apply fieldtype_wf with ( (Fs' ++ a :: Fs)) (length Fs');auto. apply nth_length;auto. apply IHFs with (Fs':>a). simpl. rewrite <- snoc_app. auto.
Qed.
Lemma fieldtype_wf_forall': forall C Fs Fs', Reffields C (Fs' ++ Fs) -> (forall y, Forall (WFtype (Cons y (TRefn (TNom (TClass C)) PEmpty) Empty)) (map (openT_at 0 y) (map ReffieldType Fs))).
Proof.
  intros.
  apply fieldtype_wf_forall in H.
  induction Fs. intros. simpl. apply Forall_nil.
  inversion H. apply IHFs in H3. intros.
  apply Forall_cons. apply H2. apply H3.
Qed.


Lemma fieldtype_wf_tsub_forall: forall c Fs l, 
Reffields c Fs -> HasFJtype FEmpty (ExpNew c l) (TNom (TClass c)) -> isLC (ExpNew c l) ->  Forall (WFtype Empty) (map (tsubBV (ExpNew c l)) (map ReffieldType Fs)).
Proof.
  intros.
  assert ((forall y, Forall (WFtype (Cons y (TRefn (TNom (TClass c)) PEmpty) Empty)) (map (openT_at 0 y) (map ReffieldType Fs)))). apply fieldtype_wf_forall' with nil. simpl. auto. 
  remember (fresh (frees (map ReffieldType Fs))) as y.  assert (~Elem y (frees (map ReffieldType Fs))). rewrite Heqy. apply fresh_not_elem. 
  assert ((map (tsubBV (ExpNew c l)) (map ReffieldType Fs)) = (map (tsubFV y (ExpNew c l)) (map (openT_at 0 y) (map ReffieldType Fs)))). 
  rewrite tsubFV_unbindT_forall with y (ExpNew c l) (map ReffieldType Fs);auto. rewrite H4.
  apply subst_wf_top_forall with ( (TRefn (TNom (TClass c)) PEmpty));auto.
  ***
    simpl;auto.
Qed.


Lemma fieldtype_wf_subst_forall': forall C Fs Fs' g v, Reffields C (Fs' ++ Fs) -> unique g -> isLC v -> HasFJtype (erase_env g) v (TNom (TClass C)) -> Forall (WFtype g) (map (tsubBV v) (map ReffieldType Fs)).
Proof.
  intros.
  assert ((forall y, Forall (WFtype (Cons y (TRefn (TNom (TClass C)) PEmpty) Empty)) (map (openT_at 0 y) (map ReffieldType Fs)))). eapply fieldtype_wf_forall';eauto. 
  remember (fresh (union (frees (map ReffieldType Fs)) (binds g))) as y. assert (~Elem y (union (frees (map ReffieldType Fs)) (binds g))). rewrite Heqy. apply fresh_not_elem. assert (map (tsubBV v) (map ReffieldType Fs) = map (tsubFV y v) (map (openT_at 0 y) (map ReffieldType Fs))). apply tsubFV_unbindT_forall;notin_solve_one.
  rewrite H5.
  apply subst_wf_top_forall with (TRefn (TNom (TClass C)) PEmpty);simpl;auto.
  unfold in_env. notin_solve_one.
  assert ((Cons y (TRefn (TNom (TClass C)) PEmpty) g) = (concatE (g) (Cons y (TRefn (TNom (TClass C)) PEmpty) Empty))). simpl. auto. rewrite H6.
  apply weaken_many_wf_r_forall;auto.  
  simpl. constructor;simpl;auto. 
  assert (binds (Cons y (TRefn (TNom (TClass C)) PEmpty) Empty) = names_add y (binds (Empty))). simpl. auto. rewrite H7. apply intersect_names_add_intro_r. simpl. apply intersect_empty_r. notin_solve_one. 
Qed.
  

Lemma mtype_t_wf_sub_fjtype: forall m C ps t rt g e1, mtype(m, C) = ps ~> t ~> rt -> HasFJtype (erase_env g) e1 (erase (TRefn (TNom (TClass C)) ps)) -> 
WFEnv g -> isLC e1 -> 
WFtype g  (tsubBV e1 t).
Proof.
  intros. assert True. auto. 
  assert (wf_under (TRefn (TNom (TClass C)) ps) t). eapply mtype_t_wf;eauto.
  unfold wf_under in H4.
  eapply wf_sub_fjtype;eauto.
Qed.

(*---------------Basic Properties of csubst and Class Table---------------*)
Lemma csubst_mtype_ps: forall m C ps t rt th, mtype( m, C)= ps ~> t ~> rt ->  (ctsubst th (TRefn (TNom (TClass C)) ps)) = (TRefn (TNom (TClass C)) ps).
Proof.
  intros. rewrite ctsubst_nofree;auto.
  simpl.
  eapply mtype_t_no_fvP;eauto.
Qed.
Lemma csubst_mtypei_ps: forall m C ps t rt th, mtypei( m, C)= ps ~> t ~> rt ->  (ctsubst th (TRefn (TNom (TInterface C)) ps)) = (TRefn (TNom (TInterface C)) ps).
Proof.
  intros. rewrite ctsubst_nofree;auto.
  simpl.
  eapply mtypei_t_no_fvP;eauto.
Qed.
Lemma csubst_mtype_t: forall m C ps t rt th, mtype( m, C)= ps ~> t ~> rt ->  (ctsubst th t) = t.
Proof.
  intros. rewrite ctsubst_nofree;auto.
  eapply mtype_t_no_fv;eauto.
Qed.

Lemma csubst_mtype_rt: forall m C ps t rt th, mtype( m, C)= ps ~> t ~> rt ->  (ctsubst th rt) = rt.
Proof.
  intros. rewrite ctsubst_nofree;auto.
  eapply mtype_rt_no_fv;eauto.
Qed.
Lemma csubst_mtypei_t: forall m C ps t rt th, mtypei( m, C)= ps ~> t ~> rt ->  (ctsubst th t) = t.
Proof.
  intros. rewrite ctsubst_nofree;auto.
  eapply mtypei_t_no_fv;eauto.
Qed.
Lemma csubst_mtypei_rt: forall m C ps t rt th, mtypei( m, C)= ps ~> t ~> rt ->  (ctsubst th rt) = rt.
Proof.
  intros. rewrite ctsubst_nofree;auto.
  eapply mtypei_rt_no_fv;eauto.
Qed.

Lemma csubst_fjtype': forall C Fs fi i th, Reffields C Fs -> nth_error Fs i = Some fi -> (ctsubst th (ReffieldType fi)) = (ReffieldType fi).
Proof.
  intros. rewrite ctsubst_nofree;auto.
  eapply fieldtype_no_fv;eauto.
Qed.


Lemma csubst_fjtype: forall C Fs th Ts, Reffields C Fs -> Ts = (map ReffieldType Fs) -> map (ctsubst th) Ts = Ts.
Proof.
  intros. rewrite ctsubst_nofree_forall;auto.
  eapply fieldtype_no_fv_forall;eauto.
Qed.




