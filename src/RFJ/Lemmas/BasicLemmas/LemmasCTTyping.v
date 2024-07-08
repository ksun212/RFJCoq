Require Import Relations Decidable.
Require Import Forall2.
Require Import Lists.
Require Import ZArith.
Require Import Coq.Program.Equality.

Require Import RFJ.Utils.


Require Export Definitions.Syntax.
Require Export Definitions.Names.
Require Import Definitions.FJTyping.

Require Import Definitions.Semantics.
Require Import Definitions.SubDenotation.

Require Import Definitions.Typing.
Require Import Definitions.CTSanity.

Require Import Lemmas.TypingLemmas.LemmasTransitive.
Require Import Lemmas.BasicLemmas.LemmasFJTyping.
Require Import Lemmas.BasicLemmas.LemmasEnvironments.
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasSubstitution.
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasWFSubstitution.
Require Import Lemmas.BasicLemmas.LemmasWFWeaken.
Require Import Lemmas.BasicLemmas.LemmasWF.
Require Import Lemmas.BasicLemmas.LemmasWFNarrow.
Require Import Lemmas.BasicLemmas.LemmasWFSubstitution.
Require Import Lemmas.BasicLemmas.LemmasCTBasics.

Require Import Lemmas.LogicalLemmas.LemmasCSubst.
Require Import Lemmas.LogicalLemmas.LemmasSImp.
Require Import Lemmas.TypingLemmas.LemmasNarrowing.
Require Import Lemmas.TypingLemmas.LemmasWeakenTyp.
Require Import Lemmas.TypingLemmas.LemmasTyping.
Require Import Lemmas.TypingLemmas.LemmasRefl.



(*---------------More Basic Properties of Class Table---------------*)




(*---------------Pre-order Property of under and under2---------------*)
Lemma subtype_under_trans: forall C Ds Cs Es ps, WFtype Empty (TRefn (TNom (TClass C)) ps) -> 
wf_under (TRefn (TNom (TClass C)) ps) Cs -> wf_under (TRefn (TNom (TClass C)) ps) Ds -> wf_under (TRefn (TNom (TClass C)) ps) Es -> 
subtype_under (TRefn (TNom (TClass C)) ps) Cs Ds -> subtype_under (TRefn (TNom (TClass C)) ps) Ds Es -> subtype_under (TRefn (TNom (TClass C)) ps) Cs Es.
Proof.
  intros.
  unfold subtype_under in *.
  intros. apply sub_trans with (openT_at 0 y Ds);auto.
Qed.

Lemma subtype_under2_trans: forall C C0 D0 E0 Cs ps, subtype_under2 (TRefn (TNom (TClass C)) ps) Cs C0 D0 -> subtype_under2 (TRefn (TNom (TClass C)) ps) Cs D0 E0 -> 
WFtype Empty (TRefn (TNom (TClass C)) ps) ->
wf_under (TRefn (TNom (TClass C)) ps) Cs -> 
wf_under2 (TRefn (TNom (TClass C)) ps) Cs C0 -> wf_under2 (TRefn (TNom (TClass C)) ps) Cs D0 -> wf_under2 (TRefn (TNom (TClass C)) ps) Cs E0 -> 
subtype_under2 (TRefn (TNom (TClass C)) ps) Cs C0 E0.
Proof.
  intros.
  unfold subtype_under2 in *.
  intros. apply sub_trans with (openT_at 1 y (openT_at 0 y' D0));auto.
  apply WFEBind. apply WFEBind;simpl;auto. unfold in_env. simpl. unfold not. intros. destruct H7. assert (y'<>y). auto. auto. auto.
  apply H2.
Qed.
Lemma subtype_under_refl: forall C Cs ps, WFtype Empty (TRefn (TNom C) ps) -> 
wf_under (TRefn (TNom C) ps) Cs -> subtype_under (TRefn (TNom C) ps) Cs Cs.
Proof.
  intros.
  unfold subtype_under in *.
  intros.
  apply sub_refl. auto.
Qed.
Lemma subtype_under2_refl: forall C C0 Cs ps, WFtype Empty (TRefn (TNom C) ps) -> 
wf_under (TRefn (TNom C) ps) Cs -> wf_under2 (TRefn (TNom C) ps) Cs C0 ->
subtype_under2 (TRefn (TNom C) ps) Cs C0 C0.
Proof.
  intros.
  unfold subtype_under2 in *.
  intros. apply sub_refl. apply H1. auto. 
Qed.


Lemma subtype_under_narrow: forall C D Ds Cs ps ps', Subtype Empty (TRefn (TNom D) ps') (TRefn (TNom C) ps) -> wf_under (TRefn (TNom C) ps) Cs  -> wf_under (TRefn (TNom C) ps) Ds -> WFtype Empty (TRefn (TNom C) ps) -> WFtype Empty (TRefn (TNom D) ps') -> subtype_under (TRefn (TNom C) ps) Ds Cs -> subtype_under (TRefn (TNom D) ps') Ds Cs.
Proof.
  intros.
  unfold subtype_under in *.
  unfold wf_under in *.
  intros. 
  apply narrow_subtype_top with (TRefn (TNom C) ps);simpl;auto.
  apply narrow_wf_top with (TRefn (TNom C) ps);simpl;auto. 
  apply narrow_wf_top with (TRefn (TNom C) ps);simpl;auto. 
Qed.


Lemma narrow_wf_under2: forall ps ps' b2 b3 t t' tt, 
WFtype Empty (TRefn (TNom b2) ps') -> WFtype Empty (TRefn (TNom b3) ps) -> 
wf_under (TRefn (TNom b3) ps) t  -> wf_under(TRefn (TNom b2) ps') t' -> 
Subtype Empty (TRefn (TNom b2) ps') (TRefn (TNom b3) ps) -> subtype_under (TRefn (TNom b3) ps) t' t -> 
wf_under2 (TRefn (TNom b3) ps) t tt-> 
wf_under2 (TRefn (TNom b2) ps') t' tt.
Proof.
  intros.
  unfold wf_under in *. unfold wf_under2 in *.
  intros. 
  intros.
  assert (y' <> y). auto.
  apply narrow_wf_top with (openT_at 0 y t);simpl;auto. 
  assert (Cons y' (openT_at 0 y t) (Cons y (TRefn (TNom b2) ps') Empty) = concatE (Cons y (TRefn (TNom b2) ps') Empty) (Cons y' (openT_at 0 y t) Empty)). reflexivity.
  rewrite H8. apply narrow_wf' with (concatE (Cons y (TRefn (TNom b3) ps) Empty) (Cons y' (openT_at 0 y t) Empty)) (TRefn (TNom b3) ps);simpl;auto. 
  unfold in_env. simpl. unfold not. intros. destruct H9;auto.
  unfold in_env. simpl. unfold not. intros. destruct H8;auto.
  apply narrow_subtype_top with (TRefn (TNom b3) ps);simpl;auto. 
  apply narrow_wf_top with (TRefn (TNom b3) ps);simpl;auto. 
Qed.

Lemma subtype_under2_narrow: forall C D Ds Cs ps ps' t t', 
              Subtype Empty (TRefn (TNom D) ps') (TRefn (TNom C) ps) -> 
              wf_under (TRefn (TNom C) ps) t  -> wf_under (TRefn (TNom C) ps) t' -> 
              wf_under2 (TRefn (TNom C) ps) t Cs  -> wf_under2 (TRefn (TNom C) ps) t Ds -> 
              WFtype Empty (TRefn (TNom C) ps) -> WFtype Empty (TRefn (TNom D) ps') -> 
              subtype_under (TRefn (TNom C) ps) t' t-> 
              subtype_under2 (TRefn (TNom C) ps) t Ds Cs -> subtype_under2 (TRefn (TNom D) ps') t' Ds Cs.
Proof.
  intros.
  unfold subtype_under in *. unfold subtype_under2 in *. 
  intros. 
  remember H8 as neq. clear Heqneq.
  apply H7 in H8. 
  assert (Cons y' (openT_at 0 y t) (Cons y (TRefn (TNom D) ps') Empty) = concatE (Cons y (TRefn (TNom D) ps') Empty) (Cons y' (openT_at 0 y t) Empty)). reflexivity.
  
  apply narrow_subtype_top with (openT_at 0 y t);simpl;auto.
  rewrite H9.
  apply narrow_subtyp' with (concatE (Cons y (TRefn (TNom C) ps) Empty) (Cons y' (openT_at 0 y t) Empty)) (TRefn (TNom C) ps);simpl;auto.  
  unfold in_env. simpl. unfold not. intros. destruct H10;auto.
  apply WFEBind. apply WFEBind;simpl;auto. unfold in_env. simpl. unfold not. intros. destruct H10;auto.   apply narrow_wf_top with (TRefn (TNom C) ps);simpl;auto. 
  rewrite H9. apply narrow_wf' with (concatE (Cons y (TRefn (TNom C) ps) Empty) (Cons y' (openT_at 0 y t) Empty)) (TRefn (TNom C) ps);simpl;auto.
  unfold in_env. simpl. unfold not. intros. destruct H10;auto.
  unfold in_env. simpl. unfold not. intros. destruct H10;auto.
  apply narrow_wf_top with (TRefn (TNom C) ps);simpl;auto. 
  apply narrow_wf_top with (TRefn (TNom C) ps);simpl;auto. 
  apply narrow_subtype_top with (TRefn (TNom C) ps);simpl;auto.
  apply narrow_wf_top with (TRefn (TNom C) ps);simpl;auto. 
  apply narrow_wf_top with (TRefn (TNom C) ps);simpl;auto. 
  apply narrow_wf_top with (openT_at 0 y t);simpl;auto.
  rewrite H9. apply narrow_wf' with (concatE (Cons y (TRefn (TNom C) ps) Empty) (Cons y' (openT_at 0 y t) Empty)) (TRefn (TNom C) ps);simpl;auto.
  unfold in_env. simpl. unfold not. intros. destruct H10;auto.
  unfold in_env. simpl. unfold not. intros. destruct H10;auto.
  
  apply narrow_subtype_top with (TRefn (TNom C) ps) ;simpl;auto.
  apply narrow_wf_top with (TRefn (TNom C) ps);simpl;auto. 
  apply narrow_wf_top with (TRefn (TNom C) ps);simpl;auto. 
  apply narrow_wf_top with (openT_at 0 y t);simpl;auto.
  rewrite H9. apply narrow_wf' with (concatE (Cons y (TRefn (TNom C) ps) Empty) (Cons y' (openT_at 0 y t) Empty)) (TRefn (TNom C) ps);simpl;auto. 
  unfold in_env. simpl. unfold not. intros. destruct H10;auto.
  unfold in_env. simpl. unfold not. intros. destruct H10;auto.
  
  apply narrow_subtype_top with (TRefn (TNom C) ps) ;simpl;auto.
  apply narrow_wf_top with (TRefn (TNom C) ps);simpl;auto. 
  apply narrow_wf_top with (TRefn (TNom C) ps);simpl;auto. 
Qed.

(*---------------Properties of Narrowing and Class Table---------------*)
Lemma mtype_body_ok: forall m C t rt ps e, mtype( m, C)= ps ~> t ~> rt -> mbody( m, C)= e ->  (forall y y', y <> y' -> Hastype (Cons y' (openT_at 0 y t) (Cons y (TRefn (TNom (TClass C)) ps) Empty)) (open_at 1 y (open_at 0 y' e)) (openT_at 1 y (openT_at 0 y' rt))).
Proof.
  intros.
  induction H.
  apply cok in H. inversion H.
  
  inversion H0. assert (Ms1 = Ms). rewrite H16 in H14. inversion H14. auto. subst Ms1. rewrite H17 in H2. 
  inversion H2. subst rt0. subst e0. subst ps0. subst t0.  
  assert (MType_OK C (MDefn (MDecl rt m ps t) e)). eapply Forall_find;eauto. inversion H21. apply H34. auto.
  assert (Ms1 = Ms). rewrite H16 in H14. inversion H14. auto. subst Ms1. rewrite H17 in H2. inversion H2.
  inversion H0. assert (Ms0 = Ms). rewrite H4 in H. inversion H. auto. inversion H2. subst Ms0. rewrite H5 in H2. inversion H2.
  assert (Ms0 = Ms). rewrite H4 in H. inversion H. auto. subst Ms0. rewrite H4 in H. inversion H. subst K0. subst Fs0. subst e0. subst D0. subst m0. subst C0. 

  assert (wf_under (TRefn (TNom ((TClass D))) ps) t). eapply mtype_t_wf. eauto. 
  apply IHm_type in H6. intros. intros.
  assert (Cons y' (openT_at 0 y t) (Cons y (TRefn (TNom (TClass C)) ps) Empty) = concatE (Cons y (TRefn (TNom (TClass C)) ps) Empty) (Cons y' (openT_at 0 y t) Empty)). reflexivity.
  rewrite H8. apply narrow_typ' with (concatE (Cons y (TRefn (TNom ((TClass D))) ps) Empty) (Cons y' (openT_at 0 y t) Empty)) (TRefn (TNom ((TClass D))) ps);simpl;auto. 
  unfold in_env. simpl. unfold not. intros. destruct H9;auto. assert (y'<> y). auto. 
  apply wf_narrow_subclass with (TClass D).  eapply SubCInh;eauto. eapply mtype_ps_wf;eauto.
  eapply mtype_ps_wf;eauto.
  apply SBase with empty. apply SubBClass. eapply SubCInh. eauto. intros. apply IRefl.
  apply WFEBind. apply WFEBind;simpl;auto. apply wf_narrow_subclass with (TClass D).  eapply SubCInh;eauto. eapply mtype_ps_wf;eauto.
  unfold in_env. simpl. unfold not. intros. destruct H9;auto. assert (y'<> y). auto. 
  apply narrow_wf_top with (TRefn (TNom ((TClass D))) ps);simpl;auto. apply SBase with empty. apply SubBClass. eapply SubCInh. eauto. intros. apply IRefl.
Qed.

Lemma methods_subi_signature: forall C D Is Fs noDupfs K Ms noDupMds Ds D0 m ps i I,
    find C RefCT = Some (RefCDecl C D Is Fs noDupfs K Ms noDupMds) ->
    nth_error Is i = Some I -> 
    mtypei(m, I) = ps ~> Ds ~> D0 ->
    (exists Ds' D0' ps', mtype(m, C) = ps' ~> Ds' ~> D0' /\ Subtype Empty (TRefn (TNom (TClass C)) ps) (TRefn (TNom (TClass C)) ps') /\ subtype_under (TRefn (TNom (TClass C)) ps) Ds Ds' /\ subtype_under2 (TRefn (TNom (TClass C)) ps) Ds D0' D0).
Proof.
  intros.
  apply cok in H. inversion H.
  inversion H1.
  eapply H14 in H0.
  inversion H0. rewrite H15 in H22. inversion H22. subst Ms1.
  apply H23 in H16. unfold implement in H16. 
  eauto.
Qed.

Lemma methods_sub_signature: forall C D Is Fs noDupfs K Ms noDupMds Ds D0 m ps,
    find C RefCT = Some (RefCDecl C D Is Fs noDupfs K Ms noDupMds) ->
    mtype(m, D) = ps ~> Ds ~> D0 ->
    (exists ps' Ds' D0', mtype(m, C) = ps' ~> Ds' ~> D0' /\ Subtype Empty (TRefn (TNom (TClass C)) ps) (TRefn (TNom (TClass C)) ps') /\ subtype_under (TRefn (TNom (TClass C)) ps) Ds Ds' /\ subtype_under2 (TRefn (TNom (TClass C)) ps) Ds D0' D0).
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
    constructor. 
    eapply mty_ok;eauto.
    constructor;auto. 
  -
    intros. exists ps. exists Ds. exists D0.
    constructor. 
    eapply mty_no_override;eauto.
    constructor.
    apply sub_refl. apply wf_narrow_subclass with (TClass D);auto. eapply SubCInh;eauto. eapply mtype_ps_wf;eauto. 
    constructor.
    apply subtype_under_narrow with (TClass D) ps. apply SBase with empty. apply SubBClass. eapply SubCInh;eauto. intros. apply IRefl. 
    eapply mtype_t_wf;eauto.
    eapply mtype_t_wf;eauto.
    eapply mtype_ps_wf;eauto.
    apply wf_narrow_subclass with (TClass D). eapply SubCInh;eauto.  eapply mtype_ps_wf;eauto.
    apply subtype_under_refl. eapply mtype_ps_wf;eauto. eapply mtype_t_wf;eauto.
    
    apply subtype_under2_narrow with (TClass D) ps Ds. apply SBase with empty. apply SubBClass. eapply SubCInh;eauto. intros. apply IRefl. 
    eapply mtype_t_wf;eauto.
    eapply mtype_t_wf;eauto.
    eapply mtype_rt_wf;eauto.
    eapply mtype_rt_wf;eauto.
    eapply mtype_ps_wf;eauto.
    apply wf_narrow_subclass with (TClass D). eapply SubCInh;eauto.  eapply mtype_ps_wf;eauto.
    apply subtype_under_refl. eapply mtype_ps_wf;eauto. eapply mtype_t_wf;eauto.
    apply subtype_under2_refl. eapply mtype_ps_wf;eauto. eapply mtype_t_wf;eauto. eapply mtype_rt_wf;eauto. 
Qed.


Lemma class_sub': forall C0 ps C m t rt, FJSubtype (TNom (TClass C0)) (TNom (TClass C)) -> mtype(m, C) = ps ~> t ~> rt -> (exists ps' t' rt', mtype(m, C0) = ps' ~> t' ~> rt' /\ Subtype Empty (TRefn (TNom (TClass C0)) ps) (TRefn (TNom (TClass C0)) ps') /\ subtype_under (TRefn (TNom (TClass C0)) ps) t t' /\ subtype_under2 (TRefn (TNom (TClass C0)) ps) t rt' rt).
Proof.
  intros.
  inversion H.
  subst C1. subst D.
  generalize dependent t. generalize dependent rt. generalize dependent ps.
  dependent induction H3.
  -
  intros. exists ps. exists t. exists rt. constructor;auto.
  unfold subtype_under. intros. assert ((forall y, WFtype (Cons y (TRefn (TNom (TClass C)) ps) Empty) (openT_at 0 y t))). eapply mtype_t_wf. apply H0. 
  constructor. 
  apply sub_refl. eapply mtype_ps_wf;eauto.
  constructor. 
  intros.
  apply sub_refl.  apply H1.
  unfold subtype_under2. assert (wf_under2 (TRefn (TNom (TClass C)) ps) t rt). eapply mtype_rt_wf;eauto. intros. apply H2 in H3. intros. apply sub_refl. apply H3.
  -
  rename C0 into b1. rename C into b3.
  assert (exists xx, b2 = TClass xx). eapply subclass_class;eauto. destruct H0 as [xx]. subst b2. rename xx into b2.

  intros.
  assert (FJSubtype (TNom (TClass b2)) (TNom (TClass b3))). apply SubBClass. auto. eapply IHSubClass2 in H1;eauto. destruct H1 as [ps' [t' [rt']]]. destruct H1. destruct H2. destruct H3.
  assert (FJSubtype (TNom (TClass b1)) (TNom (TClass b2))). apply SubBClass. auto. eapply IHSubClass1 in H5;auto. Focus 2. apply H1. destruct H5 as [ps''[t'' [rt'']]]. destruct H5. destruct H6. destruct H7. 
  
  exists ps''. exists t''. exists rt''.  constructor;auto.
  assert (SubClass (TClass b1) (TClass b3)). apply SubCTrans with (TClass b2);auto.
  assert (Empty |-s TRefn (TNom (TClass b1)) ps <:: TRefn  (TNom (TClass b2)) ps). apply SBase with empty. auto. intros. apply IRefl.
  assert (Empty |-s TRefn  (TNom (TClass b2)) ps <:: TRefn (TNom (TClass b3)) ps). apply SBase with empty. auto. intros. apply IRefl.
  assert (Empty |-s TRefn (TNom (TClass b1)) ps' <:: TRefn  (TNom (TClass b2)) ps'). apply SBase with empty. auto. intros. apply IRefl.
  assert (Empty |-s TRefn  (TNom (TClass b2)) ps' <:: TRefn (TNom (TClass b3)) ps'). apply SBase with empty. auto. intros. apply IRefl.
  assert (Empty |-s TRefn (TNom (TClass b1)) ps'' <:: TRefn  (TNom (TClass b2)) ps''). apply SBase with empty. auto. intros. apply IRefl.
  assert (Empty |-s TRefn  (TNom (TClass b2)) ps'' <:: TRefn (TNom (TClass b3)) ps''). apply SBase with empty. auto. intros. apply IRefl.
  assert (Empty |-s TRefn (TNom (TClass b1)) ps <:: TRefn  (TNom (TClass b2)) ps'). inversion H2. apply SBase with nms. auto. intros. assert (Cons y (TRefn (TNom (TClass b1)) PEmpty) Empty = concatE (Cons y (TRefn (TNom (TClass b1)) PEmpty) Empty) Empty). auto. rewrite H24. apply INarrow with (TRefn  (TNom (TClass b2)) PEmpty);simpl;auto. apply SBase with empty. auto. intros. apply IRefl. 
  assert (Empty |-s TRefn (TNom (TClass b1)) ps <:: TRefn (TNom (TClass b1)) ps'). inversion H2. apply SBase with nms. auto. intros. assert (Cons y (TRefn (TNom (TClass b1)) PEmpty) Empty = concatE (Cons y (TRefn (TNom (TClass b1)) PEmpty) Empty) Empty). auto. rewrite H25. apply INarrow with (TRefn  (TNom (TClass b2)) PEmpty);simpl;auto. apply SBase with empty. auto. intros. apply IRefl. 
  assert (Empty |-s TRefn (TNom (TClass b1)) ps <:: TRefn (TNom (TClass b1)) ps''). apply sub_trans with (TRefn (TNom (TClass b1)) ps');auto. apply wf_narrow_subclass with (TClass b3);auto. eapply mtype_ps_wf;eauto. apply wf_narrow_subclass with (TClass b2);auto. eapply mtype_ps_wf;eauto. eapply mtype_ps_wf;eauto.  

  assert (wf_under (TRefn (TNom (TClass b1)) ps) t). apply narrow_wf_under with ps (TClass b3);auto. apply SBase with empty. apply SubBClass. apply SubCTrans with (TClass b2);auto. intros. apply IRefl. eapply mtype_t_wf;eauto.
  assert (wf_under (TRefn (TNom (TClass b1)) ps') t'). apply narrow_wf_under with ps' (TClass b2);auto. eapply mtype_t_wf;eauto.
  assert (wf_under (TRefn (TNom (TClass b1)) ps) t'). apply narrow_wf_under with ps' (TClass b2);auto. eapply mtype_t_wf;eauto.
  assert (wf_under (TRefn (TNom (TClass b1)) ps'') t''). eapply mtype_t_wf;eauto.
  assert (wf_under (TRefn (TNom (TClass b1)) ps) t''). apply narrow_wf_under with ps' (TClass b1);auto. eapply narrow_wf_under with ps'' (TClass b1);auto. 
  assert (wf_under (TRefn  (TNom (TClass b2)) ps') t'). eapply mtype_t_wf;eauto.
  assert (wf_under (TRefn  (TNom (TClass b2)) ps) t). apply narrow_wf_under with ps (TClass b3);auto. eapply mtype_t_wf;eauto.
  assert (wf_under (TRefn (TNom (TClass b3)) ps) t). eapply mtype_t_wf;eauto.
  assert (wf_under (TRefn (TNom (TClass b1)) ps') t''). apply narrow_wf_under with ps'' (TClass b1);auto.
  assert (wf_under (TRefn  (TNom (TClass b2)) ps) t').  apply narrow_wf_under with ps' (TClass b2);auto. 
  assert (WFtype Empty (TRefn (TNom (TClass b1)) ps'')). eapply mtype_ps_wf;eauto.
  assert (WFtype Empty (TRefn  (TNom (TClass b2)) ps')). eapply mtype_ps_wf;eauto.
  assert (WFtype Empty (TRefn (TNom (TClass b3)) ps)). eapply mtype_ps_wf;eauto.
  assert (WFtype Empty (TRefn (TNom (TClass b1)) ps)). apply wf_narrow_subclass with (TClass b2);auto. apply wf_narrow_subclass with (TClass b3);auto.
  assert (WFtype Empty (TRefn (TNom (TClass b1)) ps')). apply wf_narrow_subclass with (TClass b2);auto. 
  assert (WFtype Empty (TRefn  (TNom (TClass b2)) ps)). apply wf_narrow_subclass with (TClass b3);auto.

  assert (subtype_under (TRefn (TNom (TClass b1)) ps) t t'). apply subtype_under_narrow with (TClass b2) ps;auto. 
  assert (subtype_under (TRefn (TNom (TClass b1)) ps) t' t''). apply subtype_under_narrow with (TClass b1) ps';auto. 
  
  (* assert (subtype_under (TRefn  (TNom (TClass b2)) ps') t t'). apply subtype_under_narrow with b2 ps';auto. *)
  assert (wf_under2 (TRefn (TNom (TClass b3)) ps) t rt).  eapply mtype_rt_wf;eauto.
  assert (wf_under2 (TRefn  (TNom (TClass b2)) ps) t rt). apply narrow_wf_under2 with ps (TClass b3) t;auto. apply subtype_under_refl;auto.
  assert (wf_under2 (TRefn  (TNom (TClass b2)) ps') t' rt'). eapply mtype_rt_wf;eauto.
  assert (wf_under2 (TRefn (TNom (TClass b1)) ps') t' rt'). apply narrow_wf_under2 with ps' (TClass b2) t';auto. apply subtype_under_refl;auto.
  assert (wf_under2 (TRefn  (TNom (TClass b2)) ps) t' rt'). apply narrow_wf_under2 with ps' (TClass b2) t';auto.  apply subtype_under_refl;auto.
  assert (wf_under2 (TRefn  (TNom (TClass b2)) ps) t rt'). apply narrow_wf_under2 with ps (TClass b2) t';auto. apply sub_refl;auto.
  assert (wf_under2 (TRefn (TNom (TClass b1)) ps') t'' rt''). apply narrow_wf_under2 with ps'' (TClass b1) t'';auto. apply subtype_under_refl;auto. eapply mtype_rt_wf;eauto. 
  assert (wf_under2 (TRefn (TNom (TClass b1)) ps) t'' rt''). apply narrow_wf_under2 with ps' (TClass b1) t'';auto.  apply subtype_under_refl;auto.
  assert (wf_under2 (TRefn (TNom (TClass b1)) ps') t' rt''). apply narrow_wf_under2 with ps' (TClass b1) t'';auto. apply sub_refl;auto. 
  assert (wf_under2 (TRefn (TNom (TClass b1)) ps) t' rt''). apply narrow_wf_under2 with ps' (TClass b1) t';auto. apply subtype_under_refl;auto. 
  assert (wf_under2 (TRefn (TNom (TClass b1)) ps) t rt'). apply narrow_wf_under2 with ps (TClass b2) t';auto.
  assert (wf_under2 (TRefn (TNom (TClass b1)) ps) t rt''). apply narrow_wf_under2 with ps (TClass b1) t'';auto. apply sub_refl;auto.  apply subtype_under_trans with t';auto. 
  
  assert (wf_under2 (TRefn (TNom (TClass b1)) ps) t rt). apply narrow_wf_under2 with ps (TClass b3) t;auto. apply sub_trans with (TRefn (TNom (TClass b2)) ps);auto. apply subtype_under_refl;auto.
  
  assert (subtype_under2 (TRefn (TNom (TClass b1)) ps) t' rt'' rt'). apply subtype_under2_narrow with (TClass b1) ps' t';auto. apply subtype_under_refl;auto. 
  
  constructor;auto.
  constructor;auto.
  apply subtype_under_trans with t';auto. 
  apply subtype_under2_trans with rt';auto.
  apply subtype_under2_narrow with (TClass b1) ps t';auto. apply sub_refl;auto.
  apply narrow_wf_under2 with ps (TClass b2) t';auto. apply subtype_under_refl;auto.  

  apply subtype_under2_narrow with (TClass b2) ps t;auto.
  apply subtype_under_refl;auto.  
  -
  intros.
  apply cok in H0. inversion H0. eapply methods_sub_signature in H13. Focus 2. apply H1.
  destruct H13 as [ps'[Ds'[D0']]]. destruct H13. destruct H15. exists ps'.  exists Ds'. exists D0'. constructor;auto.
Qed.
Lemma class_sub'i: forall C0 ps C m t rt, FJSubtype (TNom (TClass C0)) (TNom (TInterface C)) -> mtypei(m, C) = ps ~> t ~> rt -> (exists ps' t' rt', mtype(m, C0) = ps' ~> t' ~> rt' /\ Subtype Empty (TRefn (TNom (TClass C0)) ps) (TRefn (TNom (TClass C0)) ps') /\ subtype_under (TRefn (TNom (TClass C0)) ps) t t' /\ subtype_under2 (TRefn (TNom (TClass C0)) ps) t rt' rt).
Proof.
  intros.
  inversion H.
  clear H1. clear H2. clear H. 
  dependent induction H3.
  -
  apply subclass_class' in H3_0 as HH. destruct HH. subst b2.
  eapply IHSubClass1 in H0;eauto.
  destruct H as [bb]. subst b2.
  apply IHSubClass2 with bb C in H0 as HH;auto. 
  destruct HH as [ps'[t'[rt']]]. destruct H. destruct H1. destruct H2.
  assert (FJSubtype (TNom (TClass C0)) (TNom (TClass bb))). apply SubBClass. apply H3_. apply class_sub' with C0 ps' bb m t' rt' in H4;auto.
  destruct H4 as [ps''[t''[rt'']]]. destruct H4. destruct H5. destruct H6.
  exists ps''. exists t''. exists rt''.
  constructor;auto.
  rename bb into b2. rename C into b3. rename C0 into b1.
  
  assert (SubClass (TClass b1) (TInterface b3)). apply SubCTrans with (TClass b2);auto.
  assert (Empty |-s TRefn (TNom (TClass b1)) ps <:: TRefn  (TNom (TClass b2)) ps). apply SBase with empty. auto. intros. apply IRefl.
  assert (Empty |-s TRefn  (TNom (TClass b2)) ps <:: TRefn (TNom (TInterface b3)) ps). apply SBase with empty. auto. intros. apply IRefl.
  assert (Empty |-s TRefn (TNom (TClass b1)) ps' <:: TRefn  (TNom (TClass b2)) ps'). apply SBase with empty. auto. intros. apply IRefl.
  assert (Empty |-s TRefn  (TNom (TClass b2)) ps' <:: TRefn (TNom (TInterface b3)) ps'). apply SBase with empty. auto. intros. apply IRefl.
  assert (Empty |-s TRefn (TNom (TClass b1)) ps'' <:: TRefn  (TNom (TClass b2)) ps''). apply SBase with empty. auto. intros. apply IRefl.
  assert (Empty |-s TRefn  (TNom (TClass b2)) ps'' <:: TRefn (TNom (TInterface b3)) ps''). apply SBase with empty. auto. intros. apply IRefl.
  assert (Empty |-s TRefn (TNom (TClass b1)) ps <:: TRefn  (TNom (TClass b2)) ps'). inversion H1. apply SBase with nms. auto. intros. assert (Cons y (TRefn (TNom (TClass b1)) PEmpty) Empty = concatE (Cons y (TRefn (TNom (TClass b1)) PEmpty) Empty) Empty). auto. rewrite H23. apply INarrow with (TRefn  (TNom (TClass b2)) PEmpty);simpl;auto. apply SBase with empty. auto. intros. apply IRefl. 
  assert (Empty |-s TRefn (TNom (TClass b1)) ps <:: TRefn (TNom (TClass b1)) ps'). inversion H1. apply SBase with nms. auto. intros. assert (Cons y (TRefn (TNom (TClass b1)) PEmpty) Empty = concatE (Cons y (TRefn (TNom (TClass b1)) PEmpty) Empty) Empty). auto. rewrite H24. apply INarrow with (TRefn  (TNom (TClass b2)) PEmpty);simpl;auto. apply SBase with empty. auto. intros. apply IRefl. 
  assert (Empty |-s TRefn (TNom (TClass b1)) ps <:: TRefn (TNom (TClass b1)) ps''). apply sub_trans with (TRefn (TNom (TClass b1)) ps');auto. apply wf_narrow_subclass with (TInterface b3);auto. eapply mtypei_ps_wf;eauto. apply wf_narrow_subclass with (TClass b2);auto. eapply mtype_ps_wf;eauto. eapply mtype_ps_wf;eauto.  

  assert (wf_under (TRefn (TNom (TClass b1)) ps) t). apply narrow_wf_under with ps (TInterface b3);auto. apply SBase with empty. apply SubBClass. apply SubCTrans with (TClass b2);auto. intros. apply IRefl. eapply mtypei_t_wf;eauto.
  assert (wf_under (TRefn (TNom (TClass b1)) ps') t'). apply narrow_wf_under with ps' (TClass b2);auto. eapply mtype_t_wf;eauto.
  assert (wf_under (TRefn (TNom (TClass b1)) ps) t'). apply narrow_wf_under with ps' (TClass b2);auto. eapply mtype_t_wf;eauto.
  assert (wf_under (TRefn (TNom (TClass b1)) ps'') t''). eapply mtype_t_wf;eauto.
  assert (wf_under (TRefn (TNom (TClass b1)) ps) t''). apply narrow_wf_under with ps' (TClass b1);auto. eapply narrow_wf_under with ps'' (TClass b1);auto. 
  assert (wf_under (TRefn  (TNom (TClass b2)) ps') t'). eapply mtype_t_wf;eauto.
  assert (wf_under (TRefn  (TNom (TClass b2)) ps) t). apply narrow_wf_under with ps (TInterface b3);auto. eapply mtypei_t_wf;eauto.
  assert (wf_under (TRefn (TNom (TInterface b3)) ps) t). eapply mtypei_t_wf;eauto.
  assert (wf_under (TRefn (TNom (TClass b1)) ps') t''). apply narrow_wf_under with ps'' (TClass b1);auto.
  assert (wf_under (TRefn  (TNom (TClass b2)) ps) t').  apply narrow_wf_under with ps' (TClass b2);auto. 
  assert (WFtype Empty (TRefn (TNom (TClass b1)) ps'')). eapply mtype_ps_wf;eauto.
  assert (WFtype Empty (TRefn  (TNom (TClass b2)) ps')). eapply mtype_ps_wf;eauto.
  assert (WFtype Empty (TRefn (TNom (TInterface b3)) ps)). eapply mtypei_ps_wf;eauto.
  assert (WFtype Empty (TRefn (TNom (TClass b1)) ps)). apply wf_narrow_subclass with (TClass b2);auto. apply wf_narrow_subclass with (TInterface b3);auto.
  assert (WFtype Empty (TRefn (TNom (TClass b1)) ps')). apply wf_narrow_subclass with (TClass b2);auto. 
  assert (WFtype Empty (TRefn  (TNom (TClass b2)) ps)). apply wf_narrow_subclass with (TInterface b3);auto.

  assert (subtype_under (TRefn (TNom (TClass b1)) ps) t t'). apply subtype_under_narrow with (TClass b2) ps;auto. 
  assert (subtype_under (TRefn (TNom (TClass b1)) ps) t' t''). apply subtype_under_narrow with (TClass b1) ps';auto. 
  
  (* assert (subtype_under (TRefn  (TNom (TClass b2)) ps') t t'). apply subtype_under_narrow with b2 ps';auto. *)
  assert (wf_under2 (TRefn (TNom (TInterface b3)) ps) t rt).  eapply mtypei_rt_wf;eauto.
  assert (wf_under2 (TRefn  (TNom (TClass b2)) ps) t rt). apply narrow_wf_under2 with ps (TInterface b3) t;auto. apply subtype_under_refl;auto.
  assert (wf_under2 (TRefn  (TNom (TClass b2)) ps') t' rt'). eapply mtype_rt_wf;eauto.
  assert (wf_under2 (TRefn (TNom (TClass b1)) ps') t' rt'). apply narrow_wf_under2 with ps' (TClass b2) t';auto. apply subtype_under_refl;auto.
  assert (wf_under2 (TRefn  (TNom (TClass b2)) ps) t' rt'). apply narrow_wf_under2 with ps' (TClass b2) t';auto.  apply subtype_under_refl;auto.
  assert (wf_under2 (TRefn  (TNom (TClass b2)) ps) t rt'). apply narrow_wf_under2 with ps (TClass b2) t';auto. apply sub_refl;auto.
  assert (wf_under2 (TRefn (TNom (TClass b1)) ps') t'' rt''). apply narrow_wf_under2 with ps'' (TClass b1) t'';auto. apply subtype_under_refl;auto. eapply mtype_rt_wf;eauto. 
  assert (wf_under2 (TRefn (TNom (TClass b1)) ps) t'' rt''). apply narrow_wf_under2 with ps' (TClass b1) t'';auto.  apply subtype_under_refl;auto.
  assert (wf_under2 (TRefn (TNom (TClass b1)) ps') t' rt''). apply narrow_wf_under2 with ps' (TClass b1) t'';auto. apply sub_refl;auto. 
  assert (wf_under2 (TRefn (TNom (TClass b1)) ps) t' rt''). apply narrow_wf_under2 with ps' (TClass b1) t';auto. apply subtype_under_refl;auto. 
  assert (wf_under2 (TRefn (TNom (TClass b1)) ps) t rt'). apply narrow_wf_under2 with ps (TClass b2) t';auto.
  assert (wf_under2 (TRefn (TNom (TClass b1)) ps) t rt''). apply narrow_wf_under2 with ps (TClass b1) t'';auto. apply sub_refl;auto.  apply subtype_under_trans with t';auto. 
  
  assert (wf_under2 (TRefn (TNom (TClass b1)) ps) t rt). apply narrow_wf_under2 with ps (TInterface b3) t;auto. apply sub_trans with (TRefn (TNom (TClass b2)) ps);auto. apply subtype_under_refl;auto.
  
  assert (subtype_under2 (TRefn (TNom (TClass b1)) ps) t' rt'' rt'). apply subtype_under2_narrow with (TClass b1) ps' t';auto. apply subtype_under_refl;auto. 
  
  constructor;auto.
  constructor;auto.
  apply subtype_under_trans with t';auto. 
  apply subtype_under2_trans with rt';auto.
  apply subtype_under2_narrow with (TClass b1) ps t';auto. apply sub_refl;auto.
  apply narrow_wf_under2 with ps (TClass b2) t';auto. apply subtype_under_refl;auto.  

  apply subtype_under2_narrow with (TClass b2) ps t;auto.
  apply subtype_under_refl;auto.
  -
  eapply methods_subi_signature in H;eauto. 
  destruct H as [Ds'[D0'[ps']]]. destruct H. destruct H2. destruct H3. exists ps'.  exists Ds'. exists D0'. constructor;auto.
Qed.



Lemma mtype_rt_wf_sub: forall m C ps t rt g e1 e2 nms ps' t', mtype(m, C) = ps ~> t ~> rt -> Hastype g e1 (TRefn (TNom (TClass C)) ps') -> 
( forall y : vname, ~ Elem y nms -> Subtype (Cons y (TRefn (TNom (TClass C)) ps') g) t' (openT_at 0 y t)) -> 
WFEnv g -> isLC e1 -> isLC e2 -> g |-s TRefn (TNom (TClass C)) ps' <:: TRefn (TNom (TClass C)) ps -> Hastype g e2 t' -> 
WFtype g (tsubBV_at 1 e1 (tsubBV e2 rt)).
Proof.
  intros. rename H6 into ge2t.
  assert (wf_under2 (TRefn (TNom (TClass C)) ps) t rt). eapply mtype_rt_wf;eauto. 
  assert (wf_under (TRefn (TNom (TClass C)) ps) t). eapply mtype_t_wf;eauto. rename H7 into HH. 

  remember (fresh (union (free (tsubBV_at 0 e2 rt)) (union empty (union (binds g) nms)))) as y. assert (~Elem y (union (free (tsubBV_at 0 e2 rt)) (union empty (union (binds g) nms)))). rewrite Heqy.  apply fresh_not_elem. 
  assert (~Elem y empty). notin_solve_one. 
  remember (fresh (union (free rt) (union (singleton y) (union empty (union empty (union (binds g) nms)))))) as y'. assert (~Elem y' (union (free rt) (union (singleton y) (union empty (union empty (union (binds g) nms)))))). rewrite Heqy'.  apply fresh_not_elem.
  
  assert (g = concatE g Empty). reflexivity. auto. rewrite H10. 
  assert (y'<>y). apply not_elem_singleton. notin_solve_one.
  assert (Empty = (esubFV y e1 (esubFV y' e2 Empty))) by reflexivity. rewrite H12.
  apply wf_bind_sub2' with ((openT_at 1 y (openT_at 0 y' rt))) (concatE (Cons y' (openT_at 0 y t) (Cons y (TRefn (TNom (TClass C)) ps') g)) Empty) t (TRefn (TNom (TClass C)) ps');auto.
  
  assert (concatE (Cons y' (openT_at 0 y t) (Cons y (TRefn (TNom (TClass C)) ps') g)) Empty = concatE ((Cons y (TRefn (TNom (TClass C)) ps') g)) (concatE (Cons y' (openT_at 0 y t) Empty) Empty)). apply push. rewrite H13.
  apply narrow_wf' with ((Cons y' (openT_at 0 y t)
  (Cons y (TRefn (TNom (TClass C)) ps) g))) (TRefn (TNom (TClass C)) ps);auto. assert (concatE g (Cons y' (openT_at 0 y t)
  (Cons y (TRefn (TNom (TClass C)) ps) Empty))  = (Cons y' (openT_at 0 y t)
  (Cons y (TRefn (TNom (TClass C)) ps) g))). reflexivity. rewrite <- H14. apply weaken_many_wf_r;auto. 
  apply wfenv_unique;auto.  simpl. constructor. unfold in_env. simpl. unfold not. intros. destruct H15;auto. constructor;auto. 
  assert (binds (Cons y' (openT_at 0 y t) (Cons y (TRefn (TNom (TClass C)) ps) Empty)) = names_add y' (names_add y empty)). simpl. reflexivity. rewrite H15. apply intersect_names_add_intro_r. apply intersect_names_add_intro_r. apply intersect_empty_r. notin_solve_one. notin_solve_one. 
  apply wfenv_unique;auto.
  simpl. constructor;simpl;auto.
  apply subset_in_intersect with (union (binds (Cons y' (openT_at 0 y t) Empty)) (binds Empty)). apply intersect_union_intro_r. simpl. apply intersect_empty_r. assert (binds (Cons y' (openT_at 0 y t) Empty) = names_add y' empty). simpl. reflexivity. rewrite H14. apply intersect_names_add_intro_r. apply intersect_empty_r. notin_solve_one. apply binds_concat.
  unfold in_env. notin_solve_one. unfold in_env. apply not_elem_concat_intro. simpl. unfold not. intros. destruct H14;auto. simpl. auto.

  simpl. apply not_elem_union_intro;simpl;auto. apply not_elem_union_intro. notin_solve_one.  apply not_elem_union_intro. notin_solve_one. notin_solve_one.
  simpl. apply not_elem_union_intro;simpl;auto. apply not_elem_union_intro;simpl;auto. notin_solve_one. notin_solve_one.
  rewrite <- erase_openT_at with t 0 y. assert (erase_env (Cons y (TRefn (TNom (TClass C)) ps') g) = FCons y (erase (TRefn (TNom (TClass C)) ps')) (erase_env g)). reflexivity. rewrite <- H13. apply typing_hasfjtype.
  apply TSub with t'. apply weaken_typ_top;auto. apply wfenv_unique. auto. unfold in_env. notin_solve_one. apply narrow_wf_top with (TRefn (TNom (TClass C)) ps);auto. assert ((Cons y (TRefn (TNom (TClass C)) ps) g) = concatE g (Cons y (TRefn (TNom (TClass C)) ps) Empty)). simpl. auto. rewrite H14. apply weaken_many_wf_r. apply HH. simpl. apply wfenv_unique;auto. simpl. constructor;auto. assert (binds (Cons y (TRefn (TNom (TClass C)) ps) Empty) = (names_add y empty)). simpl. auto. rewrite H15. apply intersect_names_add_intro_r. apply intersect_empty_r. notin_solve_one. apply wfenv_unique;auto. unfold in_env. notin_solve_one.
  apply H1. notin_solve_one.
  
  apply typing_hasfjtype;auto.
  apply wfenv_unique. auto. simpl. auto. simpl. apply intersect_empty_r. 
Qed. 

Lemma fieldtype_wf': forall C Fs fi i e g, Reffields C Fs -> nth_error Fs i = Some fi -> isLC e -> WFEnv g -> Hastype g e (TRefn (TNom (TClass C)) PEmpty) ->
WFtype g (tsubBV e (ReffieldType fi)).
Proof.
  intros.
  assert (wf_under (TRefn (TNom (TClass C)) PEmpty) (ReffieldType fi)). eapply fieldtype_wf;eauto. 
  remember (fresh (binds g) ) as y. assert (~Elem y (binds g)). rewrite Heqy.  apply fresh_not_elem. 
  assert (tsubBV e (ReffieldType fi) = tsubFV y e (unbindT y (ReffieldType fi))). apply tsubFV_unbindT. erewrite fieldtype_no_fv;eauto. rewrite H6.
  apply subst_wf_top with (TRefn (TNom (TClass C)) PEmpty);simpl;auto.
  assert ((Cons y (TRefn (TNom (TClass C)) PEmpty) g) = concatE g (Cons y (TRefn (TNom (TClass C)) PEmpty) Empty)). reflexivity. rewrite H7. apply weaken_many_wf_r. apply H4. auto. 
  apply wfenv_unique. auto. simpl;constructor;simpl;auto. assert ((binds (Cons y (TRefn (TNom (TClass C)) PEmpty) Empty)) = names_add y empty). reflexivity. rewrite H8. apply intersect_names_add_intro_r. apply intersect_empty_r. notin_solve_one.
  apply wfenv_unique. auto. unfold in_env. 
  assert (TNom (TClass C) = erase (TRefn (TNom (TClass C)) PEmpty)). reflexivity. rewrite H7.
  apply typing_hasfjtype;auto. 
Qed.



(*---------------Properties relating mbody to isLC using typ_islc---------------*)
Lemma mbody_islc2: forall m C e, mbody( m, C)= e -> isLC_at 2 e. 
Proof. 
  intros.
  induction H.
  -
    apply cok in H. inversion H.
    assert (MType_OK C (MDefn (MDecl rt m ps t) e)). eapply Forall_find;eauto. inversion H14.
    remember (fresh (empty)) as y.  assert (~Elem y empty). rewrite Heqy. apply fresh_not_elem.
    remember (fresh (singleton y)) as y'.  assert (~Elem y' (singleton y)). rewrite Heqy'. apply fresh_not_elem.
    assert (y'<>y). apply not_elem_singleton;auto. 
    assert (y<>y'). auto. 
    apply H26 in H34.
    assert (isLC (open_at 1 y (open_at 0 y' e))).
    apply typ_islc with ( Cons y' (openT_at 0 y t) (Cons y (TRefn (TNom (TClass C)) ps) Empty)) (openT_at 1 y (openT_at 0 y' rt));auto. 
    assert ((forall (e : expr) (j : index) (y : vname),
    isLC_at j (open_at j y e) -> isLC_at (j+1) e )). 
    apply islc_at_after_open_at.
    assert (2 = 1 + 1). auto. rewrite H37.
    apply H36 with y.
    assert (1 = 0 + 1). auto. rewrite H38.
    apply H36 with y'.
    rewrite commute_open_at_open_at;auto.
  -
    auto.
Qed.