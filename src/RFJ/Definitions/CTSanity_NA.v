Require Import Relations Decidable.
Require Import RFJ.Utils.
Require Export Definitions.Syntax.
Require Import Forall2.
Require Import Lists.
Require Import RFJ.Utils.Referable.
Require Export Definitions.Names.
Require Import ZArith.
Require Import Definitions.FJTyping.

Require Import Definitions.Semantics.
Require Import Lists.ListSet.

Require Import Definitions.SubDenotation.

Require Import Definitions.Typing.
Require Import Coq.Program.Equality.
Require Import RFJ.Tactics.

Require Import Lemmas.LogicalLemmas.LemmasCSubst.
(* Require Import Lemmas.LogicalLemmas.LemmasDenotes. *)
Require Import Lemmas.BasicLemmas.LemmasSemantics.

(*
1. we use contra and co variant. 
2. if the subtype is fine under a narrower context then we are fine.
since we can are actually using them when playing as supertype, it is safe to assume we have this narrower context. 
*)
Definition override (m: MethodName) (C: ClassName) (D: ClassName) (ps: preds) (Cs: type) (C0: type) :=
  (forall Ds D0 ps', mtype(m, D) = ps' ~> Ds ~> D0 -> 
  (Subtype Empty (TRefn (TNom (TClass C)) ps') (TRefn (TNom (TClass C)) ps) /\ 
  subtype_under (TRefn (TNom (TClass C)) ps') Ds Cs /\ 
  subtype_under2 (TRefn (TNom (TClass C)) ps') Ds C0 D0)
  ).
Definition implement (C: ClassName) (m: MethodName) (t0: type) (ps: preds) (t: type) :=
  (exists Ds D0 ps', mtype(m, C) = ps' ~> Ds ~> D0 /\
  (Subtype Empty (TRefn (TNom (TClass C)) ps) (TRefn (TNom (TClass C)) ps') /\ 
  subtype_under (TRefn (TNom (TClass C)) ps) t Ds /\ 
  subtype_under2 (TRefn (TNom (TClass C)) ps) t D0 t0)
  ).

Inductive MType_OK : ClassName -> MethodDefn -> Prop :=
| WF_Method : forall ps rt t e (C:ClassName) D Is Fs noDupfs K Ms noDupMds m,
          find C RefCT = Some (RefCDecl C D Is Fs noDupfs K Ms noDupMds)->
          find m Ms = Some (MDefn (MDecl rt m ps t) e) ->
          override m C D ps t rt->
          (WFtype Empty (TRefn (TNom (TClass C)) ps)) -> 
          wf_under (TRefn (TNom (TClass C)) ps) t -> 
          wf_under2 (TRefn (TNom (TClass C)) ps) t rt -> 
          (forall y y', y <> y' -> Hastype (Cons y' (openT_at 0 y t) (Cons y (TRefn (TNom (TClass C)) ps) Empty)) (open_at 1 y (open_at 0 y' e)) (openT_at 1 y (openT_at 0 y' rt))) -> 
          (fv e = empty) -> 
          (free t = empty) -> (free rt = empty) -> 
          MType_OK C (MDefn (MDecl rt m ps t) e).
Inductive FType_OK : ClassName -> RefFieldDecl -> Prop :=
| WF_Field : forall C t f,
          free t = empty -> 
          wf_under (TRefn (TNom (TClass C)) PEmpty) t -> 
          FType_OK C (RefFDecl t f).
Inductive Class_implemented: ClassName -> InterfaceName -> Prop := 
| CI: forall C I iMs noDupiMds, 
  find I RefIT = Some (RefIDecl I iMs noDupiMds) ->
  (forall im irt ips it, 
  find im iMs = Some (MDecl irt im ips it) -> 
  implement C im irt ips it) -> 
  Class_implemented C I.
Inductive CType_OK: RefClassDecl -> Prop :=
| T_Class : forall C D Fs noDupfs Is K Ms noDupMds fdecl ,
          K = KDecl C (Fs ++ fdecl) (refs fdecl) (zipWith Assgnmt (map (ExpFieldAccess (BV 0)) (refs Fs)) (map FV (refs Fs))) ->
          Reffields D fdecl ->
          NoDup (refs (fdecl ++ Fs)) ->
          Forall (MType_OK C) (Ms) ->
          Forall (FType_OK C) (Fs) ->
          find C RefCT = Some (RefCDecl C D Is Fs noDupfs K Ms noDupMds) ->
          (forall i I, 
          nth_error Is i = Some I -> 
          Class_implemented C I) -> 
          (* find I RefIT = Some (RefIDecl I iMs noDupiMds) ->
          find im iMs = Some (MDecl irt im ips it) -> 
          implement C im irt ips it) ->  *)
          CType_OK (RefCDecl C D Is Fs noDupfs K Ms noDupMds).
#[global] Hint Constructors CType_OK.
Inductive MType_OK_I : ClassName -> MethodDecl -> Prop :=
| WF_MethodI : forall ps rt t (C:InterfaceName) m,
          (WFtype Empty (TRefn (TNom (TInterface C)) ps)) -> 
          wf_under (TRefn (TNom (TInterface C)) ps) t -> 
          wf_under2 (TRefn (TNom (TInterface C)) ps) t rt -> 
          (free t = empty) -> (free rt = empty) -> 
          MType_OK_I C (MDecl rt m ps t).
Inductive IType_OK: RefInterfaceDecl -> Prop :=
| T_ClassI : forall I iMs noDupiMds ,
          Forall (MType_OK_I I) (iMs) ->
          find I RefIT = Some (RefIDecl I iMs noDupiMds) ->
          IType_OK (RefIDecl I iMs noDupiMds).
          
Lemma semantic_equalize_value_int': forall v v', isValue v -> 
EvalsTo (ExpBinOp Eq v' v) (Bc true) -> isValue v' ->  v = v'.
Proof. intros. rename H1 into isvalv'. dependent induction H0.
  inversion H1. 
  - apply value_stuck in H6. simpl in H6. contradiction.
  - apply value_stuck in H7. simpl in H7. contradiction.
  - assert (isValue e2). apply bdelta_value with Eq v' v pf;auto.  apply value_refl in H0;auto. rewrite H0 in H4.
    assert (bdelta Eq v' v pf =  bdelta Eq v' v (isCpt_Eq v' v H6 H7)). apply delta_pf_indep. rewrite H9 in H4. simpl in H4.
    inversion H4.  
    apply veq_eq';auto.
Qed. 
Theorem cok: forall C D Fs noDupfs K Is Ms noDupMds, 
            find C RefCT = Some (RefCDecl C D Is Fs noDupfs K Ms noDupMds) ->
            CType_OK (RefCDecl C D Is Fs noDupfs K Ms noDupMds).
Proof.
  unfold RefCT. simpl.
  intros.
  destruct (C=? crust_class_name).
  unfold crust_class in *. inversion H. subst Ms. subst C. subst D. subst Is. subst Fs. subst K.
  apply T_Class with nil;auto.
  apply RefF_Obj.
  -
  unfold crust_mdefns. apply Forall_cons.
  + 
  unfold price_crust_mdefn.
  eapply WF_Method;eauto.
  ++
    unfold override.
    intros.
    dependent induction H0.
  ++
    unfold unit_type. unfold wf_under. simpl. intros. apply WFBase.
  ++
    unfold unit_type. unfold int_0_1. unfold wf_under2. intros. simpl. 
    apply WFRefn with (union (singleton y) (singleton y')). 
    apply WFBase.
    discriminate.
    intros. unfold unbindP. simpl. apply PFTCons.
    apply FTBinOP.
    +++
    apply FTBinOP.  
    apply FTSub with TInt. apply FTVar. simpl. left;auto. auto.
    apply FTSub with TInt. apply FTIC. auto.
    +++
    apply FTBinOP.  
    apply FTSub with TInt. apply FTVar. simpl. left;auto. auto.
    apply FTSub with TInt. apply FTIC. auto.
    +++
    apply PFTEmp.
  ++
    intros. simpl.
    apply TSub with (tyic 1). 
    apply TIC.
    +++
    apply WFRefn with (union (singleton y) (singleton y')). 
    apply WFBase.
    discriminate.
    intros. unfold unbindP. simpl. apply PFTCons.
    apply FTBinOP.
    ++++
    apply FTBinOP.  
    apply FTSub with TInt. apply FTVar. simpl. left;auto. auto.
    apply FTSub with TInt. apply FTIC. auto.
    ++++
    apply FTBinOP.  
    apply FTSub with TInt. apply FTVar. simpl. left;auto. auto.
    apply FTSub with TInt. apply FTIC. auto.
    ++++
    apply PFTEmp.
    +++
      apply SBase with (union (singleton y) (singleton y')).
      auto.
      intros.
      apply SImp. intros.
      unfold unbindP in H3. simpl in H3. rewrite cpsubst_pcons in H3. rewrite csubst_binop in H3. inversion H3.
      rewrite csubst_ic in H6. assert ((csubst th (FV y0)) = (Ic 1)). apply semantic_equalize_value_int';simpl;auto.
      apply csubst_sub_isValue. eapply denotesenv_substitutable;eauto.
      assert (binds (Cons y0 (TRefn TInt PEmpty) (Cons y' (TRefn TBool PEmpty) (Cons y (TRefn (TNom (TClass crust_class_name)) PEmpty) Empty))) = bindsC th).
      apply binds_env_th;auto. simpl in H8. unfold in_csubst. rewrite <- H8. apply elem_names_add_intro. left. auto.
      unfold unbindP in *. simpl in *. 
      rewrite cpsubst_pcons.
      apply PECons.
      rewrite csubst_binop. rewrite csubst_binop. rewrite csubst_binop. rewrite H8.
      apply lemma_evals_trans with (ExpBinOp Or (Bc true) (Bc false));auto.
      apply lemma_evals_trans with (ExpBinOp Or (Bc true) (ExpBinOp Eq (Ic 1) (csubst th (Ic 2))));auto.
      apply binop_many. apply step_evals. rewrite csubst_ic. assert (isValue (Ic 1));simpl; auto. assert (Bc true = bdelta Eq (Ic 1) (Ic 1) (isCpt_Eq (Ic 1) (Ic 1) H9 H9)). auto. rewrite H10. apply EBinOp3;auto.
      apply binop_many';simpl;auto. apply step_evals. rewrite csubst_ic. assert (isValue (Ic 1));simpl; auto. assert (isValue (Ic 2));simpl; auto. assert (Bc false = bdelta Eq (Ic 1) (Ic 2) (isCpt_Eq (Ic 1) (Ic 2) H9 H10)). auto. rewrite H11. apply EBinOp3;auto. 
      apply step_evals. assert (Bc true = bdelta Or (Bc true) (Bc false) (isCpt_Or true false)). auto. rewrite H9. apply EBinOp3;simpl;auto. 
      rewrite cpsubst_pempty. apply PEEmp.
  +
  apply Forall_nil.
  -
  intros.
  destruct i. simpl in *. inversion H0.
  eapply CI.
  simpl. unfold pizza_interface. eauto.
  intros.
  unfold implement.

  unfold mdecls in H1. simpl in H1. destruct (im =? price). unfold price_mdecl in H1. inversion H1. subst irt. subst im. subst ips. subst it.
  exists unit_type. exists int_0_1. exists PEmpty.
  constructor. eapply mty_ok. simpl. unfold crust_class. eauto.
  unfold crust_mdefns. simpl. unfold price_crust_mdefn. unfold price_crust_mdecl. eauto.
  constructor. apply SBase with empty. auto. intros.
  apply SImp; trivial.
  constructor. unfold subtype_under. intros. simpl. apply SBase with (singleton y). auto.
  intros. apply SImp; trivial.
  unfold subtype_under2. intros. apply SBase with (union (singleton y) (singleton y')). auto. 
  intros. apply SImp;trivial.
  inversion H2.
  inversion H1.
  simpl in *. induction i;simpl in H0;inversion H0. 
  - 
  inversion H.
Qed.
Theorem obj_notin_dom: find Object RefCT = None.
Proof.
  simpl. auto.
Qed.
Lemma example_iok1: MType_OK_I pizza_interface_name price_mdecl.
Proof.
  apply WF_MethodI.
  - apply WFBase.
  - unfold wf_under. intros. simpl. apply WFBase.
  - unfold wf_under2. intros. simpl. 
    apply WFRefn with (union (singleton y) (singleton y')). 
    apply WFBase.
    discriminate.
    intros. unfold unbindP. simpl. apply PFTCons.
    apply FTBinOP.
    +
    apply FTBinOP.  
    apply FTSub with TInt. apply FTVar. simpl. left;auto. auto.
    apply FTSub with TInt. apply FTIC. auto.
    +
    apply FTBinOP.  
    apply FTSub with TInt. apply FTVar. simpl. left;auto. auto.
    apply FTSub with TInt. apply FTIC. auto.
    +
    apply PFTEmp.
  -
    simpl. auto.
  -
    simpl. auto.
Qed.
Theorem iok: forall I iMs noDupiMds,
            find I RefIT = Some (RefIDecl I iMs noDupiMds) ->
            IType_OK (RefIDecl I iMs noDupiMds).
Proof.
  unfold RefIT. simpl.
  intros.
  destruct (I=? pizza_interface_name).
  unfold pizza_interface in *. inversion H. subst iMs. subst I.
  apply T_ClassI.
  -
    unfold mdecls. apply Forall_cons.
    +
      apply example_iok1.
    +
      apply Forall_nil.
  -
    unfold RefIT. simpl.
    auto.
  -
    inversion H.
Qed.



Lemma fields_obj_nil: forall f,
Reffields Object f -> f = nil.
Proof.
  intros.
  inversion H.
  reflexivity.
  rewrite obj_notin_dom in H0.

  crush.
  Qed.

#[global] Hint Resolve fields_obj_nil.
Lemma reffields_det: forall C f1 f2,
Reffields C f1 ->
Reffields C f2 ->
f1 = f2.
  Proof.
  
  intros.
  gen f2.
  induction H.
  -
    intros.
    forwards: (fields_obj_nil f2 H0).
    crush.
  -
    intros.
    inversion H2.
    +
      crush.
    +
      crush.
      forwards: (IHReffields fs'0 H4).
      crush.
Qed.

