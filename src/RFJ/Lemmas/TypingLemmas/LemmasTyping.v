Require Import ZArith.
Require Import Lists.ListSet.
Require Import Lists.

Require Import Definitions.Syntax.
Require Import Definitions.Names.
Require Import Definitions.FJTyping.

Require Import Definitions.Typing.
Require Import Definitions.CTSanity.
Require Import Definitions.Semantics.
Require Import Definitions.SubDenotation.

Require Import Lemmas.BasicLemmas.LemmasFJTyping.
Require Import Lemmas.BasicLemmas.LemmasSubstitution.
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasEnvironments.
Require Import Lemmas.BasicLemmas.LemmasWF.
Require Import Lemmas.BasicLemmas.LemmasWFNarrow.
Require Import Lemmas.BasicLemmas.LemmasWFWeaken.
Require Import Lemmas.BasicLemmas.LemmasWF.
Require Import Lemmas.BasicLemmas.LemmasWFNarrow.
Require Import Lemmas.BasicLemmas.LemmasPrimitivesBasics.
Require Import Lemmas.BasicLemmas.LemmasFJSubstitution.
Require Import Lemmas.BasicLemmas.LemmasFJWeaken.
Require Import Lemmas.BasicLemmas.LemmasWFSubstitution.
Require Import Lemmas.BasicLemmas.LemmasCTBasics.
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.LogicalLemmas.LemmasCSubst.
Require Import Lemmas.LogicalLemmas.LemmasSImp.



(*---------------Basic Properties of Typing---------------*)

Lemma forall_erase: forall Us v, ((map erase Us) = (map erase (map (tsubBV v) Us))).
Proof.
  intros.
  induction Us.
  simpl. reflexivity.
  simpl. f_equal.
  rewrite <-erase_tsubBV_at with 0  v a. reflexivity.
  auto.
Qed.

Lemma forall_erase': forall Us y, ((map erase Us) = (map erase (map (openT_at 0 y) Us))).
Proof.
  intros.
  induction Us.
  simpl. reflexivity.
  simpl. f_equal.
  rewrite <-erase_openT_at with a 0 y. reflexivity.
  auto.
Qed.

Lemma forall_fjtype: forall g es Ts, WFEnv g -> 
Forall2 (fun (e : expr) (t : type) => WFEnv g -> HasFJtype (erase_env g) e (erase t)) es Ts ->
Forall2 (HasFJtype (erase_env g)) es (map erase Ts).
Proof.
  intros.
  generalize dependent Ts.
  induction es.
  -
    intros.
    destruct Ts.
    simpl. apply Forall2_nil.
    inversion H0.
  -
    intros.
    destruct Ts.
    inversion H0.
    inversion H0.
    apply Forall2_cons.
    apply H4;auto.
    apply IHes;auto.
Qed.




Lemma forall_hasfjtype' : forall (g:env) (es:[expr]) (Ts:[type]),
  Forall2 (fun (e : expr) (t : type) => HasFJtype (erase_env g) e (erase t)) es Ts -> 
  Forall2 (HasFJtype (erase_env g)) es (map erase Ts).
Proof.
  intro. intro. induction es.
  intros.
  destruct Ts. apply Forall2_nil. inversion H.
  destruct Ts. intros. inversion H.
  intros. inversion H. apply Forall2_cons;auto.
Qed. 
Lemma forall_fsubtyping : forall (g:fjenv) (es:[expr]) (ts:[fjtype]) (ss:[fjtype]),
    Forall2 (FJSubtype) ts ss -> Forall2 (HasFJtype g) es ts-> Forall2 (HasFJtype g) es ss.
Proof.
  intros.
  generalize dependent ss.
  generalize dependent ts.
  induction es.
  -
    intros.
    destruct ss.
    apply Forall2_nil.
    destruct ts. inversion H. inversion H0.
  -
    intros.
    destruct ss.
    destruct ts. inversion H0. inversion H.
    destruct ts. inversion H.
    inversion H. inversion H0. 
    apply Forall2_cons. apply FTSub with f0;auto. 
    apply IHes with ts;auto.
Qed.

Lemma forall_subtyping : forall (g:env) (es:[expr]) (ts:[type]) (ss:[type]), WFEnv g ->
    Forall (WFtype g) ss -> 
    Forall2 (Subtype g) ts ss -> Forall2 (Hastype g) es ts-> Forall2 (Hastype g) es ss.
Proof.
  intros.
  generalize dependent ss.
  generalize dependent ts.
  induction es.
  -
    intros.
    destruct ss.
    apply Forall2_nil.
    destruct ts. inversion H1. inversion H2.
  -
    intros.
    destruct ss.
    destruct ts. inversion H2. inversion H1.
    destruct ts. inversion H2.
    inversion H1. inversion H2. inversion H0.
    apply Forall2_cons. apply TSub with t0;auto. 
    apply IHes with ts;auto.
Qed.
(*connecting hastype with fhastype*)
Lemma typing_hasfjtype : forall (g:env) (e:expr) (t:type),
  Hastype g e t -> HasFJtype (erase_env g) e (erase t).
Proof. intros g e t p_e_t; induction p_e_t using Hastype_ind'; intros.
- apply FTBC.
- apply FTIC. 
-
  rewrite erase_self; apply FTVar; apply boundin_erase_env; apply H.
-
  rewrite erase_tsubBV. auto. 
  pick_fresh zz. remember (fresh zz ) as y.
  assert (~Elem y zz). rewrite Heqy. apply fresh_not_elem. rewrite Heqzz in H1.
  apply FTUnOP;auto.
  apply FTSub with (erase t);auto. apply subtype_fsubtype with g. apply H.
-
  rewrite erase_tsubBV_at. auto. rewrite erase_tsubBV. auto.
  pick_fresh zz. remember (fresh zz ) as y.
  assert (~Elem y zz). rewrite Heqy. apply fresh_not_elem. rewrite Heqzz in H3.
  apply FTBinOP;auto.
  simpl. apply FTSub with (erase t);auto. apply subtype_fsubtype with g. apply H.
  rewrite <- erase_tsubBV_at with 0 e1 (snd (intype2 op)).
  apply FTSub with (erase t');auto. apply subtype_fsubtype with g;auto.
-
  rewrite erase_self. rewrite erase_tsubBV_at. auto. rewrite erase_tsubBV.
  assert (HasFJtype (erase_env g) e2 (erase t)). apply FTSub with (erase t');auto. rewrite <- erase_tsubBV_at with 0 e1 t. unfold tsubBV in H1. apply subtype_fsubtype with g;auto.
  apply FTInvok with t C ps;auto.
-
  rewrite erase_self. rewrite erase_tsubBV_at. auto. rewrite erase_tsubBV.
  assert (HasFJtype (erase_env g) e2 (erase t)). apply FTSub with (erase t');auto. rewrite <- erase_tsubBV_at with 0 e1 t. unfold tsubBV in H1. apply subtype_fsubtype with g;auto.
  apply FTInvokI with t C ps;auto.
-
  assert (HasFJtype (erase_env g) e ((TNom (TClass C)))) as pp. apply IHp_e_t;auto.
  rewrite erase_self.  
  rewrite erase_tsubBV. 
  eapply FTField;eauto. 
-
    simpl. 
  eapply FTNew;eauto.
  rewrite <- H.
  (* remember (fresh nms ) as y. assert (~Elem y nms). rewrite Heqy. apply fresh_not_elem. apply H5 in H6. *)
  assert (map erase Us = map erase (map (tsubBV (ExpNew C es)) Us)).
  rewrite <- forall_erase; auto.
  rewrite H6.
  apply forall_fsubtyping with (map erase Ts) ;auto. apply forall_subtype_fsubtype with g;auto.
  apply forall_hasfjtype';auto.
- (* TSub *) apply FTSub with (erase s); auto. apply subtype_fsubtype with g;auto. 
- apply FTLet with (erase b) (union nms (binds g));auto. intros. simpl in H1. rewrite erase_self. rewrite <- erase_unbind with y b'. apply H1. notin_solve_one.
Qed.

Lemma typing_hasfjtype_forall : forall (g:env) (es:[expr]) (ts:[type]),
    Forall2 (Hastype g) es ts -> Forall2 (HasFJtype (erase_env g)) es (map (erase) ts).
Proof. intros. generalize dependent es.
  induction ts.
  - intros. destruct es. simpl. apply Forall2_nil. inversion H.
  - intros. destruct es. inversion H. inversion H. apply Forall2_cons. apply typing_hasfjtype;auto. apply IHts;auto.
Qed.

Lemma typing_hasfjtype_forall' : forall (g:env) (es:[expr]) (ts:[type]),
    Forall2 (Hastype g) es ts -> Forall2 (fun (e : expr) (t : type) => HasFJtype (erase_env g) e (erase t)) es ts.
Proof. intros. generalize dependent es.
  induction ts.
  - intros. destruct es. simpl. apply Forall2_nil. inversion H.
  - intros. destruct es. inversion H. inversion H. apply Forall2_cons. apply typing_hasfjtype;auto. apply IHts;auto.
Qed.
(*connecting hastype with fhastype*)
Lemma typing_wf : forall (g:env) (e:expr) (t:type),
  Hastype g e t -> WFEnv g -> WFtype g t.
Proof. intros g e t p_e_t; induction p_e_t using Hastype_ind'; intro p_g.
- (* TBC *) apply wf_tybc.
- (* TIC *) apply wf_tyic.
- (* TVar *) 
  apply selfify_wf with (self t (FV x));simpl;auto.
  rewrite erase_self.
  apply FTVar; apply boundin_erase_env. apply H.
-
  assert (HasFJtype (erase_env g) e (erase t)) as pp. apply typing_hasfjtype;auto. 
  assert (concatE g Empty = g). simpl. reflexivity. rewrite <- H1.
  pick_fresh zz. 
  remember (fresh zz ) as y.
  assert (~Elem y zz). rewrite Heqy. apply fresh_not_elem. rewrite Heqzz in H2. 
  apply wf_sub_fjtype with (intype op);auto.
  apply wf_ty'1;auto.
  apply FTSub with (erase t);auto. apply subtype_fsubtype with g;auto.
-
  assert (HasFJtype (erase_env g) e1 (erase t)) as pp1. apply typing_hasfjtype;auto.
  assert (HasFJtype (erase_env g) e2 (erase t')) as pp2. apply typing_hasfjtype;auto.
  
  assert (concatE g Empty = g). simpl. reflexivity. rewrite <- H3.
  assert (wf_under2 (fst (intype2 op)) (snd (intype2 op)) (ty'2 op)). apply wf_ty'2. 
  pick_fresh zz. remember (fresh zz ) as y.
  assert (~Elem y zz). rewrite Heqy. apply fresh_not_elem. rewrite Heqzz in H5.
  pick_fresh zz'. remember (fresh zz') as y'. assert (~Elem y' zz'). rewrite Heqy'. apply fresh_not_elem. rewrite Heqzz' in H6.
  assert (~ Elem y' (singleton y)). notin_solve_one. assert (y'<>y). apply not_elem_singleton;auto.
  apply wf_sub_fjtype2 with ((snd (intype2 op))) (fst (intype2 op));auto.
  apply FTSub with (erase t);auto. apply subtype_fsubtype with g;auto.
  apply FTSub with (erase t');auto. apply subtype_fsubtype with g;auto.
-
  simpl in *. 
  apply IHp_e_t1 in p_g as pp. 
  apply IHp_e_t2 in p_g as qq. 
  assert (HasFJtype (erase_env g) e2 (erase t)). apply FTSub with (erase t');auto. apply typing_hasfjtype;auto. rewrite <- erase_tsubBV_at with 0 e1 t. unfold tsubBV in H1. apply subtype_fsubtype with g;auto.
  assert (Hastype g e1 (TRefn (TNom (TClass C)) ps)). apply TSub with (TRefn (TNom (TClass C)) ps');auto. eapply mtype_ps_wf_g;eauto. apply wfenv_unique;auto.
  assert (Hastype g e2 (tsubBV e1 t)). apply TSub with (t');auto. apply wf_sub_fjtype with (TRefn (TNom (TClass C)) ps);auto. eapply mtype_t_wf;eauto. apply typing_hasfjtype;auto.
  
  assert (HasFJtype (erase_env g) (ExpMethodInvoc e1 m e2)
  (erase rt)) as hasf. apply FTInvok with t C ps;auto.
  assert (TNom (TClass C) = erase (TRefn (TNom (TClass C)) ps)). auto. rewrite H7. 
  apply typing_hasfjtype;auto.
  apply selfify_wf with (rt);auto.
  apply wf_sub_fjtype2 with t (TRefn (TNom (TClass C)) ps);auto. eapply mtype_rt_wf;eauto. 
  apply typing_hasfjtype;auto.
  apply typing_hasfjtype;auto.
-
  simpl in *. 
  apply IHp_e_t1 in p_g as pp. 
  apply IHp_e_t2 in p_g as qq. 
  assert (HasFJtype (erase_env g) e2 (erase t)). apply FTSub with (erase t');auto. apply typing_hasfjtype;auto. rewrite <- erase_tsubBV_at with 0 e1 t. unfold tsubBV in H1. apply subtype_fsubtype with g;auto.
  assert (Hastype g e1 (TRefn (TNom (TInterface C)) ps)). apply TSub with (TRefn (TNom (TInterface C)) ps');auto. eapply mtypei_ps_wf_g;eauto. apply wfenv_unique;auto.
  assert (Hastype g e2 (tsubBV e1 t)). apply TSub with (t');auto. apply wf_sub_fjtype with (TRefn (TNom (TInterface C)) ps);auto. eapply mtypei_t_wf;eauto. apply typing_hasfjtype;auto.

  assert (HasFJtype (erase_env g) (ExpMethodInvoc e1 m e2)
  (erase rt)) as hasf. apply FTInvokI with t C ps;auto.
  assert (TNom (TInterface C) = erase (TRefn (TNom (TInterface C)) ps)). auto. rewrite H7. 
  apply typing_hasfjtype;auto.
  apply selfify_wf with (rt);auto.
  apply wf_sub_fjtype2 with t (TRefn (TNom (TInterface C)) ps);auto. eapply mtypei_rt_wf;eauto. 
  apply typing_hasfjtype;auto.
  apply typing_hasfjtype;auto.
-
  assert (HasFJtype (erase_env g) e (erase (TRefn (TNom (TClass C)) ps))) as pp. apply typing_hasfjtype; auto.
  assert (concatE g Empty = g). simpl. reflexivity. rewrite <- H3.
  assert (wf_under (TRefn (TNom (TClass C)) PEmpty) (ReffieldType fi)). eapply fieldtype_wf;eauto. unfold wf_under in H4.
  remember (ReffieldType fi) as Rf.
  pick_fresh zz. 
  remember (fresh zz ) as y.
  assert (~Elem y zz). rewrite Heqy. apply fresh_not_elem. rewrite Heqzz in H5.
  (* assert (FJSubtype (erase (self (tsubBV e Rf) (ExpFieldAccess e f5))) (erase (tsubBV e Rf))) as fsub. rewrite erase_self. auto.
   *)
  apply selfify_wf with  (tsubBV e Rf);simpl;auto. rewrite <- H3. apply wf_bind_sub with (unbindT y Rf) (Cons y (TRefn (TNom (TClass C)) ps) g) y (TRefn (TNom (TClass C)) ps);auto.
  assert ((Cons y (TRefn (TNom (TClass C)) ps) g) = concatE g (Cons y (TRefn (TNom (TClass C)) ps) Empty)). reflexivity. rewrite H6. apply weaken_many_wf_r;auto. apply narrow_wf_top with (TRefn (TNom (TClass C)) PEmpty);simpl;auto. apply SBase with empty. apply SubBClass. apply SubCRefl. intros. simpl. apply IFaith.
  apply wfenv_unique;auto. simpl;constructor;simpl;auto. assert ((binds (Cons y (TRefn (TNom (TClass C)) ps) Empty)) = names_add y empty). reflexivity. rewrite H7. apply intersect_names_add_intro_r. apply intersect_empty_r. notin_solve_one. 

  (* apply wf_bind_sub with (unbindT y Rf) (Cons y (TRefn (TNom (TClass C)) ps) g) y (TRefn (TNom (TClass C)) ps);auto. *)
  apply not_elem_union_intro. notin_solve_one. notin_solve_one. 
  apply wfenv_unique;auto.
  rewrite erase_tsubBV. eapply FTField;eauto. 
- 
  apply selfify_wf with (TRefn (TNom (TClass C)) PEmpty);simpl;auto.
  apply FTNew with Fs (map erase (map ReffieldType Fs)) (map ReffieldName Fs);auto.
  rewrite <- H. 
  assert (Forall2 (HasFJtype (erase_env g)) es (map erase Ts)). apply forall_hasfjtype';auto.
  apply typing_hasfjtype_forall';auto.

  apply forall_fsubtyping with (map erase Ts) ;auto.
  rewrite forall_erase with Us (ExpNew C es).
  apply forall_subtype_fsubtype with g;auto.
- (* TSub *) apply H || (apply H).
- 
  apply selfify_wf with (self b' (ExpLet e_x e));simpl;auto.
  rewrite erase_self.
  apply FTLet with (erase b) (union nms (binds g));auto. apply typing_hasfjtype;auto. intros.

  rewrite <- erase_unbind with y b'. assert (FCons y (erase b) (erase_env g) = erase_env (Cons y b g)). auto. rewrite H3.   apply typing_hasfjtype;auto. apply H0. notin_solve_one. 
Qed.


Lemma typing_wf_forall': forall g es Ts, 
Forall2 (Hastype g) es Ts -> 
WFEnv g ->
Forall (WFtype g) Ts.
Proof.
  intros.
  generalize dependent Ts.
  induction es.
  -
    intros. destruct Ts. apply Forall_nil. inversion H.
  -
    intros. destruct Ts. inversion H. inversion H. apply Forall_cons. eapply typing_wf;eauto. apply IHes;auto.
Qed.

Lemma typing_wf_hasfjtype': forall g es Ts, 
Forall2 (Hastype g) es Ts -> 
WFEnv g ->
Forall2 (HasFJtype (erase_env g)) es (map erase Ts).
Proof.
  intros.
  generalize dependent Ts.
  induction es.
  -
    intros. destruct Ts. apply Forall2_nil. inversion H.
  -
    intros. destruct Ts. inversion H. inversion H. apply Forall2_cons. eapply typing_hasfjtype;eauto. apply IHes;auto.
Qed.



Lemma fv_subset_binds : forall (g:env) (e:expr) (t:type),
    Hastype g e t -> Subset (fv e) (binds g).
Proof. intros. rewrite binds_erase_env. 
  apply fv_subset_bindsFJ with (erase t); apply typing_hasfjtype; assumption. Qed.

Lemma typ_islc : forall (g:env) (e:expr) (t:type),
    Hastype g e t -> isLC e.
Proof. intros; apply fjtyp_islc with (erase_env g) (erase t); 
  apply typing_hasfjtype; assumption. Qed.

Lemma t_wf_sub_fjtype: forall CC t g e1, wf_under CC t -> Hastype g e1 CC -> 
WFEnv g -> isLC e1 -> 
WFtype g  (tsubBV e1 t).
Proof.
  intros. assert True. auto. 
  apply wf_sub_fjtype with CC;auto.
  apply typing_hasfjtype;auto.
Qed.

Lemma t_wf_sub_fjtype2: forall t rt g e1 e2 CC, wf_under2 CC t rt -> Hastype g e1 CC -> 
(Hastype (g) e2 (tsubBV e1 t)) -> 
WFEnv g -> isLC e1 -> isLC e2 -> 
WFtype g (tsubBV_at 1 e1 (tsubBV e2 rt)).
Proof.
  intros.
  apply wf_sub_fjtype2 with t CC;auto.
  apply typing_hasfjtype;auto.
  apply typing_hasfjtype;auto.
Qed. 

Lemma tybc_exact : forall (g:env) (b:bool), 
    Subtype g (tybc b) (self (tybc b) (Bc b)).
Proof. intros; destruct b; unfold tybc; simpl; unfold eqlPred;
  apply SBase with (binds g); intros; unfold unbindP; simpl; try apply SubBBool; try apply SubBInt;
  apply IRepeat. Qed.
  
Lemma tyic_exact : forall (g:env) (n:Z),
    Subtype g (tyic n) (self (tyic n) (Ic n)).
Proof. intros; unfold tyic; simpl; unfold eqlPred;
  apply SBase with (binds g); intros; unfold unbindP; simpl; try apply SubBBool; try apply SubBInt;
  apply IRepeat. Qed.

Lemma selfify_wf_typing : forall (g:env) (s t:type) (e:expr),
    WFtype g t  -> Hastype g e s -> WFEnv g
                  -> WFtype g (self t e). 
Proof.
    intros. apply selfify_wf with s;auto.
    apply typing_hasfjtype;auto.
Qed.
