Require Import List.
Require Import Lia.
Require Import Coq.Program.Equality.

Require Import Definitions.Syntax.
Require Import Definitions.Names.
Require Import Definitions.FJTyping.

Require Import Definitions.Typing.
Require Import Definitions.SubDenotation.
Require Import Definitions.Semantics.

Require Import Definitions.CTSanity.

Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasFJTyping.
Require Import Lemmas.BasicLemmas.LemmasSubstitution.
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasEnvironments.
Require Import Lemmas.BasicLemmas.LemmasWF.
Require Import Lemmas.BasicLemmas.LemmasWFNarrow.
Require Import Lemmas.BasicLemmas.LemmasFJWeaken.
Require Import Lemmas.BasicLemmas.LemmasWFWeaken.
Require Import Lemmas.TypingLemmas.LemmasWeakenTyp.
Require Import Lemmas.BasicLemmas.LemmasSemantics.
Require Import Lemmas.BasicLemmas.LemmasWF.
Require Import Lemmas.BasicLemmas.LemmasWFNarrow.
Require Import Lemmas.BasicLemmas.LemmasTypeSubstitution.
Require Import Lemmas.BasicLemmas.LemmasWFSubstitution.
Require Import Lemmas.TypingLemmas.LemmasTyping.
Require Import Lemmas.LogicalLemmas.LemmasCSubst.
Require Import Lemmas.LogicalLemmas.LemmasDenotes.
Require Import Lemmas.LogicalLemmas.LemmasSImp.
Require Import Lemmas.LogicalLemmas.LemmasCSubstSemantics.
Require Import Lemmas.BasicLemmas.LemmasBigStepSemantics.
Require Import Lemmas.BasicLemmas.LemmasCTBasics.
Require Import Lemmas.BasicLemmas.LemmasCTTyping.
Require Import Lemmas.TypingLemmas.LemmasNarrowing.

(*---------------The Exactness Lemmas---------------*)

Lemma self_idempotent_upper : forall (g:env) (t:type) (e:expr),
    WFtype g t -> Subtype g (self t e) (self (self t e) e).
Proof. 
  intros.
  induction t.
  apply SBase with (binds g); intros;auto. apply IRepeat.
Qed.

Lemma IEvals2 : forall (g:env) (p p':expr) (ps:preds),
EvalsTo p' p -> LImplies g (PCons p ps) (PCons p' ps).
Proof. intros.
    apply SImp ; intros.
    rewrite cpsubst_pcons in H1.
    rewrite cpsubst_pcons; inversion H1.
    apply PECons.
    (* apply csubst_evals with th p' p in e; *)
    apply lemma_evals_trans with (csubst th p).
    apply csubst_evals;auto.
    apply denotesenv_loc_closed with g;auto.
    apply denotesenv_substitutable with g; auto.
    auto.
    auto.
Qed.
Lemma tsubBV_idempotent_step_upper' : forall (g:env) (e' e:expr) op,
   e ~~> e' -> isLC e' -> isLC e-> Subtype g (tsubBV e' (ty' op)) (tsubBV e (ty' op)).
Proof. 
  intros.
  unfold tsubBV. destruct op. simpl. 
  apply SBase with (binds g); 
  intros;auto. unfold unbindP. simpl. assert (open_at 0 y e' = e'). apply open_at_lc_at;auto. assert (open_at 0 y e = e). apply open_at_lc_at;auto. 
  rewrite H3. rewrite H4.
  apply IEvals2.
  apply step_evals. apply EBinOp1. apply EUnOp1. auto.
Qed.
Lemma self_idempotent_step_upper : forall (g:env) (t:type) (e' e:expr),
    WFtype g t -> e' ~~> e -> isLC e' -> isLC e-> Subtype g (self t e) (self (self t e) e').
Proof. 
  intros.
  induction t.
  apply SBase with (binds g); 
  intros;auto. unfold unbindP. simpl. assert (open_at 0 y e' = e'). apply open_at_lc_at;auto. assert (open_at 0 y e = e). apply open_at_lc_at;auto. 
  rewrite H4.
  fold (strengthen (PCons (ExpBinOp Eq e' (FV y)) PEmpty)  (PCons (ExpBinOp Eq (open_at 0 y e) (FV y)) (openP_at 0 y ps))).
  assert (LImplies (Cons y (TRefn b PEmpty) g)
  (PCons (ExpBinOp Eq (open_at 0 y e) (FV y)) (openP_at 0 y ps)) (PCons (ExpBinOp Eq (open_at 0 y e) (FV y)) (openP_at 0 y ps))).
  apply IRefl.
  assert (LImplies (Cons y (TRefn b PEmpty) g)
  (PCons (ExpBinOp Eq (open_at 0 y e) (FV y)) (openP_at 0 y ps)) (PCons (ExpBinOp Eq e' (FV y)) PEmpty)).
  apply ITrans with (PCons (ExpBinOp Eq e' (FV y)) (openP_at 0 y ps)). rewrite H5.
  apply IEvals2.
  apply step_evals. apply EBinOp1. auto.
  apply ICons1.
  apply IConj;auto.
Qed.
(*This is a special case of tsubBV_invariant, 
where the predicate is just an expression with known evaluation relation, in this case, proving needs no induction. 
while in the general case, we only knows about subBV, in this case, proving needs induction on (big-step semantic). 
*)
Lemma self_idempotent_step_upper' : forall (g:env) (t:type) (e' e:expr),
    WFtype g t -> e' ~~> e -> isLC e' -> isLC e-> Subtype g (self t e) (self t e').
Proof. 
  intros.
  induction t.
  apply SBase with (binds g); 
  intros;auto. unfold unbindP. simpl. assert (open_at 0 y e' = e'). apply open_at_lc_at;auto. assert (open_at 0 y e = e). apply open_at_lc_at;auto. 
  rewrite H4. rewrite H5.
  apply IEvals2.
  apply step_evals. apply EBinOp1. auto.
Qed.

Lemma self_idempotent_step_upper'' : forall (g:env) (s t:type) (e' e:expr),
    WFtype g t -> e' ~~> e -> isLC e' -> isLC e-> Subtype g s t -> Subtype g (self s e) (self t e').
Proof. 
  intros. inversion H3. unfold self.
  apply SBase with (union nms (binds g)); 
  intros;auto.
  unfold unbindP. simpl. assert (open_at 0 y e' = e'). apply open_at_lc_at;auto. assert (open_at 0 y e = e). apply open_at_lc_at;auto. 
  rewrite H10. rewrite H11.
  apply ITrans with (PCons (ExpBinOp Eq e (FV y)) (openP_at 0 y p2)).  apply ICons3. apply H5. notin_solve_one. 
  apply IEvals2.
  apply step_evals. apply EBinOp1. auto.
Qed.


Lemma self_idempotent_new: forall (g:env) es C,
Subtype g (self (TRefn (TNom (TClass C)) (PEmpty)) (ExpNew C es)) (self (self (TRefn (TNom (TClass C)) (PEmpty)) (ExpNew C es)) (ExpNew C es)).
Proof.
  intros.
  apply SBase with (binds g); intros; auto. apply IRepeat.
Qed.



Lemma unop_type_exact: forall op e, (tsubBV e (ty' op) = self (TRefn TBool PEmpty) (ExpUnOp op e)). 
Proof.
  intros.
  destruct op. unfold ty'. unfold self. unfold eqlPred. unfold refn_pred. unfold tsubBV. reflexivity.
Qed.
Lemma binop_type_exact: forall op e1 e2, isLC e2 -> ((tsubBV_at 1 e1 (tsubBV e2 (ty'2 op))) = self (TRefn TBool PEmpty) (ExpBinOp op e1 e2)). 
Proof.
  intros.
  destruct op. 
  unfold ty'2. unfold self. unfold eqlPred. unfold refn_pred2. unfold tsubBV. simpl. assert (subBV_at 2 e1 e2 = e2). apply subBV_at_lc_at with 2;auto.  apply islc_at_weaken with 0;auto. rewrite H0. reflexivity.
  unfold ty'2. unfold self. unfold eqlPred. unfold refn_pred2. unfold tsubBV. simpl. assert (subBV_at 2 e1 e2 = e2). apply subBV_at_lc_at with 2;auto.  apply islc_at_weaken with 0;auto. rewrite H0. reflexivity.
  unfold ty'2. unfold self. unfold eqlPred. unfold refn_pred2. unfold tsubBV. simpl. assert (subBV_at 2 e1 e2 = e2). apply subBV_at_lc_at with 2;auto.  apply islc_at_weaken with 0;auto. rewrite H0. reflexivity.
Qed.


Lemma exact_type : forall (g:env) (v:expr) (t:type),
    (* isValue v -> *) Hastype g v t -> WFtype g t -> WFEnv g -> Hastype g v (self t v).
Proof. intros g v t p_v_t. intros. 
  induction p_v_t. (* simpl in Hv; try contradiction. *)
  - (* TBC *) apply TSub with (tybc b). 
    apply TBC.
    apply selfify_wf with (tybc b) ;auto.
    apply tybc_exact.
    

  - (* TIC *) apply TSub with (tyic m).
          apply TIC.
          apply selfify_wf with (tyic m);auto.
          apply tyic_exact.
  -
    apply TSub with (tsubBV e (ty' op)).
    eapply TUnOP; eauto.
    apply selfify_wf with (tsubBV e (ty' op)). auto. apply typing_hasfjtype; try (apply TUnOP;auto); auto.
    eapply TUnOP;eauto.
    rewrite unop_type_exact. apply self_idempotent_upper;auto.
  -
    apply TSub with (tsubBV_at 1 e1 (tsubBV e2 (ty'2 op))).
    eapply TBinOP; eauto.
    apply selfify_wf with (tsubBV_at 1 e1 (tsubBV e2 (ty'2 op))). auto. apply typing_hasfjtype; try (apply TBinOP;auto); auto.
    eapply TBinOP; eauto.
    rewrite binop_type_exact. apply self_idempotent_upper;auto. auto.
  -
    (* TVar *) 
  apply TSub with (self t (FV x)).
  apply TVar;auto.
  apply selfify_wf with (self t (FV x));auto. apply typing_hasfjtype; try (apply TVar;auto); auto.
  apply self_idempotent_upper;auto.
  -
    apply TSub with (self (tsubBV_at 1 e1 (tsubBV e2 rt)) (ExpMethodInvoc e1 m e2)).
    eapply TInvok;eauto.
      +
        eapply selfify_wf;auto. apply typing_hasfjtype. eapply TInvok;eauto.
      +
        apply self_idempotent_upper;auto.
        apply t_wf_sub_fjtype2 with t (TRefn (TNom (TClass C)) ps);auto. eapply mtype_rt_wf;eauto. 
        apply TSub with (TRefn (TNom (TClass C)) ps');auto. eapply mtype_ps_wf_g;eauto. apply wfenv_unique;auto.
        apply TSub with t';auto. apply t_wf_sub_fjtype with (TRefn (TNom (TClass C)) ps);auto. eapply mtype_t_wf;eauto. apply TSub with (TRefn (TNom (TClass C)) ps');auto. eapply mtype_ps_wf_g;eauto. apply wfenv_unique;auto.
  -
    apply TSub with (self (tsubBV_at 1 e1 (tsubBV e2 rt)) (ExpMethodInvoc e1 m e2)).
    eapply TInvokI;eauto.
      +
        eapply selfify_wf;auto. apply typing_hasfjtype. eapply TInvokI;eauto.
      +
        apply self_idempotent_upper;auto.
        apply t_wf_sub_fjtype2 with t (TRefn (TNom (TInterface I)) ps);auto. eapply mtypei_rt_wf;eauto. 
        apply TSub with (TRefn (TNom (TInterface I)) ps');auto. eapply mtypei_ps_wf_g;eauto. apply wfenv_unique;auto.
        apply TSub with t';auto. apply t_wf_sub_fjtype with (TRefn (TNom (TInterface I)) ps);auto. eapply mtypei_t_wf;eauto. apply TSub with (TRefn (TNom (TInterface I)) ps');auto. eapply mtypei_ps_wf_g;eauto. apply wfenv_unique;auto.
  -
    apply TSub with (self (tsubBV e (ReffieldType fi)) (ExpFieldAccess e f)).
    eapply TField;eauto.
    eapply selfify_wf;auto. apply typing_hasfjtype. eapply TField;eauto. auto.
    apply self_idempotent_upper;auto.
    eapply fieldtype_wf';eauto.
    apply TSub with (TRefn (TNom (TClass C)) ps);auto. apply SBase with empty. apply SubBClass. apply SubCRefl. intros. apply IFaith.
  -
    apply TSub with (self (TRefn (TNom (TClass C)) PEmpty) (ExpNew C es)).
    eapply TNew;eauto.
    apply selfify_wf with (self (TRefn (TNom (TClass C)) PEmpty) (ExpNew C es));auto. apply typing_hasfjtype. eapply TNew;eauto. auto.
    apply self_idempotent_new.

  -
    apply TSub with (self b' (ExpLet e_x e)).
    eapply TLet;eauto.
    apply selfify_wf with (self b' (ExpLet e_x e));auto. apply typing_hasfjtype; try (eapply TLet;eauto); auto.
    apply self_idempotent_upper;auto.
  - (* TSub *) 
    apply TSub with (self s e).
    apply IHp_v_t;auto.
    eapply typing_wf;eauto.
    apply selfify_wf with t.
    apply H1.
    apply typing_hasfjtype.
    apply TSub with s;auto.
    auto. auto.
    apply exact_subtype;auto.
    eapply typing_wf;eauto.
    eapply typ_islc;eauto.
Qed.

Lemma exact_eval': forall (g:env) (v:expr) (s t:type) e (*C Fs i vs fi*), 
(*isValue v -> *) Hastype g v (self t v) -> WFtype g t -> WFEnv g -> (*g = Empty -> *)
e ~~> v -> HasFJtype (erase_env g) e (erase s) -> 
Hastype g v (self t e).
Proof.
  intros. 
  assert (isLC v). apply fjtyp_islc with  (erase_env g) (erase (self t v)). apply typing_hasfjtype;auto.
  assert (isLC e). apply fjtyp_islc with  (erase_env g) (erase s). auto. 
  generalize dependent s.
  dependent induction H; intros; try contradiction.
  -
    apply TSub with (self t (Bc b));auto. rewrite <- x. apply TBC. 
    apply selfify_wf with s;auto.
    apply self_idempotent_step_upper';auto. 
  -
    apply TSub with (self t (Ic m));auto. rewrite <- x. apply TIC. 
    apply selfify_wf with s;auto.
    apply self_idempotent_step_upper';auto. 
  -
    apply TSub with ((tsubBV e0 (ty' op)) );auto. eapply TUnOP;eauto. 
    apply selfify_wf with s;auto.
    rewrite x.  apply self_idempotent_step_upper';auto.
  - 
    apply TSub with (tsubBV_at 1 e1 (tsubBV e2 (ty'2 op)));auto. eapply TBinOP;eauto. 
    apply selfify_wf with s;auto. 
    rewrite x.  apply self_idempotent_step_upper';auto. 
  -
    apply TSub with (self t (FV x0));auto. rewrite <- x. apply TVar; auto. 
    apply selfify_wf with s;auto.
    apply self_idempotent_step_upper';auto.
  -
    apply TSub with (self (tsubBV_at 1 e1 (tsubBV e2 rt)) (ExpMethodInvoc e1 m e2));auto. eapply TInvok; eauto. 
    apply selfify_wf with s;auto.
    rewrite x.  apply self_idempotent_step_upper';auto.
  -
    apply TSub with (self (tsubBV_at 1 e1 (tsubBV e2 rt)) (ExpMethodInvoc e1 m e2));auto. eapply TInvokI; eauto. 
    apply selfify_wf with s;auto.
    rewrite x.  apply self_idempotent_step_upper';auto.
  -
    apply TSub with (self t (ExpFieldAccess e0 f));auto. rewrite <- x. eapply TField; eauto.
    apply selfify_wf with s;auto.
    apply self_idempotent_step_upper';auto.
  -
    (* subst g.  *)
    apply TSub with (self t (ExpNew C es));auto. rewrite <- x. eapply TNew; eauto.
    apply selfify_wf with s;auto.
    apply self_idempotent_step_upper';auto.
  -
    apply TSub with (self t (ExpLet e_x e0)). rewrite <- x.
    eapply TLet;eauto.
    apply selfify_wf with s;auto.
    apply self_idempotent_step_upper';auto.
  - 
    apply TSub with (self t e0). 
    apply TSub with s;auto.
    apply selfify_wf with s0;auto.
    apply self_idempotent_step_upper';auto.
  
Qed. 

Lemma exact_eval: forall (g:env) (v:expr) (s t:type) e (*C Fs i vs fi*), 
(*isValue v -> *) Hastype g v t -> WFtype g t -> WFEnv g -> (*g = Empty -> *)
e ~~> v -> HasFJtype (erase_env g) e (erase s) -> 
Hastype g v (self t e).
Proof.
  intros. 
  assert (isLC v). apply fjtyp_islc with  (erase_env g) (erase t). apply typing_hasfjtype;auto.
  assert (isLC e). apply fjtyp_islc with  (erase_env g) (erase s). auto. 
  generalize dependent s.
  induction H; intros; try contradiction.
  -
    apply TSub with (self (tybc b) (Bc b));auto. apply exact_type;auto. apply TBC. 
    apply selfify_wf with s;auto.
    apply self_idempotent_step_upper';auto.
  -
    apply TSub with (self (tyic m) (Ic m));auto. apply exact_type;auto. apply TIC. 
    apply selfify_wf with s;auto.
    apply self_idempotent_step_upper';auto.
  -
    apply TSub with ((tsubBV e0 (ty' op)) );auto. eapply TUnOP;eauto. 
    apply selfify_wf with s;auto. 
    rewrite unop_type_exact. apply self_idempotent_step_upper;auto.  
  -
    apply TSub with (tsubBV_at 1 e1 (tsubBV e2 (ty'2 op)));auto. eapply TBinOP;eauto. 
    apply selfify_wf with s;auto. 
    rewrite binop_type_exact. apply self_idempotent_step_upper;auto. unfold isLC in H4. simpl in H4. destruct H4. auto.  
  -
    apply TSub with (self t (FV x));auto. apply TVar; auto. 
    apply selfify_wf with s;auto.
    apply self_idempotent_step_upper;auto.
  -
    apply TSub with (self (tsubBV_at 1 e1 (tsubBV e2 rt)) (ExpMethodInvoc e1 m e2));auto. eapply TInvok; eauto. 
    apply selfify_wf with s;auto.
    apply self_idempotent_step_upper.
    apply selfify_wf' with (ExpMethodInvoc e1 m e2);auto.
    auto.
    eapply fjtyp_islc;eauto. 
    unfold isLC. simpl. constructor;auto.
  -
    apply TSub with (self (tsubBV_at 1 e1 (tsubBV e2 rt)) (ExpMethodInvoc e1 m e2));auto. eapply TInvokI; eauto. 
    apply selfify_wf with s;auto.
    apply self_idempotent_step_upper.
    apply selfify_wf' with (ExpMethodInvoc e1 m e2);auto.
    auto.
    eapply fjtyp_islc;eauto. 
    unfold isLC. simpl. constructor;auto.
  -
    apply TSub with (self (tsubBV e0 (ReffieldType fi)) (ExpFieldAccess e0 f));auto. eapply TField; eauto. 
    apply selfify_wf with s;auto.
    apply self_idempotent_step_upper.
    apply selfify_wf' with (ExpFieldAccess e0 f);auto.
    auto.
    eapply fjtyp_islc;eauto. 
    unfold isLC. simpl. auto. 
  -
    (* subst g.  *)
    apply TSub with (self (TRefn (TNom (TClass C)) (PEmpty)) (ExpNew C es));auto. eapply TNew; eauto.
    apply selfify_wf with s;auto.
    apply self_idempotent_step_upper;auto.
    (* apply selfify_wf' with (ExpNew C es);auto. *)
  -
    apply TSub with (self b' (ExpLet e_x e0)).
    eapply TLet;eauto.
    apply selfify_wf with s;auto. 
    apply self_idempotent_step_upper;auto.
  - 
    apply TSub with (self s e).
    apply IHHastype with s0;auto.
    eapply typing_wf;eauto.
    (* apply subtype_fsubtype in H10.
    apply FTSub with (erase t);auto.  *)
    (* assert (erase s = erase t). apply erase_subtype with g;auto. rewrite H11; auto. *)
    apply selfify_wf  with s0;auto.
    apply exact_subtype;auto.
    eapply typing_wf;eauto.
Qed. 
