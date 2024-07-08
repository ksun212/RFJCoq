Require Import Referable.
Require Import List.
Require Import Crush.
Require Import Lists.ListSet.
Require Import Lists.
Require Import ZArith.
Require Import RFJ.Tactics.
Require Import Coq.Program.Equality.
Require Import Lia.

Require Import Definitions.Syntax. 
Require Import Definitions.Names.
Require Import Definitions.Semantics.
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
Require Import Lemmas.LogicalLemmas.LemmasSImp.
Require Import Lemmas.BasicLemmas.LemmasExactness.
Require Import Lemmas.BasicLemmas.LemmasTypeSubstitution.
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasPrimitivesBasics.
Require Import Lemmas.TypingLemmas.LemmasTyping.
Require Import Lemmas.BasicLemmas.LemmasTypeSubstitution.
Require Import Lemmas.TypingLemmas.LemmasNarrowing.
Require Import Lemmas.TypingLemmas.LemmasInversion.
Require Import Lemmas.BasicLemmas.LemmasWF.
Require Import Lemmas.BasicLemmas.LemmasWFNarrow.
Require Import Lemmas.TypingLemmas.LemmasTransitive.
Require Import Lemmas.TypingLemmas.LemmasSubstitutionTyping.
Require Import Lemmas.BasicLemmas.LemmasWFSubstitution.
Require Import Lemmas.BasicLemmas.LemmasCTBasics.
Require Import Lemmas.BasicLemmas.LemmasCTTyping.
Require Import Lemmas.TypingLemmas.LemmasRefl.
Require Import Lemmas.TypingLemmas.LemmasWeakenTyp.

Require Import Lemmas.BasicLemmas.LemmasFJWeaken.
Require Import Lemmas.BasicLemmas.LemmasWFWeaken.
Require Import Lemmas.LogicalLemmas.LemmasDenotesEnv.
Require Import Lemmas.LogicalLemmas.LemmasDenotesTyping.

Require Import Lemmas.LogicalLemmas.LemmasCSubst.
Require Import Lemmas.LogicalLemmas.LemmasDenotes.
Require Import Lemmas.BasicLemmas.LemmasSubstitution.
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasSemantics.
Require Import Lemmas.TypingLemmas.Preservation_Progress.
Require Import Theorems.TypeSoundness.



(*---------------The Closing Substitution Lemma---------------*)

Lemma denotesenv_concat: forall g g' th th1, 
DenotesEnv g th -> DenotesEnv (csubst_env th g') th1 -> intersect (binds g) (binds g') = empty -> DenotesEnv (concatE g g') (CconcatE th th1).
Proof.
  intros. rename H1 into inter.
  generalize dependent g. generalize dependent th. generalize dependent g'.
  induction th1;intros.
  -
    inversion H0. 
    assert(g' = Empty). destruct g'. auto. rewrite csubst_cons_env in H2. inversion H2. 
    simpl. rewrite H1. simpl. auto.
  -
    inversion H0. destruct g'. rewrite csubst_env_empty in H1. inversion H1.
    rewrite csubst_cons_env in H1. inversion H1. subst x1. subst x0. 
    simpl. apply DExt;auto.
    ++ 
      apply IHth1;auto. rewrite <- H11. auto. simpl in inter. apply intersect_names_add_elim_r in inter. destruct inter. auto. 
    ++
      unfold in_env. apply not_elem_concat_intro. 
      apply intersect_names_add_elim_r in inter. destruct inter. auto. 
      unfold in_env in H6. rewrite H11 in H6. rewrite csubst_env_binds in H6. auto.
    ++
      rewrite H10 in H7.
      rewrite <- ctsubst_concat; auto.
      +++
        simpl in inter. apply intersect_names_add_elim_r in inter. destruct inter. 
        rewrite <- binds_env_th with g th;auto. rewrite <- binds_env_th with g0 th1;auto.
        assert (binds g0 = binds g'). rewrite H11. rewrite csubst_env_binds. auto. rewrite H9.
        apply intersect_commute. auto.
      +++
        apply denotesenv_substitutable with g0;auto.
      +++
        apply denotesenv_substitutable with g;auto.
Qed.  

Lemma denotesenv_subtype_generalized: forall t s g th g', 
  Subtype (concatE g g') t s -> WFEnv g -> DenotesEnv g th -> intersect (binds g) (binds g') = empty -> Subtype (csubst_env th g') (ctsubst th t) (ctsubst th s).
Proof.
  intros.
  assert (loc_closed th) as loc. apply denotesenv_loc_closed with g;auto.
  assert (closed th) as clo. apply denotesenv_closed with g;auto.
  assert (substitutable th) as subs. apply denotesenv_substitutable with g;auto.
  
  rename H2 into inter. destruct t. destruct s. inversion H. rewrite ctsubst_refn. rewrite ctsubst_refn. 
  apply SBase with (union (binds g') (union (binds g) nms)). auto.
  intros. assert (~Elem y nms) as xx. notin_solve_one. apply H8 in xx. inversion xx. 
  apply SImp. intros. (*only do csubst for g'*) 
  assert (~ in_csubst y th) as nin.  unfold in_csubst. rewrite <- binds_env_th with g th;auto. notin_solve_one. 
  assert (unbindP y (cpsubst th ps0) = cpsubst th (unbindP y ps0)). rewrite ctsubst_unbindP;auto. rewrite H16.
  inversion H14. simpl. 
  assert (psubFV y v (cpsubst th (unbindP y ps0)) = cpsubst (CCons y v th ) (unbindP y ps0)). rewrite unroll_cpsubst_left;auto. apply value_closed. apply den_isvalue with (ctsubst th1 (TRefn b PEmpty));auto. rewrite H24.
  assert (DenotesEnv (Cons y (TRefn b PEmpty) (concatE g g')) (CCons y v (CconcatE th th1))). 
  apply DExt. 
    + apply denotesenv_concat;auto.
    + unfold in_env. apply not_elem_concat_intro; notin_solve_one. 
    + rewrite ctsubst_refn in H23. rewrite cpsubst_pempty in H23. 
      rewrite ctsubst_refn. rewrite cpsubst_pempty.  auto.
  +
  apply H10 in H25.
  assert (cpsubst th1 (cpsubst (CCons y v th) (unbindP y ps0)) = cpsubst (CCons y v (CconcatE th th1)) (unbindP y ps0)). simpl. rewrite cpsubst_concat;auto. rewrite <- binds_env_th with g th;auto. rewrite <- binds_env_th with (csubst_env th g') th1;auto. rewrite csubst_env_binds. apply intersect_commute;auto. apply denotesenv_substitutable with (csubst_env th g');auto.  rewrite H26. auto.
  rewrite <- H21 in H15.
  assert (cpsubst (CCons y v th1) (unbindP y (cpsubst th ps)) = cpsubst (CCons y v (CconcatE th th1)) (unbindP y ps)). simpl. assert(psubFV y v (unbindP y (cpsubst th ps)) = cpsubst th (psubFV y v (unbindP y ps))). rewrite <-ctsubst_unbindP; auto. rewrite <-cpsubst_psubFV;auto.  apply den_isvalue with (ctsubst th1 (TRefn b PEmpty));auto.  rewrite H26. rewrite cpsubst_concat;auto. rewrite <- binds_env_th with g th;auto. rewrite <- binds_env_th with (csubst_env th g') th1;auto. rewrite csubst_env_binds. apply intersect_commute;auto. apply denotesenv_substitutable with (csubst_env th g');auto.  rewrite <- H26. auto.
Qed.
Lemma denotesenv_subtype_generalized_forall: forall ts ss g th g', 
  Forall2 (Subtype (concatE g g')) ts ss -> WFEnv g -> DenotesEnv g th -> intersect (binds g) (binds g') = empty -> Forall2 (Subtype (csubst_env th g')) (map (ctsubst th) ts) (map (ctsubst th) ss).
Proof. 
  intros. generalize dependent ts. 
  induction ss;intros.
  - destruct ts. simpl. apply Forall2_nil. inversion H.
  - destruct ts. inversion H. inversion H. apply Forall2_cons. 
    apply denotesenv_subtype_generalized with g;auto.
    apply IHss;auto.
Qed.



Lemma csubst_env_bound_in: forall x t g th, bound_in x t g -> bound_in x (ctsubst th t) (csubst_env th g).
Proof.
  intros. induction g. 
  -
    simpl in H. contradiction.
  -
    simpl in H. destruct H.
    +
      rewrite csubst_cons_env. simpl. destruct H. 
      left. constructor;auto. f_equal;auto.
    +
      rewrite csubst_cons_env. simpl. 
      right. apply IHg;auto.
Qed.

Lemma boundin_hastype':  forall (t:type) g th x,
  bound_in x t g -> WFEnv g -> DenotesEnv g th -> Hastype Empty (csubst th (FV x)) (ctsubst th (self t (FV x))).
Proof.
  intros. generalize dependent g. generalize dependent t. induction th.
  -
  intros. inversion H1. subst g. simpl in H. contradiction.
  -
  intros. inversion H1. subst g. inversion H0. subst x0. simpl in H. destruct H. 
  +
    destruct H. subst x1. subst t0. rewrite ctsubst_self_noFTV. simpl. inversion H1.
    assert (fv v_x = empty). apply value_closed;auto. apply den_isvalue with (ctsubst th t); auto.
    assert (~ Elem x (free t)). apply free_bound_in_env with g0;auto.
    simpl. case_eq (PeanoNat.Nat.eqb x x). intros. 
    *
      rewrite csubst_nofv;auto. rewrite tsubFV_notin;simpl;auto.
      apply exact_type;simpl;auto.
      ** 
        apply denotestyping; auto. 
        apply ctsubst_wf with g0;auto.
        apply wfenv_unique ;auto.
      **
        apply ctsubst_wf with g0;auto.
        apply wfenv_unique ;auto.
    * 
      intros. apply PeanoNat.Nat.eqb_neq in H22. contradiction. 
  +
    assert (x<>x1). assert (x1<>x). unfold in_env in H7.  apply boundin_inenv in H. apply not_elem_elem_neq with (binds g0);auto. auto. 
    assert(~Elem x1 (free t)). apply free_bound_in_env with g0;auto. apply boundin_wfenv_wftype with x;auto.
    apply IHth in H;auto. simpl.  case_eq (PeanoNat.Nat.eqb x1 x). intros.
    * apply PeanoNat.Nat.eqb_eq in H15. rewrite H15 in H2. contradiction.
    * intros. rewrite tsubFV_notin;auto. apply not_elem_subset with ((union (fv (FV x))  (free t)) ). apply free_self. apply not_elem_union_intro;auto. simpl. unfold not. intros. destruct H16;auto. 
Qed. 

Lemma boundin_hastype:  forall (t:type) g th x g',
  bound_in x t (concatE g g') -> WFEnv g -> DenotesEnv g th -> unique g' ->  WFEnv (csubst_env th g') -> 
  intersect (binds g) (binds g') = empty -> WFtype (concatE g g') t -> 
  Hastype (csubst_env th g') (csubst th (FV x)) (ctsubst th (self t (FV x))).
Proof.
  intros. rename H2 into uni. rename H3 into wfenv. rename H4 into inter. rename H5 into wft.
  assert (bound_in x t (concatE g g'));auto. rename H2 into bd.
  apply boundin_concat in H. apply boundin_concat_unique in bd;auto.  destruct H.
  -
    assert (Hastype Empty (csubst th (FV x)) (ctsubst th (self t (FV x)))). apply boundin_hastype' with g;auto.
    assert (csubst_env th g' = concatE Empty (csubst_env th g') ). rewrite empty_concatE. auto. rewrite H3. 
    apply weaken_many_typ;simpl;auto.
    + apply csubst_env_unique;auto.
    + rewrite empty_concatE. auto. 
  -  
    destruct bd. destruct H2. assert (Elem x (binds g')). apply boundin_inenv with t;auto. contradiction.
    destruct H2. 
    assert (csubst th (FV x) = FV x). apply csubst_nofv'. simpl. rewrite <- binds_env_th with g th;auto. apply intersect_singleton;auto.  rewrite H4. rewrite ctsubst_self_noFTV. rewrite H4.
    apply TVar. apply csubst_env_bound_in;auto. 
    apply ctsubst_wf' with g;auto.  apply wfenv_unique;auto.
Qed.


Lemma aux1: forall th b, ctsubst th (tybc b) = tybc b.
Proof. induction th. intros. unfold tybc. simpl. auto.
intros. simpl. rewrite <- IHth. unfold tybc. auto.
Qed.
Lemma aux2: forall th b, ctsubst th (tyic b) = tyic b.
Proof. induction th. intros. unfold tyic. simpl. auto.
intros. simpl. rewrite <- IHth. unfold tyic. auto.
Qed.

Lemma denotesenv_preserve_value_typing_generalized: forall (t:type) g th e g',
Hastype (concatE g g') e t -> isValue e -> WFEnv g -> unique g' -> intersect (binds g) (binds g') = empty -> DenotesEnv g th -> Hastype (csubst_env th g') (csubst th e) (ctsubst th t).
Proof.
  intros. assert (fv e = empty). apply value_closed;auto. rewrite csubst_nofv;auto.
  dependent induction H using Hastype_ind';simpl in H0;try contradiction.
  -
    rewrite aux1. apply TBC.
  -
    rewrite aux2. apply TIC.
  -
    rewrite ctsubst_self_noFTV. rewrite csubst_nofv;auto. rewrite ctsubst_nofree;auto. 
   apply Definitions.Typing.TNew with (map (ctsubst th) Ts) Fs (map ReffieldType Fs) (map ref Fs);auto.  
    +
      clear H5. generalize dependent es. induction Ts. intros. destruct es. apply Forall2_nil. inversion H4.
      intros. destruct es. inversion H4. inversion H4. inversion H3. inversion H1. destruct H0. simpl in H10. apply union_eq_empty in H10. destruct H10. apply Forall2_cons. apply H12 with g;auto. apply IHTs;auto. 
    +
      intros.
      assert ((map (tsubBV (ExpNew C (map (csubst th) es))) (map (ctsubst th) (map ReffieldType Fs))) = (map (ctsubst th) (map (tsubBV (ExpNew C es)) (map ReffieldType Fs)))). rewrite <-csubst_new. rewrite <- ctsubst_tsubBV_forall. auto. apply denotesenv_loc_closed with g;auto. apply denotesenv_substitutable with g;auto.
      assert ((map (ctsubst th) (map ReffieldType Fs)) = (map ReffieldType Fs)). apply csubst_fjtype with C Fs;auto. rewrite <- H11.
      rewrite <- csubst_nofv with th (ExpNew C es);auto. rewrite csubst_new. 
      rewrite H.
      apply denotesenv_subtype_generalized_forall with g;auto.
  -
    apply TSub with (ctsubst th s);auto.
    +
      apply IHHastype with g;simpl;auto. 
    +
      apply ctsubst_wf' with g;auto.
      apply wfenv_unique;auto.
    +
      apply denotesenv_subtype_generalized with g;auto.
Qed.
(*We should be able to remove one of the two WFEnv *)
Lemma denotesenv_subst_typing_generalized:  forall (t:type) g g' th e ,
  Hastype (concatE g g') e t -> WFEnv g -> DenotesEnv g th -> unique g' -> 
  WFEnv (csubst_env th g') -> WFEnv (concatE g g') -> intersect (binds g) (binds g') = empty ->  
  Hastype (csubst_env th g') (csubst th e) (ctsubst th t).
Proof.
  intros. rename H4 into wfenv'. rename H5 into inter. rename H2 into uni. rename H3 into wfenv.
  assert (loc_closed th) as loc. apply denotesenv_loc_closed with g;auto.
  assert (substitutable th) as subs. apply denotesenv_substitutable with g;auto.

  generalize dependent th. dependent induction H using Hastype_ind';intros.
  -
    apply denotesenv_preserve_value_typing_generalized with g;simpl;auto. apply TBC. 
  -
    apply denotesenv_preserve_value_typing_generalized with g;simpl;auto. apply TIC.
  -
    apply boundin_hastype with g;auto.
  -
    rewrite csubst_unop. rewrite ctsubst_tsubBV;auto. 
    assert ((ctsubst th (ty' op)) = ty' op). apply csubst_ty'. rewrite H4. 
    apply TUnOP with (ctsubst th t);auto.   

    apply IHHastype with g;auto.
    assert ((ctsubst th (intype op)) = intype op). apply csubst_intype. rewrite <- H5. 
    apply denotesenv_subtype_generalized with g;auto.
    apply csubst_lc;auto.
  - 
    rewrite csubst_binop. rewrite ctsubst_tsubBV';auto. rewrite ctsubst_tsubBV;auto. 
    assert ((ctsubst th (ty'2 op)) = ty'2 op). apply csubst_ty'2. rewrite H7. 
    apply TBinOP with (ctsubst th t) (ctsubst th t');auto.
    apply IHHastype1 with g;auto.
    assert ((ctsubst th (fst (intype2 op))) = (fst (intype2 op))). apply csubst_intype2. 
    
    rewrite <- H8.
    apply denotesenv_subtype_generalized with g;auto.
    apply IHHastype2 with g;auto.
    
    intros.
    assert ((ctsubst th (snd (intype2 op))) = (snd (intype2 op))). apply csubst_intype2'. rewrite <- H8.
    rewrite <- ctsubst_tsubBV;auto. 
    apply denotesenv_subtype_generalized with g;auto. 
    apply csubst_lc;auto.
    apply csubst_lc;auto.
  -
    assert (isLC (csubst th e1)). apply csubst_lc;auto. 
    assert (isLC (csubst th e2)). apply csubst_lc;auto.
    rewrite ctsubst_self_noFTV;auto. rewrite csubst_invok;auto. rewrite ctsubst_tsubBV';auto. rewrite ctsubst_tsubBV;auto.
    assert (ctsubst th rt = rt). eapply csubst_mtype_rt;eauto. rewrite H10.
    apply TInvok with t (ctsubst th t') C ps (cpsubst th ps');auto.
    +
      rewrite <- ctsubst_refn. 
      apply IHHastype1 with g;auto.
    +
      assert (TRefn (TNom (TClass C)) ps = (ctsubst th (TRefn (TNom (TClass C)) ps))). erewrite csubst_mtype_ps;eauto. rewrite H11.
      rewrite <- ctsubst_refn.
      apply denotesenv_subtype_generalized with g;auto.
    +
      apply IHHastype2 with g;auto.
    +  
      assert (ctsubst th t = t). erewrite csubst_mtype_t;eauto. rewrite <- H11.
      rewrite <- ctsubst_tsubBV;auto.
      apply denotesenv_subtype_generalized with g;auto. 
    -
      assert (isLC (csubst th e1)). apply csubst_lc;auto. 
      assert (isLC (csubst th e2)). apply csubst_lc;auto.
      rewrite ctsubst_self_noFTV;auto. rewrite csubst_invok;auto. rewrite ctsubst_tsubBV';auto. rewrite ctsubst_tsubBV;auto.
      assert (ctsubst th rt = rt). eapply csubst_mtypei_rt;eauto. rewrite H10.
      apply TInvokI with t (ctsubst th t') C ps (cpsubst th ps');auto.
      +
        rewrite <- ctsubst_refn. 
        apply IHHastype1 with g;auto.
      +
        
        assert (TRefn (TNom (TInterface C)) ps = (ctsubst th (TRefn (TNom (TInterface C)) ps))). erewrite csubst_mtypei_ps;eauto. rewrite H11.
        rewrite <- ctsubst_refn.
        apply denotesenv_subtype_generalized with g;auto.
      +
        apply IHHastype2 with g;auto.
      +  
        assert (ctsubst th t = t). erewrite csubst_mtypei_t;eauto. rewrite <- H11.
        rewrite <- ctsubst_tsubBV;auto.
        apply denotesenv_subtype_generalized with g;auto. 
    
  -
    assert (isLC (csubst th e)). apply csubst_lc;auto.  
    rewrite ctsubst_self_noFTV;auto. rewrite csubst_access;auto. rewrite ctsubst_tsubBV;auto.
    assert (ctsubst th (ReffieldType fi) = (ReffieldType fi)). erewrite csubst_fjtype';eauto. rewrite H6.
    apply TField with C Fs i (cpsubst th ps);auto.
    + 
      rewrite <- ctsubst_refn. 
      apply IHHastype with g;auto.
  -
    rewrite ctsubst_self_noFTV. rewrite csubst_new. rewrite aux3. apply Definitions.Typing.TNew with (map (ctsubst th) Ts) Fs (map ReffieldType Fs) (map ref Fs);auto. apply csubst_lc_forall;auto. 
    +
      clear H5. generalize dependent es. induction Ts. intros. destruct es. apply Forall2_nil. inversion H4.
      intros. destruct es. inversion H4. inversion H4. inversion H3. inversion H1. apply Forall2_cons. apply H8 with g;auto. apply IHTs;auto. 
    +
      intros.
      assert ((map (tsubBV (ExpNew C (map (csubst th) es))) (map (ctsubst th) (map ReffieldType Fs))) = (map (ctsubst th) (map (tsubBV (ExpNew C es)) (map ReffieldType Fs)))). rewrite <-csubst_new. rewrite <- ctsubst_tsubBV_forall. auto. apply denotesenv_loc_closed with g;auto. apply denotesenv_substitutable with g;auto.
      assert ((map (ctsubst th) (map ReffieldType Fs)) = (map ReffieldType Fs)). apply csubst_fjtype with C Fs;auto. rewrite <- H7.
      rewrite H.
      apply denotesenv_subtype_generalized_forall with g;auto.  
  -
    apply TSub with (ctsubst th s);auto. apply IHHastype with g;auto. apply ctsubst_wf' with g;auto. apply wfenv_unique;auto. apply denotesenv_subtype_generalized with g;auto.
  -
  rewrite ctsubst_self_noFTV;auto. rewrite csubst_let;auto. 
  apply TLet with (ctsubst th b) (union (binds g') (union (binds g) nms)).
  apply ctsubst_wf' with g;auto. apply wfenv_unique;auto. 
  apply IHHastype with g;auto.
  intros.
  rewrite <- csubst_unbind;auto. rewrite <- ctsubst_unbindT;auto.
  assert (Cons y (ctsubst th b) (csubst_env th g') = csubst_env th (Cons y b g')). rewrite csubst_cons_env;auto. rewrite H6.
  apply H2 with g;auto.
  notin_solve_one.
  simpl. constructor;auto. unfold in_env. notin_solve_one.
  simpl. apply WFEBind;auto. unfold in_env. apply not_elem_concat_intro;notin_solve_one. apply typing_wf with e_x;auto.  
  simpl. apply intersect_names_add_intro_r;auto. notin_solve_one.
  rewrite csubst_cons_env;auto. apply WFEBind;auto. unfold in_env. rewrite csubst_env_binds. notin_solve_one. apply ctsubst_wf' with g;auto. apply typing_wf with e_x;auto. apply wfenv_unique;auto.
  unfold in_csubst. rewrite <-binds_env_th with g th;auto. notin_solve_one.
  unfold in_csubst. rewrite <-binds_env_th with g th;auto. notin_solve_one.
Qed.

Lemma closing_substitution:  forall (t:type) g th e ,
  Hastype g e t -> WFEnv g -> DenotesEnv g th -> Hastype Empty (csubst th e) (ctsubst th t).
Proof.
  intros.
  assert (Empty = (csubst_env th Empty)). rewrite csubst_env_empty. auto. rewrite H2.
  apply  denotesenv_subst_typing_generalized with g;simpl;auto. 
  rewrite csubst_env_empty. auto.
  apply intersect_empty_r.
Qed.