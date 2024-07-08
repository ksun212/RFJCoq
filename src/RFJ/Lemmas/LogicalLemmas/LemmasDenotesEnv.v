Require Import Arith.
Require Import Lists.ListSet.

Require Import Definitions.Syntax.
Require Import Definitions.Names.
Require Import Definitions.Semantics.
Require Import Definitions.FJTyping.

Require Import Definitions.Typing.

Require Import Definitions.SubDenotation.

Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasFJTyping.
Require Import Lemmas.BasicLemmas.LemmasSubstitution.
Require Import Lemmas.BasicLemmas.LemmasWFSubstitution.
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasEnvironments.
Require Import Lemmas.BasicLemmas.LemmasWF.
Require Import Lemmas.BasicLemmas.LemmasWFNarrow.
Require Import Lemmas.BasicLemmas.LemmasFJSubstitution.
Require Import Lemmas.BasicLemmas.LemmasFJWeaken.
Require Import Lemmas.BasicLemmas.LemmasWFWeaken.
Require Import Lemmas.TypingLemmas.LemmasTyping.
Require Import Lemmas.BasicLemmas.LemmasSemantics.
Require Import Lemmas.LogicalLemmas.LemmasCSubst.
Require Import Lemmas.LogicalLemmas.LemmasDenotes.





(*---------------Basic Properties of Environment Denotation---------------*)

Lemma concat_shift : forall (g:env) (x:vname) (t_x:type) (g':env),
    ~ (in_env x g) -> ~ (in_env x g') -> intersect (binds g) (binds g') = empty
        -> concatE (Cons x t_x g) g' = concatE g (concatE (Cons x t_x Empty) g').
Proof. intros g x t_x; induction g'; simpl; intros; try reflexivity;
  f_equal; apply IHg'; unfold in_env in H0; simpl in H0;
  apply not_elem_names_add_elim in H0; destruct H0; 
  apply intersect_names_add_elim_r in H1; destruct H1;  trivial. Qed.

Lemma csubst_env_empty : forall (th:csub),
    csubst_env th Empty = Empty.
Proof. induction th; simpl; reflexivity || apply IHth. Qed.

Lemma csubst_cons_env : forall (th:csub) (x:vname) (t_x:type) (g:env),
    csubst_env th (Cons x t_x g) = Cons x (ctsubst th t_x) (csubst_env th g).
Proof. induction th; simpl; intros; reflexivity || apply IHth. Qed.


Lemma esubFV_concat : forall (x:vname) (v:expr) (g g':env),
    esubFV x v (concatE g g') = concatE (esubFV x v g) (esubFV x v g').
Proof. intros; induction g'; simpl; try rewrite IHg'; reflexivity. Qed.

Lemma csubst_env_concat : forall (th:csub) (g g':env),
    csubst_env th (concatE g g') = concatE (csubst_env th g) (csubst_env th g').
Proof. induction th; simpl; intros; try rewrite esubFV_concat;
  try rewrite esubFTV_concat; apply IHth || reflexivity. Qed.

Lemma csubst_env_binds : forall (th:csub) (g:env),
    binds (csubst_env th g) = binds g.
Proof. induction th; intros; simpl; try rewrite IHth;
  try apply esubFV_binds; try apply esubFTV_binds; reflexivity. Qed.

Lemma csubst_env_unique : forall (th:csub) (g:env),
    unique g -> unique (csubst_env th g).
Proof. induction th; intros; simpl; try apply IHth;
  try apply esubFV_unique; try apply esubFTV_unique; apply H. Qed.

Lemma commute_esubFV : forall (g:env) (x:vname) (v_x:expr) (y:vname) (v_y:expr),
    y <> x -> ~ Elem x (fv v_y) -> ~ Elem y (fv v_x)
        -> esubFV y v_y (esubFV x v_x g) = esubFV x (subFV y v_y v_x) (esubFV y v_y g).
Proof. induction g; simpl; intros; reflexivity || rewrite <- IHg;
  try rewrite commute_tsubFV; 
  try rewrite subFV_notin'; trivial. Qed.


Lemma csubst_hasfjtype' : forall (g g':env) (e:expr) (t:type) (th:csub),
    HasFJtype (erase_env (concatE g g')) e (erase t) 
        -> unique g -> unique g'
        -> intersect (binds g) (binds g') = empty
        -> DenotesEnv g th
        -> HasFJtype (erase_env (csubst_env th g')) (csubst th e) (erase (ctsubst th t)).
Proof.
  induction g.
  -
  intros. inversion H3. simpl in *.  rewrite erase_concat in H. simpl in H.  rewrite empty_concatF in H. auto.
  -
  intros. inversion H0.  inversion H3. simpl.
  apply IHg;auto.
  + 
    rewrite erase_concat. rewrite erase_tsubFV. rewrite erase_concat in H. simpl in H. rewrite erase_esubFV.
    apply subst_fjtyp with (erase t);auto.
    ++ apply unique_erase_env; auto.
    ++ apply unique_erase_env; auto.
    ++
      rewrite <- binds_erase_env. rewrite <- binds_erase_env.  simpl in H2. apply intersect_names_add_elim_l in H2.
      destruct H2. auto.
    ++ 
      unfold in_envFJ. rewrite <- binds_erase_env. unfold in_env in H4. auto.
    ++ 
      unfold in_envFJ. rewrite <- binds_erase_env.  simpl in H2.
      apply intersect_names_add_elim_l in H2. destruct H2. auto.
    ++ apply value_lc. apply den_isvalue with (ctsubst th0 t). auto.
    ++ apply den_hasfjtype in H12. rewrite erase_ctsubst in H12. assert (concatF FEmpty (erase_env g) = (erase_env g)). apply empty_concatF. rewrite <- H13. apply weaken_many_fjtyp; simpl; auto. apply unique_erase_env;auto.
  +
    apply esubFV_unique. auto.
  + 
    rewrite esubFV_binds. simpl in H2. apply intersect_names_add_elim_l in H2. destruct H2. auto.
Qed.


                                    
Lemma csubst_hasfjtype : forall (g:env) (e:expr) (t:type) (th:csub),
    HasFJtype (erase_env g) e (erase t)
        -> unique g -> DenotesEnv g th
        -> HasFJtype FEmpty (csubst th e) (erase (ctsubst th t)).
Proof. intros; assert (FEmpty = erase_env (csubst_env th Empty))
      by (rewrite csubst_env_empty; reflexivity);
  rewrite H2; apply csubst_hasfjtype' with g; simpl;
  try apply intersect_empty_r; trivial. Qed.

Lemma ctsubst_wf' : forall (g g':env) (t:type) (th:csub),
    WFtype (concatE g g') t -> WFEnv g
        -> unique g -> unique g'
        -> intersect (binds g) (binds g') = empty
        -> DenotesEnv g th
        -> WFtype (csubst_env th g') (ctsubst th t).
Proof. induction g; intros.
  inversion H4. simpl. rewrite empty_concatE in H. auto.
  inversion H0. inversion H1. inversion H4. simpl in H3. apply intersect_names_add_elim_l in H3. destruct H3.  simpl. apply IHg; auto.
  apply subst_wf with t;auto. apply value_lc. apply den_isvalue with (ctsubst th0 t). auto.  
  apply den_hasfjtype in H19. rewrite erase_ctsubst in H19. assert (concatF FEmpty (erase_env g) = (erase_env g)). apply empty_concatF. rewrite <- H21. apply weaken_many_fjtyp; simpl; auto. apply unique_erase_env;auto. apply esubFV_unique. auto.
  rewrite esubFV_binds. auto.
  Qed.  
    
Lemma ctsubst_wf : forall (g:env) (t:type) (th:csub),
    WFtype g t -> WFEnv g -> unique g -> DenotesEnv g th
        -> WFtype Empty (ctsubst th t).
Proof. intros; assert (Empty = csubst_env th Empty)
      by (symmetry; apply csubst_env_empty);
  rewrite H3; apply ctsubst_wf' with g; simpl;
  try apply intersect_empty_r; trivial. Qed.

Lemma remove_var_denotes : forall (th:csub) (t:type) (v:expr) (x:vname),
    Denotes (ctsubst th t) v -> Elem x (bindsC th) 
        -> ~ Elem x (free t)
        -> closed th -> uniqueC th -> substitutable th
        -> Denotes (ctsubst (remove_fromCS th x) t) v.
Proof. intros; rewrite <- remove_ctsubst; trivial. Qed.

Lemma remove_var_denotessenv : forall (g g':env) (x:vname) (t_x:type) (th:csub),
    unique g -> unique g'
        -> intersect (binds g) (binds g') = empty
        -> ~ (in_env x g) -> ~ (in_env x g') 
        -> WFEnv (concatE g g')
        -> closed th -> uniqueC th -> substitutable th
        -> DenotesEnv (concatE (Cons x t_x g) g') th
        -> DenotesEnv (concatE g g') (remove_fromCS th x).
Proof. intro g; induction g'; simpl; intros.
  - (* CEmpty *) inversion H8; simpl;
    assert (x = x) by reflexivity;
    apply Nat.eqb_eq in H16; rewrite H16; apply H12.
  - (* CCons  *) 
    (*get th0 from DenotesEnv (concatE (Cons x t_x g) g') th*)
    inversion H4; inversion H8.
    unfold in_env in H3; simpl in *.
    apply not_elem_names_add_elim in H3; destruct H3;
    apply Nat.eqb_neq in H3; rewrite H3.
    
    (*prove th0^x, x:v denotes*)
    apply DExt.
    +
      destruct H0. apply intersect_names_add_elim_r in H1. destruct H1.
      apply IHg' with t_x;auto.
      apply denotesenv_closed with (concatE (Cons x0 t_x g) g');auto.
      apply denotesenv_uniqueC with (concatE (Cons x0 t_x g) g');auto.
      apply denotesenv_substitutable with (concatE (Cons x0 t_x g) g');auto.
    +
      unfold in_env. simpl. unfold not. intros. apply binds_concat in H23. assert (~Elem x (union (binds g) (binds g'))). 
      unfold in_env in H20. apply not_elem_concat_elim in H20. destruct H20. simpl in H20. apply not_elem_names_add_elim in H20. destruct H20. apply not_elem_union_intro;auto. auto.
    +
      apply remove_var_denotes;auto.  rewrite <- binds_env_th with (concatE (Cons x0 t_x g) g') th0;auto.
      pose proof (binds_concat (Cons x0 t_x g) g'); destruct H23.
      apply H24. apply  set_union_intro1. apply set_add_intro2. auto.
      apply free_subset_binds in H14. apply not_elem_subset with (binds (concatE g g')).
      apply subset_trans with (binds (concatE g g'));auto. apply binds_subset.
      apply not_elem_concat_intro;auto. 
      apply denotesenv_closed with (concatE (Cons x0 t_x g) g');auto.
      apply denotesenv_uniqueC with (concatE (Cons x0 t_x g) g');auto.
      apply denotesenv_substitutable with (concatE (Cons x0 t_x g) g');auto.
Qed.
(*this can be generalized to remove the premises*)
Lemma idempotent_csubst: forall th v_x,
  Subset (fv v_x) (bindsC th)
  -> closed th -> substitutable th
  -> (csubst th (csubst th v_x)) = (csubst th v_x).
Proof.
  intros. assert (fv (csubst th v_x) = empty). apply csubst_no_more_fv;auto.
  rewrite csubst_nofv;auto. 
Qed.
Lemma add_var_denotessenv2 : 
  forall (g g':env) (x x':vname) (v_x v_x':expr) (t_x t_x':type) (th:csub),
    unique g -> unique g'
        -> intersect (binds g) (binds g') = empty
        -> ~ (in_env x g) -> ~ (in_env x g') -> True
        -> ~ (in_env x' g) -> ~ (in_env x' g') -> True
        -> (Subset (fv v_x) (binds g)) 
        -> Denotes (ctsubst th t_x) (csubst th v_x)
        -> DenotesEnv (concatE g (esubFV x v_x (esubFV x' v_x' g'))) th
        -> WFtype g t_x -> WFtype g (tsubBV v_x t_x')
        -> (Subset (fv v_x') (binds g)) 
        -> Denotes (ctsubst th (tsubBV v_x t_x')) (csubst th  v_x') -> x' <> x
        -> exists th', DenotesEnv (concatE (Cons x' (openT_at 0 x t_x') (Cons x t_x g)) g') th' /\
                  (forall e, csubst th' e = csubst th (subFV x v_x (subFV x' v_x' e))) /\        
                  (forall t, ctsubst th' t = ctsubst th (tsubFV x v_x (tsubFV x' v_x' t))) /\ 
                  (forall ps, cpsubst th' ps = cpsubst th (psubFV x v_x (psubFV x' v_x' ps))).
Proof. intro g; induction g'; simpl; intros.
  - (* CEmpty *)
    assert (loc_closed th) as loc. apply denotesenv_loc_closed with g;auto. assert (substitutable th) as sus. apply denotesenv_substitutable with g;auto. assert (closed th) as clo. apply denotesenv_closed with g;auto. assert (uniqueC th) as uni. apply denotesenv_uniqueC with g;auto.
    exists (CCons x' (csubst th v_x') (CCons x (csubst th v_x) th)); repeat split. 
    apply DExt; intros; simpl;auto.
    apply DExt;intros; simpl;auto. unfold in_env. simpl. apply not_elem_names_add_intro;constructor;auto. 
    rewrite <- tsubFV_unbindT. rewrite ctsubst_tsubBV;auto. rewrite ctsubst_tsubBV in H14;auto. rewrite idempotent_csubst;auto. rewrite <-binds_env_th with g th;auto.
    apply not_elem_subset with (free ((tsubBV v_x t_x'))). apply fv_tsubBV_intro.
    apply not_elem_subset with (binds g);auto. apply free_subset_binds;auto.
    intros. simpl.
    assert (subFV x v_x (subFV x' v_x' e) = subFV x' v_x' (subFV x v_x e)). rewrite commute_subFV;auto. apply not_elem_subset with (binds g);auto. apply not_elem_subset with (binds g);auto. rewrite H16.
    assert (csubst th (subFV x' v_x' (subFV x v_x e)) = csubst th (subFV x' (csubst th v_x') (subFV x v_x e))). rewrite <- csubst_subFV_extract;auto. unfold in_csubst. rewrite <-binds_env_th with g th;auto. rewrite <-binds_env_th with g th;auto. rewrite H17.
    assert ((subFV x' (csubst th v_x') (subFV x v_x e)) = subFV x v_x (subFV x' (csubst th v_x') e)). rewrite <- commute_subFV;auto. apply not_elem_subset with (binds g);auto. rewrite csubst_no_more_fv;auto. rewrite <-binds_env_th with g th;auto. rewrite H18.
    assert (csubst th (subFV x v_x (subFV x' (csubst th v_x') e)) = csubst th (subFV x (csubst th v_x) (subFV x' (csubst th v_x') e))). rewrite <- csubst_subFV_extract;auto.  unfold in_csubst.  rewrite <-binds_env_th with g th;auto.  rewrite <-binds_env_th with g th;auto. rewrite H19.
    auto.
    intros. simpl.
    assert (tsubFV x v_x (tsubFV x' v_x' t) = tsubFV x' v_x' (tsubFV x v_x t)). rewrite commute_tsubFV;auto. apply not_elem_subset with (binds g);auto. apply not_elem_subset with (binds g);auto. rewrite H16.
    assert (ctsubst th (tsubFV x' v_x' (tsubFV x v_x t)) = ctsubst th (tsubFV x' (csubst th v_x') (tsubFV x v_x t))). rewrite <- ctsubst_tsubFV_extract;auto. unfold in_csubst. rewrite <-binds_env_th with g th;auto. rewrite <-binds_env_th with g th;auto. rewrite H17.
    assert ((tsubFV x' (csubst th v_x') (tsubFV x v_x t)) = tsubFV x v_x (tsubFV x' (csubst th v_x') t)). rewrite <- commute_tsubFV;auto. apply not_elem_subset with (binds g);auto. rewrite csubst_no_more_fv;auto. rewrite <-binds_env_th with g th;auto. rewrite H18.
    assert (ctsubst th (tsubFV x v_x (tsubFV x' (csubst th v_x') t)) = ctsubst th (tsubFV x (csubst th v_x) (tsubFV x' (csubst th v_x') t))). rewrite <- ctsubst_tsubFV_extract;auto.  unfold in_csubst.  rewrite <-binds_env_th with g th;auto.  rewrite <-binds_env_th with g th;auto. rewrite H19.
    auto.
    intros. simpl.
    assert (psubFV x v_x (psubFV x' v_x' ps) = psubFV x' v_x' (psubFV x v_x ps)). rewrite commute_psubFV;auto. apply not_elem_subset with (binds g);auto. apply not_elem_subset with (binds g);auto. rewrite H16.
    assert (cpsubst th (psubFV x' v_x' (psubFV x v_x ps)) = cpsubst th (psubFV x' (csubst th v_x') (psubFV x v_x ps))). rewrite <- cpsubst_psubFV_extract;auto. unfold in_csubst. rewrite <-binds_env_th with g th;auto. rewrite <-binds_env_th with g th;auto. rewrite H17.
    assert ((psubFV x' (csubst th v_x') (psubFV x v_x ps)) = psubFV x v_x (psubFV x' (csubst th v_x') ps)). rewrite <- commute_psubFV;auto. apply not_elem_subset with (binds g);auto. rewrite csubst_no_more_fv;auto. rewrite <-binds_env_th with g th;auto. rewrite H18.
    assert (cpsubst th (psubFV x v_x (psubFV x' (csubst th v_x') ps)) = cpsubst th (psubFV x (csubst th v_x) (psubFV x' (csubst th v_x') ps))). rewrite <- cpsubst_psubFV_extract;auto.  unfold in_csubst.  rewrite <-binds_env_th with g th;auto.  rewrite <-binds_env_th with g th;auto. rewrite H19.
    auto.
  -
    destruct H0;
    apply intersect_names_add_elim_r in H1; destruct H1;
    apply not_elem_names_add_elim in H3; destruct H3.
    inversion H4.
    unfold in_env in H6. simpl in H6. apply not_elem_names_add_elim in H6. destruct H6.
    inversion H10. apply IHg' with x0 x' v_x v_x' t_x t_x' th0 in H23 as IH;
    fold binds in H18; auto.

     (* exists th', DenotesEnv (Cons x t (concatE (Cons x0 t_x g) g')) th' *)
     destruct IH as [th' [d_env_th' [Hcs [Hcs' Hcs'']]]].
     exists (CCons x v th'); simpl; repeat split.
     apply DExt;auto.
     unfold in_env. simpl. apply not_elem_subset with (union (binds (Cons x' (openT_at 0 x0 t_x') (Cons x0 t_x g))) (binds g')). apply binds_concat.
     apply not_elem_union_intro;auto. simpl. apply not_elem_names_add_intro. constructor;auto. apply not_elem_names_add_intro;auto. 
     rewrite Hcs'. apply H26.
     intros. rewrite Hcs. 
     assert ((subFV x' v_x' (subFV x v e)) = (subFV x v (subFV x' v_x' e))). rewrite commute_subFV;auto.  apply den_nofv in H26. rewrite H26. auto.  rewrite H27.
     assert ((subFV x0 v_x (subFV x v (subFV x' v_x' e))) = subFV x v ((subFV x0 v_x (subFV x' v_x' e)))).  rewrite commute_subFV;auto. apply den_nofv in H26. rewrite H26. auto. rewrite H28.
     auto.
     intros. rewrite Hcs'.
     assert ((tsubFV x' v_x' (tsubFV x v t1)) = (tsubFV x v (tsubFV x' v_x' t1))). rewrite commute_tsubFV;auto. apply den_nofv in H26. rewrite H26. auto. rewrite H27.
     assert ((tsubFV x0 v_x (tsubFV x v (tsubFV x' v_x' t1))) = tsubFV x v ((tsubFV x0 v_x (tsubFV x' v_x' t1)))).  rewrite commute_tsubFV;auto. apply den_nofv in H26. rewrite H26. auto. rewrite H28.
     auto.
     intros. rewrite Hcs''.
     assert ((psubFV x' v_x' (psubFV x v ps)) = (psubFV x v (psubFV x' v_x' ps))). rewrite commute_psubFV;auto. apply den_nofv in H26. rewrite H26. auto.  rewrite H27.
     assert ((psubFV x0 v_x (psubFV x v (psubFV x' v_x' ps))) = psubFV x v ((psubFV x0 v_x (psubFV x' v_x' ps)))).  rewrite commute_psubFV;auto. apply den_nofv in H26. rewrite H26. auto. rewrite H28.
     auto.
     

     try apply DExt;
     try apply not_elem_concat_intro;
     try apply not_elem_names_add_intro; try split;
     try rewrite (Hcs' t); auto;
     intros; try rewrite commute_tsubFV; try apply Hcs';
     try rewrite commute_subFV; try apply Hcs;
     try rewrite commute_psubFV; try apply Hcs'';
     apply den_nofv in H26 as Hv; 
     try rewrite Hv; auto;
     try apply not_elem_subset with (binds g);
     try apply not_elem_subset with (binds g);
     try apply fv_subset_binds with t_x;
     try apply binds_subset; auto.
 

    subst th; simpl in H9;
    rewrite subFV_notin' in H9;
    rewrite tsubFV_notin in H9;
    (* apply typing_wf in H5 as Htx; *)
    try apply not_elem_subset with (binds g);
    try apply not_elem_subset with (binds g);
    (* try apply fv_subset_binds with t_x; *)
    try apply free_subset_binds;
    try apply binds_subset; auto.

    subst th; simpl in H14;
    rewrite subFV_notin' in H14;
    rewrite tsubFV_notin in H14;
    (* apply typing_wf in H5 as Htx; *)
    try apply not_elem_subset with (binds g);
    try apply not_elem_subset with (binds g);
    (* try apply fv_subset_binds with t_x; *)
    try apply free_subset_binds;
    try apply binds_subset; auto.
         

   

Qed.

Lemma add_var_denotessenv : 
  forall (g g':env) (x:vname) (v_x:expr) (t_x:type) (th:csub),
    unique g -> unique g'
        -> intersect (binds g) (binds g') = empty
        -> ~ (in_env x g) -> ~ (in_env x g') -> WFEnv g
        -> (Subset (fv v_x) (binds g)) 
        -> Denotes (ctsubst th t_x) (csubst th v_x)
        -> DenotesEnv (concatE g (esubFV x v_x g')) th
        -> WFtype g t_x
        -> exists th', DenotesEnv (concatE (Cons x t_x g) g') th' /\
                  (forall e, csubst th' e = csubst th (subFV x v_x e)) /\        
                  (forall t, ctsubst th' t = ctsubst th (tsubFV x v_x t)) /\ 
                  (forall ps, cpsubst th' ps = cpsubst th (psubFV x v_x ps)).
Proof. intro g; induction g'; simpl; intros;rename H8 into wft.
  - (* CEmpty *) exists (CCons x (csubst th v_x) th); repeat split;
    try apply DExt; intros; simpl;
    try apply csubst_subFV_extract;
    try apply ctsubst_tsubFV_extract;
    try apply cpsubst_psubFV_extract;
    unfold in_csubst; try rewrite <- binds_env_th with g th;
    (* try rewrite <- binds_env_th with g th;
    try rewrite <- binds_env_th with g th; *)
    try auto;
    try apply denotesenv_closed with g;
    try apply denotesenv_substitutable with g;
    try apply denotesenv_uniqueC with g; trivial.  
  - (* CCons  *) destruct H0.
   
    apply intersect_names_add_elim_r in H1; destruct H1;
    apply not_elem_names_add_elim in H3; destruct H3.
    inversion H7. apply IHg' with x0 v_x t_x th0 in H14 as IH;
    fold binds in H10; auto.
    (* exists th', DenotesEnv (Cons x t (concatE (Cons x0 t_x g) g')) th' *)
    destruct IH as [th' [d_env_th' [Hcs [Hcs' Hcs'']]]].
    exists (CCons x v th'); simpl; repeat split; 
    try apply DExt;
    try apply not_elem_concat_intro;
    try apply not_elem_names_add_intro; try split;
    try rewrite (Hcs' t); auto;
    intros; try rewrite commute_tsubFV; try apply Hcs';
    try rewrite commute_subFV; try apply Hcs;
    try rewrite commute_psubFV; try apply Hcs'';
    apply den_nofv in H17 as Hv; (*destruct Hv. *)
    try rewrite Hv; auto;
    try apply not_elem_subset with (binds g);
    try apply not_elem_subset with (binds g);
    try apply fv_subset_binds with t_x;
    try apply binds_subset; auto.
    (* Denotes (ctsubst th0 t_x) (csubst th0 v_x) *)
    subst th; simpl in H6;
    rewrite subFV_notin' in H6;
    rewrite tsubFV_notin in H6;
    (* apply typing_wf in H5 as Htx; *)
    try apply not_elem_subset with (binds g);
    try apply not_elem_subset with (binds g);
    (* try apply fv_subset_binds with t_x; *)
    try apply free_subset_binds;
    try apply binds_subset; auto.    
Qed.

Lemma extend_denotess : forall (g g':env) (th:csub) (t:type) (v:expr),
    DenotesEnv (concatE g g') th
        -> WFtype g t
        -> ( forall th1, DenotesEnv g th1 
                  -> Denotes (ctsubst th1 t) (csubst th1 v) )
        -> Denotes (ctsubst th t) (csubst th v).
Proof. intro g; induction g'; simpl; intros.
  - apply H1; apply H.
  - 
    inversion H; rewrite unroll_csubst_left;
    try rewrite unroll_ctsubst_left;
    try rewrite subFV_notin';
    try rewrite tsubFV_notin;
    assert (Denotes (ctsubst th0 t0) (csubst th0 v)) by auto;
    assert (free (ctsubst th0 t0) = empty) 
      by (apply ctsubst_no_more_fv;
          try rewrite <- binds_env_th with (concatE g g') th0;
          try apply free_subset_binds;
          try apply weaken_many_wf;
          try apply denotesenv_closed with (concatE g g');
          try apply denotesenv_substitutable with (concatE g g');
          apply denotesenv_unique in H5 as Hu; 
          apply concat_unique in Hu as [Hg [Hg' Hi]]; auto); 
    try apply den_nofv in H8 as Hv0;
    try apply den_nofv in H9 as Hv; 
    try rewrite Hv; try rewrite H10; try rewrite H11; unfold in_csubst;
    try rewrite <- binds_env_th with (concatE g g') th0;
    try apply denotesenv_closed with (concatE g g');
    try apply denotesenv_substitutable with (concatE g g'); auto. 
Qed.


Lemma widen_denotess : 
  forall (g g':env) (x:vname) (s_x t_x:type) (th:csub),
    unique g -> unique g'
        -> intersect (binds g) (binds g') = empty
        -> ~ (in_env x g) -> ~ (in_env x g') 
        -> (forall (v:expr) (th0:csub), isValue v -> DenotesEnv g th0
              -> Denotes (ctsubst th0 s_x) v -> Denotes (ctsubst th0 t_x) v)
        -> DenotesEnv (concatE (Cons x s_x g) g') th 
        -> DenotesEnv (concatE (Cons x t_x g) g') th.
Proof. intro g; induction g'; intros; simpl.
  - simpl in H5; inversion H5; apply DExt; try apply H4; 
    try apply den_isvalue with (ctsubst th0 s_x); trivial.
  - simpl in H5; inversion H5; subst x1 t0 g0.
    apply DExt;  try apply IHg' with s_x;
    simpl in H0; destruct H0; 
    simpl in H1; apply intersect_names_add_elim_r in H1;
    destruct H1;
    unfold in_env in H3; simpl in H3; 
    apply not_elem_names_add_elim in H3; destruct H3;
    try apply not_elem_concat_intro; simpl; 
    try apply not_elem_names_add_intro; auto.
  Qed.
