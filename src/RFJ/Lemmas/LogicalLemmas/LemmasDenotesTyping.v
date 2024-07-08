Require Import Lists.
Require Import Arith.
Require Import Lists.ListSet.
Require Import Crush.
Require Import Coq.Program.Equality.

Require Import Definitions.Syntax.
Require Import Definitions.Names.
Require Import Definitions.Semantics.
Require Import Definitions.FJTyping.

Require Import Definitions.Typing.
Require Import Definitions.CTSanity.

Require Import Definitions.SubDenotation.

Require Import Lemmas.BasicLemmas.LemmasFJTyping.
Require Import Lemmas.BasicLemmas.LemmasPrimitivesBasics.
Require Import Lemmas.BasicLemmas.LemmasSubstitution.
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasEnvironments.
Require Import Lemmas.BasicLemmas.LemmasWF.
Require Import Lemmas.BasicLemmas.LemmasWFNarrow.
Require Import Lemmas.BasicLemmas.LemmasCTBasics.
Require Import Lemmas.BasicLemmas.LemmasWF.
Require Import Lemmas.BasicLemmas.LemmasWFNarrow.
Require Import Lemmas.TypingLemmas.LemmasTyping.
Require Import Lemmas.BasicLemmas.LemmasWFWeaken.
Require Import Lemmas.BasicLemmas.LemmasWFSubstitution.
Require Import Lemmas.TypingLemmas.LemmasWeakenTyp.
Require Import Lemmas.LogicalLemmas.LemmasCSubst.
Require Import Lemmas.LogicalLemmas.LemmasSImp.
Require Import Lemmas.TypingLemmas.LemmasRefl.
Require Import Lemmas.LogicalLemmas.LemmasDenotes.
Require Import Lemmas.BasicLemmas.LemmasSemantics.
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasSemantics.





(*---------------Lemmas Connecting Denotation and Typing---------------*)


Lemma value_noeval: forall e v, EvalsTo v e -> isValue v -> e = v.
Proof.
  intros.
  induction H.
  reflexivity.
  apply value_stuck in H.
  contradiction.
Qed.

(*This is the crucial lemma of subtyping -> denotes*)
Lemma denotessubtype:(
  forall g (t1 t2:type) th,  Subtype g t1 t2 -> DenotesEnv g th -> 
    (forall (v:expr), isValue v -> Denotes (ctsubst th t1) v -> Denotes (ctsubst th t2) v) ).
Proof. 
  intros. 
  destruct H.
  (*get "p1 -*> True then p2 -*> True" from subtype*)
  remember (fresh (union (fvP p2) (union (fvP p1) (union (binds g) nms)))) as y. assert (~Elem y (union (fvP p2) (union (fvP p1) (union (binds g) nms)))). rewrite Heqy. apply fresh_not_elem. assert (~Elem y nms) as H7'. notin_solve_one. apply H3 in H7'. 
  inversion H7'. 
  assert (loc_closed th). apply denotesenv_loc_closed with g;auto.
  assert (substitutable th). apply denotesenv_substitutable with g;auto.
  destruct v; simpl in H4; try contradiction.
  -
    destruct b1;rewrite ctsubst_refn in H2. 
    + (*"b1" is "Any"*)
    inversion H.
    * (*"b2" is "Any"*)
      apply denotes_refn in H2.
      rewrite ctsubst_refn.
      apply DenotesUpcast with TBool;auto.  
      apply DenotesBool;auto.
      **
        (*merge psubBV into cpsubst*) 
        assert ((Bc b) = (csubst th (Bc b))). rewrite csubst_nofv;auto. rewrite H13.
        rewrite <- cpsubst_psubBV;auto. assert (~ Elem y (fvP p2)). notin_solve_one. rewrite psubFV_unbindP with y (Bc b) p2;auto. 
        assert ((psubFV y (Bc b) (unbindP y p2)) = cpsubst (CCons y (Bc b) CEmpty) (unbindP y p2)). reflexivity. rewrite H15. assert (cpsubst th (cpsubst (CCons y (Bc b) CEmpty) (unbindP y p2)) = cpsubst (CCons y (Bc b) th) (unbindP y p2)). reflexivity. rewrite H16.
        apply H5. (*use " p1 -*> True then p2 -*> True "*)
        ***
          apply DExt;simpl;auto. unfold in_env. notin_solve_one. rewrite ctsubst_refn. apply DenotesUpcast with TBool;auto.  
          apply DenotesBool;auto.  rewrite cpsubst_pempty. unfold psubBV. simpl. apply PEEmp. 
        ***
          assert ((Bc b) = (csubst th (Bc b))). rewrite csubst_nofv;auto. 
          rewrite H17 in H2. rewrite <- cpsubst_psubBV in H2;auto. rewrite psubFV_unbindP with y (Bc b) p1 in H2;auto.
          notin_solve_one.
    + (*"b1" is "Bool"*)
    inversion H.
    * (*"b2" is "Any"*)
      apply denotes_refn in H2. rewrite ctsubst_refn.  
      apply DenotesUpcast with TBool;auto.  
      apply DenotesBool;auto.
      **
        (*merge psubBV into cpsubst*) 
        assert ((Bc b) = (csubst th (Bc b))). rewrite csubst_nofv;auto. rewrite H13.
        rewrite <- cpsubst_psubBV;auto. assert (~ Elem y (fvP p2)). notin_solve_one. rewrite psubFV_unbindP with y (Bc b) p2;auto. 
        assert ((psubFV y (Bc b) (unbindP y p2)) = cpsubst (CCons y (Bc b) CEmpty) (unbindP y p2)). reflexivity. rewrite H15. assert (cpsubst th (cpsubst (CCons y (Bc b) CEmpty) (unbindP y p2)) = cpsubst (CCons y (Bc b) th) (unbindP y p2)). reflexivity. rewrite H16.
        apply H5. (*use " p1 -*> True then p2 -*> True "*)
        ***
          apply DExt;simpl;auto. unfold in_env. notin_solve_one. rewrite ctsubst_refn. apply DenotesUpcast with TBool;auto.  
          apply DenotesBool;auto.  rewrite cpsubst_pempty. unfold psubBV. simpl. apply PEEmp. 
        ***
          assert ((Bc b) = (csubst th (Bc b))). rewrite csubst_nofv;auto. 
          rewrite H17 in H2. rewrite <- cpsubst_psubBV in H2;auto. rewrite psubFV_unbindP with y (Bc b) p1 in H2;auto.
          notin_solve_one.
    * (*"b2" is "Bool"*) 
    apply denotes_refn in H2. rewrite ctsubst_refn.  
    apply DenotesUpcast with TBool;auto.  
    apply DenotesBool;auto.
    **
      (*merge psubBV into cpsubst*) 
      assert ((Bc b) = (csubst th (Bc b))). rewrite csubst_nofv;auto. rewrite H11.
      rewrite <- cpsubst_psubBV;auto. assert (~ Elem y (fvP p2)). notin_solve_one. rewrite psubFV_unbindP with y (Bc b) p2;auto. 
      assert ((psubFV y (Bc b) (unbindP y p2)) = cpsubst (CCons y (Bc b) CEmpty) (unbindP y p2)). reflexivity. rewrite H14. assert (cpsubst th (cpsubst (CCons y (Bc b) CEmpty) (unbindP y p2)) = cpsubst (CCons y (Bc b) th) (unbindP y p2)). reflexivity. rewrite H15.
      apply H5. (*use " p1 -*> True then p2 -*> True "*)
      ***
        apply DExt;simpl;auto. unfold in_env. notin_solve_one. rewrite ctsubst_refn. apply DenotesUpcast with TBool;auto.  
        apply DenotesBool;auto.  rewrite cpsubst_pempty. unfold psubBV. simpl. apply PEEmp. 
      ***
        assert ((Bc b) = (csubst th (Bc b))). rewrite csubst_nofv;auto. 
        rewrite H16 in H2. rewrite <- cpsubst_psubBV in H2;auto. rewrite psubFV_unbindP with y (Bc b) p1 in H2;auto.
        notin_solve_one.
    + (*"b1" is "Int", impossible for a bool value*)
      inversion H2. inversion H15. subst b1. apply den_hasfjtype in H13. apply int_values in H13;auto. simpl in H13. contradiction. 
    + (*"b1" is "Class", impossible for a bool value*)
      inversion H2. inversion H15. subst b1. apply den_hasfjtype in H13. apply lemma_nominal_values in H13;auto. simpl in H13. contradiction. 
  -
    destruct b1;rewrite ctsubst_refn in H2. 
    + (*"b1" is "Any"*)
    inversion H.
    * (*"b2" is "Any"*)
      apply denotes_refn in H2.
      rewrite ctsubst_refn.
      apply DenotesUpcast with TInt;auto.  
      apply DenotesInt;auto.
      **
        (*merge psubBV into cpsubst*) 
        assert ((Ic n) = (csubst th (Ic n))). rewrite csubst_nofv;auto. rewrite H13.
        rewrite <- cpsubst_psubBV;auto. assert (~ Elem y (fvP p2)). notin_solve_one. rewrite psubFV_unbindP with y (Ic n) p2;auto. 
        assert ((psubFV y (Ic n) (unbindP y p2)) = cpsubst (CCons y (Ic n) CEmpty) (unbindP y p2)). reflexivity. rewrite H15. assert (cpsubst th (cpsubst (CCons y (Ic n) CEmpty) (unbindP y p2)) = cpsubst (CCons y (Ic n) th) (unbindP y p2)). reflexivity. rewrite H16.
        apply H5. (*use " p1 -*> True then p2 -*> True "*)
        ***
          apply DExt;simpl;auto. unfold in_env. notin_solve_one. rewrite ctsubst_refn. apply DenotesUpcast with TInt;auto.  
          apply DenotesInt;auto.  rewrite cpsubst_pempty. unfold psubBV. simpl. apply PEEmp. 
        ***
          assert ((Ic n) = (csubst th (Ic n))). rewrite csubst_nofv;auto. 
          rewrite H17 in H2. rewrite <- cpsubst_psubBV in H2;auto. rewrite psubFV_unbindP with y (Ic n) p1 in H2;auto.
          notin_solve_one.
    + (*"b1" is "Bool", impossible for a int value*)
      inversion H2. inversion H15. subst b1. apply den_hasfjtype in H13.  apply bool_values in H13;auto. simpl in H13. contradiction. 
    + (*"b1" is "Int"*)
    inversion H.
    * (*"b2" is "Any"*)
      apply denotes_refn in H2. rewrite ctsubst_refn.  
      apply DenotesUpcast with TInt;auto.  
      apply DenotesInt;auto.
      **
        (*merge psubBV into cpsubst*) 
        assert ((Ic n) = (csubst th (Ic n))). rewrite csubst_nofv;auto. rewrite H13.
        rewrite <- cpsubst_psubBV;auto. assert (~ Elem y (fvP p2)). notin_solve_one. rewrite psubFV_unbindP with y (Ic n) p2;auto. 
        assert ((psubFV y (Ic n) (unbindP y p2)) = cpsubst (CCons y (Ic n) CEmpty) (unbindP y p2)). reflexivity. rewrite H15. assert (cpsubst th (cpsubst (CCons y (Ic n) CEmpty) (unbindP y p2)) = cpsubst (CCons y (Ic n) th) (unbindP y p2)). reflexivity. rewrite H16.
        apply H5. (*use " p1 -*> True then p2 -*> True "*)
        ***
          apply DExt;simpl;auto. unfold in_env. notin_solve_one. rewrite ctsubst_refn. apply DenotesUpcast with TInt;auto.  
          apply DenotesInt;auto.  rewrite cpsubst_pempty. unfold psubBV. simpl. apply PEEmp. 
        ***
          assert ((Ic n) = (csubst th (Ic n))). rewrite csubst_nofv;auto. 
          rewrite H17 in H2. rewrite <- cpsubst_psubBV in H2;auto. rewrite psubFV_unbindP with y (Ic n) p1 in H2;auto.
          notin_solve_one.
    * (*"b2" is "Bool"*) 
    apply denotes_refn in H2. rewrite ctsubst_refn.  
    apply DenotesUpcast with TInt;auto.  
    apply DenotesInt;auto.
    **
      (*merge psubBV into cpsubst*) 
      assert ((Ic n) = (csubst th (Ic n))). rewrite csubst_nofv;auto. rewrite H11.
      rewrite <- cpsubst_psubBV;auto. assert (~ Elem y (fvP p2)). notin_solve_one. rewrite psubFV_unbindP with y (Ic n) p2;auto. 
      assert ((psubFV y (Ic n) (unbindP y p2)) = cpsubst (CCons y (Ic n) CEmpty) (unbindP y p2)). reflexivity. rewrite H14. assert (cpsubst th (cpsubst (CCons y (Ic n) CEmpty) (unbindP y p2)) = cpsubst (CCons y (Ic n) th) (unbindP y p2)). reflexivity. rewrite H15.
      apply H5. (*use " p1 -*> True then p2 -*> True "*)
      ***
        apply DExt;simpl;auto. unfold in_env. notin_solve_one. rewrite ctsubst_refn. apply DenotesUpcast with TInt;auto.  
        apply DenotesInt;auto.  rewrite cpsubst_pempty. unfold psubBV. simpl. apply PEEmp. 
      ***
        assert ((Ic n) = (csubst th (Ic n))). rewrite csubst_nofv;auto. 
        rewrite H16 in H2. rewrite <- cpsubst_psubBV in H2;auto. rewrite psubFV_unbindP with y (Ic n) p1 in H2;auto.
        notin_solve_one.
    
    + (*"b1" is "Class", impossible for a bool value*)
      inversion H2. inversion H15. subst b1. apply den_hasfjtype in H13.  apply lemma_nominal_values in H13;auto. simpl in H13. contradiction. 
  -
    destruct b1;rewrite ctsubst_refn in H2. 
    + (*"b1" is "Any"*)
    inversion H.
    * (*"b2" is "Any"*)
      apply invert_new_denotes in H2 as inv. destruct inv. destruct H14 as [Fs]. destruct H14. 
      apply denotes_refn in H2.
      rewrite ctsubst_refn.
      apply DenotesUpcast with (TNom (TClass c));auto.   
      apply DenotesClass with Fs;auto.
      **
        (*merge psubBV into cpsubst*) 
        assert (((ExpNew c l)) = (csubst th ((ExpNew c l)))). rewrite csubst_nofv;auto. apply value_closed. auto. rewrite H16.
        rewrite <- cpsubst_psubBV;auto. assert (~ Elem y (fvP p2)). notin_solve_one. rewrite psubFV_unbindP with y ((ExpNew c l)) p2;auto. 
        assert ((psubFV y ((ExpNew c l)) (unbindP y p2)) = cpsubst (CCons y ((ExpNew c l)) CEmpty) (unbindP y p2)). reflexivity. rewrite H18. assert (cpsubst th (cpsubst (CCons y ((ExpNew c l)) CEmpty) (unbindP y p2)) = cpsubst (CCons y ((ExpNew c l)) th) (unbindP y p2)). reflexivity. rewrite H19.
        apply H5. (*use " p1 -*> True then p2 -*> True "*)
        ***
          apply DExt;simpl;auto. unfold in_env. notin_solve_one. rewrite ctsubst_refn. apply DenotesUpcast with (TNom (TClass c));auto.  
          apply DenotesClass with Fs;auto.  rewrite cpsubst_pempty. unfold psubBV. simpl. apply PEEmp. 
        ***
          assert (((ExpNew c l)) = (csubst th ((ExpNew c l)))). rewrite csubst_nofv;auto.  apply value_closed. auto. 
          rewrite H20 in H2. rewrite <- cpsubst_psubBV in H2;auto. rewrite psubFV_unbindP with y ((ExpNew c l)) p1 in H2;auto.
          notin_solve_one.
    + (*"b1" is "Bool", impossible for a int value*)
      inversion H2. inversion H15. subst b1. apply den_hasfjtype in H13.  apply bool_values in H13;auto. simpl in H13. contradiction.
      + (*"b1" is "Bool", impossible for a int value*)
      inversion H2. inversion H15. subst b1. apply den_hasfjtype in H13.  apply int_values in H13;auto. simpl in H13. contradiction.
    
    + (*"b1" is "Class c0"*)
    inversion H.
    * (*"b2" is "Any"*)
      apply invert_new_denotes in H2 as inv. destruct inv. destruct H14 as [Fs]. destruct H14.  
      apply denotes_refn in H2.
      rewrite ctsubst_refn.
      apply DenotesUpcast with (TNom (TClass c));auto.  
      apply DenotesClass with Fs;auto.
      **
        (*merge psubBV into cpsubst*) 
        assert (((ExpNew c l)) = (csubst th ((ExpNew c l)))). rewrite csubst_nofv;auto. apply value_closed. auto. rewrite H16.
        rewrite <- cpsubst_psubBV;auto. assert (~ Elem y (fvP p2)). notin_solve_one. rewrite psubFV_unbindP with y ((ExpNew c l)) p2;auto. 
        assert ((psubFV y ((ExpNew c l)) (unbindP y p2)) = cpsubst (CCons y ((ExpNew c l)) CEmpty) (unbindP y p2)). reflexivity. rewrite H18. assert (cpsubst th (cpsubst (CCons y ((ExpNew c l)) CEmpty) (unbindP y p2)) = cpsubst (CCons y ((ExpNew c l)) th) (unbindP y p2)). reflexivity. rewrite H19.
        apply H5. (*use " p1 -*> True then p2 -*> True "*)
        ***
          apply DExt;simpl;auto. unfold in_env. notin_solve_one. rewrite ctsubst_refn.  apply DenotesUpcast with (TNom (TClass c));auto.  
          apply DenotesClass with Fs;auto.  rewrite cpsubst_pempty. unfold psubBV. simpl. apply PEEmp. 
        ***
          assert (((ExpNew c l)) = (csubst th ((ExpNew c l)))). rewrite csubst_nofv;auto.  apply value_closed. auto. 
          rewrite H20 in H2. rewrite <- cpsubst_psubBV in H2;auto. rewrite psubFV_unbindP with y ((ExpNew c l)) p1 in H2;auto.
          notin_solve_one.
    * (*"b2" is "Class"*) 
    apply invert_new_denotes in H2 as inv. destruct inv. destruct H15 as [Fs]. destruct H15. 
    apply denotes_refn in H2.
    rewrite ctsubst_refn.
    apply DenotesUpcast with (TNom (TClass c));auto.  
    apply DenotesClass with Fs;auto.
    **
      (*merge psubBV into cpsubst*) 
      assert (((ExpNew c l)) = (csubst th ((ExpNew c l)))). rewrite csubst_nofv;auto. apply value_closed. auto. rewrite H17.
      rewrite <- cpsubst_psubBV;auto. assert (~ Elem y (fvP p2)). notin_solve_one. rewrite psubFV_unbindP with y ((ExpNew c l)) p2;auto. 
      assert ((psubFV y ((ExpNew c l)) (unbindP y p2)) = cpsubst (CCons y ((ExpNew c l)) CEmpty) (unbindP y p2)). reflexivity. rewrite H19. assert (cpsubst th (cpsubst (CCons y ((ExpNew c l)) CEmpty) (unbindP y p2)) = cpsubst (CCons y ((ExpNew c l)) th) (unbindP y p2)). reflexivity. rewrite H20.
      apply H5. (*use " p1 -*> True then p2 -*> True "*)
      ***
        apply DExt;simpl;auto. unfold in_env. notin_solve_one. rewrite ctsubst_refn. apply DenotesUpcast with (TNom (TClass c));auto.  
        apply DenotesClass with Fs;auto.  rewrite cpsubst_pempty. unfold psubBV. simpl. apply PEEmp. 
      ***
        assert (((ExpNew c l)) = (csubst th ((ExpNew c l)))). rewrite csubst_nofv;auto. apply value_closed. auto. 
        rewrite H21 in H2. rewrite <- cpsubst_psubBV in H2;auto. rewrite psubFV_unbindP with y ((ExpNew c l)) p1 in H2;auto.
        notin_solve_one.
    **
      apply SubBClass. apply SubCTrans with n;auto. inversion H14. auto. 
Qed.


Lemma denotessubtype_forall:(
  forall g (t1s t2s:[type]) th,  Forall2 (Subtype g) t1s t2s -> DenotesEnv g th -> 
    (forall (vs:[expr]), Forall isValue vs -> Forall2 Denotes (map (ctsubst th) t1s) vs -> Forall2 Denotes (map (ctsubst th) t2s) vs) ).
Proof.
  intros. generalize dependent t1s. generalize dependent t2s. induction vs;intros.
  -
  destruct t2s. apply Forall2_nil. destruct t1s. inversion H. inversion H2.
  -
  destruct t2s. destruct t1s. inversion H2. inversion H. destruct t1s. inversion H. inversion H. inversion H2. inversion H. inversion H1. inversion H5.  apply Forall2_cons. 
  +
    apply denotessubtype with g t0;auto.
  +
    apply IHvs with t1s;auto.
Qed.


Lemma aux1: forall th b, ctsubst th (tybc b) = tybc b.
Proof. induction th. intros. unfold tybc. simpl. auto.
intros. simpl. rewrite <- IHth. unfold tybc. auto.
Qed.
Lemma aux2: forall th b, ctsubst th (tyic b) = tyic b.
Proof. induction th. intros. unfold tyic. simpl. auto.
intros. simpl. rewrite <- IHth. unfold tyic. auto.
Qed.

Lemma aux3: forall th C, ctsubst th (TRefn (TNom (TClass C)) PEmpty) = TRefn (TNom (TClass C)) PEmpty.
Proof. induction th. intros. simpl. auto.
intros. simpl. rewrite IHth. auto.
Qed.

Lemma forall_hasfjtype'' : forall (g:env) (es:[expr]) (Ts:[type]) th,
  WFEnv g -> 
  Forall isValue es ->  WFEnv g -> DenotesEnv g th -> 
  Forall2
       (fun (v : expr) (t : type) =>
        isValue v ->
        WFEnv g -> DenotesEnv g th -> HasFJtype FEmpty (csubst th v) (erase t)) es Ts -> 
  Forall2 (HasFJtype (FEmpty)) (map (csubst th) es) (map erase Ts).
Proof.
  intro. intros. generalize dependent Ts. induction es.
  intros.
  destruct Ts. apply Forall2_nil. inversion H3.
  destruct Ts. intros. inversion H3.
  intros. inversion H3. inversion H0. apply Forall2_cons;auto.
Qed. 

Lemma valueF_hasfjtype: forall (g:env) (v:expr) (t:type) th,
  Hastype g v t -> isValue v -> WFEnv g -> DenotesEnv g th -> HasFJtype FEmpty (csubst th v) (erase t).
Proof.
  intros.
  induction H using Hastype_ind'; try contradiction.
  - rewrite csubst_bc. apply FTBC.
  - rewrite csubst_ic. apply FTIC.
  - rewrite erase_self. rewrite csubst_new. eapply FTNew;eauto.
    rewrite <- H. 
    assert (Forall2 (HasFJtype (FEmpty)) (map (csubst th) es) (map erase Ts)). eapply forall_hasfjtype'';eauto. simpl in H0. apply Forall_fun;auto. 
    apply forall_fsubtyping with (map erase Ts) ;auto.
    +
      rewrite forall_erase with Us (ExpNew C es). 
      apply forall_subtype_fsubtype with g;auto. 
  -
    apply FTSub with (erase s);auto.
    apply subtype_fsubtype with g;auto.
Qed.

Lemma valueF_hasfjtype_forall: forall (g:env) (vs:[expr]) (ts:[type]) th,
  Forall2 (Hastype g) vs ts -> Forall isValue vs -> WFEnv g -> DenotesEnv g th -> Forall2 (HasFJtype FEmpty) (map (csubst th) vs) (map (erase) ts).
Proof.
  intros.
  generalize dependent ts.
  induction vs.
  -
    intros. destruct ts. simpl. apply Forall2_nil. inversion H.
  -
    intros. destruct ts. inversion H.
    inversion H0. inversion H. apply Forall2_cons. apply valueF_hasfjtype with g;auto.
    apply IHvs;auto.
Qed.

Lemma typing_denotes': forall (g:env) (v:expr) (t:type) th,
  Hastype g v t -> isValue v -> DenotesEnv g th -> Denotes (ctsubst th t) (csubst th v). 
Proof.
    intros.
    assert (Subset (fv v) (binds g)) as subset. apply fv_subset_binds with t;auto.
    assert (uniqueC th). apply denotesenv_uniqueC with g;auto.
    assert (substitutable th). apply denotesenv_substitutable with g;auto.
    assert (loc_closed th). apply denotesenv_loc_closed with g;auto.
    assert (closed th). apply denotesenv_closed with g;auto. 
    induction H using Hastype_ind'; try contradiction.
    -
      rewrite csubst_bc. rewrite aux1. apply den_tybc.
    -
      rewrite csubst_ic. rewrite aux2. apply den_tyic.
    -
      apply denotes_ctsubst_self;auto. apply value_lc;auto.  
      apply denotesselfify;auto.
      + 
        apply csubst_value;auto.
      + 
        rewrite ctsubst_refn. rewrite csubst_new. 
        apply DenotesClass with Fs;auto.
        *
          rewrite <- csubst_new.
          apply value_after_csubst;auto.  
          rewrite <- binds_env_th with g th;auto.
        * 
          rewrite cpsubst_pempty. apply PEEmp.
        *   
          rewrite <- H.
          assert ((map (tsubBV (ExpNew C (map (csubst th) es))) Us) = (map (ctsubst th) (map (tsubBV (ExpNew C es)) Us) )). rewrite ctsubst_tsubBV_forall;auto. rewrite csubst_new;auto. erewrite csubst_fjtype;eauto. rewrite H12.
          apply denotessubtype_forall with g Ts;auto.
          **
            apply value_after_csubst_forall;auto. simpl in H0. apply Forall_fun;auto.  simpl in subset. rewrite <-binds_env_th with g th;auto.
          **
            clear H12. clear H11.
            generalize dependent Ts. induction es.
            ***
              intros. destruct Ts. simpl. apply Forall2_nil. inversion H10.
            ***
              intros. destruct Ts. inversion H10.
              inversion H10. inversion H11. inversion H7. inversion H9. simpl in subset. apply subset_union_elim in subset. destruct subset.  apply Forall2_cons. apply H14;auto. simpl in H0. destruct H0. auto. apply IHes;auto. simpl. apply Forall_fun;auto. simpl in H0. destruct H0. apply Forall_fun;auto. 
    -
      intros.
      (* assert (ctsubst CEmpty t = t). simpl; reflexivity. rewrite <- H2. *)
      apply denotessubtype with g s;auto.
      apply value_after_csubst;auto.  rewrite <- binds_env_th with g th;auto. 
Qed.


Lemma typing_denotes: forall (g:env) (v:expr) (t:type) th,
  Hastype g v t -> isValue v -> DenotesEnv g th -> Denotes (ctsubst th t) v. 
Proof.
  intros.
  assert (csubst th v = v). apply csubst_nofv. apply value_closed;auto. rewrite <- H2.
  eapply typing_denotes';eauto.
Qed.

(*Denotation Typing*)





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

Lemma semantic_equalize_value_int: forall v v', isValue v -> isValue v' -> 
PEvalsTrue (PCons (ExpBinOp Eq v' v) PEmpty) -> v = v'.
Proof.
  intros. inversion H1. apply semantic_equalize_value_int';auto.
Qed.
  

Lemma denotesequalize_value_int: forall y th t v',
DenotesEnv (Cons y t Empty) th -> PEvalsTrue (cpsubst th (unbindP y (PCons (ExpBinOp Eq v' (BV 0)) PEmpty))) ->  isValue v' -> 
th = CCons y v' CEmpty.
Proof.
  intros.  rename H1 into isval. inversion H. inversion H4. f_equal.
  rewrite <- H5 in H0. simpl in H0. 
  case_eq(PeanoNat.Nat.eqb y y).
  - intros. rewrite H8 in H0. rewrite <- H9 in H0. simpl in H0. apply semantic_equalize_value_int;auto. eapply den_isvalue;eauto. assert ((open_at 0 y v') = v'). apply open_at_lc_at. apply value_lc;auto. rewrite H10 in H0. assert ((fv v') = empty). apply value_closed;auto. rewrite subFV_notin' in H0;auto. rewrite H11;simpl;auto.  
  - intros. apply PeanoNat.Nat.eqb_neq in H8. contradiction.
Qed.


Lemma aux: forall l Ts,
Forall (fun v_x : expr => isValue v_x -> forall t : type, Denotes t v_x -> WFtype Empty t -> Empty |--- v_x : t) l -> 
Forall isValue l -> Forall2 Denotes Ts l -> Forall (WFtype Empty) Ts-> Forall2 (Hastype Empty) l Ts.
Proof.
  intros.
  generalize dependent Ts. induction l.
  **
    intros. destruct Ts. simpl. apply Forall2_nil. inversion H1.
  **
    intros. destruct Ts. inversion H1. 
    inversion H1. simpl in H0. inversion H0. inversion H. inversion H2.
    apply Forall2_cons. apply H15;auto. 
    apply IHl;auto.
Qed.
Lemma denotestyping: forall t v_x, 
  Denotes t v_x -> WFtype Empty t -> Hastype Empty v_x t.
Proof.
  intros. rename H0 into wft. assert (isValue v_x). apply den_isvalue with t;auto.
  generalize dependent t.
  induction v_x using expr_ind'; simpl in H0; try contradiction.
  -
    intros.
    dependent induction H. 
    + (*"t" is "Bool"*)
      apply TSub with (tybc b). apply TBC. auto.  
      unfold tybc. simpl. apply SBase with (fvP ps). apply SubBBool. intros. apply SImp. intros. 
      assert (th = CCons y (Bc b) CEmpty). apply denotesequalize_value_int with (TRefn TBool PEmpty);auto. subst th. simpl. rewrite <- psubFV_unbindP. auto.  notin_solve_one.
    + (*"t" is "Any"*)
      apply TSub with (TRefn b1 ps);auto. 
      apply IHDenotes;auto.
      eapply wf_narrow_fsubtype;eauto.
      apply SBase with (fvP ps);auto. intros. apply IRefl.
  -
    intros.
    dependent induction H. 
    + (*"t" is "Int"*)
      apply TSub with (tyic n). apply TIC. auto. 
      unfold tyic. simpl. apply SBase with (fvP ps). apply SubBInt. intros. apply SImp. intros. 
      assert (th = CCons y (Ic n) CEmpty). apply denotesequalize_value_int with (TRefn TInt PEmpty);auto. subst th. simpl. rewrite <- psubFV_unbindP. auto.  notin_solve_one.
    + (*"t" is "Any"*)
      apply TSub with (TRefn b1 ps);auto. 
      apply IHDenotes;auto.
      eapply wf_narrow_fsubtype;eauto.
      apply SBase with (fvP ps);auto. intros. apply IRefl.
  -
    intros.
    dependent induction H1. 
    + (*"t" is "Class"*)
      apply TSub with ((self (TRefn (TNom (TClass c)) PEmpty) (ExpNew c l))).
      *  
        eapply Definitions.Typing.TNew;eauto.
        **
          apply value_lc_forall;auto. simpl in H4. apply Forall_fun. auto. 
        ** 
          assert(Forall2 (Hastype Empty) l (map (tsubBV (ExpNew c l)) (map ReffieldType Fs))).
          ***
            simpl in H4. apply aux;auto. apply Forall_fun. auto.
            apply fieldtype_wf_tsub_forall;auto.
            ****
              assert (Denotes (TRefn (TNom (TClass c)) ps) (ExpNew c l) ). eapply DenotesClass;eauto.
              assert (TNom (TClass c) = erase ((TRefn (TNom (TClass c)) ps))). auto. rewrite H6.
              apply den_hasfjtype;auto.
            **** 
              apply value_lc. auto. 
          ***
            apply H5.
        ** 
          apply sub_refl_forall.
          apply fieldtype_wf_tsub_forall;auto.
          ***
              assert (Denotes (TRefn (TNom (TClass c)) ps) (ExpNew c l) ). eapply DenotesClass;eauto.
              assert (TNom (TClass c) = erase ((TRefn (TNom (TClass c)) ps))). auto. rewrite H6.
              apply den_hasfjtype;auto.
          ***
            apply value_lc. auto. 
      *
        auto.
      * 
        unfold self. unfold eqlPred. simpl. apply SBase with (fvP ps). apply SubBClass. auto. intros. apply SImp. intros. 
        assert (th = CCons y (ExpNew c l) CEmpty). apply denotesequalize_value_int with (TRefn (TNom (TClass c)) PEmpty);auto.  subst th. simpl. rewrite <- psubFV_unbindP. auto.  notin_solve_one.
    + (*"t" is "Any"*)

     apply TSub with (TRefn b1 ps);auto. 
    apply IHDenotes;auto.
    eapply wf_narrow_fsubtype;eauto.

    apply SBase with (fvP ps);auto. intros. apply IRefl.
Qed.