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
Require Import Lemmas.BasicLemmas.LemmasExactness.
Require Import Lemmas.BasicLemmas.LemmasBigStepSemantics.
Require Import Lemmas.BasicLemmas.LemmasPrimitivesBasics.
Require Import Lemmas.TypingLemmas.LemmasTyping.
Require Import Lemmas.BasicLemmas.LemmasTypeSubstitution.
Require Import Lemmas.TypingLemmas.LemmasNarrowing.
Require Import Lemmas.TypingLemmas.LemmasInversion.
Require Import Lemmas.TypingLemmas.LemmasTransitive.
Require Import Lemmas.TypingLemmas.LemmasSubstitutionTyping.
Require Import Lemmas.BasicLemmas.LemmasWFSubstitution.
Require Import Lemmas.BasicLemmas.LemmasCTBasics.
Require Import Lemmas.BasicLemmas.LemmasCTTyping.
Require Import Lemmas.TypingLemmas.LemmasRefl.
Require Import Lemmas.TypingLemmas.LemmasWeakenTyp.
Require Import Lemmas.BasicLemmas.LemmasFJWeaken.
Require Import Lemmas.BasicLemmas.LemmasWFWeaken.
Require Import Lemmas.LogicalLemmas.LemmasDenotesTyping.
Require Import Lemmas.LogicalLemmas.LemmasCSubst.
Require Import Lemmas.LogicalLemmas.LemmasDenotes.
Require Import Lemmas.BasicLemmas.LemmasSemantics.
Require Import Lemmas.LogicalLemmas.LemmasSImp.

(*---------------Progress and Preservation---------------*)

Lemma foldref: forall fi0, 
match fi0 with | RefFDecl _ fn => fn end = ref fi0.
simpl;reflexivity. Qed.


Lemma fjtype_type_emp_bool: forall e, Empty |--- e : TRefn TBool PEmpty -> HasFJtype FEmpty e (TBool).
Proof.
  intros.
  assert (FEmpty = erase_env Empty) by (simpl; reflexivity). rewrite H0. assert (erase (TRefn TBool PEmpty) = (TBool)) by reflexivity. rewrite <- H1.  apply typing_hasfjtype;auto.
Qed.



Theorem progress' : forall (g:env) (e:expr) (t:type),
    Hastype g e t -> g = Empty -> isValue e \/ exists e'', Step e e''.
Proof. intros g e t p_e_t. induction p_e_t using Hastype_ind'; intro emp; simpl; subst g;
    (* values *) auto.
  - 
    right. 
    assert (isValue e \/ (exists e'', e ~~> e'')). apply IHp_e_t;auto. 
    destruct H1.
    +
      destruct op. simpl in H.
      assert (HasFJtype FEmpty e (TBool)). assert (FEmpty = erase_env Empty) by (simpl; reflexivity). rewrite H2.
      assert (FJSubtype (erase t) (erase  (intype Not))). apply subtype_fsubtype with Empty;auto.
      apply FTSub with (erase t);auto.
      apply typing_hasfjtype;auto.
      assert (isBool e). apply bool_values;auto.
      destruct e; try contradiction.
      assert (isCompat Not (Bc b)). apply isCpt_Not.
      exists (udelta Not (Bc b) H4). apply EUnOp2;auto. 
    +
      destruct H1 as [e''].
      exists (ExpUnOp op e''). apply EUnOp1;auto. 
  -
    right.
    assert (isValue e1 \/ (exists e'', e1 ~~> e'')). apply IHp_e_t1;auto.
    destruct H3.
    +
      assert (isValue e2 \/ (exists e'', e2 ~~> e'')). apply IHp_e_t2;auto.
      destruct H4.
      ++
        destruct op.
        +++   
          assert (HasFJtype FEmpty e1 (TBool)). assert (FEmpty = erase_env Empty) by (simpl; reflexivity). rewrite H5. 
          assert (FJSubtype (erase t) (erase (fst (intype2 And)))). apply subtype_fsubtype with Empty;auto. simpl in H6. inversion H6.
          rewrite H8.
          apply typing_hasfjtype;auto.
          assert (isBool e1). apply bool_values;auto.
          destruct e1; try contradiction. 

          assert (HasFJtype FEmpty e2 (TBool)). assert (FEmpty = erase_env Empty) by (simpl; reflexivity). rewrite H7.
          assert (FJSubtype (erase t') (erase (tsubBV (Bc b) (snd (intype2 And))))). apply subtype_fsubtype with Empty;auto.
          rewrite erase_tsubBV in H8.
          apply FTSub with (erase t');auto. 
          apply typing_hasfjtype;auto.
          assert (isBool e2). apply bool_values;auto.
          destruct e2; try contradiction. 

          exists (bdelta And (Bc b) (Bc b0) (isCpt_And b b0)).
          apply EBinOp3;auto.
        +++
          assert (HasFJtype FEmpty e1 (TBool)). assert (FEmpty = erase_env Empty) by (simpl; reflexivity). rewrite H5. 
          assert (FJSubtype (erase t) (erase (fst (intype2 Or)))). apply subtype_fsubtype with Empty;auto. simpl in H6. inversion H6.
          rewrite H8.
          apply typing_hasfjtype;auto.
          assert (isBool e1). apply bool_values;auto.
          destruct e1; try contradiction. 

          assert (HasFJtype FEmpty e2 (TBool)). assert (FEmpty = erase_env Empty) by (simpl; reflexivity). rewrite H7.
          assert (FJSubtype (erase t') (erase (tsubBV (Bc b) (snd (intype2 And))))). apply subtype_fsubtype with Empty;auto.
          rewrite erase_tsubBV in H8.
          apply FTSub with (erase t');auto. 
          apply typing_hasfjtype;auto.
          assert (isBool e2). apply bool_values;auto.
          destruct e2; try contradiction. 

          exists (bdelta Or (Bc b) (Bc b0) (isCpt_Or b b0)).
          apply EBinOp3;auto.
        +++
          exists (bdelta Eq e1 e2 (isCpt_Eq e1 e2 H3 H4)).
          apply EBinOp3;auto.
      ++
        destruct H4 as [e''].
        exists (ExpBinOp op e1 e''). apply EBinOp2;auto.
    +
      destruct H3 as [e''].
      exists (ExpBinOp op e'' e2).
      apply EBinOp1;auto.
  -
    right.
    assert (isValue e1 \/ (exists e'', e1 ~~> e'')). apply IHp_e_t1;auto.
    destruct H4.
    +
      assert (isValue e2 \/ (exists e'', e2 ~~> e'')). apply IHp_e_t2;auto.
      destruct H5.
      ++ 
        assert (HasFJtype FEmpty e1 ((TNom (TClass C)))). assert (FEmpty = erase_env Empty) by (simpl; reflexivity). rewrite H6. assert (erase (TRefn (TNom (TClass C)) ps') = (TNom (TClass C))) by reflexivity. rewrite <- H7.  apply typing_hasfjtype;auto.
        assert (isClass C e1). apply lemma_class_values;auto.
        destruct e1; try contradiction. simpl in H7. destruct H7. (*subst c.*)
        assert (exists mb, mbody( m, c)= mb). apply mtype_mbody with C t rt ps; auto. destruct H9 as[mb]. 
        exists (subBV_at 1 (ExpNew c l) (subBV e2 mb)). apply Refc_Invok3;auto. 
      ++
        destruct H5 as [e''].
        exists (ExpMethodInvoc e1 m e''). apply Refc_Invok2;auto.
    +
      destruct H4 as [e''].
      exists (ExpMethodInvoc e'' m e2).
      apply Refc_Invok1;auto.
  -
    right.
    assert (isValue e1 \/ (exists e'', e1 ~~> e'')). apply IHp_e_t1;auto.
    destruct H4.
    +
      assert (isValue e2 \/ (exists e'', e2 ~~> e'')). apply IHp_e_t2;auto.
      destruct H5.
      ++ 
        assert (HasFJtype FEmpty e1 ((TNom (TInterface C)))). assert (FEmpty = erase_env Empty) by (simpl; reflexivity). rewrite H6. assert (erase (TRefn (TNom (TInterface C)) ps') = (TNom (TInterface C))) by reflexivity. rewrite <- H7.  apply typing_hasfjtype;auto.
        assert (isInterface C e1). apply lemma_interface_values;auto.
        destruct e1; try contradiction. simpl in H7. destruct H7. (*subst c.*)
        assert (exists mb, mbody( m, c)= mb). apply mtypei_mbody with C t rt ps; auto. destruct H9 as[mb]. 
        exists (subBV_at 1 (ExpNew c l) (subBV e2 mb)). apply Refc_Invok3;auto. 
      ++
        destruct H5 as [e''].
        exists (ExpMethodInvoc e1 m e''). apply Refc_Invok2;auto.
    +
      destruct H4 as [e''].
      exists (ExpMethodInvoc e'' m e2).
      apply Refc_Invok1;auto.
  -
    right.
    subst f5.
    assert (isValue e \/ (exists e'', e ~~> e'')). apply IHp_e_t;auto.
    destruct H2.
    + 
      assert (HasFJtype FEmpty e ((TNom (TClass C)))). assert (erase_env Empty = FEmpty). simpl. reflexivity. 
      rewrite <-H3. assert (erase (TRefn (TNom (TClass C)) ps
      )=((TNom (TClass C)))). simpl. reflexivity. rewrite <- H4. apply typing_hasfjtype;auto.
      apply lemma_class_values with e C in H3;auto.
      
      destruct e; try contradiction.
      simpl in H3. destruct H3.
      eapply invert_new in p_e_t;eauto.
      destruct p_e_t as [Fs1 [Ts']].
      destruct H5. destruct H6. 
      assert (nth_error Fs1 i = Some fi). eapply subtype_field_nth_same;eauto.

      remember ((map ReffieldType Fs1)) as Us'.
      assert (nth_error (Us') i = Some (ReffieldType fi)). rewrite HeqUs'. apply f_morp. auto.
      
      assert (nth_error (map (tsubBV (ExpNew c l)) Us') i = Some ((tsubBV (ExpNew c l)) (ReffieldType fi))). apply f_morp. auto.
      assert (exists Ti, nth_error Ts' i = Some Ti). eapply forall2_exists1;eauto.  destruct H11 as [Ti].
      assert (exists ei, nth_error l i = Some ei). eapply forall2_exists1;eauto. destruct H12 as [ei]. 
      assert (Empty = Empty) by reflexivity.
      apply IHp_e_t in H13. destruct H13. exists ei.
      apply Refc_Field with Fs1 i;auto. destruct H13 as [e'']. exists (ExpFieldAccess (e'') (ref fi) ). apply RefRC_Field;auto.
    +
      destruct H2 as [e''].
      exists (ExpFieldAccess e'' (ref fi)).
      apply RefRC_Field;auto.
  -
      assert (Forall isValue es \/ (exists i ei, nth_error es i= Some ei /\ exists e'', ei ~~> e'')).
      clear H1. clear H2. clear H3. clear H5. clear H. clear H0.
      generalize dependent Ts. induction es;intros.
      left;auto.
      destruct Ts. inversion H4.
      inversion H4.
      assert (isValue a \/ (exists e'', a ~~> e'')). apply H2;auto. destruct H6.
      assert (Forall isValue es \/ (exists (i : nat) (ei : expr), nth_error es i = Some ei /\ (exists e'', ei ~~> e''))). apply IHes with Ts;auto. destruct H7.
      left. apply Forall_cons;auto.
      right. destruct H7 as [i[ei]]. destruct H7. exists (S i). exists ei. constructor. simpl. auto. auto.
      destruct H6 as [e'']. right. exists 0. exists a. constructor;auto. exists e''. auto.
      destruct H6.
      + 
        left. apply Forall_fun;auto.
      + 
        right.
        destruct H6 as [i[ei]]. destruct H6. destruct H7 as [ei'].

        exists (ExpNew C (replace es i ei')). apply RefRC_New_Arg with ei' ei i;auto.
        apply replace_just_replace;auto. apply nth_error_Some;auto. rewrite H6. unfold not. intros. inversion H8. 
        apply replace_just_replace. apply nth_error_Some;auto. rewrite H6. unfold not. intros. inversion H8.
        apply replace_length_eq. 
  -
    right. assert (Empty = Empty) by reflexivity. apply IHp_e_t in H2. destruct H2. exists (subBV e_x e). apply ELetV;auto.
    destruct H2 as [e'']. exists (ExpLet e'' e). apply ELet;auto.
Qed.

Theorem progress : forall (e:expr) (t:type),
    Hastype Empty e t -> isValue e \/ exists e'', Step e e''.
Proof. intros; apply progress' with Empty t; apply H || reflexivity. Qed.

Theorem preservation' : forall (g:env) (e:expr) (t:type) (e':expr),
    Hastype g e t -> g = Empty -> Step e e' -> Hastype Empty e' t.
Proof. intros g e t e' p_e_t; revert e'. induction p_e_t using Hastype_ind'.
  -
  intros e'' emp st_e_e''; simpl; subst g;
  apply value_stuck in st_e_e'' as H'; simpl in H'; try contradiction.
  -
  intros e'' emp st_e_e''; simpl; subst g;
  apply value_stuck in st_e_e'' as H'; simpl in H'; try contradiction.
  -
  intros e'' emp st_e_e''; simpl; subst g;
  apply value_stuck in st_e_e'' as H'; simpl in H'; try contradiction.
  -
  intros e'' emp st_e_e''; simpl; subst g;
  apply value_stuck in st_e_e'' as H'; simpl in H'; try contradiction.
  inversion st_e_e''.
  +
    assert (Empty |--- ExpUnOp op e' : tsubBV e' (ty' op)).
    eapply TUnOP;eauto. apply sem_lc with e;auto.
    apply TSub with (tsubBV e' (ty' op));auto.
    apply wf_ty'g;auto. apply typing_hasfjtype;auto.
    apply TSub with t;auto. apply wf_intype;auto.
    apply tsubBV_idempotent_step_upper';auto.
    apply sem_lc with e;auto.
  +
    destruct op. destruct pf. subst w. subst e''. 
    simpl. unfold tsubBV. simpl. case_eq (b); intros. 
    apply TSub with (tybc false). apply TBC. assert (TRefn TBool (PCons (ExpBinOp Eq (ExpUnOp Not (Bc true)) (BV 0)) PEmpty) = (tsubBV (Bc true) (ty' Not))) by reflexivity. rewrite H3. apply wf_ty'g;auto. unfold tybc. apply SBase with empty;auto. intros. apply IEvals2. 
    case_eq (PeanoNat.Nat.eqb (0 + 1) 1). 
    intros. case_eq (PeanoNat.Nat.eqb (0 + 1) 0). intros. apply PeanoNat.Nat.eqb_eq in H5. simpl in H5. discriminate. intro. case_eq (PeanoNat.Nat.eqb 0 0). intros.
    apply step_evals. apply EBinOp1. assert (Bc false = (udelta Not (Bc true) (isCpt_Not true))) by reflexivity. rewrite H8. apply EUnOp2;auto. (*apply step_evals. assert ((subBV (Bc false) (ExpBinOp Eq (BV 0) (FV y))) = ExpBinOp Eq (Bc false) (FV y)). unfold subBV. reflexivity. rewrite <- H7. apply ELetV;auto.*)
    intro. apply PeanoNat.Nat.eqb_neq in H7. contradiction. intro. apply PeanoNat.Nat.eqb_neq in H5. simpl in H5. contradiction.
    apply TSub with (tybc true). apply TBC. assert (TRefn TBool (PCons (ExpBinOp Eq (ExpUnOp Not (Bc false)) (BV 0)) PEmpty) = (tsubBV (Bc false) (ty' Not))) by reflexivity. rewrite H3. apply wf_ty'g;auto. unfold tybc. apply SBase with empty;auto. intros. apply IEvals2. 
    case_eq (PeanoNat.Nat.eqb (0 + 1) 1). 
    intros. case_eq (PeanoNat.Nat.eqb (0 + 1) 0). intros. apply PeanoNat.Nat.eqb_eq in H5. simpl in H5. discriminate. intro. case_eq (PeanoNat.Nat.eqb 0 0). intros.
    apply step_evals. apply EBinOp1.  assert (Bc true = (udelta Not (Bc false) (isCpt_Not false))) by reflexivity. rewrite H8. apply EUnOp2;auto. (*apply step_evals. assert ((subBV (Bc true) (ExpBinOp Eq (BV 0) (FV y))) = ExpBinOp Eq (Bc true) (FV y)). unfold subBV. reflexivity. rewrite <- H7. apply ELetV;auto.*)
    intro. apply PeanoNat.Nat.eqb_neq in H7. contradiction. intro. apply PeanoNat.Nat.eqb_neq in H5. simpl in H5. contradiction.
  -
    intros e'' emp st_e_e''; simpl; subst g.
    apply value_stuck in st_e_e'' as H'.  simpl in H'; try contradiction.
    inversion st_e_e''.
    --
      assert (Empty |--- ExpBinOp op e' e2 : tsubBV_at 1 e' (tsubBV e2 (ty'2 op))).
      eapply TBinOP;eauto.
      +
        apply sub_trans with (tsubBV e1 (snd (intype2 op)));auto.
        eapply typing_wf;eauto.
        apply t_wf_sub_fjtype with (fst (intype2 op));auto. apply wf_intype2s;auto. apply TSub with t;auto. apply wf_intype2f;simpl;auto.
        apply t_wf_sub_fjtype with (fst (intype2 op));auto. apply wf_intype2s;auto. apply TSub with t;auto. apply wf_intype2f;simpl;auto.
        apply sem_lc with e1;auto.
        apply tsubBV_invariant';auto.
        apply sem_lc with e1;auto.
      + 
        apply sem_lc with e1;eauto.
      +
        apply TSub with (tsubBV_at 1 e' (tsubBV e2 (ty'2 op)));auto.
        apply t_wf_sub_fjtype2 with (snd (intype2 op)) (fst (intype2 op));auto.
        apply wf_ty'2;auto.
        apply TSub with t;auto. apply wf_intype2f;simpl;auto.
        apply TSub with t';auto. 
        apply t_wf_sub_fjtype with (fst (intype2 op));auto. apply wf_intype2s;auto. apply TSub with t;auto. apply wf_intype2f;simpl;auto.
        apply tsubBV_invariant;auto.
        apply sem_lc with e1;auto.
    -- 
      assert (Empty |--- ExpBinOp op e1 e' : tsubBV_at 1 e1 (tsubBV e' (ty'2 op))).
      eapply TBinOP;eauto.
      + 
        apply sem_lc with e2;eauto.
      +
        apply TSub with (tsubBV_at 1 e1 (tsubBV e' (ty'2 op)));auto.
        apply t_wf_sub_fjtype2 with (snd (intype2 op)) (fst (intype2 op));auto.
        apply wf_ty'2;auto.
        apply TSub with t;auto. apply wf_intype2f;simpl;auto.
        apply TSub with t';auto. 
        apply t_wf_sub_fjtype with (fst (intype2 op));auto. apply wf_intype2s;auto. apply TSub with t;auto. apply wf_intype2f;simpl;auto.
        unfold tsubBV. rewrite <- commute_tsubBV_tsubBV;auto. rewrite commute_tsubBV_tsubBV with (ty'2 op) 1 0 e1 e2;auto.
        apply tsubBV_invariant;auto.
        apply sem_lc with e2;auto.
        apply sem_lc with e2;auto.
    --
      destruct op;  dependent destruction pf. 
      +
        simpl. case_eq (b1); intros. case_eq (b2); intro; simpl. 
        apply TSub with (tybc true). apply TBC. assert (TRefn TBool (PCons (ExpBinOp Eq (ExpBinOp And (Bc true) (Bc true)) (BV 0)) PEmpty) = (tsubBV_at 1 (Bc true) (tsubBV (Bc true) (ty'2 And)))) by reflexivity. rewrite H11. apply wf_and;auto. unfold tybc. apply SBase with empty;auto. intros. apply IEvals2. 

        case_eq (PeanoNat.Nat.eqb (0 + 1) 1). intros. case_eq (PeanoNat.Nat.eqb (0 + 1) 0). intros. apply PeanoNat.Nat.eqb_eq in H12. simpl in H12. discriminate. intro. case_eq (PeanoNat.Nat.eqb 0 0). intros.
        apply step_evals. assert (Bc true = (bdelta And (Bc true) (Bc true) (isCpt_And true true))) by reflexivity. apply EBinOp1;auto. rewrite H15 at 3. apply EBinOp3; auto. 
        intro. apply PeanoNat.Nat.eqb_neq in H14. contradiction. intro. apply PeanoNat.Nat.eqb_neq in H12. simpl in H12. contradiction.
        
        apply TSub with (tybc false). apply TBC. assert (TRefn TBool (PCons (ExpBinOp Eq (ExpBinOp And (Bc true) (Bc false)) (BV 0)) PEmpty) = (tsubBV_at 1 (Bc true) (tsubBV (Bc false) (ty'2 And)))) by reflexivity. rewrite H11. apply t_wf_sub_fjtype2 with (snd (intype2 And)) (fst (intype2 And));auto. apply wf_ty'2;auto. apply TSub with (tybc true);auto. apply TBC;auto. apply wf_intype2f;auto. unfold tybc. simpl. apply SBase with empty;auto. intros. apply IFaith;auto. apply TSub with (tybc false);auto. apply TBC;auto. apply t_wf_sub_fjtype with (fst (intype2 And));auto. apply wf_intype2s;auto. apply TSub with (tybc true);auto. apply TBC;auto. apply wf_intype2f;auto. unfold tybc. simpl. apply SBase with empty;auto. intros. apply IFaith;auto. unfold tybc. apply SBase with empty;auto. intros. unfold unbindP. simpl. apply IFaith. unfold tybc. apply SBase with empty;auto. intros. apply IEvals2. 
        case_eq (PeanoNat.Nat.eqb (0 + 1) 1). intros. case_eq (PeanoNat.Nat.eqb (0 + 1) 0). intros. apply PeanoNat.Nat.eqb_eq in H13. simpl in H13. discriminate. intro. case_eq (PeanoNat.Nat.eqb 0 0). intros.
        apply step_evals. assert (Bc false = (bdelta And (Bc true) (Bc false) (isCpt_And true false))) by reflexivity. apply EBinOp1;auto. rewrite H15 at 2. apply EBinOp3;auto. 
        intro. apply PeanoNat.Nat.eqb_neq in H14. contradiction. intro. apply PeanoNat.Nat.eqb_neq in H12. simpl in H12. contradiction.

        case_eq (b2); intro; simpl. 
        apply TSub with (tybc false). apply TBC. assert (TRefn TBool (PCons (ExpBinOp Eq (ExpBinOp And (Bc false) (Bc true)) (BV 0)) PEmpty) = (tsubBV_at 1 (Bc false) (tsubBV (Bc true) (ty'2 And)))) by reflexivity. rewrite H11. apply t_wf_sub_fjtype2 with (snd (intype2 And)) (fst (intype2 And));auto. apply wf_ty'2;auto. apply TSub with (tybc false);auto. apply TBC;auto. apply wf_intype2f;auto. unfold tybc. simpl. apply SBase with empty;auto. intros. apply IFaith;auto. apply TSub with (tybc true);auto. apply TBC;auto. apply t_wf_sub_fjtype with (fst (intype2 And));auto. apply wf_intype2s;auto. apply TSub with (tybc false);auto. apply TBC;auto. apply wf_intype2f;auto. unfold tybc. simpl. apply SBase with empty;auto. intros. apply IFaith;auto. unfold tybc. apply SBase with empty;auto. intros. unfold unbindP. simpl. apply IFaith. unfold tybc. apply SBase with empty;auto. intros. apply IEvals2. 
        case_eq (PeanoNat.Nat.eqb (0 + 1) 1). intros. case_eq (PeanoNat.Nat.eqb (0 + 1) 0). intros. apply PeanoNat.Nat.eqb_eq in H13. simpl in H13. discriminate. intro. case_eq (PeanoNat.Nat.eqb 0 0). intros.
        apply step_evals. assert (Bc false = (bdelta And (Bc false) (Bc true) (isCpt_And false true))) by reflexivity. rewrite H15 at 2. apply EBinOp1;auto. apply EBinOp3;auto. 
        intro. apply PeanoNat.Nat.eqb_neq in H14. contradiction. intro. apply PeanoNat.Nat.eqb_neq in H12. simpl in H10. contradiction.

        apply TSub with (tybc false). apply TBC. assert (TRefn TBool (PCons (ExpBinOp Eq (ExpBinOp And (Bc false) (Bc false)) (BV 0)) PEmpty) = (tsubBV_at 1 (Bc false) (tsubBV (Bc false) (ty'2 And)))) by reflexivity. rewrite H11. apply t_wf_sub_fjtype2 with (snd (intype2 And)) (fst (intype2 And));auto. apply wf_ty'2;auto. apply TSub with (tybc false);auto. apply TBC;auto. apply wf_intype2f;auto. unfold tybc. simpl. apply SBase with empty;auto. intros. apply IFaith;auto. apply TSub with (tybc false);auto. apply TBC;auto. apply t_wf_sub_fjtype with (fst (intype2 And));auto. apply wf_intype2s;auto. apply TSub with (tybc false);auto. apply TBC;auto. apply wf_intype2f;auto. unfold tybc. simpl. apply SBase with empty;auto. intros. apply IFaith;auto. unfold tybc. apply SBase with empty;auto. intros. unfold unbindP. simpl. apply IFaith. unfold tybc. apply SBase with empty;auto. intros. apply IEvals2. 
        case_eq (PeanoNat.Nat.eqb (0 + 1) 1). intros. case_eq (PeanoNat.Nat.eqb (0 + 1) 0). intros. apply PeanoNat.Nat.eqb_eq in H13. simpl in H13. discriminate. intro. case_eq (PeanoNat.Nat.eqb 0 0). intros.
        apply step_evals. assert (Bc false = (bdelta And (Bc false) (Bc false) (isCpt_And false false))) by reflexivity. rewrite H15 at 3. apply EBinOp1;auto. apply EBinOp3;auto. 
        intro. apply PeanoNat.Nat.eqb_neq in H14. contradiction. intro. apply PeanoNat.Nat.eqb_neq in H12. simpl in H10. contradiction.
    
    +
      simpl. case_eq (b1); intros. case_eq (b2); intro; simpl. 
      apply TSub with (tybc true). apply TBC. assert (TRefn TBool (PCons (ExpBinOp Eq (ExpBinOp Or (Bc true) (Bc true)) (BV 0)) PEmpty) = (tsubBV_at 1 (Bc true) (tsubBV (Bc true) (ty'2 Or)))) by reflexivity. rewrite H11. apply wf_or;auto. unfold tybc. apply SBase with empty;auto. intros. apply IEvals2. 
      case_eq (PeanoNat.Nat.eqb (0 + 1) 1). intros. case_eq (PeanoNat.Nat.eqb (0 + 1) 0). intros. apply PeanoNat.Nat.eqb_eq in H13. simpl in H13. discriminate. intro. case_eq (PeanoNat.Nat.eqb 0 0). intros.
      apply step_evals. assert (Bc true = (bdelta Or (Bc true) (Bc true) (isCpt_Or true true))) by reflexivity. rewrite H15 at 3. apply EBinOp1; auto. apply EBinOp3;auto. 
      intro. apply PeanoNat.Nat.eqb_neq in H14. contradiction. intro. apply PeanoNat.Nat.eqb_neq in H12. simpl in H10. contradiction.
      
      apply TSub with (tybc true). apply TBC. assert (TRefn TBool (PCons (ExpBinOp Eq (ExpBinOp Or (Bc true) (Bc false)) (BV 0)) PEmpty) = (tsubBV_at 1 (Bc true) (tsubBV (Bc false) (ty'2 Or)))) by reflexivity. rewrite H11. apply wf_or;auto. unfold tybc. apply SBase with empty;auto. intros. apply IEvals2. 
      case_eq (PeanoNat.Nat.eqb (0 + 1) 1). intros. case_eq (PeanoNat.Nat.eqb (0 + 1) 0). intros. apply PeanoNat.Nat.eqb_eq in H13. simpl in H13. discriminate. intro. case_eq (PeanoNat.Nat.eqb 0 0). intros.
      apply step_evals. assert (Bc true = (bdelta Or (Bc true) (Bc false) (isCpt_Or true false))) by reflexivity. rewrite H15 at 2. apply EBinOp1; auto. apply EBinOp3;auto.  
      intro. apply PeanoNat.Nat.eqb_neq in H14. contradiction. intro. apply PeanoNat.Nat.eqb_neq in H12. simpl in H10. contradiction.

      case_eq (b2); intro; simpl. 
      apply TSub with (tybc true). apply TBC. assert (TRefn TBool (PCons (ExpBinOp Eq (ExpBinOp Or (Bc false) (Bc true)) (BV 0)) PEmpty) = (tsubBV_at 1 (Bc false) (tsubBV (Bc true) (ty'2 Or)))) by reflexivity. rewrite H11. apply wf_or;auto. unfold tybc. apply SBase with empty;auto. intros. apply IEvals2. 
      case_eq (PeanoNat.Nat.eqb (0 + 1) 1). intros. case_eq (PeanoNat.Nat.eqb (0 + 1) 0). intros. apply PeanoNat.Nat.eqb_eq in H13. simpl in H13. discriminate. intro. case_eq (PeanoNat.Nat.eqb 0 0). intros.
      apply step_evals. assert (Bc true = (bdelta Or (Bc false) (Bc true) (isCpt_Or false true))) by reflexivity. rewrite H15 at 2. apply EBinOp1; auto. apply EBinOp3;auto. 
      intro. apply PeanoNat.Nat.eqb_neq in H14. contradiction. intro. apply PeanoNat.Nat.eqb_neq in H12. simpl in H10. contradiction.

      apply TSub with (tybc false). apply TBC. assert (TRefn TBool (PCons (ExpBinOp Eq (ExpBinOp Or (Bc false) (Bc false)) (BV 0)) PEmpty) = (tsubBV_at 1 (Bc false) (tsubBV (Bc false) (ty'2 Or)))) by reflexivity. rewrite H11. apply wf_or;auto. unfold tybc. apply SBase with empty;auto. intros. apply IEvals2. 
      case_eq (PeanoNat.Nat.eqb (0 + 1) 1). intros. case_eq (PeanoNat.Nat.eqb (0 + 1) 0). intros. apply PeanoNat.Nat.eqb_eq in H13. simpl in H13. discriminate. intro. case_eq (PeanoNat.Nat.eqb 0 0). intros.
      apply step_evals. assert (Bc false = (bdelta Or (Bc false) (Bc false) (isCpt_Or false false))) by reflexivity. rewrite H15 at 3.  apply EBinOp1; auto. apply EBinOp3;auto.  
      intro. apply PeanoNat.Nat.eqb_neq in H14. contradiction. intro. apply PeanoNat.Nat.eqb_neq in H12. simpl in H10. contradiction.
    +
      simpl. subst v0. subst v3. case_eq (veq v1 v2); intro.
      assert (subBV_at 2 v1 v2 = v2). apply subBV_at_lc_at with 2;auto.  apply islc_at_weaken with 0;auto. rewrite H6. 
      apply TSub with (tybc true). apply TBC. assert (TRefn TBool (PCons (ExpBinOp Eq (ExpBinOp Eq v1 v2) (BV 0)) PEmpty) = (tsubBV_at 1 v1 (tsubBV v2 (ty'2 Eq)))). simpl. rewrite H6. reflexivity. rewrite H9. eapply wf_eq;eauto. rewrite erase_empty. eapply typing_hasfjtype;eauto. rewrite erase_empty. eapply typing_hasfjtype;eauto. unfold tybc. apply SBase with empty;auto. intros. apply IEvals2. 
      case_eq (PeanoNat.Nat.eqb (0 + 1) 1). intros. case_eq (PeanoNat.Nat.eqb (0 + 1) 0). intros. apply PeanoNat.Nat.eqb_eq in H11. simpl in H11. discriminate. intro. case_eq (PeanoNat.Nat.eqb 0 0). intros.
      assert (open_at 0 y v1 = v1). apply open_at_lc_at. apply value_lc;auto. unfold open_at in H13. rewrite H13.
      assert (open_at 0 y v2 = v2). apply open_at_lc_at. apply value_lc;auto. unfold open_at in H14. rewrite H14.
      apply step_evals. assert (Bc (veq v1 v2) = (bdelta Eq v1 v2 (isCpt_Eq v1 v2 i i0))) by reflexivity. rewrite H4 in H15. rewrite H15. apply EBinOp1;auto. apply EBinOp3;auto. 
      intro. apply PeanoNat.Nat.eqb_neq in H12. contradiction. intro. apply PeanoNat.Nat.eqb_neq in H10. simpl in H8. contradiction.

      assert (subBV_at 2 v1 v2 = v2). apply subBV_at_lc_at with 2;auto. apply islc_at_weaken with 0;auto. rewrite H6. 
      apply TSub with (tybc false). apply TBC. assert (TRefn TBool (PCons (ExpBinOp Eq (ExpBinOp Eq v1 v2) (BV 0)) PEmpty) = (tsubBV_at 1 v1 (tsubBV v2 (ty'2 Eq)))). simpl. rewrite H6. reflexivity. rewrite H9. eapply wf_eq;eauto. rewrite erase_empty. eapply typing_hasfjtype;eauto. rewrite erase_empty. eapply typing_hasfjtype;eauto. unfold tybc. apply SBase with empty;auto. intros. apply IEvals2. 
      case_eq (PeanoNat.Nat.eqb (0 + 1) 1). intros. case_eq (PeanoNat.Nat.eqb (0 + 1) 0). intros. apply PeanoNat.Nat.eqb_eq in H11. simpl in H1. discriminate. intro. case_eq (PeanoNat.Nat.eqb 0 0). intros.
      assert (open_at 0 y v1 = v1). apply open_at_lc_at. apply value_lc;auto. unfold open_at in H13. rewrite H13.
      assert (open_at 0 y v2 = v2). apply open_at_lc_at. apply value_lc;auto. unfold open_at in H14. rewrite H14.
      apply step_evals. assert (Bc (veq v1 v2) = (bdelta Eq v1 v2 (isCpt_Eq v1 v2 i i0))) by reflexivity. rewrite H4 in H15. rewrite H15. apply EBinOp1;auto. apply EBinOp3;auto. 
      intro. apply PeanoNat.Nat.eqb_neq in H12. contradiction. intro. apply PeanoNat.Nat.eqb_neq in H10. simpl in H8. contradiction.

  -
    intros.
    inversion H5.
    +
      assert (isLC e1'). eapply sem_lc;eauto.
      subst g.
      assert (Empty |--- e1 : TRefn (TNom (TClass C)) ps). apply TSub with (TRefn (TNom (TClass C)) ps');auto. eapply mtype_ps_wf;eauto.
      assert (Empty |--- e1' : TRefn (TNom (TClass C)) ps). apply TSub with (TRefn (TNom (TClass C)) ps');auto. eapply mtype_ps_wf;eauto.
      assert (fv e1 = empty). apply fjtyp_nofv with FEmpty (erase (TRefn (TNom (TClass C)) ps'));auto. assert (FEmpty = erase_env Empty) by reflexivity. rewrite H13. apply typing_hasfjtype;auto.
      assert (WFtype Empty (tsubBV_at 1 e1 (tsubBV e2 rt))). apply t_wf_sub_fjtype2 with t (TRefn (TNom (TClass C)) ps);auto. eapply mtype_rt_wf;eauto. 
      apply TSub with t';auto. assert (Empty |--- e1 : TRefn (TNom (TClass C)) ps). apply TSub with (TRefn (TNom (TClass C)) ps');auto. eapply mtype_ps_wf;eauto. eapply t_wf_sub_fjtype;eauto. eapply mtype_t_wf;eauto.
      assert (Empty |--- ExpMethodInvoc e1' m e2 : self (tsubBV_at 1 e1' (tsubBV e2 rt)) (ExpMethodInvoc e1' m e2)).
      apply TInvok with t t' C ps ps';auto. apply sub_trans with (tsubBV e1 t);auto. eapply typing_wf;eauto. apply t_wf_sub_fjtype with (TRefn (TNom (TClass C)) ps);auto. eapply mtype_t_wf;eauto. apply t_wf_sub_fjtype with (TRefn (TNom (TClass C)) ps);auto. eapply mtype_t_wf;eauto. apply tsubBV_invariant';auto. 
      apply TSub with (self (tsubBV_at 1 e1' (tsubBV e2 rt)) (ExpMethodInvoc e1' m e2));auto.
      * 
        apply selfify_wf_typing with (self (tsubBV_at 1 e1 (tsubBV e2 rt)) (ExpMethodInvoc e1 m e2));auto.
        apply TInvok with t t' C ps ps';auto.
      * 
        apply self_idempotent_step_upper'';auto.
        apply Refc_Invok1;auto.
        unfold isLC. simpl;constructor;auto.
        unfold isLC. simpl;constructor;auto. 
        apply tsubBV_invariant;auto.
    +
      assert (isLC e'0). apply sem_lc with e2;eauto.
      subst g.
      assert (Empty |--- e1 : TRefn (TNom (TClass C)) ps). apply TSub with (TRefn (TNom (TClass C)) ps');auto. eapply mtype_ps_wf;eauto.
      assert (Empty |--- e2 : tsubBV e1 t). apply TSub with t';auto. apply t_wf_sub_fjtype with (TRefn (TNom (TClass C)) ps);auto. eapply mtype_t_wf;eauto.  
      assert (Empty |--- e'0 :  tsubBV e1 t). apply TSub with t';auto. apply t_wf_sub_fjtype with (TRefn (TNom (TClass C)) ps);auto. eapply mtype_t_wf;eauto.  
      (* assert (fv e1 = empty). apply fjtyp_nofv with FEmpty (erase (TRefn (TNom (TClass C)) ps'));auto. assert (FEmpty = erase_env Empty) by reflexivity. rewrite H13. apply typing_hasfjtype;auto. *)
      assert (WFtype Empty (tsubBV_at 1 e1 (tsubBV e2 rt))). apply t_wf_sub_fjtype2 with t (TRefn (TNom (TClass C)) ps);auto. eapply mtype_rt_wf;eauto. 
      (* apply TSub with t';auto. assert (Empty |--- e1 : TRefn (TNom (TClass C)) ps). apply TSub with (TRefn (TNom (TClass C)) ps');auto. eapply mtype_ps_wf;eauto. eapply t_wf_sub_fjtype;eauto. eapply mtype_t_wf;eauto.  *)
      assert (Empty |--- ExpMethodInvoc e1 m e'0 : self (tsubBV_at 1 e1 (tsubBV e'0 rt)) (ExpMethodInvoc e1 m e'0)). apply TInvok with t t' C ps ps';auto.
      
      (* apply sub_trans with (tsubBV e1 t);auto. eapply typing_wf;eauto. apply t_wf_sub_fjtype with (TRefn (TNom (TClass C)) ps);auto. eapply mtype_t_wf;eauto. apply t_wf_sub_fjtype with (TRefn (TNom (TClass C)) ps);auto. eapply mtype_t_wf;eauto. apply tsubBV_invariant';auto.  *)
      apply TSub with (self (tsubBV_at 1 e1 (tsubBV e'0 rt)) (ExpMethodInvoc e1 m e'0));auto.
      * 
        apply selfify_wf_typing with (self (tsubBV_at 1 e1 (tsubBV e2 rt)) (ExpMethodInvoc e1 m e2));auto.
        apply TInvok with t t' C ps ps';auto.
      * 
        apply self_idempotent_step_upper'';auto.
        apply Refc_Invok2;auto.
        unfold isLC. simpl;constructor;auto.
        unfold isLC. simpl;constructor;auto.
        
        (*TL*) unfold tsubBV. rewrite <- commute_tsubBV_tsubBV;auto. rewrite commute_tsubBV_tsubBV with rt 1 0 e1 e2;auto.
        apply tsubBV_invariant;auto.
    +
      rename H12 into val_new.
      (*Simply Checking Against Pempty, ps' == Pempty, should also be OK. *)
      rename H1 into Hsub. rename H11 into H1.
      assert (g |--- e1 : TRefn (TNom (TClass C0)) ps') as p_e_t1'. rewrite <- H6. eapply subclass_prev_inv;eauto. rewrite <- H6 in p_e_t1. apply p_e_t1. subst g. simpl;auto. 
      assert (FJSubtype (TNom (TClass C0)) (TNom (TClass C))) as fsub. eapply class_sub;eauto. rewrite <- H6 in p_e_t1. apply p_e_t1.  eapply class_sub' in fsub;eauto. destruct fsub as [ps''[t''[rt']]]. rename H11 into fsub. destruct fsub. rename H11 into mtype'. rename H12 into fsub.
      destruct fsub. rename H11 into fsub_. destruct H12. rename H11 into fsub. rename H12 into fsub'. unfold subtype_under in fsub.  unfold subtype_under2 in fsub'.
      assert (FJSubtype (TNom (TClass C0)) (TNom (TClass C))) as rfsub. eapply class_sub;eauto.  rewrite <- H6 in p_e_t1. apply p_e_t1. assert (SubClass (TClass C0) (TClass C)) as csub. inversion rfsub. auto. 
      assert (wf_under (TRefn(TNom (TClass C0)) ps) t''). apply narrow_wf_under with ps'' (TClass C0);auto. eapply mtype_t_wf;eauto.
      assert (wf_under (TRefn (TNom (TClass C)) ps) t). eapply mtype_t_wf;eauto.
      assert (wf_under2 (TRefn (TNom (TClass C)) ps) t rt).  eapply mtype_rt_wf;eauto. 
      (* assert (t'' = t0) as teq. apply mtype_body_teq with m C0 rt' ps e;auto. rewrite <- teq in H9.  *)
      assert ((forall y y', y<>y' -> Hastype (Cons y' (openT_at 0 y t'') (Cons y (TRefn (TNom (TClass C0)) ps'') Empty)) (open_at 1 y (open_at 0 y' e)) (openT_at 1 y (openT_at 0 y' rt')))) as mt. apply mtype_body_ok with m;auto. 
      assert ((forall y y', y<>y' -> Hastype (Cons y' (openT_at 0 y t) (Cons y (TRefn (TNom (TClass C0)) ps) Empty)) (open_at 1 y (open_at 0 y' e)) (openT_at 1 y (openT_at 0 y' rt)))). 
      intros. intros.
      apply TSub with (openT_at 1 y (openT_at 0 y' rt')). apply narrow_typ_top2 with (openT_at 0 y t'') (TRefn (TNom (TClass C0)) ps'');simpl;auto. 
      apply wf_narrow_subclass with (TClass C);auto. eapply mtype_ps_wf;eauto. eapply mtype_ps_wf;eauto. 
      (* unfold in_env. simpl. unfold not. intros. destruct H15. assert (y'<>y). auto. auto. auto. *)
      apply narrow_wf_top with (TRefn (TNom (TClass C)) ps);simpl;auto. eapply SBase with empty. eapply class_sub;eauto. rewrite <- H6 in p_e_t1. apply p_e_t1.  intros. apply IRefl.
      assert ((Cons y' (openT_at 0 y t) (Cons y (TRefn (TNom (TClass C0)) ps) Empty)) = concatE (Cons y (TRefn (TNom (TClass C0)) ps) Empty) (Cons y' (openT_at 0 y t) Empty)). reflexivity. rewrite H15. 
      apply narrow_wf' with (concatE (Cons y (TRefn (TNom (TClass C)) ps) Empty) (Cons y' (openT_at 0 y t) Empty)) (TRefn (TNom (TClass C)) ps);simpl;eauto.  unfold in_env. simpl. unfold not. intros. destruct H16. assert (y'<>y). auto. auto. auto.
      apply SBase with empty. eapply class_sub;eauto. rewrite <- H6 in p_e_t1. apply p_e_t1. intros. apply IRefl.
      apply fsub'. assert (y'<>y). auto. auto.
  

      remember (fresh (union empty (union empty (union (free rt) ( union (fv e2) (union (fv e) (union empty (union empty (union empty (union empty (union empty empty))))) )))))) as y. assert (~Elem y (union empty (union (empty) (union (free rt) ( union (fv e2) (union (fv e) (union empty (union empty (union empty (union empty (union empty empty))))))))))). rewrite Heqy. apply fresh_not_elem. 
      intros. assert (~Elem y empty). notin_solve_one.
      remember (fresh (union empty (union (free rt) ( union (fv e2) (union (fv e) (union empty (union empty (union empty (union empty (union empty (union empty (union empty (union (singleton y) empty))))))))))))) as y'. assert (~Elem y' (union empty (union (free rt) ( union (fv e2) (union (fv e)(union empty (union empty (union empty (union empty (union empty (union empty (union empty (union (singleton y) empty))))))))))))). rewrite Heqy'. apply fresh_not_elem.
      assert (y' <> y). apply not_elem_singleton. notin_solve_one.  
      assert (subBV e2 e = subFV y' e2 (unbind y' e)). apply subFV_unbind. notin_solve_one. rewrite H19.
      assert (subBV_at 1 (ExpNew C0 es) (subFV y' e2 (unbind y' e)) = subFV y (ExpNew C0 es) (open_at 1 y (subFV y' e2 (unbind y' e)))). apply subFV_open_at.  rewrite <- subFV_unbind. unfold not. intros.  apply fv_subBV_elim in H20. assert (~Elem y (union (fv e) (fv e2))). apply not_elem_union_intro; notin_solve_one. contradiction. notin_solve_one. rewrite H20.
      rewrite <- commute_tsubFV_subFV';auto. 
      assert (tsubBV e2 rt = tsubFV y' e2 (unbindT y' rt)). apply tsubFV_unbindT. notin_solve_one. rewrite H21.
      assert (tsubBV_at 1 (ExpNew C0 es) (tsubFV y' e2 (unbindT y' rt)) = tsubFV y (ExpNew C0 es) (openT_at 1 y (tsubFV y' e2 (unbindT y' rt)))). apply subFV_open_at. rewrite <- tsubFV_unbindT.  unfold not. intros.  apply fv_tsubBV_elim in H22. assert (~Elem y (union (free rt) (fv e2))). apply not_elem_union_intro; notin_solve_one. contradiction. notin_solve_one. rewrite H22.
      rewrite <- commute_tsubFV_unbindT';auto.
      assert (Empty = concatE Empty (esubFV y (ExpNew C0 es) (esubFV y' e2 Empty))). reflexivity. rewrite H23.
      assert (Empty |-s TRefn (TNom (TClass C0)) ps <:: TRefn (TNom (TClass C)) ps). apply SBase with empty. eapply class_sub;eauto. rewrite H4 in p_e_t1. rewrite <- H6 in p_e_t1. apply p_e_t1.   intros. apply IRefl. 
      assert (Empty |-s TRefn (TNom (TClass C0)) ps' <:: TRefn (TNom (TClass C0)) ps). inversion H0.  apply SBase with nms. apply SubBClass. apply SubCRefl. intros. subst g. assert (Cons y0 (TRefn (TNom (TClass C0)) PEmpty) Empty = concatE (Cons y0 (TRefn (TNom (TClass C0)) PEmpty) Empty) Empty). reflexivity. rewrite H4. apply INarrow with (TRefn (TNom (TClass C)) PEmpty);simpl;auto. apply SBase with empty. eapply class_sub;eauto. rewrite <- H6 in p_e_t1. subst g0. apply p_e_t1. intros. apply IRefl. 
      assert (Empty |-s TRefn (TNom (TClass C0)) ps' <:: TRefn (TNom (TClass C)) ps'). apply SBase with empty. eapply class_sub;eauto. rewrite H4 in p_e_t1. rewrite <- H6 in p_e_t1. apply p_e_t1.   intros. apply IRefl. 
      
      assert (Empty |-s TRefn (TNom (TClass C0)) ps' <:: TRefn (TNom (TClass C)) ps). inversion H0.  apply SBase with nms. eapply class_sub;eauto. rewrite H4 in p_e_t1. rewrite <- H6 in p_e_t1. apply p_e_t1. intros.  subst g. assert (Cons y0 (TRefn (TNom (TClass C0)) PEmpty) Empty = concatE (Cons y0 (TRefn (TNom (TClass C0)) PEmpty) Empty) Empty). reflexivity. rewrite H4. apply INarrow with (TRefn (TNom (TClass C)) PEmpty);simpl;auto. apply SBase with empty. eapply class_sub;eauto. rewrite <- H6 in p_e_t1. subst g0. apply p_e_t1. intros. apply IRefl.
      (* assert (WFtype (Cons y (TRefn (TClass C0) ps) Empty) (openT_at 0 y t)). apply narrow_wf_top with (TRefn (TNom (TClass C)) ps);simpl;auto.
      assert (Cons y (TRefn (TClass C0) ps') Empty |--- e2 : openT_at 0 y t). apply TSub with t'. apply weaken_typ_top;simpl;auto. subst g. auto. apply narrow_wf_top with (TRefn (TNom (TClass C)) ps);simpl;auto. apply narrow_subtype_top with (TRefn (TNom (TClass C)) ps');simpl;auto. subst g. apply Hsub. notin_solve_one. apply wf_narrow_subclass with C. assert (FJSubtype (TClass C0) (TNom (TClass C))). eapply class_sub;eauto. rewrite H4 in p_e_t1. rewrite <- H6 in p_e_t1. apply p_e_t1. inversion H29. auto.  apply typing_wf with e1;subst g;auto. apply typing_wf with e1;subst g;auto. eapply mtype_ps_wf;eauto. eapply mtype_ps_wf;eauto.  apply weaken_wf_top;simpl;auto. subst g. apply typing_wf with e2;simpl;auto. apply narrow_wf_top with (TRefn (TClass C0) ps);simpl;auto. *)
      apply exact_eval with (tsubFV y (ExpNew C0 es) (tsubFV y' e2 (openT_at 1 y (unbindT y' rt))));auto.
      *  
      subst e1. subst e2. subst g. 
      apply subst_typ2 with (TRefn (TNom (TClass C0)) ps) t;simpl;auto. 
      **
        apply TSub with  (TRefn (TNom (TClass C0)) ps');auto.
        apply wf_narrow_subclass with (TClass C).  inversion rfsub. auto. eapply mtype_ps_wf;eauto.
      **
        apply TSub with  t';auto.
        apply t_wf_sub_fjtype with (TRefn (TNom (TClass C)) ps);auto. 
        apply TSub with  (TRefn (TNom (TClass C0)) ps');auto.
        eapply mtype_ps_wf;eauto.
      **
        apply WFEBind;auto. apply WFEBind;auto. apply wf_narrow_subclass with (TClass C).  inversion rfsub. auto. eapply mtype_ps_wf;eauto. 
        unfold in_env. simpl. unfold not. intros. destruct H4;auto.
        apply narrow_wf_top with (TRefn (TNom (TClass C)) ps);simpl;auto.
      **
        apply wf_narrow_subclass with (TClass C);auto.
        inversion rfsub. auto.
        eapply mtype_ps_wf;eauto.
      * 
      subst e1. subst e2. subst g. 
      assert (WFtype (Cons y' (openT_at 0 y t)  (Cons y (TRefn (TNom (TClass C0)) ps) Empty)) (openT_at 1 y (openT_at 0 y' rt))). eapply typing_wf. apply H14. auto. apply WFEBind. apply WFEBind. apply WFEEmpty. simpl;auto. apply wf_narrow_subclass with (TClass C). assert (FJSubtype (TNom (TClass C0)) (TNom (TClass C))). eapply class_sub;eauto. inversion H4. auto. eapply mtype_ps_wf;eauto. 
      unfold in_env. simpl. unfold not. intros. destruct H4; auto. apply narrow_wf_top with (TRefn (TNom (TClass C)) ps);simpl;auto. 
      
      rewrite commute_tsubFV_unbindT';auto. rewrite <- H22. rewrite <- H21.
      apply t_wf_sub_fjtype2 with t (TRefn (TNom (TClass C)) ps);auto. 
      simpl.   apply TSub with  (TRefn (TNom (TClass C0)) ps');auto. eapply mtype_ps_wf;eauto.
      simpl.   apply TSub with  t';auto. apply t_wf_sub_fjtype with (TRefn (TNom (TClass C)) ps);auto. 
      apply TSub with  (TRefn (TNom (TClass C0)) ps');auto.
      eapply mtype_ps_wf;eauto.
      * 
        assert (subFV y (ExpNew C0 es) (subFV y' e2 (open_at 1 y (unbind y' e))) = (subBV_at 1 (ExpNew C0 es) (subBV e2 e))). rewrite subFV_unbind with y' e2 e.
        assert ((forall (e:expr) (j:index) (y:vname) (v:expr), ~ Elem y (fv e) -> subBV_at j v e = subFV y v (open_at j y e) )). apply subFV_open_at. rewrite H28 with (subFV y' e2 (unbind y' e)) 1 y (ExpNew C0 es).
        rewrite commute_tsubFV_subFV'. auto. auto. apply value_lc. auto. rewrite <- subFV_unbind. unfold not. intros. apply fv_subBV_elim in H29. assert (~ Elem y (union (fv e) (fv e2))). apply not_elem_union_intro. notin_solve_one. notin_solve_one. contradiction. notin_solve_one. notin_solve_one.
        rewrite H28. eapply Refc_Invok3;eauto.
      * 
        assert (tsubFV y (ExpNew C0 es) (tsubFV y' e2 (openT_at 1 y (unbindT y' rt))) = (tsubBV_at 1 (ExpNew C0 es) (tsubBV e2 rt))).
        assert (forall (t:type) (j:index) (y:vname) (v:expr), ~ Elem y (free t) -> tsubBV_at j v t = tsubFV y v (openT_at j y t) ). apply subFV_open_at. unfold tsubBV. rewrite H28 with rt 0 y' e2. rewrite H28 with (tsubFV y' e2 (openT_at 0 y' rt)) 1 y (ExpNew C0 es). rewrite commute_tsubFV_unbindT'. auto. auto. apply value_lc. auto.
        rewrite <- H28. unfold not. intros. apply fv_tsubBV_elim in H29. assert (~Elem y (union (free rt) (fv e2))).  apply not_elem_union_intro. notin_solve_one. notin_solve_one. contradiction. notin_solve_one. notin_solve_one.
        rewrite H28. rewrite <- erase_self with (tsubBV_at 1 (ExpNew C0 es) (tsubBV e2 rt)) (ExpMethodInvoc (ExpNew C0 es) m e2). apply typing_hasfjtype.  eapply TInvok;eauto.
        rewrite <- H23. rewrite H6. rewrite <-H4. apply p_e_t1.
        rewrite <- H23. inversion H0.  apply SBase with nms. apply SubBClass. apply SubCRefl. intros. subst g. apply H35. notin_solve_one .  
        rewrite <- H23. rewrite H4 in p_e_t2. apply p_e_t2. 
        intros. simpl. subst g. subst e1. auto. 
        rewrite H6. auto. 
  -
    intros.
    inversion H5.
    +
      assert (isLC e1'). eapply sem_lc;eauto.
      subst g.
      assert (Empty |--- e1 : TRefn (TNom (TInterface C)) ps). apply TSub with (TRefn (TNom (TInterface C)) ps');auto. eapply mtypei_ps_wf;eauto. 
      assert (Empty |--- e1' : TRefn (TNom (TInterface C)) ps). apply TSub with (TRefn (TNom (TInterface C)) ps');auto. eapply mtypei_ps_wf;eauto.
      assert (fv e1 = empty). apply fjtyp_nofv with FEmpty (erase (TRefn (TNom (TInterface C)) ps'));auto. assert (FEmpty = erase_env Empty) by reflexivity. rewrite H13. apply typing_hasfjtype;auto.
      assert (WFtype Empty (tsubBV_at 1 e1 (tsubBV e2 rt))). apply t_wf_sub_fjtype2 with t (TRefn (TNom (TInterface C)) ps);auto. eapply mtypei_rt_wf;eauto. 
      apply TSub with t';auto. assert (Empty |--- e1 : TRefn (TNom (TInterface C)) ps). apply TSub with (TRefn (TNom (TInterface C)) ps');auto. eapply mtypei_ps_wf;eauto. eapply t_wf_sub_fjtype;eauto. eapply mtypei_t_wf;eauto.
      assert (Empty |--- ExpMethodInvoc e1' m e2 : self (tsubBV_at 1 e1' (tsubBV e2 rt)) (ExpMethodInvoc e1' m e2)).
      apply TInvokI with t t' C ps ps';auto. apply sub_trans with (tsubBV e1 t);auto. eapply typing_wf;eauto. apply t_wf_sub_fjtype with (TRefn (TNom (TInterface C)) ps);auto.  eapply mtypei_t_wf;eauto. apply t_wf_sub_fjtype with (TRefn (TNom (TInterface C)) ps);auto. eapply mtypei_t_wf;eauto. apply tsubBV_invariant';auto. 
      apply TSub with (self (tsubBV_at 1 e1' (tsubBV e2 rt)) (ExpMethodInvoc e1' m e2));auto.
      * 
        apply selfify_wf_typing with (self (tsubBV_at 1 e1 (tsubBV e2 rt)) (ExpMethodInvoc e1 m e2));auto.
        apply TInvokI with t t' C ps ps';auto.
      * 
        apply self_idempotent_step_upper'';auto.
        apply Refc_Invok1;auto.
        unfold isLC. simpl;constructor;auto.
        unfold isLC. simpl;constructor;auto. 
        apply tsubBV_invariant;auto.
    +
      assert (isLC e'0). apply sem_lc with e2;eauto.
      subst g.
      assert (Empty |--- e1 : TRefn (TNom (TInterface C)) ps). apply TSub with (TRefn (TNom (TInterface C)) ps');auto. eapply mtypei_ps_wf;eauto.
      assert (Empty |--- e2 : tsubBV e1 t). apply TSub with t';auto. apply t_wf_sub_fjtype with (TRefn (TNom (TInterface C)) ps);auto. eapply mtypei_t_wf;eauto.  
      assert (Empty |--- e'0 :  tsubBV e1 t). apply TSub with t';auto. apply t_wf_sub_fjtype with (TRefn (TNom (TInterface C)) ps);auto. eapply mtypei_t_wf;eauto.  
      (* assert (fv e1 = empty). apply fjtyp_nofv with FEmpty (erase (TRefn (TNom (TClass C)) ps'));auto. assert (FEmpty = erase_env Empty) by reflexivity. rewrite H13. apply typing_hasfjtype;auto. *)
      assert (WFtype Empty (tsubBV_at 1 e1 (tsubBV e2 rt))). apply t_wf_sub_fjtype2 with t (TRefn (TNom (TInterface C)) ps);auto. eapply mtypei_rt_wf;eauto. 
      (* apply TSub with t';auto. assert (Empty |--- e1 : TRefn (TNom (TClass C)) ps). apply TSub with (TRefn (TNom (TClass C)) ps');auto. eapply mtype_ps_wf;eauto. eapply t_wf_sub_fjtype;eauto. eapply mtype_t_wf;eauto.  *)
      assert (Empty |--- ExpMethodInvoc e1 m e'0 : self (tsubBV_at 1 e1 (tsubBV e'0 rt)) (ExpMethodInvoc e1 m e'0)). apply TInvokI with t t' C ps ps';auto.
      
      (* apply sub_trans with (tsubBV e1 t);auto. eapply typing_wf;eauto. apply t_wf_sub_fjtype with (TRefn (TNom (TClass C)) ps);auto. eapply mtype_t_wf;eauto. apply t_wf_sub_fjtype with (TRefn (TNom (TClass C)) ps);auto. eapply mtype_t_wf;eauto. apply tsubBV_invariant';auto.  *)
      apply TSub with (self (tsubBV_at 1 e1 (tsubBV e'0 rt)) (ExpMethodInvoc e1 m e'0));auto.
      * 
        apply selfify_wf_typing with (self (tsubBV_at 1 e1 (tsubBV e2 rt)) (ExpMethodInvoc e1 m e2));auto.
        apply TInvokI with t t' C ps ps';auto.
      * 
        apply self_idempotent_step_upper'';auto.
        apply Refc_Invok2;auto.
        unfold isLC. simpl;constructor;auto.
        unfold isLC. simpl;constructor;auto.
        
        (*TL*) unfold tsubBV. rewrite <- commute_tsubBV_tsubBV;auto. rewrite commute_tsubBV_tsubBV with rt 1 0 e1 e2;auto.
        apply tsubBV_invariant;auto.
    +
      rename H12 into val_new.
      (*Simply Checking Against Pempty, ps' == Pempty, should also be OK. *)
      rename H1 into Hsub. rename H11 into H1.
      assert (g |--- e1 : TRefn (TNom (TClass C0)) ps') as p_e_t1'. rewrite <- H6. eapply subclass_prev_invn;eauto. rewrite <- H6 in p_e_t1. apply p_e_t1. subst g. simpl;auto. 
      assert (FJSubtype (TNom (TClass C0)) (TNom (TInterface C))) as fsub. eapply class_sub;eauto. rewrite <- H6 in p_e_t1. apply p_e_t1.  
      eapply class_sub'i in fsub;eauto. destruct fsub as [ps''[t''[rt']]]. rename H11 into fsub. destruct fsub. rename H11 into mtype'. rename H12 into fsub.
      destruct fsub. rename H11 into fsub_. destruct H12. rename H11 into fsub. rename H12 into fsub'. unfold subtype_under in fsub.  unfold subtype_under2 in fsub'.
      assert (FJSubtype (TNom (TClass C0)) (TNom (TInterface C))) as rfsub. eapply class_sub;eauto.  rewrite <- H6 in p_e_t1. apply p_e_t1. assert (SubClass (TClass C0) (TInterface C)) as csub. inversion rfsub. auto. 
      assert (wf_under (TRefn(TNom (TClass C0)) ps) t''). apply narrow_wf_under with ps'' (TClass C0);auto. eapply mtype_t_wf;eauto.
      assert (wf_under (TRefn (TNom (TInterface C)) ps) t). eapply mtypei_t_wf;eauto.
      assert (wf_under2 (TRefn (TNom (TInterface C)) ps) t rt).  eapply mtypei_rt_wf;eauto. 
      (* assert (t'' = t0) as teq. apply mtype_body_teq with m C0 rt' ps e;auto. rewrite <- teq in H9.  *)
      assert ((forall y y', y<>y' -> Hastype (Cons y' (openT_at 0 y t'') (Cons y (TRefn (TNom (TClass C0)) ps'') Empty)) (open_at 1 y (open_at 0 y' e)) (openT_at 1 y (openT_at 0 y' rt')))) as mt. apply mtype_body_ok with m;auto. 
      assert ((forall y y', y<>y' -> Hastype (Cons y' (openT_at 0 y t) (Cons y (TRefn (TNom (TClass C0)) ps) Empty)) (open_at 1 y (open_at 0 y' e)) (openT_at 1 y (openT_at 0 y' rt)))). 
      intros. intros.
      apply TSub with (openT_at 1 y (openT_at 0 y' rt')). apply narrow_typ_top2 with (openT_at 0 y t'') (TRefn (TNom (TClass C0)) ps'');simpl;auto. 
      apply wf_narrow_subclass with (TInterface C);auto. eapply mtypei_ps_wf;eauto. eapply mtype_ps_wf;eauto. 
      (* unfold in_env. simpl. unfold not. intros. destruct H15. assert (y'<>y). auto. auto. auto. *)
      apply narrow_wf_top with (TRefn (TNom (TInterface C)) ps);simpl;auto. eapply SBase with empty. eapply class_sub;eauto. rewrite <- H6 in p_e_t1. apply p_e_t1.  intros. apply IRefl.
      assert ((Cons y' (openT_at 0 y t) (Cons y (TRefn (TNom (TClass C0)) ps) Empty)) = concatE (Cons y (TRefn (TNom (TClass C0)) ps) Empty) (Cons y' (openT_at 0 y t) Empty)). reflexivity. rewrite H15. 
      apply narrow_wf' with (concatE (Cons y (TRefn (TNom (TInterface C)) ps) Empty) (Cons y' (openT_at 0 y t) Empty)) (TRefn (TNom (TInterface C)) ps);simpl;eauto.  unfold in_env. simpl. unfold not. intros. destruct H16. assert (y'<>y). auto. auto. auto.
      apply SBase with empty. eapply class_sub;eauto. rewrite <- H6 in p_e_t1. apply p_e_t1. intros. apply IRefl.
      apply fsub'. assert (y'<>y). auto. auto.


      remember (fresh (union empty (union empty (union (free rt) ( union (fv e2) (union (fv e) (union empty (union empty (union empty (union empty (union empty empty))))) )))))) as y. assert (~Elem y (union empty (union (empty) (union (free rt) ( union (fv e2) (union (fv e) (union empty (union empty (union empty (union empty (union empty empty))))))))))). rewrite Heqy. apply fresh_not_elem. 
      intros. assert (~Elem y empty). notin_solve_one.
      remember (fresh (union empty (union (free rt) ( union (fv e2) (union (fv e) (union empty (union empty (union empty (union empty (union empty (union empty (union empty (union (singleton y) empty))))))))))))) as y'. assert (~Elem y' (union empty (union (free rt) ( union (fv e2) (union (fv e)(union empty (union empty (union empty (union empty (union empty (union empty (union empty (union (singleton y) empty))))))))))))). rewrite Heqy'. apply fresh_not_elem.
      assert (y' <> y). apply not_elem_singleton. notin_solve_one.  
      assert (subBV e2 e = subFV y' e2 (unbind y' e)). apply subFV_unbind. notin_solve_one. rewrite H19.
      assert (subBV_at 1 (ExpNew C0 es) (subFV y' e2 (unbind y' e)) = subFV y (ExpNew C0 es) (open_at 1 y (subFV y' e2 (unbind y' e)))). apply subFV_open_at.  rewrite <- subFV_unbind. unfold not. intros.  apply fv_subBV_elim in H20. assert (~Elem y (union (fv e) (fv e2))). apply not_elem_union_intro; notin_solve_one. contradiction. notin_solve_one. rewrite H20.
      rewrite <- commute_tsubFV_subFV';auto. 
      assert (tsubBV e2 rt = tsubFV y' e2 (unbindT y' rt)). apply tsubFV_unbindT. notin_solve_one. rewrite H21.
      assert (tsubBV_at 1 (ExpNew C0 es) (tsubFV y' e2 (unbindT y' rt)) = tsubFV y (ExpNew C0 es) (openT_at 1 y (tsubFV y' e2 (unbindT y' rt)))). apply subFV_open_at. rewrite <- tsubFV_unbindT.  unfold not. intros.  apply fv_tsubBV_elim in H22. assert (~Elem y (union (free rt) (fv e2))). apply not_elem_union_intro; notin_solve_one. contradiction. notin_solve_one. rewrite H22.
      rewrite <- commute_tsubFV_unbindT';auto.
      assert (Empty = concatE Empty (esubFV y (ExpNew C0 es) (esubFV y' e2 Empty))). reflexivity. rewrite H23.
      assert (Empty |-s TRefn (TNom (TClass C0)) ps <:: TRefn (TNom (TInterface C)) ps). apply SBase with empty. eapply class_sub;eauto. rewrite H4 in p_e_t1. rewrite <- H6 in p_e_t1. apply p_e_t1.   intros. apply IRefl. 
      assert (Empty |-s TRefn (TNom (TClass C0)) ps' <:: TRefn (TNom (TClass C0)) ps). inversion H0.  apply SBase with nms. apply SubBClass. apply SubCRefl. intros. subst g. assert (Cons y0 (TRefn (TNom (TClass C0)) PEmpty) Empty = concatE (Cons y0 (TRefn (TNom (TClass C0)) PEmpty) Empty) Empty). reflexivity. rewrite H4. apply INarrow with (TRefn (TNom (TInterface C)) PEmpty);simpl;auto. apply SBase with empty. eapply class_sub;eauto. rewrite <- H6 in p_e_t1. subst g0. apply p_e_t1. intros. apply IRefl. 
      assert (Empty |-s TRefn (TNom (TClass C0)) ps' <:: TRefn (TNom (TInterface C)) ps'). apply SBase with empty. eapply class_sub;eauto. rewrite H4 in p_e_t1. rewrite <- H6 in p_e_t1. apply p_e_t1.   intros. apply IRefl. 
      
      assert (Empty |-s TRefn (TNom (TClass C0)) ps' <:: TRefn (TNom (TInterface C)) ps). inversion H0.  apply SBase with nms. eapply class_sub;eauto. rewrite H4 in p_e_t1. rewrite <- H6 in p_e_t1. apply p_e_t1. intros.  subst g. assert (Cons y0 (TRefn (TNom (TClass C0)) PEmpty) Empty = concatE (Cons y0 (TRefn (TNom (TClass C0)) PEmpty) Empty) Empty). reflexivity. rewrite H4. apply INarrow with (TRefn (TNom (TInterface C)) PEmpty);simpl;auto. apply SBase with empty. eapply class_sub;eauto. rewrite <- H6 in p_e_t1. subst g0. apply p_e_t1. intros. apply IRefl.
      (* assert (WFtype (Cons y (TRefn (TClass C0) ps) Empty) (openT_at 0 y t)). apply narrow_wf_top with (TRefn (TNom (TClass C)) ps);simpl;auto.
      assert (Cons y (TRefn (TClass C0) ps') Empty |--- e2 : openT_at 0 y t). apply TSub with t'. apply weaken_typ_top;simpl;auto. subst g. auto. apply narrow_wf_top with (TRefn (TNom (TClass C)) ps);simpl;auto. apply narrow_subtype_top with (TRefn (TNom (TClass C)) ps');simpl;auto. subst g. apply Hsub. notin_solve_one. apply wf_narrow_subclass with C. assert (FJSubtype (TClass C0) (TNom (TClass C))). eapply class_sub;eauto. rewrite H4 in p_e_t1. rewrite <- H6 in p_e_t1. apply p_e_t1. inversion H29. auto.  apply typing_wf with e1;subst g;auto. apply typing_wf with e1;subst g;auto. eapply mtype_ps_wf;eauto. eapply mtype_ps_wf;eauto.  apply weaken_wf_top;simpl;auto. subst g. apply typing_wf with e2;simpl;auto. apply narrow_wf_top with (TRefn (TClass C0) ps);simpl;auto. *)
      apply exact_eval with (tsubFV y (ExpNew C0 es) (tsubFV y' e2 (openT_at 1 y (unbindT y' rt))));auto.
      *  
      subst e1. subst e2. subst g. 
      apply subst_typ2 with (TRefn (TNom (TClass C0)) ps) t;simpl;auto. 
      **
        apply TSub with  (TRefn (TNom (TClass C0)) ps');auto.
        apply wf_narrow_subclass with (TInterface C).  inversion rfsub. auto. eapply mtypei_ps_wf;eauto.
      **
        apply TSub with  t';auto.
        apply t_wf_sub_fjtype with (TRefn (TNom (TInterface C)) ps);auto. 
        apply TSub with  (TRefn (TNom (TClass C0)) ps');auto.
        eapply mtypei_ps_wf;eauto.
      **
        apply WFEBind;auto. apply WFEBind;auto. apply wf_narrow_subclass with (TInterface C).  inversion rfsub. auto. eapply mtypei_ps_wf;eauto. 
        unfold in_env. simpl. unfold not. intros. destruct H4;auto.
        apply narrow_wf_top with (TRefn (TNom (TInterface C)) ps);simpl;auto.
      **
        apply wf_narrow_subclass with (TInterface C);auto.
        inversion rfsub. auto.
        eapply mtypei_ps_wf;eauto.
      * 
      subst e1. subst e2. subst g. 
      assert (WFtype (Cons y' (openT_at 0 y t)  (Cons y (TRefn (TNom (TClass C0)) ps) Empty)) (openT_at 1 y (openT_at 0 y' rt))). eapply typing_wf. apply H14. auto. apply WFEBind. apply WFEBind. apply WFEEmpty. simpl;auto. apply wf_narrow_subclass with (TInterface C). assert (FJSubtype (TNom (TClass C0)) (TNom (TInterface C))). eapply class_sub;eauto. inversion H4. auto. eapply mtypei_ps_wf;eauto. (*mtype ps*) (*eapply typing_wf. rewrite <- H4. apply p_e_t1'. apply WFEEmpty.*) 
      
      unfold in_env. simpl. unfold not. intros. destruct H4; auto. apply narrow_wf_top with (TRefn (TNom (TInterface C)) ps);simpl;auto. 
      
      rewrite commute_tsubFV_unbindT';auto. rewrite <- H22. rewrite <- H21.
      apply t_wf_sub_fjtype2 with t (TRefn (TNom (TInterface C)) ps);auto. 
      simpl.   apply TSub with  (TRefn (TNom (TClass C0)) ps');auto. eapply mtypei_ps_wf;eauto.
      simpl.   apply TSub with  t';auto. apply t_wf_sub_fjtype with (TRefn (TNom (TInterface C)) ps);auto. 
      apply TSub with  (TRefn (TNom (TClass C0)) ps');auto.
      eapply mtypei_ps_wf;eauto.
      * 
        assert (subFV y (ExpNew C0 es) (subFV y' e2 (open_at 1 y (unbind y' e))) = (subBV_at 1 (ExpNew C0 es) (subBV e2 e))). rewrite subFV_unbind with y' e2 e.
        assert ((forall (e:expr) (j:index) (y:vname) (v:expr), ~ Elem y (fv e) -> subBV_at j v e = subFV y v (open_at j y e) )). apply subFV_open_at. rewrite H28 with (subFV y' e2 (unbind y' e)) 1 y (ExpNew C0 es).
        rewrite commute_tsubFV_subFV'. auto. auto. apply value_lc. auto. rewrite <- subFV_unbind. unfold not. intros. apply fv_subBV_elim in H29. assert (~ Elem y (union (fv e) (fv e2))). apply not_elem_union_intro. notin_solve_one. notin_solve_one. contradiction. notin_solve_one. notin_solve_one.
        rewrite H28. eapply Refc_Invok3;eauto.
      * 
        assert (tsubFV y (ExpNew C0 es) (tsubFV y' e2 (openT_at 1 y (unbindT y' rt))) = (tsubBV_at 1 (ExpNew C0 es) (tsubBV e2 rt))).
        assert (forall (t:type) (j:index) (y:vname) (v:expr), ~ Elem y (free t) -> tsubBV_at j v t = tsubFV y v (openT_at j y t) ). apply subFV_open_at. unfold tsubBV. rewrite H28 with rt 0 y' e2. rewrite H28 with (tsubFV y' e2 (openT_at 0 y' rt)) 1 y (ExpNew C0 es). rewrite commute_tsubFV_unbindT'. auto. auto. apply value_lc. auto.
        rewrite <- H28. unfold not. intros. apply fv_tsubBV_elim in H29. assert (~Elem y (union (free rt) (fv e2))).  apply not_elem_union_intro. notin_solve_one. notin_solve_one. contradiction. notin_solve_one. notin_solve_one.
        rewrite H28. rewrite <- erase_self with (tsubBV_at 1 (ExpNew C0 es) (tsubBV e2 rt)) (ExpMethodInvoc (ExpNew C0 es) m e2). apply typing_hasfjtype.  eapply TInvokI;eauto.
        rewrite <- H23. rewrite H6. rewrite <-H4. apply p_e_t1.
        rewrite <- H23. inversion H0.  apply SBase with nms. apply SubBClass. apply SubCRefl. intros. subst g. apply H35. notin_solve_one .  
        rewrite <- H23. rewrite H4 in p_e_t2. apply p_e_t2. 
        intros. simpl. subst g. subst e1. auto. 
        rewrite H6. auto. 
  -
    intros.
    inversion H4.
    +
      rename H11 into val_new. 
      assert (HasFJtype FEmpty e ((TNom (TClass C)))). assert (erase_env Empty = FEmpty). simpl. reflexivity. 
      rewrite <-H11. assert (erase (TRefn (TNom (TClass C)) ps
      )=((TNom (TClass C)))). simpl. reflexivity. rewrite <- H12. apply typing_hasfjtype. rewrite <- H3. auto. auto.

     
      remember p_e_t as p_e_tt. clear Heqp_e_tt.
      assert (e = ExpNew C0 es). auto.
      assert (SubClass (TClass C0) (TClass C)). apply hasfjtype_subclass with es.
      assert (FEmpty = erase_env Empty). auto. rewrite H13.
      assert (TNom (TClass C) = erase (TRefn (TNom (TClass C)) ps)). auto. rewrite H14.
      apply typing_hasfjtype;auto. rewrite <- H12. subst g. auto.
      eapply invert_new in p_e_t;eauto. 
      
      destruct p_e_t as [Fs' [Ts']]. destruct H14. destruct H15. (*destruct H15. *)
      remember ((map ReffieldType Fs')) as Us.
      (* assert (Fs0 = Fs). apply reffields_det with C; auto.
      subst Fs0. *)
      assert (Fs0= Fs'). apply reffields_det with C0; auto.
      assert (nth_error Fs' i = Some fi). apply subtype_field_nth_same with C0 C Fs;auto. 
      subst Fs'.
      assert (nth_error (Us) i = Some (ReffieldType fi)). rewrite HeqUs. apply f_morp. auto.
      (* assert (True) as H17 by auto. assert (True) as H17 by auto.  *)
      remember empty as nms.
      assert (wf_under (TRefn (TNom (TClass C)) PEmpty) (ReffieldType fi)). eapply fieldtype_wf;eauto. rename H19 into WFC.
      remember (fresh (union (fv ei) (union empty nms)) ) as y.  assert (~Elem y (union (fv ei) (union empty nms))). rewrite Heqy. apply fresh_not_elem. rename H19 into nelem. assert (~Elem y nms). notin_solve_one. (*pose proof (H15 y H18) as xx. *)
      assert (nth_error (map (tsubBV (ExpNew C0 es)) Us) i = Some ((tsubBV (ExpNew C0 es)) (ReffieldType fi))). apply f_morp. auto.
      (* assert (nth_error (map (openT_at 0 y) Us) i = Some (openT_at 0 y (ReffieldType fi))). apply f_morp. auto. *)
      assert (exists Ti, nth_error Ts' i = Some Ti). eapply forall2_exists1;eauto. destruct H21 as [Ti].
      assert (exists ei, nth_error es i = Some ei). eapply forall2_exists1;eauto. destruct H22 as [ei']. 
        fold ref in H6.
        rewrite foldref in H6.
        rewrite <- H6 in H2.
        inversion H2.
        
        assert (i = i0).
        assert (nth_error (refs Fs0) i0 = Some (ref fi0)) by (eapply f_morp;auto).
        assert (nth_error (refs Fs0) i = Some (ref fi)) by (eapply f_morp;auto).
        assert (NoDup (refs Fs0)) by (eapply reffields_NoDup;eauto).
        eapply fields_i_eq;eauto.
        subst i0.
        rewrite H18 in H8. inversion H8. subst fi0.
        rewrite H9 in H22.
        inversion H22.
        subst ei'. auto. subst e'.
        assert (Hastype g ei Ti).
        eapply forall2_corres;eauto.

        assert (nth_error Us i = Some (ReffieldType fi)).

        rewrite HeqUs.
        apply f_morp;auto.
        assert (Subtype g Ti (tsubBV  (ExpNew C0 es) (ReffieldType fi))).
        eapply forall2_corres;eauto.
        (* apply f_morp;auto.
        subst g. *)
        (* subst e. *)
        assert (nth_error (map (tsubBV  (ExpNew C0 es)) Us) i = Some (tsubBV  (ExpNew C0 es) (ReffieldType fi))).
        apply f_morp;auto.
        subst g.
        assert (HasFJtype FEmpty (ExpNew C0 es) (TNom (TClass C))). assert (FEmpty = erase_env Empty). auto. rewrite H3. assert (TNom (TClass C) = erase (TRefn (TNom (TClass C)) ps)). auto. rewrite H27. apply typing_hasfjtype;auto. subst e. auto. 
        eapply exact_eval;eauto.
        (*substitution *)
        assert (tsubBV (ExpNew C0 es) (ReffieldType fi) = tsubFV y (ExpNew C0 es) (openT_at 0 y (ReffieldType fi))). apply tsubFV_unbindT.   erewrite fieldtype_no_fv;eauto. 
        (* rewrite H3.
        assert (ei = subFV y (ExpNew c es) ei). rewrite subFV_notin';auto. notin_solve_one. rewrite H26. *)
        assert (Empty |--- ExpNew C0 es : (self (TRefn (TNom (TClass C0)) (PEmpty)) (ExpNew C0 es))). apply TNew with Ts' Fs0 Us (map ref Fs0);auto. subst e. simpl in H. apply Forall_fun;auto.  
        apply TSub with Ti;auto. (*apply weaken_typ_top;simpl;auto. apply narrow_wf_top with (TRefn (TNom (TClass C)) (PCons (eqlPred (ExpNew c es)) PEmpty));simpl;auto. apply narrow_wf_top with (TRefn (TNom (TClass C)) PEmpty); simpl;auto. apply WFC. notin_solve_one. apply SBase with empty. apply SubBClass. destruct H12. auto. intros. unfold unbindP. simpl. apply IFaith. apply SBase with empty. destruct H12. auto. intros. apply IRefl.*)
        assert (tsubBV (ExpNew C0 es) (ReffieldType fi) = tsubFV y (ExpNew C0 es) (openT_at 0 y (ReffieldType fi))). apply tsubFV_unbindT.   erewrite fieldtype_no_fv;eauto. 
        rewrite H29. apply subst_wf_top with (TRefn (TNom (TClass C)) PEmpty);simpl;auto. 
        apply value_lc. auto. 
        assert (tsubBV (ExpNew C0 es) (ReffieldType fi) = tsubFV y (ExpNew C0 es) (openT_at 0 y (ReffieldType fi))). apply tsubFV_unbindT.   erewrite fieldtype_no_fv;eauto.
        
        rewrite H27. apply subst_wf_top with (TRefn (TNom (TClass C)) PEmpty);simpl;auto. 
        apply value_lc. auto. 

        rewrite foldref. eapply Refc_Field;eauto. 
        (* unfold tsubBV. rewrite erase_tsubBV_at. eapply FTField;eauto.  *)
        
    +
      assert (HasFJtype FEmpty e ((TNom (TClass C)))). assert (erase_env Empty = FEmpty). simpl. reflexivity. 
      rewrite <-H9. assert (erase (TRefn (TNom (TClass C)) ps
      )=((TNom (TClass C)))). simpl. reflexivity. rewrite <- H10. apply typing_hasfjtype. rewrite <- H3. auto. auto.
      assert (isLC e0'). apply sem_lc with e;auto.
      assert (wf_under (TRefn (TNom (TClass C)) PEmpty) (ReffieldType fi)). eapply fieldtype_wf;eauto. rename H11 into WFC.
      remember (fresh (empty)) as y.  assert (~Elem y empty). rewrite Heqy. apply fresh_not_elem. rename H11 into nelem. 
      assert (Empty |--- ExpFieldAccess e0' f : self (tsubBV e0' (ReffieldType fi)) (ExpFieldAccess e0' f)). subst f. 
      eapply TField;eauto.
      subst f5. subst f.
      apply TSub with (self (tsubBV e0' (ReffieldType fi)) (ExpFieldAccess e0' (ref fi)));auto.
      apply selfify_wf with  (ReffieldType fi). 
      assert (tsubBV e (ReffieldType fi) = tsubFV y e (openT_at 0 y (ReffieldType fi))). apply tsubFV_unbindT. erewrite fieldtype_no_fv;eauto. 
      rewrite H2. apply subst_wf_top with (TRefn (TNom (TClass C)) PEmpty);simpl;auto. 
      eapply FTField;eauto.
      apply self_idempotent_step_upper'';auto.
      assert (tsubBV e (ReffieldType fi) = tsubFV y e (openT_at 0 y (ReffieldType fi))). apply tsubFV_unbindT. erewrite fieldtype_no_fv;eauto. 
      rewrite H2. apply subst_wf_top with (TRefn (TNom (TClass C)) PEmpty);simpl;auto. 
      apply RefRC_Field;auto.
      apply tsubBV_invariant;auto.
    
  -
    intros.
    assert (~isValue (ExpNew C es)).
    eapply value_stuck;eauto.
    unfold not in H7.
    inversion H7.

    assert (Forall isLC es').
      clear H15. clear H10. clear H9. clear H7. clear H8. clear H5. clear H3. clear H4. generalize dependent es. generalize dependent i. induction es';intros.
      
        apply Forall_nil.
      
        destruct es. simpl in H16. inversion H16.
        destruct i. 
        
          simpl in *. inversion H13. inversion H12.
          inversion H1. 
          apply Forall_cons. apply sem_lc with ei;auto. rewrite <- H5. auto. 
          assert (es = es'). apply nth_eq;auto. intros. assert (S i <> 0). lia. apply H14 in H10. simpl in H10. auto.
          subst es'. subst g. auto.
        
          simpl in *. inversion H13. inversion H12.
          inversion H1. 
          apply Forall_cons. 
          assert (e = a). assert (0 <> S i). lia. apply H14 in H10. simpl in H10. inversion H10. auto. subst a. subst g. auto.
          apply IHes' with i es;auto.
          intros.  assert (S j <> S i). lia. apply H14 in H15. simpl in H15. auto.
    
    assert (Forall2 (Hastype Empty) es' Ts).
      clear H15. clear H10. clear H9. clear H7. clear H8. clear H5.
      generalize dependent Ts. generalize dependent es. generalize dependent i. induction es';intros.
      
        destruct Ts.
        apply Forall2_nil. 
        destruct es. inversion H4. simpl in H16. inversion H16.
      
        destruct Ts.
        destruct es. simpl in H16. inversion H16. inversion H4.
        destruct es. inversion H4.
        inversion H4. inversion H3. inversion H5. inversion H1.
        destruct i.
        
        apply Forall2_cons.
        simpl in H13. inversion H13.
        simpl in H12. inversion H12. 
        apply H9;auto. rewrite H31. auto.
        assert (es = es'). apply nth_eq;auto. intros. assert (S i <> 0). lia. apply H14 in H29. simpl in H29. auto.
        subst es'. subst g. auto.
        
        
        apply Forall2_cons.
        simpl in H13. inversion H13.
        simpl in H12. inversion H12. 
        assert (e = a). assert (0 <> S i). lia. apply H14 in H29. simpl in H29. inversion H29. auto. subst a. subst g. auto.
        apply IHes' with i es;auto. inversion H17. auto.
        intros.  assert (S j <> S i). lia. apply H14 in H30. simpl in H30. auto.
    assert (Forall2 (Subtype Empty) Ts (map (tsubBV (ExpNew C es')) Us)).
      assert (Forall2 (Subtype Empty) (map (tsubBV (ExpNew C es)) Us) (map (tsubBV (ExpNew C es')) Us)).
      apply tsubBV_invariant'_forall;auto.
      eapply RefRC_New_Arg;eauto.
      unfold isLC. simpl. apply Forall_fun;auto.
      unfold isLC. simpl. apply Forall_fun;auto.
      subst g.

      assert (Forall (WFtype Empty) (map (tsubBV (ExpNew C es)) Us)).
        assert (Empty |--- ExpNew C es : (self (TRefn (TNom (TClass C)) (PEmpty)) (ExpNew C es))). apply TNew with Ts Fs Us (map ref Fs);auto. 
        rewrite H. apply fieldtype_wf_subst_forall' with C nil;simpl;auto. unfold isLC. simpl. apply Forall_fun;auto.
        assert (erase (self (TRefn (TNom (TClass C)) PEmpty) (ExpNew C es)) = TNom (TClass C)). rewrite erase_self. simpl. auto. rewrite <- H20.
        assert (FEmpty = erase_env Empty). auto. rewrite H21.
        apply typing_hasfjtype;auto. 
      apply sub_trans_forall with (map (tsubBV (ExpNew C es)) Us);auto.
      apply typing_wf_forall' with es;auto. 
      rewrite H. apply fieldtype_wf_subst_forall' with C nil;simpl;auto. unfold isLC. simpl. apply Forall_fun;auto.
      eapply FTNew;eauto.
      assert (Forall2 (Hastype Empty) es' (map (tsubBV (ExpNew C es)) Us)). apply forall_subtyping with Ts;auto. 
      rewrite <- H. rewrite forall_erase with Us (ExpNew C es).
      assert (FEmpty = erase_env Empty). auto. rewrite H21.
      apply typing_wf_hasfjtype';auto.

    assert (Empty |--- ExpNew C es' : self (TRefn (TNom (TClass C)) PEmpty) (ExpNew C es')). apply TNew with Ts Fs Us fs;auto.
    apply TSub with (self (TRefn (TNom (TClass C)) PEmpty) (ExpNew C es'));auto.
    apply selfify_wf with ((self (TRefn (TNom (TClass C)) PEmpty) (ExpNew C es)));simpl;auto.
    assert (Empty |--- ExpNew C es : (self (TRefn (TNom (TClass C)) (PEmpty)) (ExpNew C es))). subst g. apply TNew with Ts Fs Us (map ref Fs);auto.   
    assert (erase (self (TRefn (TNom (TClass C)) PEmpty) (ExpNew C es)) = TNom (TClass C)). rewrite erase_self. simpl. auto. rewrite <- H22.
      assert (FEmpty = erase_env Empty). auto. rewrite H23.
      apply typing_hasfjtype;auto. 
    apply self_idempotent_step_upper'';auto;auto.
    eapply RefRC_New_Arg;eauto.
    unfold isLC. simpl. apply Forall_fun;auto.
    unfold isLC. simpl. apply Forall_fun;auto.
    apply sub_refl;auto.
  -
    intros. subst g. 
    apply TSub with s; try apply IHp_e_t; trivial.
 -
    intros. subst g.
    inversion H3.
    + 
    apply exact_eval' with (self b' (ExpLet e_x e));auto.
    apply TLet with b nms. auto. apply IHp_e_t;auto. auto. apply ELet. auto.
    apply  typing_hasfjtype. eapply TLet;eauto.
    +
    rewrite <- tsubBV_lct with e_x b'.
    pick_fresh zz. remember (fresh zz ) as y. assert (~Elem y zz). rewrite Heqy. apply fresh_not_elem. rewrite Heqzz in H7.
    assert (subBV e_x e = subFV y e_x (unbind y e)). apply subFV_unbind. notin_solve_one. rewrite H8.
    assert (tsubBV e_x b' = tsubFV y e_x (unbindT y b')). apply tsubFV_unbindT. notin_solve_one. rewrite H9.
    apply exact_eval with (self b' (ExpLet e_x e));auto.
    apply subst_typ_top with b;auto. apply H0. notin_solve_one. simpl. auto. 
    rewrite <- H9. rewrite tsubBV_lct. auto. apply wftype_islct with Empty;auto. rewrite <- H8. rewrite H4. auto. apply typing_hasfjtype. eapply TLet;eauto. auto.
    apply wftype_islct with Empty;auto.

Qed.
  
Theorem preservation : forall (e:expr) (t:type) (e':expr),
    Hastype Empty e t -> Step e e' -> Hastype Empty e' t.
Proof. intros; apply preservation' with Empty e; trivial. Qed.

Theorem many_preservation : forall (e e':expr) (t:type),
    EvalsTo e e' -> Hastype Empty e t -> Hastype Empty e' t.
Proof. intros e e' t ev_e_e'; induction ev_e_e'.
  - (* Refl  *) trivial.
  - (* AddSt *) intro p_e1_t; apply IHev_e_e'; 
    apply preservation with e1; assumption. Qed.
