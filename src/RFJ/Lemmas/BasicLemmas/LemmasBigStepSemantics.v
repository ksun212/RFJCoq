
Require Import Lists.
Require Import Program.
Require Import Arith.
Require Import ZArith.
Require Import Lia.

Require Import RFJ.Utils.

Require Import Definitions.Syntax.
Require Import Definitions.Names.
Require Import Definitions.Semantics.
Require Import Definitions.FJTyping.
Require Import Definitions.CTSanity.

Require Import Definitions.BigStepSemantics.

Require Import Lemmas.BasicLemmas.LemmasEnvironments.
Require Import Lemmas.BasicLemmas.LemmasFJTyping.
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasSubstitution.
(*big-step semantics has to be put into sem subtyping, since it requires sem_lc which requires C OK*)
Require Import Lemmas.BasicLemmas.LemmasSemantics.

Require Import Lemmas.BasicLemmas.LemmasCTBasics.
Require Import Lemmas.BasicLemmas.LemmasCTTyping.


(*---------------Properties of the Big-step Semantics---------------*)


Lemma islc_subBV: forall v e j, isLC_at 0 v -> isLC_at (j+1) e -> isLC_at j (subBV_at j v e).
Proof. 
  intros. generalize dependent j. induction e using expr_ind';intros;simpl;auto.
  -
    unfold subBV. simpl.  case_eq (j=?i);intros. 
    apply islc_at_weaken with 0;auto. lia.
    simpl. simpl in H0. apply Nat.eqb_neq in H1. inversion H0. 
    assert (j + 1 = S j). lia. rewrite H2 in H3. inversion H3. unfold not in H1. rewrite H5 in H1. contradiction.
    unfold lt. assert (j + 1 = S j). lia. rewrite H4 in H2. inversion H2. subst m. auto. 
  -
    simpl in H0. destruct H0. constructor;auto.
  -
    simpl in H0. destruct H0. constructor;auto.
  -
    simpl in *. induction l.
    ++ 
      auto.
    ++
      inversion H0. destruct H1. constructor.
      apply H4. auto.
      apply IHl;auto.
  -
    simpl in H0. destruct H0. constructor;auto.
Qed.
Lemma sem_lc: forall e e0, isLC e -> e ~~> e0 -> isLC e0.
Proof.
  intros. induction H0;unfold isLC in *;simpl in *;auto.
  -
    apply value_lc. apply udelta_value;auto.
  -
    destruct H. constructor;auto.
  -
    destruct H. constructor;auto.
  -
    apply value_lc. eapply bdelta_value;eauto.
  -
    destruct H. constructor;auto.
  -
    destruct H. constructor;auto.
  -
    destruct H.
    assert (isLC_at 2 e). eapply mbody_islc2;eauto.
    unfold subBV.
    rewrite <- commute_subBV_subBV;auto. 
    apply islc_subBV;auto. 
    apply islc_subBV;auto.
  -
    apply forall_nth_error with es i;auto. apply Forall_fun. auto.
  -
    apply Forall_fun. apply Forall_fun in H.
    generalize dependent es. generalize dependent i; induction es';intros.
    +
      apply Forall_nil.
    +
      destruct es.
      ++
        destruct i;simpl in H1;inversion H1.
      ++
        destruct i.
        +++ 
          apply Forall_cons.
          simpl in *. inversion H2. inversion H1. subst ei. apply IHStep. inversion H. auto.
          assert (es = es'). apply nth_eq;auto. intros. assert (S i <> 0). lia. apply H3 in H5. simpl in H5. auto.
          inversion H. subst es'. auto. 
        +++
          simpl in H2. inversion H. simpl in H1. simpl in H4.
          apply Forall_cons.
          assert(e = a). assert (0 <> S i). lia. apply H3 in H9. simpl in H9. inversion H9. auto. subst a. auto.
          apply IHes' with i es;auto. intros.  assert (S j <> S i). lia. apply H3 in H10. simpl in H10. auto.
  -
    destruct H. constructor;auto.
  -
    destruct H. apply islc_subBV;auto. 
Qed.

Lemma BStepEval_closed: forall e v, BStepEval e v -> fv e = empty.
Proof.
  intros. induction H using BStepEval_ind';simpl;auto.
  -
    apply value_closed;auto.
  -
    apply union_eq_empty_intro. constructor;auto.
  -
    apply union_eq_empty_intro. constructor;auto.
  -
    generalize dependent es'. induction es;intros.
    +
      auto.
    +
      destruct es'. inversion H.
      inversion H. inversion H0. apply union_eq_empty_intro. constructor.
      auto. apply IHes with es';auto.
  -
    apply union_eq_empty_intro. constructor;auto.
    
    apply subset_empty_intro with (fv (subBV ex' e));auto.
    apply fv_subBV_intro.
Qed.

Lemma BStepEval_value: forall e v, BStepEval e v -> isValue v.
Proof.
  intros. induction H using BStepEval_ind';auto.
  -
    eapply udelta_value;eauto.
  -
    eapply bdelta_value;eauto.
  -
    simpl in IHBStepEval. apply Forall_fun in IHBStepEval. eapply forall_nth_error;eauto.
  -
    simpl.
    generalize dependent es. induction es';intros.
    + simpl;auto.
    + simpl. destruct es. inversion H. inversion H. inversion H0. constructor;auto. eapply IHes';eauto.
Qed.

Lemma BStepEval_value_forall: forall es vs, Forall2 BStepEval es vs -> Forall isValue vs.
Proof.
  intros. generalize dependent es. induction vs;intros.
  -
    apply Forall_nil;auto.
  -
    inversion H. 
    apply Forall_cons;auto.
    eapply BStepEval_value;eauto.
    eapply IHvs;eauto.
Qed.

Lemma BStepEval_value_value: forall e v, isValue e -> BStepEval e v -> e=v.
Proof.
  intros. induction H0 using BStepEval_ind';auto;simpl in H;try contradiction.
  f_equal.
  generalize dependent es. induction es';intros.
    + destruct es. simpl;auto. inversion H0.
    + simpl. destruct es. inversion H0. inversion H0. inversion H1. destruct H. f_equal. apply H11;auto. eapply IHes';eauto.
Qed.
Lemma BStepEval_value_value_forall: forall es es', Forall isValue es -> Forall2 BStepEval es es' -> es=es'.
Proof.
  intros. generalize dependent es'. induction es;intros.
  - destruct es'. auto. inversion H0.
  - destruct es'. inversion H0. inversion H. inversion H0. f_equal. apply BStepEval_value_value;auto. apply IHes;auto.
Qed.

Lemma BEValue_forall: forall es, Forall isValue es -> Forall2 BStepEval es es.
Proof.
  intros. induction es.
  apply Forall2_nil.
  inversion H. apply Forall2_cons. apply BEValue;auto. 
  apply IHes;auto.
Qed.
Lemma EvalsTo_BStepEval: forall e v, isValue v -> EvalsTo e v -> BStepEval e v .
Proof.
  intros. induction H0.
  - apply BEValue;auto.
  - apply IHEvalsTo in H. clear H1. clear IHEvalsTo. generalize dependent e3. induction H0;intros.
    + inversion H. simpl in H2;contradiction. apply BEUnOp;auto. 
    + assert (isValue (udelta c w pf)). apply udelta_value. eapply BStepEval_value_value in H1;eauto. subst e3. 
      apply BEUnOp. apply BEValue;auto.
    + inversion H. simpl in H1;contradiction. apply BEBinOp;auto.
    + inversion H1. simpl in H2;contradiction. apply BEBinOp;auto.
    + assert (isValue (bdelta c v1 v2 pf)). eapply bdelta_value;eauto. eapply BStepEval_value_value in H1;eauto. subst e3. 
      apply BEBinOp; apply BEValue;auto.
    + inversion H. simpl in H;contradiction. eapply BEInvok;eauto.
    + inversion H1. simpl in H2;contradiction. eapply BEInvok;eauto.
    + eapply BEInvok;eauto; apply BEValue;auto.
    + simpl in H2. eapply BStepEval_value_value in H3;eauto. subst e3. eapply BEAccess;eauto. apply BEValue;auto. apply Forall_fun in H2. eapply forall_nth_error;eauto.
    + inversion H. simpl in H1;contradiction. eapply BEAccess;eauto.
    + inversion H4.
      ++  (*all es' are values: besides i are already values, ei' is also value, thus e3 = ei'*) 
          simpl in H5. apply Forall_fun in H5. assert (isValue ei'). eapply forall_corres;eauto.
          assert (ei' ⇓ ei'). apply BEValue;auto. apply IHStep in H9. apply BENew.
          clear H0. clear IHStep. clear H4. clear H6. clear H7. (*expose this fact by induction on es'0*)
          generalize dependent es. generalize dependent i. induction es';intros.
          *  
            destruct es. apply Forall2_nil. destruct i;simpl in H1;inversion H1.
          *  
            destruct es. simpl in H3. inversion H3. 
            simpl in H3. inversion H3. destruct i.
            ** 
              simpl in H1. simpl in H. inversion H1. inversion H. subst a. subst e. apply Forall2_cons;auto. 
              assert (forall j, nth_error es j = nth_error es' j). intros. assert (S j <> 0). discriminate. apply H2 in H0. simpl in H0. auto. assert (es = es'). apply nth_eq;auto. subst es. apply BEValue_forall. inversion H5. auto. 
            **
              simpl in H1. simpl in H. apply Forall2_cons. assert (0 <> S i). discriminate. apply H2 in H0. simpl in H0. inversion H0. inversion H5. apply BEValue;auto.
              eapply IHes';eauto. inversion H5. auto. intros. 
              assert (S j <> S i). unfold not. intros. unfold not in H0. inversion H6. apply H0 in H10;contradiction. 
              apply H2 in H6. simpl in H6. auto.
      ++  assert (exists ei'', nth_error es'0 i = Some ei''). eapply forall2_exists2;eauto. destruct H9 as [ei''].
          assert (ei' ⇓ ei''). eapply forall2_corres;eauto. apply IHStep in H10. apply BENew. 
          (*es besides i are equal to es', to which we have bevals, ei we also has due to IH*)
          clear H0. clear IHStep. clear H4. clear H5. clear H7. clear H6. (*expose this fact by induction on es'0*)
          generalize dependent es. generalize dependent es'. generalize dependent i. induction es'0;intros.
          * destruct es. apply Forall2_nil. destruct i;simpl in H9;inversion H9. 
          * destruct es. destruct i;simpl in H;inversion H. destruct es'. simpl in H3. inversion H3. simpl in H3.  inversion H8.
            apply Forall2_cons. 
              ** destruct i. 
              *** simpl in H. inversion H. subst e. simpl in H9. inversion H9. auto. 
              *** assert (0 <> S i). discriminate. apply H2 in H12. simpl in H12. inversion H12. auto.
              ** destruct i.
              *** simpl in H9. simpl in H1. simpl in H. assert (forall j, nth_error es j = nth_error es' j). intros. assert (S j <> 0). discriminate. apply H2 in H12. simpl in H12. auto. assert (es = es'). apply nth_eq;auto. subst es. auto. 
              *** simpl in H9. simpl in H1. simpl in H. apply IHes'0 with i es';auto. intros.
              assert (S j <> S i). unfold not. intros. unfold not in H12. inversion H13. apply H12 in H15. contradiction. apply H2 in H13.
              simpl in H13. auto.
    + inversion H. simpl in H1;contradiction. eapply BELet;eauto.
    + eapply BELet;eauto. apply BEValue;auto.
Qed.


Lemma BStepEval_EvalsTo: forall e v, BStepEval e v -> EvalsTo e v.
Proof.
  intros. induction H using BStepEval_ind'.
  -
    apply Refl.
  -
    apply lemma_evals_trans with (ExpUnOp c v);auto.
    apply unop_many;auto.
    apply step_evals. apply EUnOp2;eapply BStepEval_value;eauto.
  -
    apply lemma_evals_trans with (ExpBinOp c v1 e2);auto.
    apply binop_many;auto.
    apply lemma_evals_trans with (ExpBinOp c v1 v2);auto.
    apply binop_many';auto. eapply BStepEval_value;eauto.
    apply step_evals. apply EBinOp3;eapply BStepEval_value;eauto.
  -
    assert (isValue e'). eapply BStepEval_value;eauto.
    apply lemma_evals_trans with (subBV_at 1 (ExpNew C es) (subBV v e));auto.
    apply lemma_evals_trans with (ExpMethodInvoc (ExpNew C es) m e2).
    + 
      apply invok_many;auto.
    +
      apply lemma_evals_trans with (ExpMethodInvoc (ExpNew C es) m v).
      *
        apply invok_many';auto. eapply BStepEval_value;eauto.
      *
        apply step_evals. eapply Refc_Invok3;eauto. eapply BStepEval_value;eauto. eapply BStepEval_value;eauto.
  -
    apply lemma_evals_trans with (ExpFieldAccess (ExpNew C es) f);auto.
    apply access_many;auto.
    apply step_evals. subst f. eapply Refc_Field;eauto. eapply BStepEval_value;eauto.
  -
    clear H.
    induction H0. apply Refl.
    apply lemma_evals_trans with (ExpNew C (y :: l));auto.
    +
      clear H0. clear IHForall2. induction H.
      apply Refl.
      apply AddStep with (ExpNew C (e2 :: l)).
      apply RefRC_New_Arg with e2 e1 0;auto.
      intros. destruct j. contradiction. simpl. auto.
      apply IHEvalsTo.
    + 
      clear H0. clear H.
      dependent induction IHForall2.
      apply Refl.
      inversion H.
      assert (e2 = ExpNew C es'). auto.
      apply IHIHForall2 with C es' l' in H8;auto.
      apply lemma_evals_trans with (ExpNew C (y :: es'));auto.
      apply step_evals. apply RefRC_New_Arg with ei' ei (S i);auto.
      intros. destruct j. simpl. auto. simpl. apply H5. auto. 
      simpl. f_equal;auto.
  -
    apply lemma_evals_trans with (ExpLet ex' e);auto.
    + 
    apply lemma_let_many;auto.
    +
    apply lemma_evals_trans with (subBV ex' e);auto.
    apply step_evals. eapply ELetV. eapply BStepEval_value;eauto.           
Qed.

Lemma eunop_subBV_invert: forall c w e' j p, ExpUnOp c w = subBV_at j e' p -> (p = BV j /\ e' = ExpUnOp c w) \/ (exists pp, ExpUnOp c pp = p).
Proof.
  intros. destruct p; simpl in H;try inversion H.
  -
    case_eq (j=?i);intros.
    +
      rewrite H0 in H.
      apply Nat.eqb_eq in H0. subst i. left. constructor;auto.
    +
      rewrite H0 in H. inversion H.
  -
    right. exists p. auto.
Qed.
Lemma ebinop_subBV_invert: forall c e1 e2 e' j p,  ExpBinOp c e1 e2 = subBV_at j e' p -> ((p = BV j /\ e' = ExpBinOp c e1 e2) \/ exists ee1 ee2, ExpBinOp c ee1 ee2 = p).
Proof.
  intros. destruct p; simpl in H;try inversion H.
  -
    case_eq (j=?i);intros.
    +
      rewrite H0 in H.
      apply Nat.eqb_eq in H0. subst i. left. constructor;auto.
    +
      rewrite H0 in H. inversion H.
  -
    right. exists p1. exists p2. auto.
Qed.

Lemma eaccess_subBV_invert: forall f e0 e' j p,  ExpFieldAccess e0 f  = subBV_at j e' p -> ((p = BV j /\ e' = ExpFieldAccess e0 f) \/ exists ee1,ExpFieldAccess ee1 f = p).
Proof.
  intros. destruct p; simpl in H;try inversion H.
  -
    case_eq (j=?i);intros.
    +
      rewrite H0 in H.
      apply Nat.eqb_eq in H0. subst i. left. constructor;auto.
    +
      rewrite H0 in H. inversion H.
  -
    right. exists p. auto.
Qed.



Lemma einvok_subBV_invert: forall m e1 e2 e' j p,  ExpMethodInvoc e1 m e2 = subBV_at j e' p -> ((p = BV j /\ e' = ExpMethodInvoc e1 m e2) \/ exists ee1 ee2, ExpMethodInvoc ee1 m ee2 = p).
Proof.
  intros. destruct p; simpl in H;try inversion H.
  -
    case_eq (j=?i);intros.
    +
      rewrite H0 in H.
      apply Nat.eqb_eq in H0. subst i. left. constructor;auto.
    +
      rewrite H0 in H. inversion H.
  -
    right. exists p1. exists p2. auto.
Qed.

Lemma enew_subBV_invert: forall C es e' j p,  ExpNew C es = subBV_at j e' p -> ((p = BV j /\ e' = ExpNew C es) \/ exists ees, ExpNew C ees = p). 
Proof.
  intros. destruct p; simpl in H;try inversion H.
  -
    case_eq (j=?i);intros.
    +
      rewrite H0 in H.
      apply Nat.eqb_eq in H0. subst i. left. constructor;auto.
    +
      rewrite H0 in H. inversion H.
  -
    right. exists l. auto. 
Qed.

Lemma elet_subBV_invert: forall ex e0 e' j p,  ExpLet ex e0 = subBV_at j e' p -> ((p = BV j /\ e' = ExpLet ex e0) \/ exists ee1 ee2,ExpLet ee1 ee2 = p). 
Proof.
  intros. destruct p; simpl in H;try inversion H.
  -
    case_eq (j=?i);intros.
    +
      rewrite H0 in H.
      apply Nat.eqb_eq in H0. subst i. left. constructor;auto.
    +
      rewrite H0 in H. inversion H.
  -
    right. exists p1. exists p2. auto. 
Qed.

Lemma reffields_NoDup : forall C fs,
  Reffields C fs ->
  NoDup (refs fs).
Proof.
  intros.
  induction H.
  -
    simpl.
    auto.
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

Require Import Lia.
(*essential: step cases, correspond to the bvalue case.*)
Lemma step_bevals': forall e e' v, e ~~> e' -> BStepEval e v -> BStepEval e' v.
Proof.
  intros. generalize dependent v.
  induction H;intros.
  -
    inversion H0.
    +
      simpl in H1;contradiction.
    +
      apply IHStep in H4.
      apply BEUnOp;auto.
  -
    inversion H0.
    +
      simpl in H1;contradiction.
    +
      assert (w = v0). apply BStepEval_value_value;auto. subst v0.
      assert (udelta c w pf = udelta c w pf0).
      apply udelta_pf_indep. rewrite <- H5.
      assert (isValue (udelta c w pf)). apply udelta_value;auto.
      apply BEValue;auto.
  -
    inversion H0.
    +
    simpl in H1;contradiction.
    +
      apply IHStep in H5.
      apply BEBinOp;auto.
  -
    inversion H1.
    +
    simpl in H2;contradiction.
    +
      apply IHStep in H7.
      apply BEBinOp;auto.
  -
    inversion H1.
    +
      simpl in H2;contradiction.
    +
      assert (v1 = v0). apply BStepEval_value_value;auto. subst v0.
      assert (v2 = v3). apply BStepEval_value_value;auto. subst v3.
      
      assert (isValue (bdelta c v1 v2 pf)). eapply bdelta_value;eauto.
      assert (bdelta c v1 v2 pf = bdelta c v1 v2 pf0). apply delta_pf_indep;auto. rewrite <- H9. 
      apply BEValue;auto.
  -
    inversion H0.
    +
    simpl in H1;contradiction.
    +
      apply IHStep in H4.
      eapply BEInvok;eauto.
  -
    inversion H1.
    +
    simpl in H2;contradiction.
    +
      apply IHStep in H6.
      eapply BEInvok;eauto.
  -
    inversion H2.
    +
      simpl in H3;contradiction.
    +
      assert (ExpNew C es = ExpNew C0 es0). apply BStepEval_value_value;auto. inversion H11. subst C0. subst es0.
      assert (v = v1). apply BStepEval_value_value;auto. subst v1.
      assert (e = e0). eapply mbody_det;eauto. subst e0.
      auto.
  -
    inversion H3.
    +
      simpl in H4;contradiction.
    +
      assert (ExpNew C es = ExpNew C0 es0). apply BStepEval_value_value;auto. inversion H12. subst C0. subst es0.
      assert (Fs0 = Fs). eapply reffields_det;eauto. subst Fs0.
      assert (i0 = i).
    assert (nth_error (refs Fs) i = Some (ref fi)) by (eapply f_morp;auto).
    assert (nth_error (refs Fs) i0 = Some (ref fi0)) by (eapply f_morp;auto).
    assert (NoDup (refs Fs)) by (eapply reffields_NoDup;eauto).
    eapply fields_i_eq;eauto. subst i0.
    rewrite H1 in H9. inversion H9.
    apply BEValue;auto. 
    apply forall_nth_error with es i;auto. simpl in H2. apply Forall_fun;auto. rewrite <- H14. auto.
  -
    inversion H0.
    +
      simpl in H1;contradiction.
    +
      apply IHStep in H3.
      eapply BEAccess;eauto.
  -
    inversion H4.
    +
      simpl in H5.
      assert (ei ⇓ ei).
      apply BEValue.  apply forall_nth_error with es i;auto. apply Forall_fun;auto.
      apply IHStep in H8.
      apply BENew.
      clear H4. clear H6. clear H7.
      generalize dependent es'. generalize dependent i. induction es;intros.
      ++
        destruct es'. apply Forall2_nil.
        inversion H3.
      ++
        destruct es'. inversion H3.
        destruct i. 
        +++
          simpl in *. inversion H0. inversion H1.
          apply Forall2_cons. auto.
          assert (es = es'). apply nth_eq;auto. intros.
          assert (S i <> 0). lia. apply H2 in H4. simpl in H4. auto. 
          subst es. apply BEValue_forall. destruct H5. apply Forall_fun. auto.
        +++ 
          simpl in *.
          assert (a = e). assert (0 <> S i). lia. apply H2 in H4. simpl in H4. inversion H4. auto.
          apply Forall2_cons. subst a. apply BEValue. destruct H5. auto.
          apply IHes with i;auto. destruct H5. auto.
          intros. assert (S j <> S i). lia. apply H2 in H7. simpl in H7. auto. 
    +
      assert (exists ee, nth_error es'0 i = Some ee). apply forall2_exists2 with expr es ei BStepEval;auto. destruct H9 as [ee].
      assert (ei ⇓ ee). eapply forall2_corres;eauto. apply IHStep in H10.
      (* assert (Forall isValue es'0). eapply BStepEval_value_forall;eauto.  *)
      apply BENew.
      clear H4. clear H6. clear H7.
      generalize dependent es'. generalize dependent es'0. generalize dependent i. induction es;intros.
      ++
        destruct es'0. 
        destruct es'. apply Forall2_nil.
        inversion H3.
        destruct es'. inversion H8. 
        inversion H3.
      ++
        destruct es'0.
        destruct es'. inversion H3.
        inversion H8.
        destruct es'. inversion H3.
        inversion H8. 
        destruct i. 
        +++
          simpl in *. inversion H0. inversion H1. inversion H9. 
          apply Forall2_cons. auto. 
          assert (es = es'). apply nth_eq;auto. intros.
          assert (S i <> 0). lia. apply H2 in H14. simpl in H14. auto. 
          subst es'. auto. 
        +++
          inversion H8. simpl in H3. 
          simpl in *.
          assert (a = e0). assert (0 <> S i). lia. apply H2 in H20. simpl in H20. inversion H20. auto.
          apply Forall2_cons. subst a. subst e0. auto.
          apply IHes with i;auto.
          intros. assert (S j <> S i). lia. apply H2 in H22. simpl in H22. auto. 
  -
    inversion H0.
    +
    simpl in H1;contradiction.
    +
      apply IHStep in H3.
      apply BELet with ex';auto.
  -
    inversion H0. 
    +
      simpl in H1;contradiction.
    +
      assert (v = ex'). apply BStepEval_value_value;auto. subst v.
      subst ex. auto.
Qed. 

(*essential: step cases, correspond to the bstep case.*)
Lemma step_bevals: forall e e' v, e ~~> e' -> BStepEval e' v -> BStepEval e v.
Proof.
  intros. generalize dependent v.
  induction H;intros.
  -
    inversion H0.
    +
      simpl in H1;contradiction.
    +
      apply IHStep in H4.
      apply BEUnOp;auto.
  -
    assert (isValue (udelta c w pf)). apply udelta_value;auto.
    assert (udelta c w pf = v).  apply BStepEval_value_value;auto. subst v.
    apply BEUnOp;auto.
    apply BEValue;auto.
  -
    inversion H0.
    +
    simpl in H1;contradiction.
    +
      apply IHStep in H5.
      apply BEBinOp;auto.
  -
    inversion H1.
    +
    simpl in H2;contradiction.
    +
      apply IHStep in H7.
      apply BEBinOp;auto.
  -
    assert (isValue (bdelta c v1 v2 pf)). eapply bdelta_value;eauto.
    assert (bdelta c v1 v2 pf = v).  apply BStepEval_value_value;auto. subst v.
    apply BEBinOp;auto.
    apply BEValue;auto.
    apply BEValue;auto.
  -
    inversion H0.
    +
    simpl in H1;contradiction.
    +
      apply IHStep in H4.
      eapply BEInvok;eauto.
  -
    inversion H1.
    +
    simpl in H2;contradiction.
    +
      apply IHStep in H6.
      eapply BEInvok;eauto.
  -
    eapply BEInvok;eauto.
    apply BEValue;auto.
    apply BEValue;auto.
  -
    assert (ExpNew C es ⇓ ExpNew C es). apply BEValue;auto.
    assert (ei = v). apply BStepEval_value_value;auto. simpl in H2. apply forall_nth_error with es i;auto. apply Forall_fun;auto. subst ei.
    eapply BEAccess;eauto.
  -
    inversion H0.
    +
      simpl in H1;contradiction.
    +
      apply IHStep in H3.
      eapply BEAccess;eauto.
  -
    inversion H4.
    +
      simpl in H5.
      assert (isValue ei'). apply forall_nth_error with es' i;auto. apply Forall_fun;auto.
      assert (ei' ⇓ ei'). apply BEValue;auto.
      apply IHStep in H9.
      apply BENew.
      clear H4. clear H6. clear H7.
      generalize dependent es'. generalize dependent i. induction es;intros.
      ++
        destruct es'. apply Forall2_nil.
        inversion H3.
      ++
        destruct es'. inversion H3.
        destruct i. 
        +++
          simpl in *. inversion H0. inversion H1.
          apply Forall2_cons. auto.
          assert (es = es'). apply nth_eq;auto. intros.
          assert (S i <> 0). lia. apply H2 in H4. simpl in H4. auto. 
          subst es. apply BEValue_forall. destruct H5. apply Forall_fun. auto.
        +++ 
          simpl in *.
          assert (a = e). assert (0 <> S i). lia. apply H2 in H4. simpl in H4. inversion H4. auto.
          apply Forall2_cons. subst a. apply BEValue. destruct H5. auto.
          apply IHes with i;auto.
          intros. assert (S j <> S i). lia. apply H2 in H7. simpl in H7. auto. 
          destruct H5. auto.
    +
      assert (exists ee, nth_error es'0 i = Some ee). eapply forall2_exists2;eauto. destruct H9 as [ee].
      assert (ei' ⇓ ee). eapply forall2_corres;eauto. apply IHStep in H10.
      (* assert (Forall isValue es'0). eapply BStepEval_value_forall;eauto.  *)
      apply BENew.
      clear H4. clear H6. clear H7.
      generalize dependent es'. generalize dependent es'0. generalize dependent i. induction es;intros.
      ++
        destruct es'0. 
        destruct es'. apply Forall2_nil.
        inversion H3.
        destruct es'. inversion H8. 
        inversion H3.
      ++
        destruct es'0.
        destruct es'. inversion H3.
        inversion H8.
        destruct es'. inversion H3.
        inversion H8. 
        destruct i. 
        +++
          simpl in *. inversion H0. inversion H1. inversion H9. 
          apply Forall2_cons. auto. 
          assert (es = es'). apply nth_eq;auto. intros.
          assert (S i <> 0). lia. apply H2 in H14. simpl in H14. auto. 
          subst es. auto. 
        +++
          inversion H8. simpl in H3. 
          simpl in *.
          assert (a = e0). assert (0 <> S i). lia. apply H2 in H20. simpl in H20. inversion H20. auto.
          apply Forall2_cons. subst a. auto.
          apply IHes with i es';auto.
          intros. assert (S j <> S i). lia. apply H2 in H22. simpl in H22. auto. 
  -
    inversion H0.
    +
    simpl in H1;contradiction.
    +
      apply IHStep in H3.
      apply BELet with ex';auto.
  -
    apply BELet with v;auto.
    apply BEValue;auto.
Qed.
(* Lemma xxx: isValue (subBV_at j e' p) ->  *)


Lemma evals_invariant : forall e e' (p q:expr) j,
e ~~> e'-> BStepEval (subBV_at j e' p) q -> isLC e
        -> BStepEval (subBV_at j e p) q.
Proof.
  intros. rename H1 into islc.
  dependent induction H0 using BStepEval_ind'.
  - induction p using expr_ind'; simpl in H0;try contradiction. 
    +
      simpl. apply BEValue;auto.
    +
      simpl. apply BEValue;auto.
    +
      simpl. destruct (j=?i). 
      ++
        apply EvalsTo_BStepEval;auto. apply step_evals;auto.
      ++
        simpl in H0. contradiction.
    +
      simpl.
      apply BENew. 
      induction l.
      ++
        apply Forall2_nil.
      ++
        inversion H1. inversion H0. apply Forall2_cons.
        apply H4;auto.
        apply IHl;auto. 
  -
    assert ((p = BV j /\ e' = ExpUnOp c w) \/ (exists pp, ExpUnOp c pp = p)). apply eunop_subBV_invert;auto. destruct H1.
    +
      destruct H1.
      rewrite H1 in x. simpl in x. 
      simpl. case_eq (j=?j);intros.
      ++

        rewrite H1. simpl. rewrite H3.
        assert (e'⇓ udelta c v pf ). rewrite H2. eapply BEUnOp;eauto.
        apply step_bevals with e';auto.
      ++
        apply Nat.eqb_neq in H3. contradiction.
    +
    destruct H1 as [pp].
    subst p. simpl in x. inversion x.
    eapply IHBStepEval in H2;eauto.
    assert (subBV_at j e (ExpUnOp c pp) = ExpUnOp c (subBV_at j e pp)). auto. rewrite H1.
    apply BEUnOp;auto.
  -
    assert ((p = BV j /\ e' = ExpBinOp c e1 e2) \/ exists ee1 ee2, ExpBinOp c ee1 ee2 = p). apply ebinop_subBV_invert;auto. destruct H0.
    +
      destruct H0.
      simpl. case_eq (j=?j);intros.
      ++

        rewrite H0. simpl. rewrite H2.
        assert (e'⇓ bdelta c v1 v2 pf). rewrite H1. eapply BEBinOp;eauto.
        apply step_bevals with e';auto.
      ++
        apply Nat.eqb_neq in H2. contradiction.
    +
      destruct H0 as [ee1[ee2]].
      subst p. simpl in x. inversion x.
      eapply IHBStepEval1 in H1;eauto.
      eapply IHBStepEval2 in H2;eauto.
      assert (subBV_at j e (ExpBinOp c ee1 ee2) = ExpBinOp c (subBV_at j e ee1) (subBV_at j e ee2)). auto. rewrite H0.
      apply BEBinOp;auto.
  -
    assert ((p = BV j /\ e' = ExpMethodInvoc e1 m e2) \/ exists ee1 ee2, ExpMethodInvoc ee1 m ee2 = p). apply einvok_subBV_invert;auto. destruct H1.
    +
      destruct H1.
      simpl. case_eq (j=?j);intros.
      ++
        rewrite H1. simpl. rewrite H3.
        assert (e'⇓ e'0). rewrite H2. eapply BEInvok;eauto.
        apply step_bevals with e';auto.
      ++
        apply Nat.eqb_neq in H3. contradiction.
    +
      destruct H1 as [ee1[ee2]].
      subst p. simpl in x. inversion x.
      eapply IHBStepEval1 in H2;eauto.
      eapply IHBStepEval2 in H3;eauto.
      assert (subBV_at j e (ExpMethodInvoc ee1 m ee2) = (ExpMethodInvoc (subBV_at j e ee1) m (subBV_at j e ee2))). auto. rewrite H1.
      eapply BEInvok;eauto.
  -
    assert ((p = BV j /\ e' = ExpFieldAccess e0 f) \/ exists ee1,ExpFieldAccess ee1 f = p). apply eaccess_subBV_invert;auto. destruct H5.
    +
      destruct H5.
      simpl. case_eq (j=?j);intros.
      ++
        rewrite H5. simpl. rewrite H7.
        assert (e'⇓ ei). rewrite H6. eapply BEAccess;eauto.
        apply step_bevals with e';auto.
      ++
        apply Nat.eqb_neq in H7. contradiction.
    +
      destruct H5 as [ee1].
      subst p. simpl in x. inversion x.
      eapply IHBStepEval in H6;eauto.
      assert (subBV_at j e (ExpFieldAccess ee1 f) = (ExpFieldAccess  (subBV_at j e ee1) f)). auto. rewrite H5.
      eapply BEAccess;eauto.
  -
    assert ((p = BV j /\ e' = ExpNew C es) \/ exists ees, ExpNew C ees = p). apply enew_subBV_invert;auto. destruct H2.
    +
      destruct H2.
      simpl. case_eq (j=?j);intros.
      ++
        rewrite H2. simpl. rewrite H4.
        assert (e'⇓ ExpNew C es'). rewrite H3. eapply BENew;eauto.
        apply step_bevals with e';auto.
      ++
        apply Nat.eqb_neq in H4. contradiction.
    +
      destruct H2 as [ees].
      subst p. simpl in x. inversion x.
      (* eapply IHBStepEval in H6;eauto. *)
      assert (subBV_at j e (ExpNew C ees) = ExpNew C (map (subBV_at j e) ees)). auto. rewrite H2.
      eapply BENew;eauto.
      subst es. clear x. clear H1. clear H2.
      generalize dependent ees.
      induction es';intros.
      ++
        destruct ees. simpl. apply Forall2_nil.
        simpl in H0. inversion H0.
      ++
        destruct ees. simpl. inversion H0.
        inversion H0. 
        apply Forall2_cons. eapply H4;eauto.
        eapply IHes';eauto.
  -
    assert ((p = BV j /\ e' = ExpLet ex e0) \/ exists ee1 ee2,ExpLet ee1 ee2 = p). apply elet_subBV_invert;auto. destruct H0.
    +
      destruct H0.
      simpl. case_eq (j=?j);intros.
      ++
        rewrite H0. simpl. rewrite H2.
        assert (e'⇓ e'0). rewrite H1. eapply BELet;eauto.
        apply step_bevals with e';auto.
      ++
        apply Nat.eqb_neq in H2. contradiction.
    +
      destruct H0 as [ee1[ee2]].
      subst p. simpl in x. inversion x.
      eapply IHBStepEval1 in H1;eauto.
      assert (subBV ex' e0 = subBV ex' (subBV_at (j + 1) e' ee2)). rewrite H2. auto.
      assert (subBV ex' (subBV_at (j + 1) e' ee2) = subBV_at(j+1) e' (subBV ex' ee2)). unfold subBV. rewrite commute_subBV_subBV;auto. lia. apply value_lc. eapply BStepEval_value;eauto.  apply sem_lc with e;auto. rewrite H3 in H0.
      apply IHBStepEval2 in H0;auto.
      assert (subBV_at j e (ExpLet ee1 ee2) = ExpLet (subBV_at j e ee1) (subBV_at (j+1) e ee2)). simpl. auto. rewrite H4.
      eapply BELet;eauto.
      assert (subBV ex' (subBV_at (j + 1) e ee2) = subBV_at(j+1) e (subBV ex' ee2)). unfold subBV. rewrite commute_subBV_subBV;auto. lia. apply value_lc. eapply BStepEval_value;eauto. rewrite H5. 
      auto.
Qed.

Lemma evals_invariant' : forall e e' (p q:expr) j,
e ~~> e'-> BStepEval (subBV_at j e p) q -> isLC e
        -> BStepEval (subBV_at j e' p) q.
Proof.
  intros. rename H1 into islc. dependent induction H0 using BStepEval_ind'.
  - induction p using expr_ind'; simpl in H0;try contradiction. 
    +
      simpl. apply BEValue;auto.
    +
      simpl. apply BEValue;auto.
    +
      simpl. destruct (j=?i). 
      ++
        assert (~ isValue e). apply value_stuck with e';auto. contradiction.
      ++
        simpl in H0. contradiction.
    +
      simpl.
      apply BENew. 
      induction l.
      ++
        apply Forall2_nil.
      ++
        inversion H1. inversion H0. apply Forall2_cons.
        apply H4;auto.
        apply IHl;auto. 
  -
    assert ((p = (BV j) /\ e = ExpUnOp c w) \/ exists pp, ExpUnOp c pp = p). apply eunop_subBV_invert. auto. destruct H1.
    +
      destruct H1.
      simpl. case_eq (j=?j);intros.
      ++

        rewrite H1. simpl. rewrite H3.
        assert (e⇓ udelta c v pf ). rewrite H2. eapply BEUnOp;eauto.
        apply step_bevals' with e;auto.
      ++
        apply Nat.eqb_neq in H3. contradiction.
    +
      destruct H1 as [pp].
      subst p. simpl in x. inversion x.
      eapply IHBStepEval in H2;eauto.
      assert (subBV_at j e' (ExpUnOp c pp) = ExpUnOp c (subBV_at j e' pp)). auto. rewrite H1.
      apply BEUnOp;auto.
  -
    assert ((p = (BV j) /\ e = ExpBinOp c e1 e2) \/ exists ee1 ee2, ExpBinOp c ee1 ee2 = p). apply ebinop_subBV_invert;auto. destruct H0.
    +
      destruct H0.
      simpl. case_eq (j=?j);intros.
      ++

        rewrite H0. simpl. rewrite H2.
        assert (e⇓ bdelta c v1 v2 pf). rewrite H1. eapply BEBinOp;eauto.
        apply step_bevals' with e;auto.
      ++
        apply Nat.eqb_neq in H2. contradiction.
    +
      destruct H0 as [ee1[ee2]].
      subst p. simpl in x. inversion x.
      eapply IHBStepEval1 in H1;eauto.
      eapply IHBStepEval2 in H2;eauto.
      assert (subBV_at j e' (ExpBinOp c ee1 ee2) = ExpBinOp c (subBV_at j e' ee1) (subBV_at j e' ee2)). auto. rewrite H0.
      apply BEBinOp;auto.
  -
    assert ((p = (BV j) /\ e = ExpMethodInvoc e1 m e2) \/ exists ee1 ee2, ExpMethodInvoc ee1 m ee2 = p). apply einvok_subBV_invert;auto. destruct H1.
    +
      destruct H1.
      simpl. case_eq (j=?j);intros.
      ++

        rewrite H1. simpl. rewrite H3.
        assert (e⇓ e'0). rewrite H2. eapply BEInvok;eauto.
        apply step_bevals' with e;auto.
      ++
        apply Nat.eqb_neq in H3. contradiction.
    + 
      destruct H1 as [ee1[ee2]].
      subst p. simpl in x. inversion x.
      eapply IHBStepEval1 in H2;eauto.
      eapply IHBStepEval2 in H3;eauto.
      assert (subBV_at j e' (ExpMethodInvoc ee1 m ee2) = (ExpMethodInvoc (subBV_at j e' ee1) m (subBV_at j e' ee2))). auto. rewrite H1.
      eapply BEInvok;eauto.
  -
    assert ((p = (BV j) /\ e = ExpFieldAccess e0 f) \/ exists ee1,ExpFieldAccess ee1 f = p). apply eaccess_subBV_invert;auto. destruct H5.
    +
      destruct H5.
      simpl. case_eq (j=?j);intros.
      ++
        rewrite H5. simpl. rewrite H7.
        assert (e⇓ ei). rewrite H6. eapply BEAccess;eauto.
        apply step_bevals' with e;auto.
      ++
        apply Nat.eqb_neq in H7. contradiction.
    +
      destruct H5 as [ee1].
      subst p. simpl in x. inversion x.
      eapply IHBStepEval in H6;eauto.
      assert (subBV_at j e' (ExpFieldAccess ee1 f) = (ExpFieldAccess  (subBV_at j e' ee1) f)). auto. rewrite H5.
      eapply BEAccess;eauto.
  -
    assert ((p = (BV j) /\ e = ExpNew C es) \/ exists ees, ExpNew C ees = p). apply enew_subBV_invert;auto. destruct H2.
    +
      destruct H2.
      simpl. case_eq (j=?j);intros.
      ++
        rewrite H2. simpl. rewrite H4.
        assert (e⇓ ExpNew C es'). rewrite H3. eapply BENew;eauto.
        apply step_bevals' with e;auto.
      ++
        apply Nat.eqb_neq in H4. contradiction.
    +
      destruct H2 as [ees].
      subst p. simpl in x. inversion x.
      (* eapply IHBStepEval in H6;eauto. *)
      assert (subBV_at j e' (ExpNew C ees) = ExpNew C (map (subBV_at j e') ees)). auto. rewrite H2.
      eapply BENew;eauto.
      subst es. clear x. clear H1. clear H2.
      generalize dependent ees.
      induction es';intros.
      ++
        destruct ees. simpl. apply Forall2_nil.
        simpl in H0. inversion H0.
      ++
        destruct ees. simpl. inversion H0.
        inversion H0. 
        apply Forall2_cons. eapply H4;eauto.
        eapply IHes';eauto.
  -
    assert ((p = (BV j) /\ e = ExpLet ex e0) \/ exists ee1 ee2, ExpLet ee1 ee2 = p). apply elet_subBV_invert;auto. destruct H0.
    +
      destruct H0.
      simpl. case_eq (j=?j);intros.
      ++
        rewrite H0. simpl. rewrite H2.
        assert (e⇓ e'0). rewrite H1. eapply BELet;eauto.
        apply step_bevals' with e;auto.
      ++
        apply Nat.eqb_neq in H2. contradiction.
    +
      destruct H0 as [ee1[ee2]].
      subst p. simpl in x. inversion x.
      eapply IHBStepEval1 in H1;eauto.
      assert (subBV ex' e0 = subBV ex' (subBV_at (j + 1) e ee2)). rewrite H2. auto.
      assert (subBV ex' (subBV_at (j + 1) e ee2) = subBV_at(j+1) e (subBV ex' ee2)). unfold subBV. rewrite commute_subBV_subBV;auto. lia. apply value_lc. eapply BStepEval_value;eauto. rewrite H3 in H0.
      apply IHBStepEval2 in H0;auto.
      assert (subBV_at j e' (ExpLet ee1 ee2) = ExpLet (subBV_at j e' ee1) (subBV_at (j+1) e' ee2)). simpl. auto. rewrite H4.
      eapply BELet;eauto.
      assert (subBV ex' (subBV_at (j + 1) e' ee2) = subBV_at(j+1) e' (subBV ex' ee2)). unfold subBV. rewrite commute_subBV_subBV;auto. lia. apply value_lc. eapply BStepEval_value;eauto. apply sem_lc with e;auto. rewrite H5. 
      auto.
Qed.
