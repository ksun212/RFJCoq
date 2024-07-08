Require Import Arith.
Require Import Lists.ListSet.
Require Import Lists.
Require Import Program.
Require Import ZArith.

Require Import Definitions.Syntax.
Require Import Definitions.Names.
Require Import Definitions.Semantics.
Require Import Definitions.FJTyping.

Require Import Definitions.Typing.

Require Import Definitions.SubDenotation.

Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasFJTyping.
Require Import Lemmas.BasicLemmas.LemmasSubstitution.
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasEnvironments.
Require Import Lemmas.BasicLemmas.LemmasWF.
Require Import Lemmas.BasicLemmas.LemmasWFNarrow.
Require Import Lemmas.BasicLemmas.LemmasSemantics.
Require Import Lemmas.LogicalLemmas.LemmasCSubst.
Require Import Lemmas.BasicLemmas.LemmasPrimitivesBasics.




(*---------------Basic Properties of Type Denotation---------------*)

Lemma denotes_refn: forall b ps v_x, Denotes (TRefn b ps) v_x -> PEvalsTrue (psubBV v_x ps).
Proof.
  intros. dependent induction H;auto.
  apply IHDenotes with b1;auto.
Qed.

Lemma forall_erase: forall Us v, ((map erase Us) = (map erase (map (tsubBV v) Us))).
Proof.
  intros.
  induction Us.
  simpl. reflexivity.
  simpl. f_equal.
  rewrite <-erase_tsubBV_at with 0  v a. reflexivity.
  auto.
Qed.
Lemma aux1: forall es Fs v, Forall2 (fun (t : type) (v : expr) => HasFJtype FEmpty v (erase t))
(map (tsubBV v) (map ReffieldType Fs)) es -> Forall2 (fun (t : fjtype) (v : expr) => HasFJtype FEmpty v t)
(map erase (map (tsubBV v) (map ReffieldType Fs))) es.
Proof.
  intros. generalize dependent es. induction Fs;intros.
  - 
  destruct es. apply Forall2_nil. inversion H.
  -
  destruct es. inversion H. inversion H. apply Forall2_cons.
  apply H3.
  apply IHFs;auto.
Qed.
Lemma den_hasfjtype : forall (v:expr) (t:type),
    Denotes t v -> HasFJtype FEmpty v (erase t).
Proof.
  intros; destruct t. induction H using Denotes_ind';simpl;auto.
  -
  apply FTNew with Fs (map erase (map ReffieldType Fs))  (map ReffieldName Fs);auto.
  clear H1. clear H0. clear H2. clear H.
  apply aux1 in H3.
  generalize dependent es. induction Fs;intros.
  +
    destruct es. apply Forall2_nil. inversion H3.
  + destruct es. inversion H3.
    inversion H3. 
    apply Forall2_cons. auto. 
    rewrite erase_tsubBV in H2. auto.
    apply IHFs;auto. rewrite <- forall_erase in *.  auto.
  -
  simpl in IHDenotes.
  apply FTSub with b1;auto.
Qed.
Lemma invert_new_denotes: forall ps c l t, Denotes (TRefn t ps) (ExpNew c l) -> FJSubtype (TNom (TClass c)) t /\ exists Fs, Reffields c Fs /\ Forall2 Denotes (map (tsubBV (ExpNew c l)) (map ReffieldType Fs)) l.
Proof.
  intros.
  dependent induction H. 
  constructor. apply SubBClass. apply SubCRefl. exists Fs. constructor;auto.
  assert (TRefn b1 ps = TRefn b1 ps). auto. apply IHDenotes with ps c l b1 in H1;auto. destruct H1. 
  constructor. apply FSubtype_trans with b1;auto.
  auto.
Qed.


Lemma den_nofv : forall (v:expr) (t:type),
    Denotes t v -> fv v = empty.
Proof. intros v t den_t_v; apply den_hasfjtype in den_t_v.
  apply fv_subset_bindsFJ in den_t_v; simpl in den_t_v.
  apply no_elem_empty; intro x;
  apply not_elem_subset with empty; auto. Qed.


Lemma denotesenv_loc_closed : forall (g:env) (th:csub), 
    DenotesEnv g th -> loc_closed th.
Proof. intros; induction H; simpl; try split; trivial.
  - (* CCons *) apply den_hasfjtype in H1; 
    apply fjtyp_islc in H1; assumption.
  Qed.

Lemma denotesenv_closed : forall (g:env) (th:csub), 
    DenotesEnv g th -> closed th.
Proof. intros; induction H; simpl; trivial.
  - (* CCons *) apply den_hasfjtype in H1;
    apply fv_subset_bindsFJ in H1; repeat split;
    try apply IHDenotesEnv; apply no_elem_empty; intuition.
  Qed.

Lemma bound_in_denotessenv : 
  forall (x:vname) (t:type) (g:env) (th:csub),
    DenotesEnv g th -> bound_in x t g -> WFEnv g
        -> Denotes (ctsubst th t) (csubst th (FV x)).
Proof. intros x t; induction g.
  - simpl; intuition.
  - intros; inversion H;   subst x1 t1 g0;
    try apply H1;  simpl in H0. destruct H0.
    * (* x = x0 *) destruct H0; subst x0 t0;
      inversion H1; subst x0 t0 g0.
      simpl; destruct (x =? x) eqn:X;
      try apply Nat.eqb_neq in X; try unfold not in X; 
      try contradiction.
      assert (~Elem x (free t)). apply free_bound_in_env with g;auto.
      rewrite tsubFV_notin;auto.
      rewrite csubst_nofv. auto. eapply den_nofv;eauto.
    * 
      simpl. destruct (x0 =? x) eqn:X. assert (x0 = x). apply Nat.eqb_eq. auto. subst x0. apply boundin_inenv in H0.  unfold in_env in H7. contradiction. 
      assert (x0 <> x). apply Nat.eqb_neq. auto.  
      inversion H1. apply boundin_wfenv_wftype in H0 as p_g_t;auto. assert (~Elem x0 (free t)).  apply free_bound_in_env with g;auto.
      rewrite tsubFV_notin;auto.
Qed.

(*left-distributive of ctsubst over self*)
Lemma denotes_ctsubst_self : 
  forall (th:csub) (t:type) (v v':expr),
    closed th -> loc_closed th -> substitutable th -> uniqueC th 
        -> isLC v
        -> Denotes (self (ctsubst th t) (csubst th v)) v'
        -> Denotes (ctsubst th (self t v)) v'.
Proof.
  induction th.
  intros. simpl in *. auto.
  intros. simpl. rewrite tsubFV_self. inversion H. inversion H0. inversion H1. inversion H2. apply IHth;auto.
  apply islc_at_subFV; auto.
Qed.


Lemma den_bools : forall (t:type) (v:expr),
    isValue v -> erase t = TBool -> Denotes t v -> isBool v.
Proof. 
  intros; apply den_hasfjtype in H1;
  apply bool_values; try rewrite <- H0; assumption. 
Qed.

Lemma den_ints : forall (t:type) (v:expr),
    isValue v -> erase t = TInt -> Denotes t v -> isInt v.
Proof. 
  intros; apply den_hasfjtype in H1;
  apply int_values; try rewrite <- H0; assumption. 
Qed.

Lemma den_class : forall (t:type) (v:expr) c,
isValue v -> erase t = (TNom (TClass c)) -> Denotes t v -> isClass c v.
Proof. 
  intros; apply den_hasfjtype in H1.
  apply lemma_class_values; try rewrite <- H0; assumption. 
Qed.


Lemma den_tybc : forall (b:bool), Denotes (tybc b) (Bc b).
Proof. 
  intros.
  unfold tybc.
  apply DenotesBool;simpl;auto.
  unfold psubBV. simpl.   
  apply PECons. assert (Bool.eqb b b = true). destruct b; simpl; auto. rewrite <- H.
  assert (Bool.eqb b b = (veq (Bc b) (Bc b))). simpl. auto. rewrite H0. apply lemma_eqv_semantics;simpl;auto.
  apply PEEmp. 
Qed. 

Lemma den_tyic : forall (n:Z), Denotes (tyic n) (Ic n).
Proof. 
  intros.
  unfold tybc.
  apply DenotesInt;simpl;auto.
  unfold psubBV. simpl.   
  apply PECons. assert ((veq (Ic n) (Ic n)) = true). apply veq_eq;simpl;auto. rewrite <- H.  apply lemma_eqv_semantics;simpl;auto.
  apply PEEmp. 
Qed.


Lemma denotesselfify : forall (t:type) (v:expr),
    isValue v -> Denotes t v -> Denotes (self t v) v.
Proof. intros. 
    destruct v; simpl in H; try contradiction.
    -
        dependent induction H0.
        +
        apply DenotesBool;auto.
            apply PECons.
            *   
                unfold eqlPred. case_eq (0=?0).
                **   
                    intro. assert (veq (Bc b) (Bc b) = true); try apply veq_eq;auto. try rewrite <- H2. apply lemma_eqv_semantics;auto.
                **   
                    intros; try apply Nat.eqb_neq in H1; try contradiction.
            *  
                unfold psubBV in H0. auto.
        +
        apply DenotesUpcast with b1;auto.
        apply IHDenotes;auto.
    -
        dependent induction H0. 
        +
        apply DenotesInt;auto.
            apply PECons.
            *   
                unfold eqlPred.
                case_eq (0=?0).
                **   
                    intro. assert (veq (Ic n) (Ic n) = true); try apply veq_eq;auto. try rewrite <- H2. apply lemma_eqv_semantics;auto.
                **   
                    intros; try apply Nat.eqb_neq in H1; try contradiction.
            *  
                unfold psubBV in H0. auto.
        +
        apply DenotesUpcast with b1;auto.
        apply IHDenotes;auto.
    -
        dependent induction H0. 
        +
        apply DenotesClass with Fs;auto. 
            apply PECons.
            *   
                unfold eqlPred. case_eq (0=?0).
                **   
                    intro. assert (subBV_at 0 (ExpNew c l)  (ExpNew c l)  = (ExpNew c l) ); try apply subBV_at_lc_at with 0;auto; try apply value_lc; auto. unfold subBV_at in H5. rewrite H5. 
                    assert (veq (ExpNew c l) (ExpNew c l) = true); try apply veq_eq;auto. try rewrite <- H6. apply lemma_eqv_semantics;auto.
                **   
                    intros; try apply Nat.eqb_neq in H4; try contradiction.
            *  
                unfold psubBV in H1. auto.
        +
        apply DenotesUpcast with b1;auto.
        apply IHDenotes;auto.
Qed.