Require Import Lists.
Require Import Crush.


Require Import Definitions.Syntax.
Require Import Definitions.Names.
Require Import Definitions.Semantics.
Require Import Definitions.FJTyping.


Require Import Definitions.SubDenotation.
Require Import Definitions.Typing.

Require Import Lemmas.BasicLemmas.LemmasFJTyping.
Require Import Lemmas.BasicLemmas.LemmasSubstitution.
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasEnvironments.
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasCTBasics.
Require Import Lemmas.LogicalLemmas.LemmasCSubst.

(*---------------Lemmas Connecting CSubst and Small-step Semantics---------------*)

Lemma csubst_isCompat : forall (c:UnOp) (w:expr) (th:csub),
    isCompat c w -> csubst th w = w.
Proof. intros; inversion H;
  try rewrite csubst_bc; try rewrite csubst_ic;
  reflexivity. Qed.
Lemma csubst_udelta : 
forall (c:UnOp) (w:expr) (pf:isCompat c w) (th:csub),
  csubst th (udelta c w pf) = udelta c w pf.
Proof. intros. destruct pf.
  simpl. case_eq b;
  intros; rewrite csubst_bc;auto. Qed. 
Lemma csubst_isCompat2 : forall (c:BinOp) (w1 w2:expr) (th:csub),
  isCompat2 c w1 w2 -> csubst th w1 = w1.
Proof. intros; inversion H;
try rewrite csubst_bc; try rewrite csubst_ic; try reflexivity. apply csubst_nofv. apply value_closed. auto.
Qed.
Lemma csubst_isCompat2' : forall (c:BinOp) (w1 w2:expr) (th:csub),
  isCompat2 c w1 w2 -> csubst th w2 = w2.
Proof. intros; inversion H;
try rewrite csubst_bc; try rewrite csubst_ic; try reflexivity. apply csubst_nofv. apply value_closed. auto.
Qed.
(* rewrite csubst_value. Qed. *)
Lemma csubst_bdelta : 
forall (c:BinOp) (w1 w2:expr) (pf:isCompat2 c w1 w2) (th:csub),
  csubst th (bdelta c w1 w2 pf) = bdelta c w1 w2 pf.
Proof. intros. destruct pf.
  - simpl. rewrite csubst_bc. auto.  
  - simpl. rewrite csubst_bc. auto.
  - simpl. rewrite csubst_bc. auto.
Qed.    

Lemma csubst_step : forall (th:csub) (p q:expr),
    loc_closed th -> substitutable th -> Step p q 
        -> Step (csubst th p) (csubst th q).
Proof. intros th p q Hlc Hth H; induction H.
  - repeat rewrite csubst_unop. apply EUnOp1;auto.
  - repeat rewrite csubst_unop. rewrite csubst_udelta. rewrite csubst_isCompat with c w th;auto.  apply EUnOp2;auto.
  - repeat rewrite csubst_binop. apply EBinOp1;auto.
  - repeat rewrite csubst_binop. apply EBinOp2;auto. apply csubst_value;auto.
  - repeat rewrite csubst_binop. rewrite csubst_bdelta. rewrite csubst_isCompat2 with c v1 v2 th;auto. rewrite csubst_isCompat2' with c v1 v2 th;auto. apply EBinOp3;auto.
  - repeat rewrite csubst_invok. apply Refc_Invok1;auto.
  - repeat rewrite csubst_invok. apply Refc_Invok2;auto. apply csubst_value;auto.
  - rewrite csubst_invok.  
    assert (csubst th (ExpNew C es) = ExpNew C es).  apply csubst_nofv. apply value_closed. auto. rewrite H2. 
    assert (csubst th v = v).  apply csubst_nofv. apply value_closed. auto. rewrite H3.
    assert (csubst th (subBV_at 1 (ExpNew C es) (subBV v e)) = (subBV_at 1 (ExpNew C es) (subBV v e))). apply csubst_nofv. eapply mbody_subBv_no_fv;eauto. rewrite H4. 
    apply Refc_Invok3;auto.
  - rewrite csubst_access. 
    assert (csubst th (ExpNew C es) = ExpNew C es).  apply csubst_nofv. apply value_closed. auto. rewrite H3.
    assert (csubst th ei = ei).  apply csubst_nofv. apply value_closed. apply forall_corres with es i;auto. simpl in H2. apply Forall_fun. auto. rewrite H4.
    apply Refc_Field with Fs i;auto.
  - repeat rewrite csubst_access. apply RefRC_Field;auto.
  - repeat rewrite csubst_new. eapply RefRC_New_Arg. apply IHStep. apply f_morp. apply H0. apply f_morp. apply H1. 
    intros. apply H2 in H4. rewrite nth_error_map. rewrite nth_error_map. rewrite H4. auto. rewrite map_length. rewrite map_length. auto. 
  - repeat rewrite csubst_let. apply ELet;auto.
  - rewrite csubst_let; rewrite csubst_subBV.
    apply ELetV. apply csubst_value. assumption. assumption. assumption. assumption.
  Qed.

Lemma csubst_evals : forall (th:csub) (p q:expr),
    loc_closed th -> substitutable th -> EvalsTo p q 
        -> EvalsTo (csubst th p) (csubst th q).
Proof. intros th p q H1 H2 Hpq; induction Hpq.
  - apply Refl.
  - apply AddStep with (csubst th e2); try apply csubst_step;
    assumption. Qed. 