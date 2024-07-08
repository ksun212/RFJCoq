Require Import Relations Decidable.
Require Import Forall2.
Require Import Lists.
Require Import ZArith.

Require Import RFJ.Utils.Referable.
Require Import RFJ.Utils.

Require Export Definitions.Names.
Require Export Definitions.Syntax.
Require Import Definitions.FJTyping.

Require Import Definitions.Semantics.
Require Import Definitions.SubDenotation.


Require Import Lemmas.BasicLemmas.LemmasFJTyping.
Require Import Lemmas.BasicLemmas.LemmasEnvironments.
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasSubstitution.
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasWF.
Require Import Lemmas.BasicLemmas.LemmasWFNarrow.
Require Import Lemmas.LogicalLemmas.LemmasCSubst.

(*---------------Basic Properties of SIMP---------------*)

Lemma IRefl   : forall (g:env) (ps:preds), LImplies g ps ps. 
Proof. intros. apply SImp; trivial.
Qed.

Lemma ITrans  : forall (g:env) (ps:preds) (qs:preds) (rs:preds),
LImplies g ps qs -> LImplies g qs rs -> LImplies g ps rs.
Proof. intros.
apply SImp; inversion H; inversion H0.
intros; apply H5; try apply H1; apply H9 || apply H10.
Qed.
Lemma IFaith  : forall (g:env) (ps:preds), LImplies g ps PEmpty.
Proof. intros.
  apply SImp; intros.
  rewrite cpsubst_pempty. apply PEEmp.
Qed.
Lemma lemma_strengthen_semantics : forall (ps qs:preds),
    PEvalsTrue ps -> PEvalsTrue qs -> PEvalsTrue (strengthen ps qs).
Proof. induction ps; simpl; trivial; intros.
  apply PECons; inversion H; try apply IHps; assumption. Qed.

Lemma lemma_semantics_strengthen : forall (ps qs:preds),
    PEvalsTrue (strengthen ps qs) -> PEvalsTrue ps /\ PEvalsTrue qs.
Proof. induction ps; simpl; intros; split;
  try apply PEEmp; try apply PECons; try apply H;
  inversion H; apply IHps in H3; destruct H3; assumption. Qed.  
Lemma IConj   : forall (g:env) (ps:preds) (qs:preds) (rs:preds),
LImplies g ps qs -> LImplies g ps rs -> LImplies g ps (strengthen qs rs).
Proof. intros.
apply SImp; intros;
    rewrite cpsubst_strengthen.
    apply lemma_strengthen_semantics;
    inversion H; inversion H0;
    apply H3 || apply H7; trivial.
Qed.
Lemma ICons1  : forall (g:env) (p:expr) (ps:preds), LImplies g (PCons p ps) (PCons p PEmpty).
Proof. intros. 
apply SImp; intros;
    rewrite cpsubst_pcons;
    rewrite cpsubst_pcons in H0;
    rewrite cpsubst_pempty;
    inversion H0; apply PECons; try apply PEEmp; trivial.
Qed.
Lemma ICons2  : forall (g:env) (p:expr) (ps:preds), LImplies g (PCons p ps) ps.
Proof. intros. 
apply SImp; intros;
    rewrite cpsubst_pcons in H0;
    inversion H0; apply H4.
Qed.
Lemma IRepeat : forall (g:env) (p:expr) (ps:preds), LImplies g (PCons p ps) (PCons p (PCons p ps)).
Proof. intros.
apply SImp; intro th;
    repeat rewrite cpsubst_pcons; intros;
    inversion H0; repeat apply PECons; trivial.
Qed.
