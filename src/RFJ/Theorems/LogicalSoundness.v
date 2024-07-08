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


Require Import Lemmas.BasicLemmas.LemmasSubstitution.
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasEnvironments.
Require Import Lemmas.LogicalLemmas.LemmasSImp.
Require Import Lemmas.BasicLemmas.LemmasTypeSubstitution.
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.TypingLemmas.LemmasTyping.
Require Import Lemmas.LogicalLemmas.LemmasDenotesTyping.
Require Import Lemmas.LogicalLemmas.LemmasCSubst.
Require Import Lemmas.LogicalLemmas.LemmasDenotes.
Require Import Lemmas.BasicLemmas.LemmasSemantics.
Require Import Lemmas.TypingLemmas.Closing_Substitution.
Require Import Lemmas.TypingLemmas.Preservation_Progress.
Require Import Theorems.TypeSoundness.

Theorem typing_denotation_closed: forall (e e':expr) (t:type),
  EvalsTo e e' -> Hastype Empty e t -> isValue e' -> Denotes t e'.
Proof.
  intros. apply many_preservation with e e' t in H0;auto.
  assert (DenotesEnv Empty CEmpty). apply DEmp.
  assert (ctsubst CEmpty t = t). auto.
  rewrite <- H3.
  apply typing_denotes with Empty;auto.
Qed.
Theorem logical_soundness_closed: forall (e:expr) (t:type) b ps,
  Hastype Empty e (TRefn b ps) -> (exists e', EvalsTo e e' /\ isValue e') -> PEvalsTrue (psubBV e ps).
Proof.
  intros. destruct H0 as [v]. destruct H0.
  apply typing_denotation_closed with e v (TRefn b ps) in H as HH;auto.
  apply denotes_refn in HH.
  apply evals_invariant_peval with v;auto. eapply typ_islc;eauto.
Qed.

Theorem typing_denotation: forall (e e':expr) (t:type) g th,
  Hastype g e t -> WFEnv g -> DenotesEnv g th -> EvalsTo (csubst th e) e' -> isValue e' -> Denotes (ctsubst th t) e'.
Proof.
  intros. 
  assert (Hastype Empty (csubst th e) (ctsubst th t)). apply closing_substitution with g;auto.
  apply typing_denotation_closed with (csubst th e) e' (ctsubst th t) in H2;auto.
Qed.

Theorem logical_soundness: forall (e e':expr) (t:type) g b ps,
  Hastype g e (TRefn b ps) -> WFEnv g -> Terminating g e -> LEntails g (psubBV e ps).
Proof.
  intros. unfold LEntails. intros. unfold Terminating in H1. apply H1 in H2 as H3. destruct H3 as [v]. destruct H3.
  rewrite cpsubst_psubBV;auto. 
  eapply typing_denotation in H as xx;eauto.
  rewrite ctsubst_refn in xx. apply denotes_refn in xx. auto.
  apply evals_invariant_peval with v;auto. apply csubst_lc;auto. eapply typ_islc;eauto.
  apply denotesenv_substitutable with g;auto.
  apply denotesenv_loc_closed with g;auto.
  apply denotesenv_substitutable with g;auto.
Qed.
