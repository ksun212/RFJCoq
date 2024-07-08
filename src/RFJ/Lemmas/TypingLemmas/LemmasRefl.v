Require Import Coq.Program.Equality.
Require Import List.

Require Import Definitions.Syntax.
Require Import Definitions.Names.

Require Import Definitions.Typing.
Require Import Definitions.FJTyping.
Require Import Definitions.SubDenotation.

Require Import Lemmas.BasicLemmas.LemmasSubstitution.
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasEnvironments.
Require Import Lemmas.BasicLemmas.LemmasWF.
Require Import Lemmas.BasicLemmas.LemmasWFNarrow.
Require Import Lemmas.BasicLemmas.LemmasFJTyping.
Require Import Lemmas.BasicLemmas.LemmasWFWeaken.
Require Import Lemmas.BasicLemmas.LemmasWFSubstitution.
Require Import Lemmas.TypingLemmas.LemmasTyping.
Require Import Lemmas.LogicalLemmas.LemmasSImp.
 

(*---------------Subtyping is Reflexive---------------*)

Lemma sub_refl : forall (g:env) (t:type),
    WFtype g t -> Subtype g t t.
Proof. intros g t p_g_t; induction p_g_t.
  - apply SBase with (binds g); intros; auto; apply IRefl.
  - apply SBase with (binds g); intros; auto; apply IRefl.
  Qed.

Lemma sub_refl_forall : forall (g:env) (ts:[type]),
Forall (WFtype g) ts -> Forall2 (Subtype g) ts ts.
Proof.
  intros. induction ts.
  -
    apply Forall2_nil.
  -
    inversion H.
    apply Forall2_cons. 
    + apply sub_refl. auto.
    + apply IHts. auto.
Qed.



