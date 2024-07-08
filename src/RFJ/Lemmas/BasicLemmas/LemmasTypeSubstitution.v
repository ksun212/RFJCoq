Require Import List.
Require Import Lia.
Require Import Coq.Program.Equality.


Require Import Definitions.Syntax.
Require Import Definitions.Names.
Require Import Definitions.FJTyping.

Require Import Definitions.Typing.
Require Import Definitions.SubDenotation.
Require Import Definitions.Semantics.

Require Import Definitions.CTSanity.

Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasFJTyping.
Require Import Lemmas.BasicLemmas.LemmasSubstitution.
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasEnvironments.
Require Import Lemmas.BasicLemmas.LemmasWF.
Require Import Lemmas.BasicLemmas.LemmasWFNarrow.
Require Import Lemmas.BasicLemmas.LemmasFJWeaken.
Require Import Lemmas.BasicLemmas.LemmasWFWeaken.
Require Import Lemmas.BasicLemmas.LemmasSemantics.
Require Import Lemmas.BasicLemmas.LemmasBigStepSemantics.
Require Import Lemmas.BasicLemmas.LemmasCTBasics.

Require Import Lemmas.TypingLemmas.LemmasWeakenTyp.
Require Import Lemmas.BasicLemmas.LemmasWFSubstitution.
Require Import Lemmas.TypingLemmas.LemmasTyping.
Require Import Lemmas.LogicalLemmas.LemmasCSubst.
Require Import Lemmas.LogicalLemmas.LemmasDenotes.
Require Import Lemmas.LogicalLemmas.LemmasSImp.
Require Import Lemmas.LogicalLemmas.LemmasCSubstSemantics.

(*---------------Type Substitution Invariants---------------*)

Lemma evals_invariant_ : forall e e' (p:expr) j,
isLC e -> e ~~> e'-> EvalsTo (subBV_at j e' p) (Bc true) 
        -> EvalsTo (subBV_at j e p) (Bc true).
Proof.
  intros.
  apply BStepEval_EvalsTo.
  apply evals_invariant with e';auto.
  apply EvalsTo_BStepEval;simpl;auto.
Qed.

Lemma evals_invariant_eval : forall e e' (p:expr) j,
EvalsTo e e'-> EvalsTo (subBV_at j e' p) (Bc true) -> isLC e 
        -> EvalsTo (subBV_at j e p) (Bc true).
Proof.
  intros.
  induction H.
  -
    auto.
  -
    assert (isLC e2). apply sem_lc with e1;auto.
    eapply evals_invariant_ in H;eauto.
Qed.

Lemma evals_invariant_peval : forall e e' (p:preds) j,
EvalsTo e e'-> PEvalsTrue (psubBV_at j e' p) -> isLC e 
        -> PEvalsTrue (psubBV_at j e p).
Proof.
  intros.
  induction p.
  -
    auto.
  -
    inversion H0. simpl. apply PECons.
    apply evals_invariant_eval with e';auto.
    apply IHp;auto.
Qed.
Lemma IEvals2' : forall (g:env) (p:expr) (ps:preds) e e' j,
e ~~> e' -> isLC e -> LImplies g (PCons (subBV_at j e' p) ps) (PCons (subBV_at j e p) ps).
Proof. intros. rename H0 into islc.
    apply SImp ; intros.
    rewrite cpsubst_pcons in H1.
    rewrite cpsubst_pcons; inversion H1.
    apply PECons;auto.
    rewrite csubst_subBV_at in H4.
    rewrite csubst_subBV_at.
    apply evals_invariant_ with (csubst th e');auto.
    apply csubst_lc;auto. 
    apply denotesenv_substitutable with g; auto.
    apply csubst_step;auto.
    apply denotesenv_loc_closed with g;auto.
    apply denotesenv_substitutable with g; auto.
    apply denotesenv_loc_closed with g;auto.
    apply denotesenv_substitutable with g; auto.
    apply denotesenv_loc_closed with g;auto.
    apply denotesenv_substitutable with g; auto.
Qed. 

Lemma evals_invariant'_ : forall e e' (p:expr) j,
e ~~> e'-> EvalsTo (subBV_at j e p) (Bc true) -> isLC e 
        -> EvalsTo (subBV_at j e' p) (Bc true).
Proof.
  intros. 
  apply BStepEval_EvalsTo.
  apply evals_invariant' with e;auto.
  apply EvalsTo_BStepEval;simpl;auto.
Qed.


Lemma evals_invariant'_eval : forall e e' (p:expr) j,
EvalsTo e e'-> EvalsTo (subBV_at j e p) (Bc true) -> isLC e 
        -> EvalsTo (subBV_at j e' p) (Bc true).
Proof.
  intros.
  induction H.
  -
    auto.
  -
    assert (isLC e2). apply sem_lc with e1;auto.
    eapply evals_invariant'_ in H;eauto.
Qed.

Lemma evals_invariant'_peval : forall e e' (p:preds) j,
EvalsTo e e'-> PEvalsTrue (psubBV_at j e p) -> isLC e 
        -> PEvalsTrue (psubBV_at j e' p).
Proof.
  intros.
  induction p.
  -
    auto.
  -
    inversion H0. simpl. apply PECons.
    apply evals_invariant'_eval with e;auto.
    apply IHp;auto.
Qed.



Lemma IEvals2'' : forall (g:env) (p p':expr) (ps:preds) e e' j,
e ~~> e' -> isLC e -> LImplies g (PCons (subBV_at j e p) ps) (PCons (subBV_at j e' p) ps).
Proof. intros.
    rename H0 into islc.
    apply SImp ; intros.
    rewrite cpsubst_pcons in H1.
    rewrite cpsubst_pcons; inversion H1.
    apply PECons;auto.
    rewrite csubst_subBV_at in H4.
    rewrite csubst_subBV_at.
    apply evals_invariant'_ with (csubst th e);auto.
    apply csubst_step;auto.
    apply denotesenv_loc_closed with g;auto.
    apply denotesenv_substitutable with g; auto.
    apply csubst_lc;auto.
    apply denotesenv_substitutable with g; auto.
    apply denotesenv_loc_closed with g;auto.
    apply denotesenv_substitutable with g; auto.
    apply denotesenv_loc_closed with g;auto.
    apply denotesenv_substitutable with g; auto.
Qed. 




Lemma ICons3: forall g p qs qs', LImplies g qs qs' -> LImplies g (PCons p qs) (PCons p qs').
Proof.
intros.
apply SImp. intros.
rewrite cpsubst_pcons in *.
inversion H1. inversion H.
apply PECons;auto.
Qed.
Lemma tsubBV_invariant : forall (g:env) (e' e:expr) t j,
   e ~~> e' -> isLC e' -> isLC e-> Subtype g (tsubBV_at j e' t) (tsubBV_at j e t).
Proof. 
  intros.
  unfold tsubBV. destruct t. simpl. 
  apply SBase with (binds g); 
  intros;auto. unfold unbindP.
  induction ps. simpl. apply IFaith.
  simpl. 
  assert (LImplies (Cons y (TRefn b PEmpty) g)
  (PCons (open_at 0 y (subBV_at (j+1) e' p)) (openP_at 0 y (psubBV_at (j+1) e' ps)))
  (PCons (open_at 0 y (subBV_at (j+1) e p)) (openP_at 0 y (psubBV_at (j+1) e' ps)))).
  assert (open_at 0 y (subBV_at (j+1) e' p) = subBV_at (j+1) e' (open_at 0 y p)). rewrite commute_open_at_subBV;auto. lia. rewrite H3.
  assert (open_at 0 y (subBV_at (j+1) e p) = subBV_at (j+1) e (open_at 0 y p)). rewrite commute_open_at_subBV;auto. lia. rewrite H4.
  apply IEvals2';auto. 
  apply ITrans with (PCons (open_at 0 y (subBV_at (j+1) e p)) (openP_at 0 y (psubBV_at (j+1) e' ps)));auto.
  apply ICons3;auto.
Qed.

Lemma tsubBV_invariant_forall : forall (g:env) (e' e:expr) ts j,
   e ~~> e' -> isLC e' -> isLC e-> Forall2 (Subtype g) (map (tsubBV_at j e') ts) (map (tsubBV_at j e) ts).
Proof. 
  intros. induction ts.
  -
    simpl. apply Forall2_nil.
  -
    apply Forall2_cons.
    apply tsubBV_invariant;auto.
    apply IHts;auto.
Qed.

Lemma tsubBV_invariant' : forall (g:env) (e' e:expr) t j,
   e ~~> e' -> isLC e' -> isLC e-> Subtype g (tsubBV_at j e t) (tsubBV_at j e' t).
Proof. 
  intros.
  unfold tsubBV. destruct t. simpl. 
  apply SBase with (binds g); 
  intros;auto. unfold unbindP.
  induction ps. simpl. apply IFaith.
  simpl. 
  assert (LImplies (Cons y (TRefn b PEmpty) g)
  (PCons (open_at 0 y (subBV_at (j+1) e p)) (openP_at 0 y (psubBV_at (j+1) e ps)))
  (PCons (open_at 0 y (subBV_at (j+1) e' p)) (openP_at 0 y (psubBV_at (j+1) e ps)))).
  assert (open_at 0 y (subBV_at (j+1) e' p) = subBV_at (j+1) e' (open_at 0 y p)). rewrite commute_open_at_subBV;auto. lia. rewrite H3.
  assert (open_at 0 y (subBV_at (j+1) e p) = subBV_at (j+1) e (open_at 0 y p)). rewrite commute_open_at_subBV;auto. lia. rewrite H4.
  apply IEvals2'';auto. 
  apply ITrans with (PCons (open_at 0 y (subBV_at (j+1) e' p)) (openP_at 0 y (psubBV_at (j+1) e ps)));auto.
  apply ICons3;auto.
Qed.


Lemma tsubBV_invariant'_forall : forall (g:env) (e' e:expr) ts j,
   e ~~> e' -> isLC e' -> isLC e-> Forall2 (Subtype g) (map (tsubBV_at j e) ts) (map (tsubBV_at j e') ts).
Proof. 
  intros. induction ts.
  -
    simpl. apply Forall2_nil.
  -
    apply Forall2_cons.
    apply tsubBV_invariant';auto.
    apply IHts;auto.
Qed.


