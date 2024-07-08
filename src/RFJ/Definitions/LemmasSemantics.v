Require Import Definitions.Syntax. 
Require Import Definitions.Names.
Require Import Definitions.Semantics.
Require Import Definitions.FJTyping.
(* Require Import Definitions.CTSanity. *)

Require Import Lemmas.BasicLemmas.LemmasFJTyping.
Require Import Lemmas.BasicLemmas.LemmasSubstitution.
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasEnvironments.
Require Import Definitions.WellFormedness.
(* Require Import Lemmas.BasicLemmas.LemmasWellFormedness. *)
Require Import Lemmas.BasicLemmas.LemmasCT.
Require Import Definitions.Semantics.
(* Require Import Lemmas.BasicLemmas.LemmasCTTyping. *)
Require Import Referable.
Require Import Lia.
Require Import Arith.
Require Import ZArith.
Require Import Lists.

Lemma lemma_evals_trans : forall (e1 e2 e3 : expr),
EvalsTo e1 e2 -> EvalsTo e2 e3 -> EvalsTo e1 e3.
Proof. intros e1 e3 e4 ev_e1e3 ev_e3e4. induction ev_e1e3 as [e|_e1 e2 _e3 st_e1e2 ev_e2e3 IH]. 
- apply ev_e3e4.
- apply IH in ev_e3e4. apply AddStep with e2; assumption. Qed.

Lemma step_evals : forall (e e' : expr), 
Step e e' -> EvalsTo e e'.
Proof. intros e e' st_ee'. apply AddStep with e'. assumption. apply Refl. Qed.

Lemma lemma_add_step_after : forall (e e' e'' : expr),
EvalsTo e e'  -> Step e' e'' -> EvalsTo e e''.
Proof. intros e e' e'' ev_e_e' st_e'_e''. induction ev_e_e' as [e|e e1 e' st_ee1 ev_e1e' IH].
- apply AddStep with e''.  apply st_e'_e''.  apply Refl.
- apply IH in st_e'_e'' as ev_e1_e''. apply AddStep with e1; assumption. Qed.


Theorem value_stuck : forall (e e' : expr), 
    Step e e' -> ~ (isValue e).
Proof. intros e e' st_e_e'. induction st_e_e'; simpl; unfold not; trivial.
intros.
unfold not in IHst_e_e'.
assert (Forall isValue es).
apply Forall_fix.
apply H3.
assert (isValue ei).
eapply forall_nth_error.
apply H4.
apply H.
apply IHst_e_e' in H5.
contradiction.
Qed.
Theorem value_stuck2 : forall (e e' : expr) i, 
    Step e e' -> ~ (e = (BV i)).
Proof. intros e e' st_e_e'. induction st_e_e'; simpl; unfold not; trivial.
intros. rewrite H0 in H. inversion H.
intros. rewrite H0 in H. inversion H.
Qed.

Lemma unop_many: forall w v c, 
    EvalsTo w v -> EvalsTo (ExpUnOp c w) (ExpUnOp c v).
Proof.
  intros. induction H.
  - 
    apply Refl.
  -
    apply AddStep with (ExpUnOp c e2).
    apply EUnOp1;auto.
    apply IHEvalsTo;auto.
Qed.

Lemma binop_many: forall e1 e2 v1 c,
    EvalsTo e1 v1 -> EvalsTo (ExpBinOp c e1 e2) (ExpBinOp c v1 e2).
Proof.
  intros. induction H.
  - 
    apply Refl.
  -
    apply AddStep with (ExpBinOp c e0 e2).
    apply EBinOp1;auto.
    apply IHEvalsTo;auto.
Qed.

Lemma binop_many': forall e2 v2 v1 c,
    EvalsTo e2 v2 -> isValue v1 -> EvalsTo (ExpBinOp c v1 e2) (ExpBinOp c v1 v2).
Proof.
  intros. induction H.
  - 
    apply Refl.
  -
    apply AddStep with (ExpBinOp c v1 e2).
    apply EBinOp2;auto.
    apply IHEvalsTo;auto.
Qed.
(* Lemma or_left': forall e2,
  EvalsTo (ExpBinOp Or (Bc true) e2) (Bc true).
Proof.
  intros.

Lemma or_left: forall e1 e2,
    EvalsTo e1 (Bc true) -> EvalsTo (ExpBinOp Or e1 e2) (Bc true).
Proof.
  intros. apply lemma_evals_trans with (ExpBinOp Or (Bc true) e2).
  apply binop_many. auto. *)
Lemma invok_many: forall e1 e1' e2 m,
  EvalsTo e1 e1' -> EvalsTo (ExpMethodInvoc e1 m e2) (ExpMethodInvoc e1' m e2).
Proof.
  intros. induction H.
  -
    apply Refl. 
  -
    apply AddStep with (ExpMethodInvoc e0 m e2).
    apply Refc_Invok1;auto.
    apply IHEvalsTo;auto.
Qed.

Lemma invok_many': forall v e2 e2' m,
  isValue v -> EvalsTo e2 e2' -> EvalsTo (ExpMethodInvoc v m e2) (ExpMethodInvoc v m e2').
Proof.
  intros. induction H0.
  -
    apply Refl. 
  -
    apply AddStep with (ExpMethodInvoc v m e2).
    apply Refc_Invok2;auto.
    apply IHEvalsTo;auto.
Qed.

Lemma access_many: forall e e' f, 
    EvalsTo e e' -> EvalsTo (ExpFieldAccess e f) (ExpFieldAccess e' f).
Proof.
  intros. induction H.
  -
  apply Refl.
  -
  apply AddStep with (ExpFieldAccess e2 f).
  apply RefRC_Field;auto.
  apply IHEvalsTo;auto.
Qed.

Lemma lemma_let_many : forall (e_x e_x' e : expr),
    EvalsTo e_x e_x' -> EvalsTo (ExpLet e_x e) (ExpLet e_x' e).
Proof. intros e_x e_x' e ev_ex_ex'. induction ev_ex_ex' as [|e_x e_x1 e_x' st_exex1 ev_ex1ex' IH].
  - apply Refl.
  - apply AddStep with (ExpLet e_x1 e); try (apply ELet); assumption. Qed.

Lemma value_refl : forall (v v' : expr),       
    isValue v -> EvalsTo v v' ->  v = v'.
Proof. intros v v' v_val ev_v_v'. destruct ev_v_v' as [|v e1 v' st_ve1 ev_e1v'] eqn:E.
  - reflexivity.
  - apply value_stuck in st_ve1 as H. contradiction. Qed.



Lemma udelta_value: forall c v1 pf,
  isValue (udelta c v1 pf).
Proof.
  intros. destruct c. inversion pf. subst v1.
  assert (udelta Not (Bc b) pf = udelta Not (Bc b) (isCpt_Not b)). apply udelta_pf_indep;auto. rewrite H.
  simpl. case_eq b;intros;simpl;auto.
Qed.
Lemma bdelta_value : forall (c : BinOp) (v1 : expr) (v2: expr) (pf pf' : isCompat2 c v1 v2) v,
  bdelta c v1 v2 pf = v -> isValue v.
Proof.
  intros. destruct c. 
  -
    inversion pf. subst v1. subst v2. assert (bdelta And (Bc b1) (Bc b2) pf = bdelta And (Bc b1) (Bc b2) (isCpt_And b1 b2)). apply delta_pf_indep. rewrite H0 in H. simpl in H. rewrite <- H. simpl. auto.
  -
    inversion pf. subst v1. subst v2. assert (bdelta Or (Bc b1) (Bc b2) pf = bdelta Or (Bc b1) (Bc b2) (isCpt_Or b1 b2)). apply delta_pf_indep. rewrite H0 in H. simpl in H. rewrite <- H. simpl. auto.
  -
    inversion pf. subst v0. subst v3. assert (bdelta Eq (v1) (v2) pf = bdelta Eq (v1) (v2) (isCpt_Eq v1 v2 H0 H1)). apply delta_pf_indep. rewrite H2 in H. simpl in H. rewrite <- H. simpl. auto.
Qed.


Lemma lemma_eqv_semantics : forall (e1 e2:expr),
  isValue e1 -> isValue e2 -> EvalsTo (ExpBinOp (Eq) e1 e2) (Bc (veq e1 e2)).
Proof. intros. apply step_evals. assert ((bdelta Eq e1 e2 (isCpt_Eq e1 e2 H H0)) = Bc (veq e1 e2)) by reflexivity. rewrite <- H1.
  apply EBinOp3;auto.
  Qed.

Lemma lemma_not_semantics' : forall b, (ExpUnOp (Not) (Bc b))  ~~> (Bc (negb b)).
Proof. intros. 
  destruct b. 
  -
  assert ((udelta Not (Bc true) (isCpt_Not true)) = Bc (negb true)) by reflexivity. rewrite <- H. apply EUnOp2. simpl;auto.
  -
  assert ((udelta Not (Bc false) (isCpt_Not false)) = Bc (negb false)) by reflexivity. rewrite <- H. apply EUnOp2. simpl;auto.
Qed.
Lemma lemma_not_semantics : forall b, EvalsTo (ExpUnOp (Not) (Bc b)) (Bc (negb b)).
Proof. intros. apply step_evals.  apply lemma_not_semantics'.
Qed.
