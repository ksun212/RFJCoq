Require Import Arith.
Require Import Lists.

Require Import Definitions.Syntax.
Require Import Definitions.Names.

Require Import Definitions.Typing.
Require Import Definitions.SubDenotation.
Require Import Definitions.FJTyping.

Require Import Lemmas.BasicLemmas.LemmasSubstitution.
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasEnvironments.
Require Import Lemmas.BasicLemmas.LemmasWF.
Require Import Lemmas.BasicLemmas.LemmasWFNarrow.
Require Import Lemmas.LogicalLemmas.LemmasSImp.
Require Import Lemmas.BasicLemmas.LemmasFJTyping.
Require Import Lemmas.BasicLemmas.LemmasWFWeaken.
Require Import Lemmas.BasicLemmas.LemmasWF.
Require Import Lemmas.BasicLemmas.LemmasWFNarrow.
Require Import Lemmas.BasicLemmas.LemmasWFSubstitution.
Require Import Lemmas.TypingLemmas.LemmasNarrowing.
Require Import Lemmas.TypingLemmas.LemmasTyping.
Require Import Lemmas.TypingLemmas.LemmasWeakenTyp.
Require Import Lemmas.LogicalLemmas.LemmasDenotesTyping.


(*---------------Subtyping is Transitive---------------*)

Lemma fsub_trans: forall t t' t'', FJSubtype t t' -> FJSubtype t' t'' -> FJSubtype t t''.
Proof.
  intros.
  destruct H.
  inversion H0.
  apply SubBAny.
  inversion H0. apply SubBAny. apply SubBInt.
  inversion H0. apply SubBAny. apply SubBBool.
  inversion H0. apply SubBAny. apply SubBClass. eapply SubCTrans;eauto.
Qed.
Lemma sub_trans' : forall (g:env) (t t' t'':type),
                    WFEnv g -> WFtype g t 
                    -> WFtype g t' -> WFtype g t'' 
                    -> Subtype g t t' -> Subtype g t' t'' 
                    -> Subtype g t t''.
Proof.
  intros.
  destruct t;   
  destruct t';  
  destruct t''.
  inversion H3; inversion H4; subst b0; subst b1. subst b2. subst b4.
  apply SBase with (union (binds g) (union nms nms0)); intros. eapply fsub_trans;eauto. 
  (* apply not_elem_union_elim in H14; destruct H14; *)
  apply ITrans with (unbindP y ps0).
  apply H11. notin_solve_one. 
  assert ((Cons y (TRefn b PEmpty) g) = (concatE (Cons y (TRefn b PEmpty) g) Empty)). reflexivity. rewrite H8.
  assert ((Cons y (TRefn b3 PEmpty) g) = (concatE (Cons y (TRefn b3 PEmpty) g) Empty)). reflexivity. 
  
  apply INarrow with (TRefn b3 PEmpty);auto. simpl. apply intersect_empty_r. apply wfenv_unique. auto. simpl;auto. unfold in_env. notin_solve_one.
  eapply SBase. auto. intros. apply IRefl. apply H18. notin_solve_one. 
  Unshelve. apply empty.
Qed.
Lemma sub_trans : forall (g:env) (t t' t'':type),
    WFEnv g -> WFtype g t -> WFtype g t' -> WFtype g t'' 
            -> Subtype g t t' -> Subtype g t' t'' 
            -> Subtype g t t''.
Proof. intros; 
  apply sub_trans' with t';
  trivial. Qed.

Lemma sub_trans_forall : forall (g:env) (ts ts' ts'':[type]),
  WFEnv g -> Forall (WFtype g) ts -> Forall (WFtype g) ts' -> Forall (WFtype g) ts'' 
          -> Forall2 (Subtype g) ts ts' -> Forall2 (Subtype g) ts' ts'' 
          -> Forall2 (Subtype g) ts ts''.
Proof.
  intros.
  generalize dependent ts'. generalize dependent ts''.
  induction ts;intros.
  -
    destruct ts''. 
    +
      apply Forall2_nil.
    +
      destruct ts'. inversion H4. inversion H3.
  -
    destruct ts''. 
    +
      destruct ts'. inversion H3. inversion H4. 
    +
      destruct ts'. inversion H3.
      inversion H0. inversion H1. inversion H2. inversion H3. inversion H4.
      apply Forall2_cons. apply sub_trans with t0;auto.
      apply IHts with ts';auto.
Qed.
