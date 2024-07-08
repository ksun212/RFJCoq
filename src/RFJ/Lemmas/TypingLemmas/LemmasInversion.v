Require Import List.
Require Import Coq.Program.Equality.

Require Import Definitions.Syntax.
Require Import Definitions.Names.

Require Import Definitions.Typing.
Require Import Definitions.FJTyping.
Require Import Definitions.Semantics.
Require Import Definitions.Typing.
Require Import Definitions.CTSanity.
Require Import Definitions.SubDenotation.

Require Import Lemmas.BasicLemmas.LemmasEnvironments.
Require Import Lemmas.BasicLemmas.LemmasWF.
Require Import Lemmas.BasicLemmas.LemmasWFNarrow.
Require Import Lemmas.BasicLemmas.LemmasFJTyping.
Require Import Lemmas.TypingLemmas.LemmasTyping.
Require Import Lemmas.TypingLemmas.LemmasRefl.
Require Import Lemmas.BasicLemmas.LemmasCTBasics.
Require Import Lemmas.TypingLemmas.LemmasNarrowing.
Require Import Lemmas.TypingLemmas.LemmasTransitive. 

(*---------------Several Inversion Lemmas---------------*)

Lemma invert_new: forall le g c C es ps, 
Hastype g le (TRefn (TNom (TClass c)) ps) -> le = ExpNew C es -> SubClass (TClass C) (TClass c) -> (
(exists Fs' Ts, Reffields C Fs' /\ Forall2 (Hastype g) es Ts /\ (Forall2 (Subtype g) Ts (map (tsubBV (ExpNew C es)) (map ReffieldType Fs'))) 
)).
Proof. 
intros. induction H ; try discriminate; intros.
-
  inversion H0.
  subst es0. subst C0. subst Us. subst fs.
  exists Fs. exists Ts. 
  repeat (constructor; auto). 
-
  (*we should prove subtype here, but since our conclusion does not dependent on s or t, so we are fine*)
  eapply IHHastype;auto.
Qed.


Lemma class_s: forall g C0 es n ps s, g=Empty -> WFtype g (TRefn (TNom n) ps) -> g |--- (ExpNew C0 es) : s -> Subtype g s (TRefn (TNom n) ps) -> FJSubtype (TNom (TClass C0)) (TNom n).
Proof.
  intros.
  dependent induction H1.
  simpl in H5. inversion H5. auto.
  apply IHHastype with es;auto.
  apply sub_trans with t;auto. 
  apply typing_wf with (ExpNew C0 es);auto.
Qed.
Lemma class_sub: forall g C0 es ps n, g=Empty -> g |--- (ExpNew C0 es) : (TRefn (TNom n) ps) -> FJSubtype (TNom (TClass C0)) (TNom n).
Proof.
  intros.
  apply class_s with g es ps ( TRefn (TNom n) ps);auto.
  apply typing_wf with (ExpNew C0 es);auto. subst g. auto.
  apply sub_refl.
  apply typing_wf with (ExpNew C0 es);auto. subst g. auto.
Qed.

Lemma class_nomtype: forall g C0 es s, g |--- ExpNew C0 es : s -> exists ps, (exists C, s= TRefn (TNom C) ps) \/ s = TRefn (TAny) ps.
Proof.
  intros.
  dependent induction H.
  unfold self. simpl.  exists  (PCons (eqlPred (ExpNew C0 es))
  (PEmpty)).
                                          
  left. exists (TClass C0). reflexivity.
  assert (exists ps, (exists C, s = TRefn (TNom C) ps) \/ s = TRefn TAny ps). eapply IHHastype. reflexivity.
  destruct H2 as [ps]. destruct H2. destruct H2 as [C].
  rewrite H2 in H1.
  inversion H1.
  inversion H6. 
  exists p2. right. reflexivity.
  exists p2. left. exists D. reflexivity.
  rewrite H2 in H1.
  inversion H1.
  inversion H6.
  exists p2. right. reflexivity.
Qed.
Lemma subclass_prev: forall g C0 C es ps, g=Empty -> g |--- (ExpNew C0 es) : ( TRefn (TNom (TClass C)) ps) -> (exists ps', g |--- (ExpNew C0 es) : TRefn (TNom (TClass C0)) ps').
Proof.
  intros.
  dependent induction H0.
  exists (PCons  (eqlPred (ExpNew C es))  (PEmpty)). eapply TNew;eauto.
  apply class_nomtype in H0.
  destruct H0 as [ps']. destruct H0. destruct H0 as [C'].
  subst s. inversion H1. inversion H5.  
  assert (exists bb, C' = TClass bb). eapply subclass_class;eauto. destruct H11 as [bb]. subst C'. subst b1. subst C1.
  apply IHHastype with bb ps';auto. 
  inversion H1.
  rewrite H0 in H5. inversion H5. rewrite H9 in H6. inversion H6.
Qed.
Lemma subclass_prev_inv': forall g C0 C es ps s, WFtype g (TRefn (TNom (TClass C)) ps) -> g|--- (ExpNew C0 es) : s -> Subtype g s ( TRefn (TNom (TClass C)) ps) -> WFEnv g -> (g |--- (ExpNew C0 es) : TRefn (TNom (TClass C0)) ps).
Proof.
  intros.
  dependent induction H0.
  -
    simpl in H0. inversion H0.
    apply TSub with (self (TRefn (TNom (TClass C0)) (PEmpty))(ExpNew C0 es)). eapply TNew;eauto. apply wf_narrow_subclass' with (TClass C);auto. inversion H10. auto. 
    simpl. apply SBase with (union nms nms). apply SubBClass. apply SubCRefl. intros. apply H12. notin_solve_one.
  - 
    apply IHHastype;auto.
    apply sub_trans with t;auto.
    apply typing_wf with (ExpNew C0 es);auto.
Qed.
Lemma subclass_prev_inv: forall g C0 C es ps, g |--- (ExpNew C0 es) : ( TRefn (TNom (TClass C)) ps) -> WFEnv g -> (g |--- (ExpNew C0 es) : TRefn (TNom (TClass C0)) ps).
Proof.
  intros.
  apply subclass_prev_inv' with C ( TRefn (TNom (TClass C)) ps);auto.
  apply typing_wf with (ExpNew C0 es);auto. 
  apply sub_refl.
  apply typing_wf with (ExpNew C0 es);auto. Qed.
Lemma subclass_prev_inv'n: forall g C0 es ps s n, WFtype g (TRefn (TNom n) ps) -> g|--- (ExpNew C0 es) : s -> Subtype g s (TRefn (TNom n) ps) -> WFEnv g -> (g |--- (ExpNew C0 es) : TRefn (TNom (TClass C0)) ps).
Proof.
  intros.
  dependent induction H0.
  -
    simpl in H0. inversion H0.
    apply TSub with (self (TRefn (TNom (TClass C0)) (PEmpty))(ExpNew C0 es)). eapply TNew;eauto. apply wf_narrow_subclass' with n;auto. inversion H10. auto. 
    simpl. apply SBase with (union nms nms). apply SubBClass. apply SubCRefl. intros. apply H12. notin_solve_one.
  - 
    apply IHHastype;auto.
    apply sub_trans with t;auto.
    apply typing_wf with (ExpNew C0 es);auto.
Qed.
Lemma subclass_prev_invn: forall g C0 es ps n, g |--- (ExpNew C0 es) : ( TRefn (TNom n) ps) -> WFEnv g -> (g |--- (ExpNew C0 es) : TRefn (TNom (TClass C0)) ps).
Proof.
  intros.
  apply subclass_prev_inv'n with (TRefn (TNom n) ps) n;auto.
  apply typing_wf with (ExpNew C0 es);auto. 
  apply sub_refl.
  apply typing_wf with (ExpNew C0 es);auto. Qed.

    
Lemma subclass_prev_invf': forall g C0 es s ft, HasFJtype g (ExpNew C0 es) s -> FJSubtype s ft -> (HasFJtype g (ExpNew C0 es) (TNom (TClass C0))).
Proof.
  intros.
  dependent induction H.
  -
    simpl in H0.
    eapply FJTyping.FTNew;eauto.
  -
    apply IHHasFJtype;auto.
    apply fsub_trans with t;auto.
Qed.

Lemma subclass_prev_invf: forall g C0 es ft, HasFJtype g (ExpNew C0 es) ft -> HasFJtype g (ExpNew C0 es) (TNom (TClass C0)).
Proof.
  intros.
  apply subclass_prev_invf' with ft ft;auto.
Qed.

Lemma hasfjtype_subclass: forall c c1 l,
  HasFJtype FEmpty (ExpNew c l) (TNom (TClass c1)) -> SubClass (TClass c) (TClass c1).
Proof.
  intros. dependent induction H.
  -
    apply SubCRefl.
  -
    inversion H0.
    assert (exists bb, C = TClass bb). eapply subclass_class;eauto. destruct H4 as [bb]. subst C.
    apply SubCTrans with (TClass bb);auto.
    +
      apply IHHasFJtype with l;auto.
Qed.
