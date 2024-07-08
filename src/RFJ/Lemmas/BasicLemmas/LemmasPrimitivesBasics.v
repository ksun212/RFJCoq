
Require Import ZArith.
Require Import Lia.
Require Import Coq.Program.Equality.

Require Import Definitions.Syntax.
Require Import Definitions.Names.
Require Import Definitions.Semantics.
Require Import Definitions.FJTyping.

Require Import Definitions.Typing.
Require Import Definitions.SubDenotation.

Require Import Lemmas.BasicLemmas.LemmasFJTyping.
Require Import Lemmas.BasicLemmas.LemmasSubstitution.
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasEnvironments.
Require Import Lemmas.BasicLemmas.LemmasFJWeaken.
Require Import Lemmas.BasicLemmas.LemmasWFWeaken.
Require Import Lemmas.BasicLemmas.LemmasWFSubstitution.


(*---------------Basic Properties of the Primitives---------------*)

(*--------------1. Canonical Form Lemmas---------------*)
Definition isBool (e:expr) : Prop :=
    match e with
    | (Bc _ ) => True
    | _       => False
    end.

Lemma bool_values : forall (v:expr), 
    isValue v -> HasFJtype FEmpty v (TBool) ->  isBool v.
Proof. intros v val p_v_bl. dependent induction p_v_bl; simpl; try contradiction;auto. 
    inversion H. apply IHp_v_bl;auto.
    Qed. 

Definition isInt (e:expr) : Prop :=
    match e with
    | (Ic _ ) => True
    | _       => False
    end.

Lemma int_values : forall (v:expr),
    isValue v -> HasFJtype FEmpty v (TInt) -> isInt v.
Proof. intros v val p_v_bl. dependent induction p_v_bl; simpl; try contradiction;auto. 
inversion H. apply IHp_v_bl;auto.
    Qed. 

Definition isClass (c:ClassName) (e:expr) : Prop := 
  match e with 
  | ExpNew c' es => SubClass (TClass c') (TClass c) /\ isValue (ExpNew c' es)
  | _ => False
  end. 
Lemma eq_mot_CT_class: forall t C, FJSubtype t (TNom (TClass C)) -> (exists D, t = TNom (TClass D) /\ SubClass  (TClass D) (TClass C)).
Proof.
  intros. destruct t; try (inversion H; simpl in H; discriminate).
  inversion H. subst n. 
  assert ((exists bb, C0 = TClass bb)). eapply subclass_class;eauto. destruct H0 as [CC]. subst C0. exists CC. constructor;auto.
Qed.
Lemma eq_mot_CT_nom: forall t C, FJSubtype t (TNom C) -> (exists D, t = TNom D /\ SubClass D C).
Proof.
  intros. destruct t; try (inversion H; simpl in H; discriminate).
  inversion H. subst n.
  exists C0. constructor;auto. 
Qed.
Lemma lemma_class_values : forall (v:expr)(c:ClassName),
  isValue v -> HasFJtype FEmpty v ((TNom (TClass c))) -> isClass c v.
Proof. intros v c val p_v_bl. dependent induction p_v_bl; simpl; try contradiction;auto. 
  apply eq_mot_CT_class in H. destruct H as [D]. destruct H. subst s.
  apply (@IHp_v_bl D) in val;auto. unfold isClass in val. unfold isClass. destruct e; try contradiction.
  destruct val. constructor;auto. apply SubCTrans with (TClass D);auto.
 Qed.    

 Definition isInterface (c:InterfaceName) (e:expr) : Prop := 
  match e with 
  | ExpNew c' es => SubClass (TClass c') (TInterface c) /\ isValue (ExpNew c' es)
  | _ => False
  end. 

Lemma lemma_interface_values : forall (v:expr)(c:InterfaceName),
  isValue v -> HasFJtype FEmpty v ((TNom (TInterface c))) -> isInterface c v.
Proof. intros v c val p_v_bl. dependent induction p_v_bl; simpl; try contradiction;auto. 
  apply eq_mot_CT_nom in H. destruct H as [D]. destruct H. subst s. destruct D.
  - apply lemma_class_values in p_v_bl;auto. unfold isClass in p_v_bl.  unfold isInterface. destruct e; try contradiction.
    destruct p_v_bl. constructor;auto. apply SubCTrans with (TClass c0);auto.
  - 
  apply (@IHp_v_bl i) in val;auto. unfold isInterface in val. unfold isInterface. destruct e; try contradiction.
  destruct val. constructor;auto. apply SubCTrans with (TInterface i);auto.
 Qed.  


Definition isNominal (c:nomtype) (e:expr) : Prop := 
    match e with 
    | ExpNew c' es => SubClass (TClass c') c /\ isValue (ExpNew c' es)
    | _ => False
    end. 
Lemma lemma_nominal_values : forall (v:expr)(c:nomtype),
isValue v -> HasFJtype FEmpty v ((TNom c)) -> isNominal c v.
Proof. intros v c val p_v_bl. dependent induction p_v_bl; simpl; try contradiction;auto. 
apply eq_mot_CT_nom in H. destruct H as [D]. destruct H. subst s. destruct D.
- apply lemma_class_values in p_v_bl;auto. unfold isClass in p_v_bl.  unfold isInterface. destruct e; try contradiction.
    destruct p_v_bl. constructor;auto. apply SubCTrans with (TClass c0);auto.
- 
apply (@IHp_v_bl (TInterface i)) in val;auto. unfold isInterface in val. unfold isInterface. destruct e; try contradiction.
destruct val. constructor;auto. apply SubCTrans with (TInterface i);auto.
Qed.  
  

(*--------------2. WF Lemmas for Primitives---------------*)
Lemma wf_tybc : forall (g:env) (b:bool), WFtype g (tybc b).
Proof. intros ; apply WFRefn with (binds g);
  try apply WFBase ; intros ; try apply PFTCons; try apply PFTEmp; try discriminate.
  simpl. assert ((erase (ty'2 Eq)) = TBool). reflexivity. rewrite <- H0. 
  apply FTBinOP;simpl;auto. apply FTSub with TBool;auto. 
  simpl. apply FTSub with TBool;auto. apply FTVar. try (simpl; right; left; constructor; reflexivity).  try (simpl; left; constructor; reflexivity).
Qed.

Lemma wf_tyic : forall (g:env) (n:Z), WFtype g (tyic n).
Proof. intros ; apply WFRefn with (binds g);
try apply WFBase ; intros ; try apply PFTCons; try apply PFTEmp; try discriminate.
simpl. assert ((erase (ty'2 Eq)) = TBool). reflexivity. rewrite <- H0. 
apply FTBinOP;simpl;auto. apply FTSub with TInt;auto. 
simpl. apply FTSub with TInt;auto.  apply FTVar. try (simpl; right; left; constructor; reflexivity).  try (simpl; left; constructor; reflexivity).
Qed.

Lemma wf_intype : forall (g:env) (c:UnOp), WFtype g (intype c).
Proof. intros g c.
  destruct c;simpl. apply WFBase. Qed.

Lemma wf_ty'g : forall (c:UnOp) g e, isLC e -> HasFJtype (erase_env g) e (erase (intype c)) -> WFtype g (tsubBV e (ty' c)). 
Proof. 
  intros.  unfold tsubBV.
  destruct c. simpl. 
  apply WFRefn with (binds g). apply WFBase. discriminate. intros. unfold unbindP. simpl. 
  apply PFTCons.  
  simpl. assert ((erase (ty'2 Eq)) = TBool). reflexivity. rewrite <- H2 at 2. simpl. 
  apply FTBinOP. simpl.
  apply FTSub with TBool.
  apply FTUnOP. 
  rewrite unbind_lc. apply weaken_fjtyp_top;auto. unfold in_envFJ. rewrite <- binds_erase_env. notin_solve_one. auto.
  apply SubBAny. simpl. 
  apply FTSub with TBool;auto. apply FTVar. try (simpl; right; left; constructor; reflexivity).  try (simpl; left; constructor; reflexivity). 
  apply PFTEmp.
Qed. 
Lemma wf_intype2f : forall (g:env) (c:BinOp), WFtype g (fst (intype2 c)).
Proof. intros g c.
  destruct c;simpl; apply WFBase. Qed.

Lemma wf_intype2s : forall (c:BinOp), wf_under (fst (intype2 c)) (snd (intype2 c)).
Proof. intros c un.
    unfold wf_under;intros.
    destruct c;simpl; apply WFBase. Qed.
Lemma wf_ty'1 : forall (c:UnOp), 
    wf_under (intype c) (ty' c).
Proof.
  intros. unfold wf_under. intros.
  destruct c.
  simpl. apply WFRefn with empty.
  apply WFBase.
  discriminate.
  intros. unfold unbindP. simpl. apply PFTCons. simpl; assert ((erase (ty'2 Eq)) = TBool); try reflexivity. rewrite <- H0.
  apply FTBinOP. simpl. apply FTSub with TBool. apply FTUnOP. simpl.  try apply FTVar. simpl. right. left. constructor;auto. simpl. auto.  apply FTSub with TBool.  try apply FTVar. simpl. left. constructor;auto. apply SubBAny. simpl.
  apply PFTEmp.
Qed.
Lemma wf_ty'2 : forall (c:BinOp), 
    wf_under2 (fst (intype2 c)) (snd (intype2 c)) (ty'2 c).
Proof. 
  intros. unfold wf_under2. intros. 
  destruct c.
  - 
  simpl. apply WFRefn with empty.
  apply WFBase.
  discriminate.
  intros. unfold unbindP; simpl; apply PFTCons; simpl; assert ((erase (ty'2 Eq)) = TBool); try reflexivity; rewrite <- H1.
  apply FTBinOP. simpl. apply FTSub with TBool. apply FTBinOP. simpl.  try apply FTVar. simpl. right. right. left. constructor;auto. simpl.  try apply FTVar. simpl. right. left. constructor;auto. apply SubBAny. simpl. apply FTSub with TBool.  try apply FTVar. simpl. left. constructor;auto. apply SubBAny. apply PFTEmp.
  -
  simpl. apply WFRefn with empty.
  apply WFBase.
  discriminate.
  intros. unfold unbindP; simpl; apply PFTCons; simpl; assert ((erase (ty'2 Eq)) = TBool); try reflexivity; rewrite <- H1.
  apply FTBinOP. simpl. apply FTSub with TBool. apply FTBinOP. simpl.  try apply FTVar. simpl. right. right. left. constructor;auto. simpl.  try apply FTVar. simpl. right. left. constructor;auto. apply SubBAny. simpl. apply FTSub with TBool.  try apply FTVar. simpl. left. constructor;auto. apply SubBAny. apply PFTEmp.
  -
  simpl. apply WFRefn with empty.
  apply WFBase.
  discriminate.
  intros. unfold unbindP; simpl; apply PFTCons; simpl; assert ((erase (ty'2 Eq)) = TBool); try reflexivity; rewrite <- H1.
  apply FTBinOP. simpl. apply FTSub with TBool. apply FTBinOP. simpl.  try apply FTVar. simpl. right. right. left. constructor;auto. simpl.  try apply FTVar. simpl. right. left. constructor;auto. apply SubBAny. simpl. apply FTSub with TBool.  try apply FTVar. simpl. left. constructor;auto. apply SubBAny. apply PFTEmp.
Qed.



Lemma wf_and: forall b1 b2, WFtype Empty (tsubBV_at 1 (Bc b1) (tsubBV (Bc b2) (ty'2 And))).
Proof.
  intros.
  apply wf_sub_fjtype2 with (snd (intype2 And)) (fst (intype2 And));auto. apply wf_ty'2;auto. 
  unfold isLC. simpl;auto.
  unfold isLC. simpl;auto.
Qed.
Lemma wf_or: forall b1 b2, WFtype Empty (tsubBV_at 1 (Bc b1) (tsubBV (Bc b2) (ty'2 Or))).
Proof.
  intros.
  apply wf_sub_fjtype2 with (snd (intype2 Or)) (fst (intype2 Or));auto. apply wf_ty'2;auto. 
  unfold isLC. simpl;auto.
  unfold isLC. simpl;auto.
Qed.

Lemma wf_eq: forall v1 v2 t t', isLC v1 -> isLC v2 -> HasFJtype FEmpty v1  t -> HasFJtype FEmpty  v2  t' -> WFtype Empty (tsubBV_at 1 (v1) (tsubBV (v2) (ty'2 Eq))).
Proof.
  intros.
  apply wf_sub_fjtype2 with (snd (intype2 Eq)) (fst (intype2 Eq));auto. apply wf_ty'2;auto. apply FTSub with t;auto. 
  apply FTSub with t';auto. 
Qed.