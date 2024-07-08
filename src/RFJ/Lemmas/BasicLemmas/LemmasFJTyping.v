Require Import Relations Decidable.
Require Import ZArith.
Require Import Crush.
Require Import Coq.Program.Equality.
Require Import Lists.
Require Import Forall2.


Require Import Utils.
Require Export Definitions.Syntax.
Require Export Definitions.Names.
Require Import Definitions.Semantics.
Require Import Definitions.FJTyping.
Require Import Definitions.SubDenotation.
Require Import Lemmas.BasicLemmas.LemmasSyntax.



(*---------------Basic Properties of FJ Typing---------------*)

Lemma FSubtype_refl: forall t, FJSubtype t t.
Proof.
    intros. destruct t; auto.
Qed.
Lemma FSubtype_trans: forall t1 t2 t3, FJSubtype t1 t2 -> FJSubtype t2 t3 -> FJSubtype t1 t3.
Proof.
    intros. inversion H; inversion H0;crush.
    apply SubBClass. apply SubCTrans with D;auto. 
Qed.
Lemma subclass_class: forall b2 C, SubClass b2 (TClass C) -> (exists bb, b2 = TClass bb).
Proof.
  intros. dependent induction H.
  exists C. auto.
  assert (TClass C = TClass C). auto. apply IHSubClass2 in H1. destruct H1 as [bb]. apply IHSubClass1 in H1. auto.
  exists C0. auto.
Qed.
Lemma subclass_class': forall b2 C, SubClass b2 (TInterface C) -> b2 = TInterface C \/ (exists bb, b2 = TClass bb).
Proof.
  intros. dependent induction H.
  left. auto.
  assert (TInterface C = TInterface C). auto. apply IHSubClass2 in H1. destruct H1. 
  apply IHSubClass1 in H1. destruct H1.
  left. auto.
  right. auto.
  right. destruct H1 as [bb]. subst b2. apply subclass_class with bb;auto. 
  right. exists C0. auto.
Qed.

#[export] Hint Resolve FSubtype_refl.


Lemma aux1: forall es Us, List.Forall2 (fun (e : expr) (_ : fjtype) => isLC e) es Us -> 
List.Forall (fun (e : expr) => isLC e) es.
Proof.
  intros.
  generalize dependent Us.
  induction es.
  intros.
  auto.
  intros.
  destruct Us.
  inversion H.
  inversion H.
  apply Forall_cons.
  apply H3.
  eapply IHes.
  apply H5.
Qed.
Lemma aux2: forall es, List.Forall (fun (e : expr) => isLC e) es -> 
(fix f (es' : [expr]) : Prop := match es' with
| nil => True
| e :: es'' => isLC_at 0 e /\ f es''
end) es.
Proof.
  intros.
  induction es.
  auto.
  inversion H.
  constructor;auto.
  apply IHes;auto.
Qed.
Lemma fjtyp_islc : forall (g:fjenv) (e:expr) (t:fjtype),
    HasFJtype g e t -> isLC e.
Proof. intros; induction H using HasFJtype_ind'; unfold isLC; simpl; intuition. 
  -
    apply aux2.
    eapply aux1;eauto.
  - (*FTLet *) pose proof (fresh_not_elem nms);
    set (y := fresh nms) in H2; apply H1 in H2.
    revert H2; unfold isLC.
    apply islc_at_after_open_at.
  Qed.

Lemma pbool_islcp : forall (g:fjenv) (ps:preds),
    PIsBool g ps -> isLCP ps.
Proof. intros; induction H; unfold isLCP; simpl; try split.
  apply fjtyp_islc with g (TBool); apply H.
  apply IHPIsBool. Qed.
