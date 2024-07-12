Require Import Relations Decidable.
Require Import RFJ.Utils.
Require Export Definitions.Syntax.
Require Import Forall2.
Require Import Lists.
Require Import RFJ.Utils.Referable.
Require Export Definitions.Names.
Require Import ZArith.
Require Import Definitions.FJTyping.

Require Import Definitions.Semantics.
Require Import Lists.ListSet.

Require Import Definitions.SubDenotation.

Require Import Definitions.Typing.
Require Import Coq.Program.Equality.
Require Import RFJ.Tactics.

Require Import Lia.


(*
1. we use contra and co variant. 
2. if the subtype is fine under a narrower context then we are fine.
since we can are actually using them when playing as supertype, it is safe to assume we have this narrower context. 
*)
Definition override (m: MethodName) (C: ClassName) (D: ClassName) (ps: preds) (Cs: type) (C0: type) :=
  (forall Ds D0 ps', mtype(m, D) = ps' ~> Ds ~> D0 -> 
  (Subtype Empty (TRefn (TNom (TClass C)) ps') (TRefn (TNom (TClass C)) ps) /\ 
  subtype_under (TRefn (TNom (TClass C)) ps') Ds Cs /\ 
  subtype_under2 (TRefn (TNom (TClass C)) ps') Ds C0 D0)
  ).
Definition implement (C: ClassName) (m: MethodName) (t0: type) (ps: preds) (t: type) :=
  (exists Ds D0 ps', mtype(m, C) = ps' ~> Ds ~> D0 /\
  (Subtype Empty (TRefn (TNom (TClass C)) ps) (TRefn (TNom (TClass C)) ps') /\ 
  subtype_under (TRefn (TNom (TClass C)) ps) t Ds /\ 
  subtype_under2 (TRefn (TNom (TClass C)) ps) t D0 t0)
  ).

Inductive MType_OK : ClassName -> MethodDefn -> Prop :=
| WF_Method : forall ps rt t e (C:ClassName) D Is Fs noDupfs K Ms noDupMds m,
          find C RefCT = Some (RefCDecl C D Is Fs noDupfs K Ms noDupMds)->
          find m Ms = Some (MDefn (MDecl rt m ps t) e) ->
          override m C D ps t rt->
          (WFtype Empty (TRefn (TNom (TClass C)) ps)) -> 
          wf_under (TRefn (TNom (TClass C)) ps) t -> 
          wf_under2 (TRefn (TNom (TClass C)) ps) t rt -> 
          (forall y y', y <> y' -> Hastype (Cons y' (openT_at 0 y t) (Cons y (TRefn (TNom (TClass C)) ps) Empty)) (open_at 1 y (open_at 0 y' e)) (openT_at 1 y (openT_at 0 y' rt))) -> 
          (fv e = empty) -> 
          (free t = empty) -> (free rt = empty) -> 
          MType_OK C (MDefn (MDecl rt m ps t) e).
Inductive FType_OK : ClassName -> RefFieldDecl -> Prop :=
| WF_Field : forall C t f,
          free t = empty -> 
          wf_under (TRefn (TNom (TClass C)) PEmpty) t -> 
          FType_OK C (RefFDecl t f).
Inductive Class_implemented: ClassName -> InterfaceName -> Prop := 
| CI: forall C I iMs noDupiMds, 
  find I RefIT = Some (RefIDecl I iMs noDupiMds) ->
  (forall im irt ips it, 
  find im iMs = Some (MDecl irt im ips it) -> 
  implement C im irt ips it) -> 
  Class_implemented C I.
Inductive CType_OK: RefClassDecl -> Prop :=
| T_Class : forall C D Fs noDupfs Is K Ms noDupMds fdecl ,
          K = KDecl C (Fs ++ fdecl) (refs fdecl) (zipWith Assgnmt (map (ExpFieldAccess (BV 0)) (refs Fs)) (map FV (refs Fs))) ->
          Reffields D fdecl ->
          NoDup (refs (fdecl ++ Fs)) ->
          Forall (MType_OK C) (Ms) ->
          Forall (FType_OK C) (Fs) ->
          find C RefCT = Some (RefCDecl C D Is Fs noDupfs K Ms noDupMds) ->
          (forall i I, 
          nth_error Is i = Some I -> 
          Class_implemented C I) -> 
          (* find I RefIT = Some (RefIDecl I iMs noDupiMds) ->
          find im iMs = Some (MDecl irt im ips it) -> 
          implement C im irt ips it) ->  *)
          CType_OK (RefCDecl C D Is Fs noDupfs K Ms noDupMds).
#[global] Hint Constructors CType_OK.
Inductive MType_OK_I : ClassName -> MethodDecl -> Prop :=
| WF_MethodI : forall ps rt t (C:InterfaceName) m,
          (WFtype Empty (TRefn (TNom (TInterface C)) ps)) -> 
          wf_under (TRefn (TNom (TInterface C)) ps) t -> 
          wf_under2 (TRefn (TNom (TInterface C)) ps) t rt -> 
          (free t = empty) -> (free rt = empty) -> 
          MType_OK_I C (MDecl rt m ps t).
Inductive IType_OK: RefInterfaceDecl -> Prop :=
| T_ClassI : forall I iMs noDupiMds ,
          Forall (MType_OK_I I) (iMs) ->
          find I RefIT = Some (RefIDecl I iMs noDupiMds) ->
          IType_OK (RefIDecl I iMs noDupiMds).
                 
Axiom cok: forall C D Fs noDupfs K Is Ms noDupMds, 
            find C RefCT = Some (RefCDecl C D Is Fs noDupfs K Ms noDupMds) ->
            CType_OK (RefCDecl C D Is Fs noDupfs K Ms noDupMds).
Axiom obj_notin_dom: find Object RefCT = None.
Axiom iok: forall I iMs noDupiMds,
            find I RefIT = Some (RefIDecl I iMs noDupiMds) ->
            IType_OK (RefIDecl I iMs noDupiMds).
#[global] Hint Rewrite obj_notin_dom.



Lemma fields_obj_nil: forall f,
Reffields Object f -> f = nil.
Proof.
  intros.
  inversion H.
  reflexivity.
  rewrite obj_notin_dom in H0.

  crush.
  Qed.

#[global] Hint Resolve fields_obj_nil.
Lemma reffields_det: forall C f1 f2,
Reffields C f1 ->
Reffields C f2 ->
f1 = f2.
  Proof.
  
  intros.
  gen f2.
  induction H.
  -
    intros.
    forwards: (fields_obj_nil f2 H0).
    crush.
  -
    intros.
    inversion H2.
    +

      crush.
    +
      crush.
      forwards: (IHReffields fs'0 H4).
      crush.
Qed.

