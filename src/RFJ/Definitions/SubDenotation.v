Require Import Lists.
Require Import Program.
Require Import Arith.
Require Import ZArith.
Require Import RFJ.Utils.

Require Import Definitions.Syntax.
Require Import Definitions.Names.
Require Import Definitions.Semantics.


(*---------------Subclass, FJ Subtyping and FJ Typing---------------*)

Inductive SubClass: nomtype -> nomtype -> Prop := 
| SubCRefl : forall b, SubClass b b 
| SubCTrans: forall b1 b2 b3, SubClass b1 b2 -> SubClass b2 b3 -> SubClass b1 b3
| SubCInh:   forall (C D:ClassName) Is fs noDupfs K mds noDupMds,
            find C RefCT = Some (RefCDecl C D Is fs noDupfs K mds noDupMds ) ->
            SubClass  (TClass C) (TClass D)
| SubIInh:   forall (C D:ClassName) Is I fs noDupfs K mds noDupMds i,
            find C RefCT = Some (RefCDecl C D Is fs noDupfs K mds noDupMds ) ->
            nth_error Is i = Some I -> 
            SubClass (TClass C) (TInterface I).  


Inductive FJSubtype: fjtype -> fjtype -> Prop := 
| SubBAny : forall t, FJSubtype t TAny
| SubBInt : FJSubtype TInt TInt
| SubBBool : FJSubtype TBool TBool
| SubBClass: forall C D, SubClass C D -> FJSubtype (TNom C) (TNom D).
#[export] Hint Constructors SubClass.
#[export] Hint Constructors FJSubtype.

(*---------------Closing Substitution and Related Definitions---------------*)

Inductive csub : Set :=
    | CEmpty
    | CCons  (x : vname) (v_x : expr) (th : csub).
  
Fixpoint bindsC (th : csub) : names := 
    match th with 
    | CEmpty            => empty
    | (CCons  x v_x th) => names_add x (bindsC th)
    end.
Definition in_csubst (x : vname) (th : csub) : Prop := Elem x (bindsC th).

Fixpoint bound_inC (x : vname) (v_x : expr) (th : csub) : Prop := 
    match th with
    | CEmpty             => False
    | (CCons  y v_y th)  => (x = y /\ v_x = v_y) \/ bound_inC x v_x th
    end.

Fixpoint closed (th0 : csub) : Prop :=
    match th0 with
    | CEmpty            => True
    | (CCons  x v_x th) => fv v_x = empty /\ closed th
    end.  

Fixpoint loc_closed (th0 : csub) : Prop :=
    match th0 with
    | CEmpty            => True
    | (CCons  x v_x th) => isLC v_x /\ loc_closed th
    end.  

Fixpoint substitutable (th0 : csub) : Prop :=
    match th0 with
    | CEmpty            => True
    | (CCons  x v_x th) => isValue v_x /\ substitutable th
    end.  

Fixpoint uniqueC (th0 : csub) : Prop :=
    match th0 with
    | CEmpty         => True
    | (CCons  x v_x th) => ~ in_csubst x th /\ uniqueC th
    end.   
    
Fixpoint csubst (th : csub) (e : expr) : expr := 
    match th with
    | CEmpty            => e
    | (CCons  x v_x th) => csubst th (subFV  x v_x e)
    end.

Fixpoint cpsubst (th : csub) (ps : preds) : preds := 
    match th with
    | CEmpty            => ps
    | (CCons  x v_x th) => cpsubst th (psubFV  x v_x ps)
    end.

Fixpoint ctsubst (th : csub) (t : type) : type :=
    match th with
    | CEmpty           => t
    | (CCons  x v  th) => ctsubst th (tsubFV x v t)
    end.

Fixpoint remove_fromCS (th:csub) (x:vname) : csub := 
    match th with 
    | CEmpty          => CEmpty
    | (CCons  y v th) => if x =? y then th else CCons  y v (remove_fromCS th x)
    end.
    
Fixpoint csubst_env (th0:csub) (g:env) : env :=
    match th0 with  
    | CEmpty            => g 
    | (CCons  z v_z th) => csubst_env th (esubFV  z v_z g)
    end.
    
Fixpoint CconcatE (th th'0 : csub) : csub :=
    match th'0 with
    | CEmpty          => th
    | (CCons  x t th') => CCons  x t (CconcatE th th')
    end.

(*---------------Truth, Logical Entailment, Logical Implication, Type Denotation, and Environment Denotation---------------*)

Inductive PEvalsTrue : preds -> Prop :=
    | PEEmp  : PEvalsTrue PEmpty
    | PECons : forall (p : expr) (ps : preds),
        EvalsTo p (Bc true) -> PEvalsTrue ps -> PEvalsTrue (PCons p ps).

Inductive Denotes: type -> expr -> Prop :=
| DenotesInt: forall ps i, 
    PEvalsTrue (psubBV (Ic i) ps) -> Denotes (TRefn TInt ps) (Ic i)
| DenotesBool: forall ps bol, 
    PEvalsTrue (psubBV (Bc bol) ps) -> Denotes (TRefn TBool ps) (Bc bol)
| DenotesClass: forall ps c es Fs, isValue (ExpNew c es) ->
    PEvalsTrue (psubBV (ExpNew c es) ps) -> 
    Reffields c Fs -> Forall2 Denotes (map (tsubBV (ExpNew c es)) (map ReffieldType Fs)) (es) -> 
    Denotes (TRefn (TNom (TClass c)) ps) (ExpNew c es)
| DenotesUpcast: forall b1 b ps v, 
    Denotes (TRefn b1 ps) v -> FJSubtype b1 b ->  
    Denotes (TRefn b ps) v.

Definition Denotes_ind' := fun (P : type -> expr -> Prop)
    (f0: (forall (ps : preds) (i : Z),
    PEvalsTrue (psubBV (Ic i) ps) -> P (TRefn TInt ps) (Ic i)) )
    (f1: (forall (ps : preds) (bol : bool),
    PEvalsTrue (psubBV (Bc bol) ps) -> P (TRefn TBool ps) (Bc bol)))
    (f2: (forall (ps : preds) (c : ClassName) (es : [expr])
    (Fs : [RefFieldDecl]),
  isValue (ExpNew c es) ->
  PEvalsTrue (psubBV (ExpNew c es) ps) ->
  Reffields c Fs ->
  Forall2 Denotes (map (tsubBV (ExpNew c es)) (map ReffieldType Fs)) es ->
  Forall2 P (map (tsubBV (ExpNew c es)) (map ReffieldType Fs)) es ->
  P (TRefn (TNom (TClass c)) ps) (ExpNew c es))) 
    (f3: (forall (b1 b : fjtype) (ps : preds) (v : expr),
    Denotes (TRefn b1 ps) v ->
    P (TRefn b1 ps) v -> FJSubtype b1 b -> P (TRefn b ps) v))
     => 
    fix f (t:type) (e:expr) (d:Denotes t e): P t e :=
    match d with 
    | DenotesInt ps i p1 => f0 ps i p1
    | DenotesBool ps bol p1 => f1 ps bol p1
    | DenotesClass ps c es Fs p1 p2 p3 p4 => f2 ps c es Fs p1 p2 p3 p4 ((fix list_Forall_ind (ts : [type]) (es' : [expr])  (map : Forall2 (Denotes) ts es'): 
    Forall2 (P) ts es' :=
    match map with
    | Forall2_nil _ => Forall2_nil (P)
    | (@Forall2_cons _ _ _ ex cx ees ccs H1 H2) => Forall2_cons ex cx (f ex cx H1) (list_Forall_ind ees ccs H2)
    end) (map (tsubBV (ExpNew c es)) (map ReffieldType Fs)) es p4)
    | DenotesUpcast b1 b ps v p1 p2 => f3 b1 b ps v p1 (f (TRefn b1 ps) v p1) p2
    end.

Inductive DenotesEnv : env -> csub -> Prop :=
    | DEmp  : DenotesEnv Empty CEmpty
    | DExt  : forall (g:env) (th:csub) (x:vname) (t:type) (v:expr), 
        DenotesEnv g th -> ~ in_env x g -> Denotes (ctsubst th t) v
              -> DenotesEnv (Cons x t g) (CCons x v th).

Inductive LImplies : env -> preds -> preds -> Prop :=
    | SImp : forall (g:env) (ps qs : preds),
        (forall (th:csub), DenotesEnv g th -> PEvalsTrue (cpsubst th ps) 
                                           -> PEvalsTrue (cpsubst th qs) )
            -> LImplies g ps qs.

Definition LEntails g ps:= forall th, DenotesEnv g th -> PEvalsTrue (cpsubst th ps).


(*---------------Subtyping---------------*)
Reserved Notation "Gamma '|-s' T '<::' S" (at level 41).
Inductive Subtype: env-> type -> type -> Prop :=
    | SBase : forall (g:env) (b1 b2:fjtype) (p1:preds) (p2:preds) (nms:names),
    FJSubtype b1 b2 -> 
    (forall (y:vname), ~ Elem y nms 
                    -> LImplies (Cons y (TRefn b1 PEmpty) g) (unbindP y p1) (unbindP y p2)) 
        -> Subtype g (TRefn b1 p1) (TRefn b2 p2)
      
  where "Gamma '|-s' T '<::' S" := (Subtype Gamma T S).

Lemma subtype_fsubtype : forall (g:env) (t1:type) (t2:type),
Subtype g t1 t2 -> FJSubtype (erase t1) (erase t2).
Proof. intros; induction H; simpl.
  - destruct b1; try (inversion H; reflexivity); inversion H;auto. 
Qed.


Lemma forall_subtype_fsubtype : forall (g:env) (t1s:[type]) (t2s:[type]),
  Forall2 (Subtype g) t1s t2s -> Forall2 FJSubtype (map erase t1s) (map erase t2s).
  intros.
  generalize dependent t2s.
  induction t1s.
  intros.
  destruct t2s.
  apply Forall2_nil.
  inversion H.
  intros.
  destruct t2s.
  inversion H.
  inversion H.
  simpl. apply Forall2_cons.
  apply subtype_fsubtype with g;auto.
  apply IHt1s. auto.
Qed.


Lemma binds_env_th : forall (g:env) (th:csub), 
    DenotesEnv g th -> binds g = bindsC th.
Proof. intros g th den_g_th; induction den_g_th; simpl;
  try rewrite IHden_g_th; reflexivity. Qed.

Lemma den_isvalue : forall (v:expr) (t:type),
  Denotes t v -> isValue v.
Proof.
intros; destruct t. dependent induction H;simpl;auto.
apply IHDenotes with b1 ps;auto.
Qed. 

Lemma denotesenv_substitutable : forall (g:env) (th:csub), 
    DenotesEnv g th -> substitutable th.
Proof. intros; induction H; simpl; repeat split; trivial.
  apply den_isvalue with (ctsubst th t); apply H1. Qed.

Lemma denotesenv_unique : forall (g:env) (th:csub),
    DenotesEnv g th -> unique g.
Proof. intros g th den_g_th; induction den_g_th; simpl; 
  try split; trivial; unfold in_csubst;
  rewrite <- binds_env_th with g th; trivial. Qed.

Lemma denotesenv_uniqueC : forall (g:env) (th:csub),
    DenotesEnv g th -> uniqueC th.
Proof. intros g th den_g_th; induction den_g_th; simpl; 
  try split; trivial; unfold in_csubst;
  rewrite <- binds_env_th with g th; trivial. Qed.