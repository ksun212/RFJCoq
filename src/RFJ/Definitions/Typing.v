Require Import Relations Decidable.
Require Import RFJ.Utils.
Require Export Definitions.Syntax.
Require Import Forall2.
Require Import Lists.
Require Import RFJ.Utils.Referable.
Require Export Definitions.Names.
Require Import ZArith.
Require Import Definitions.FJTyping.
Require Import Lemmas.BasicLemmas.LemmasFJTyping.

Require Import Lemmas.BasicLemmas.LemmasEnvironments.
Require Import Definitions.Semantics.



Require Import Lemmas.BasicLemmas.LemmasSyntax.

Require Import Lemmas.BasicLemmas.LemmasSubstitution.
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Definitions.SubDenotation.


Inductive WFtype : env -> type -> Prop :=
    | WFBase : forall (g : env) (b : fjtype),
           WFtype g (TRefn b PEmpty)
    | WFRefn : forall (g : env) (b : fjtype) (ps : preds) (nms : names),
          WFtype g (TRefn b PEmpty) -> ps <> PEmpty 
              -> (forall (y:vname), ~ Elem y nms 
                      -> PIsBool (FCons y (b) (erase_env g)) (unbindP y ps) )
              -> WFtype g (TRefn b ps).


Inductive WFEnv : env -> Prop :=
    | WFEEmpty : WFEnv Empty
    | WFEBind  : forall (g : env) (x : vname) (t : type),
          WFEnv g -> ~ (in_env x g) -> WFtype g t -> WFEnv (Cons x t g).

Lemma wfenv_unique : forall (g : env),
    WFEnv g -> unique g.
Proof. intros g p_g; induction p_g; simpl; trivial; split; assumption. Qed.

#[export] Hint Constructors WFtype.
#[export] Hint Constructors WFEnv.


(*---------------Typing---------------*)
Reserved Notation "Gamma '|---' x ':' C" (at level 60, x at next level).

Inductive Hastype: env -> expr -> type -> Prop :=

  | TBC   : forall (g:env) (b:bool), Hastype g (Bc b) (tybc b) 
  | TIC   : forall (g:env) (m:Z),  Hastype g (Ic m) (tyic m) 
  | TUnOP  : forall (g:env) (e:expr) (op: UnOp) t,
        Hastype g e t -> Subtype g t (intype op) -> isLC e -> Hastype g (ExpUnOp op e) (tsubBV e (ty' op))
  | TBinOP : forall (g:env) (e1 e2:expr) (op: BinOp) t t',
        Hastype g e1 t -> 
        (Subtype g t (fst (intype2 op))) -> 
        Hastype g e2 t'-> 
        (Subtype g t' (tsubBV e1 (snd (intype2 op)))) -> 
        isLC e1 -> isLC e2 -> 
        Hastype g (ExpBinOp op e1 e2) (tsubBV_at 1 e1 (tsubBV e2 (ty'2 op)))
  | TVar  : forall (g:env) (x:vname) (t:type),
    bound_in x t g -> WFtype g t -> Hastype g (FV x) (self t (FV x))
  | TInvok: forall (g:env) (e1:expr) (e2: expr) (m: MethodName) t t' rt C ps ps',
        Hastype g e1 (TRefn (TNom (TClass C)) ps') -> 
        mtype(m, C) = ps ~> t ~> rt ->
        (Subtype g (TRefn (TNom (TClass C)) ps') (TRefn (TNom (TClass C)) ps)) -> 
        (Hastype g e2 t') -> (Subtype g t' (tsubBV e1 t)) -> isLC e2 -> isLC e1 ->  
        Hastype g (ExpMethodInvoc e1 m e2) (self (tsubBV_at 1 e1 (tsubBV e2 rt)) (ExpMethodInvoc e1 m e2))
  | TInvokI: forall (g:env) (e1:expr) (e2: expr) (m: MethodName) t t' rt I ps ps',
        Hastype g e1 (TRefn (TNom (TInterface I)) ps') -> 
        mtypei(m, I) = ps ~> t ~> rt ->
        (Subtype g (TRefn (TNom (TInterface I)) ps') (TRefn (TNom (TInterface I)) ps)) -> 
        (Hastype g e2 t') -> (Subtype g t' (tsubBV e1 t)) -> isLC e2 -> isLC e1 ->  
        Hastype g (ExpMethodInvoc e1 m e2) (self (tsubBV_at 1 e1 (tsubBV e2 rt)) (ExpMethodInvoc e1 m e2))
  | TField: forall g e f C Fs i fi ps,
                     isLC e -> 
                    Hastype g e (TRefn (TNom (TClass C)) ps) -> 
                    Reffields C Fs ->
                    nth_error Fs i = Some fi ->
                    ref fi = f -> 
                    Hastype g (ExpFieldAccess e f) (self (tsubBV e (ReffieldType fi)) (ExpFieldAccess e f))
  | TNew:    forall g es Ts C Fs Us fs, 
                Us = map ReffieldType Fs -> 
                fs = map ref Fs -> 
                (Forall isLC es) -> 
                Reffields C Fs ->
                Forall2 (Hastype g) es Ts ->
                Forall2 (Subtype g) Ts (map (tsubBV (ExpNew C es)) Us) ->
                Hastype g (ExpNew C es) (self (TRefn (TNom (TClass C)) PEmpty) (ExpNew C es))
  | TLet  : forall (g:env) (e_x:expr) (b:type) (e:expr) (b':type) (nms:names),
    WFtype g b' -> Hastype g e_x b -> (forall (y:vname), ~ Elem y nms -> Hastype (Cons y b g) (unbind y e) (unbindT y b') )
    -> Hastype g (ExpLet e_x e) (self b' (ExpLet e_x e))
  
  | TSub  : forall (g:env) (e:expr) (s:type) (t:type),
                Hastype g e s -> WFtype g t -> Subtype g s t -> Hastype g e t (*we need explicit WFtype since subtype do not guarantee wf*)
  
where " g '|---' e ':' C " := (Hastype g e C).


Definition Hastype_ind' := fun (P : env -> expr -> type -> Prop)
            (f0: forall (g : env) (b : bool), P g (Bc b) (tybc b)) 
            (f1: forall (g : env) (m : Z), P g (Ic m) (tyic m)) 
            (f2: forall (g : env) (x : vname) (t : type),
            bound_in x t g -> WFtype g t -> P g (FV x) (self t (FV x)))
            (f3: forall (g : env) (e : expr) (op : UnOp) (t: type),
            g |--- e : t -> P g e t -> g |-s t <:: (intype op) ->
            isLC e -> P g (ExpUnOp op e) (tsubBV e (ty' op))) 
            (f3': (forall (g : env) (e1 e2 : expr) (op : BinOp) 
            (t t' : type),
          g |--- e1 : t ->
          P g e1 t ->
          g |-s t <:: fst (intype2 op) ->
          g |--- e2 : t' ->
          P g e2 t' ->
          (Subtype g t' (tsubBV e1 (snd (intype2 op)))) ->
           isLC e1 ->
           isLC e2 ->
          P g (ExpBinOp op e1 e2) (tsubBV_at 1 e1 (tsubBV e2 (ty'2 op)))))
            (f3'': forall (g : env) (e1 e2 : expr) (m : MethodName) 
            (t t' rt : type) (C : ClassName) (ps : preds) (ps':preds),
          g |--- e1 : TRefn (TNom (TClass C)) ps' ->
          P g e1 (TRefn (TNom (TClass C)) ps') ->
          mtype( m, C)= ps ~> t ~> rt ->
          (Subtype g (TRefn (TNom (TClass C)) ps') (TRefn (TNom (TClass C)) ps)) -> 
          g |--- e2 : t' ->
          P g e2 t' -> (Subtype g t' (tsubBV e1 t)) -> isLC e2 -> isLC e1 -> P g (ExpMethodInvoc e1 m e2) (self (tsubBV_at 1 e1 (tsubBV e2 rt)) (ExpMethodInvoc e1 m e2)))
          (f3''': forall (g : env) (e1 e2 : expr) (m : MethodName) 
            (t t' rt : type) (C : InterfaceName) (ps : preds) (ps':preds),
          g |--- e1 : TRefn (TNom (TInterface C)) ps' ->
          P g e1 (TRefn (TNom (TInterface C)) ps') ->
          mtypei( m, C)= ps ~> t ~> rt ->
          (Subtype g (TRefn (TNom (TInterface C)) ps') (TRefn (TNom (TInterface C)) ps)) -> 
          g |--- e2 : t' ->
          P g e2 t' -> (Subtype g t' (tsubBV e1 t)) -> isLC e2 -> isLC e1 -> P g (ExpMethodInvoc e1 m e2) (self (tsubBV_at 1 e1 (tsubBV e2 rt)) (ExpMethodInvoc e1 m e2)))
          
            (f4: (forall (g : env) (e : expr) (f5 : var) (C : ClassName)
            (Fs : [RefFieldDecl]) (i : nat) (fi : RefFieldDecl) 
            (ps : preds) ,
            isLC e -> 
          g |--- e : TRefn (TNom (TClass C)) ps ->
          P g e (TRefn (TNom (TClass C)) ps) ->
          Reffields C Fs ->
          nth_error Fs i = Some fi ->
          ref fi = f5 ->
          P g (ExpFieldAccess e f5)
            (self (tsubBV e (ReffieldType fi))(ExpFieldAccess e f5) )))

            (f5:(forall (g : env) (es : [expr]) (Ts : [type]) 
            (C : ClassName) (Fs : [RefFieldDecl]) (Us : [type]) 
            (fs : [var]),
          Us = map ReffieldType Fs ->
          fs = map ref Fs ->
          Forall isLC es ->
          Reffields C Fs ->
          Forall2 (Hastype g) es Ts ->
          Forall2 (P g) es Ts -> 
           Forall2 (Subtype (g)) Ts (map (tsubBV (ExpNew C es)) Us) ->
          P g (ExpNew C es) (self (TRefn (TNom (TClass C)) PEmpty) (ExpNew C es))))
            (f6: forall (g : env) (e : expr) (s t : type),
            g |--- e : s -> P g e s -> WFtype g t -> g |-s s <:: t -> P g e t)
            (f7: (forall (g : env) (e_x : expr) (b : type) (e : expr) 
            (b' : type) (nms : names),
          WFtype g b' ->
          g |--- e_x : b ->
          P g e_x b ->
          (forall y : vname, ~ Elem y nms -> Cons y b g |--- unbind y e : (unbindT y b')) ->
          (forall y : vname, ~ Elem y nms -> P (Cons y b g) (unbind y e) (unbindT y b')) ->
          P g (ExpLet e_x e) (self b' (ExpLet e_x e))))
    =>
    fix F (g:env) (e : expr) (c : type) (e0 : Hastype g e c) {struct e0} : P g e c :=
    match e0 in (Hastype g1 e1 c0) return (P g1 e1 c0) with
    | TBC g b => f0 g b
    | TIC g n => f1 g n
    | TVar g x b p1 p2 => f2 g x b p1 p2
    | TUnOP g e op t p1 p2 p3 => f3 g e op t p1 (F g e t p1) p2 p3
    | TBinOP g e1 e2 op t t' p1 p2 p3 p4 p5 p6 => f3' g e1 e2 op t t' p1 (F g e1 t p1) p2 p3 (F g e2 t' p3) p4 p5 p6 
    | TInvok g e1 e2 m t t' rt C ps ps' p1 p2 p22 p3 p4 p5 p6 => f3'' g e1 e2 m t t' rt C ps ps' p1 (F g e1 (TRefn (TNom (TClass C)) ps') p1) p2 p22 p3 (F g e2 t' p3) p4 p5 p6
    | TInvokI g e1 e2 m t t' rt C ps ps' p1 p2 p22 p3 p4 p5 p6 => f3''' g e1 e2 m t t' rt C ps ps' p1 (F g e1 (TRefn (TNom (TInterface C)) ps') p1) p2 p22 p3 (F g e2 t' p3) p4 p5 p6
    | TField g e f5 C Fs i fi ps p1 p2 p3 p4 p5=> f4 g e f5 C Fs i fi ps p1 p2 (F g e (TRefn (TNom (TClass C)) ps) p2) p3 p4 p5
    | TNew g es Ts C Fs Us fs p1 p2 p3 p4 p5 p6=> f5 g es Ts C Fs Us fs p1 p2 p3 p4 p5
                ((fix list_Forall_ind (es' : [expr]) (Cs' : [type]) 
                (map : Forall2 (Hastype g) es' Cs'): 
                Forall2 (P g) es' Cs' :=
                match map with
                | Forall2_nil _ => Forall2_nil (P g)
                | (@Forall2_cons _ _ _ ex cx ees ccs H1 H2) => Forall2_cons ex cx (F g ex cx H1) (list_Forall_ind ees ccs H2)
            end) es Ts p5) p6
    | TSub g e s t p1 p2 p3 => f6 g e s t p1 (F g e s p1) p2 p3
    | TLet g e_x b e b' nms p0 p1 p2 => f7 g e_x b e b' nms p0 p1 (F g e_x b p1) p2 (fun (y:vname) (pp: (~ Elem y nms)) => F (Cons y b g) (unbind y e) (unbindT y b') (p2 y pp) )
    end.



Definition Terminating g e:= forall th, DenotesEnv g th -> exists e', EvalsTo (csubst th e) e' /\ isValue e'.

(*no need for name quantification here*)
Definition wf_under C Ds := (forall y,  WFtype (Cons y C Empty) (openT_at 0 y Ds)).
Definition wf_under2 C Cs Ds := (forall y y', y <> y' -> WFtype (Cons y' (openT_at 0 y Cs) (Cons y C Empty)) (openT_at 1 y (openT_at 0 y' Ds))).

Definition subtype_under C Ds Cs:= (forall y, Subtype (Cons y C Empty) (openT_at 0 y Ds) (openT_at 0 y Cs)).
Definition subtype_under2 C Cs C0 D0:= (forall y y', y<>y' -> Subtype (Cons y' (openT_at 0 y Cs) (Cons y C Empty)) (openT_at 1 y (openT_at 0 y' C0)) (openT_at 1 y (openT_at 0 y' D0))) .
