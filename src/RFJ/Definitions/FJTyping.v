Require Import Relations Decidable.
Require Import Lists.
Require Import Forall2.
Require Import ZArith.
Require Import Crush.
Require Import Coq.Program.Equality.

Require Import RFJ.Utils.

Require Export Definitions.Syntax.
Require Export Definitions.Names.
Require Import Definitions.Semantics.
Require Import Definitions.SubDenotation.



(*---------------Types of the Primitives---------------*)

Definition tybc (b:bool) : type := 
TRefn TBool (PCons (ExpBinOp (Eq) (Bc b) (BV 0))  PEmpty).

Definition tyic (n:Z) : type :=
TRefn TInt  (PCons (ExpBinOp (Eq) (Ic n) (BV 0))  PEmpty).

Definition refn_pred (c:UnOp) : expr :=
match c with 
| Not      => (ExpBinOp (Eq) (ExpUnOp (Not) (BV 1)) (BV 0))
end.
    
Definition intype (c:UnOp) : type := 
match c with 
| Not     => TRefn TBool   PEmpty
end.

Definition ty' (c:UnOp) : type := 
match c with
| Not      =>  TRefn TBool (PCons (refn_pred Not) PEmpty)
end.

Definition refn_pred2 (c:BinOp) : expr :=
match c with 
| And      => (ExpBinOp (Eq) (ExpBinOp (And) (BV 2) (BV 1)) (BV 0)) 
| Or       => (ExpBinOp (Eq) (ExpBinOp (Or) (BV 2) (BV 1)) (BV 0))
| Eq       => (ExpBinOp (Eq) (ExpBinOp (Eq) (BV 2) (BV 1)) (BV 0))
end.
Definition intype2 (c:BinOp) : (type*type) := 
match c with 
| And     => (TRefn TBool PEmpty, TRefn TBool PEmpty)
| Or      => (TRefn TBool PEmpty, TRefn TBool PEmpty) 
| Eq      => (TRefn TAny PEmpty, TRefn TAny PEmpty) 
end.

Definition ty'2 (c:BinOp) : type := 
match c with
| And      => (TRefn TBool (PCons (refn_pred2 And) PEmpty))
| Or       => (TRefn TBool (PCons (refn_pred2 Or)  PEmpty))
| Eq       => (TRefn TBool (PCons (refn_pred2 Eq)  PEmpty))
end.


(*---------------FJ Typing---------------*)
Inductive HasFJtype : fjenv -> expr -> fjtype -> Prop := 
    | FTBC   : forall (g:fjenv) (b:bool),  HasFJtype g (Bc b) (TBool)
    | FTIC   : forall (g:fjenv) (n:Z),   HasFJtype g (Ic n) (TInt)
    | FTVar  : forall (g:fjenv) (x:vname) (b:fjtype),
        bound_inF x b g -> HasFJtype g (FV x) b
    | FTUnOP : forall (g:fjenv) (e:expr) (op: UnOp),
        HasFJtype g e (erase (intype op)) -> 
        HasFJtype g (ExpUnOp op e) (erase (ty' op))
    | FTBinOP : forall (g:fjenv) (e1 e2:expr) (op: BinOp),
        HasFJtype g e1 (erase (fst (intype2 op))) -> HasFJtype g e2 (erase (snd (intype2 op))) -> 
        HasFJtype g (ExpBinOp op e1 e2) (erase (ty'2 op))
    | FTInvok: forall (g:fjenv) (e1 :expr) (e2: expr) (m: MethodName) t rt C ps,
        HasFJtype g e1  (TNom (TClass C)) -> 
        mtype(m, C) = ps ~> t ~> rt ->
        HasFJtype (g) e2 (erase t) -> 
        HasFJtype g (ExpMethodInvoc e1 m e2) (erase rt)
    | FTInvokI: forall (g:fjenv) (e1 :expr) (e2: expr) (m: MethodName) t rt C ps,
        HasFJtype g e1 ((TNom (TInterface C))) -> 
        mtypei(m, C) = ps ~> t ~> rt ->
        HasFJtype (g) e2 (erase t) -> 
        HasFJtype g (ExpMethodInvoc e1 m e2) (erase rt)
    | FTField: forall g e f T C F i ff,
        HasFJtype g e ( (TNom (TClass C))) -> 
        Reffields C F -> 
        nth_error F i = Some ff ->
        ref ff = f ->
        ReffieldType ff = T ->
        HasFJtype g (ExpFieldAccess e f) (erase T)
    | FTNew:    forall g es C Fs Us fs, 
        Us = map erase (map ReffieldType Fs) -> 
        fs = map ReffieldName Fs -> 
        Reffields C Fs -> 
        Forall2 (HasFJtype g) es Us -> 
        HasFJtype g (ExpNew C es) ((TNom (TClass C)))
    | FTLet  : forall (g:fjenv) (e_x:expr) (b:fjtype) (e:expr) (b':fjtype) (nms:names),
        HasFJtype g e_x b 
            -> (forall (y:vname), ~ Elem y nms -> HasFJtype (FCons y b g) (unbind y e) b' )
            -> HasFJtype g (ExpLet e_x e) b'
    | FTSub  : forall (g:fjenv) (e:expr) (s:fjtype) (t:fjtype),
        HasFJtype g e s -> FJSubtype s t -> HasFJtype g e t 
.


Inductive PIsBool : fjenv -> preds -> Prop := 
    | PFTEmp  : forall (g:fjenv), PIsBool g PEmpty
    | PFTCons : forall (g:fjenv) (p:expr) (ps:preds),
        HasFJtype g p (TBool) -> PIsBool g ps -> PIsBool g (PCons p ps).
#[export] Hint Constructors HasFJtype.
#[export] Hint Constructors PIsBool.



Definition HasFJtype_ind' := 
    fun (P : fjenv -> expr -> fjtype -> Prop)
    (f : forall (g : fjenv) (b : bool), P g (Bc b) (TBool))
    (f0 : forall (g : fjenv) (n : Z), P g (Ic n) (TInt))
    (f1: forall (g : fjenv) (x : vname) (b : fjtype),
    bound_inF x b g -> P g (FV x) b)
    (f2: forall (g : fjenv) (e : expr) (op : UnOp),
    HasFJtype g e (erase (intype op)) ->
    P g e (erase (intype op)) -> 
    P g (ExpUnOp op e) (erase (ty' op)))
    (f3: (forall (g : fjenv) (e1 e2 : expr) (op : BinOp),
    HasFJtype g e1 (erase (fst (intype2 op))) ->
    P g e1 (erase (fst (intype2 op))) ->
    HasFJtype g e2 (erase (snd (intype2 op))) ->
    P g e2 (erase (snd (intype2 op))) ->
    P g (ExpBinOp op e1 e2) (erase (ty'2 op))))
    (f4: (forall (g : fjenv) (e1 : expr) (e2: expr) (m : MethodName) 
    (t:type) (rt : type) (C : ClassName) (ps: preds),
  HasFJtype g e1 ((TNom (TClass C))) ->
  P g e1 ((TNom (TClass C))) ->
  mtype(m, C) = ps ~> t ~> rt ->
  HasFJtype (g) e2 (erase t) -> 
  ((P g) e2 (erase t) -> 
  P g (ExpMethodInvoc e1 m e2) (erase rt))))
    (f4': (forall (g : fjenv) (e1 : expr) (e2: expr) (m : MethodName) 
    (t:type) (rt : type) (C : InterfaceName) (ps: preds),
    HasFJtype g e1 ((TNom (TInterface C))) ->
    P g e1 ((TNom (TInterface C))) ->
    mtypei(m, C) = ps ~> t ~> rt ->
    HasFJtype (g) e2 (erase t) -> 
    ((P g) e2 (erase t) -> 
    P g (ExpMethodInvoc e1 m e2) (erase rt))))
    (f5: (forall (g : fjenv) (e : expr) (f5 : var) 
    (T : type) (C : ClassName) (F : [RefFieldDecl]) 
    (i : nat) (ff : RefFieldDecl),
    (* isValue e -> *)
    HasFJtype g e (TNom (TClass C)) ->
    P g e (TNom (TClass C)) ->
    Reffields C F ->
    nth_error F i = Some ff ->
    ref ff = f5 ->
    ReffieldType ff = T -> 
    P g (ExpFieldAccess e f5) (erase T)) )
    (f6: (forall (g : fjenv) (es : [expr]) 
    (C : ClassName) (Fs : [RefFieldDecl]) (Us : [fjtype])
    (fs : [FieldName]),
  Us = map erase (map ReffieldType Fs) ->
  fs = map ReffieldName Fs ->
  Reffields C Fs ->
  Forall2 (HasFJtype g) es Us -> Forall2 (P g) es Us -> P g (ExpNew C es) (TNom (TClass C))))
    (f7: (forall (g : fjenv) (e_x : expr) (b : fjtype) 
    (e : expr) (b' : fjtype) (nms : names),
  HasFJtype g e_x b ->
  P g e_x b ->
  (forall y : vname,
   ~ Elem y nms -> HasFJtype (FCons y b g) (unbind y e) b') ->
  (forall y : vname, ~ Elem y nms -> P (FCons y b g) (unbind y e) b') ->
  P g (ExpLet e_x e) b'))
  (f8: (forall (g : fjenv) (e : expr) (s t : fjtype),
  HasFJtype g e s -> P g e s -> FJSubtype s t -> P g e t) )
    =>

    fix F (g:fjenv) (e : expr) (c : fjtype) (e0 : HasFJtype g e c) {struct e0} : P g e c :=
    match e0 in (HasFJtype g1 e1 c0) return (P g1 e1 c0) with
    | FTBC g b => f g b
    | FTIC g n => f0 g n
    | FTVar g x b bi => f1 g x b bi
    | FTUnOP g e op p1 => f2 g e op p1 (F g e (erase (intype op)) p1)
    | FTBinOP g e1 e2 op p1 p2 => f3 g e1 e2 op p1 (F g e1 (erase (fst (intype2 op))) p1) p2 (F g e2 (erase (snd (intype2 op))) p2)
    | FTInvok g e1 e2 m t rt C ps p1 p2 p3 => f4 g e1 e2 m t rt C ps p1 (F g e1 ((TNom (TClass C))) p1) p2 p3 (F g e2 (erase t) p3)
    | FTInvokI g e1 e2 m t rt C ps p1 p2 p3 => f4' g e1 e2 m t rt C ps p1 (F g e1 ((TNom (TInterface C))) p1) p2 p3 (F g e2 (erase t) p3)
    | FTField g e fz T C FF i ff p1 p2 p3 p4 p5  => f5 g e fz T C FF i ff p1 (F g e (TNom (TClass C)) p1) p2 p3 p4 p5
    | FTNew g es C Fs Us fs p1 p3 p4 p5 => f6 g es C Fs Us fs p1 p3 p4 p5 
                ((fix list_Forall_ind (es' : [expr]) (Cs' : [fjtype]) 
                (map : Forall2 (HasFJtype g) es' Cs'): 
                Forall2 (P g) es' Cs' :=
                match map with
                | Forall2_nil _ => Forall2_nil (P g)
                | (@Forall2_cons _ _ _ ex cx ees ccs H1 H2) => Forall2_cons ex cx (F g ex cx H1) (list_Forall_ind ees ccs H2)
            end) es Us p5)
    | FTLet g e_x b e b' nms p1 p2 => f7 g e_x b e b' nms p1 (F g e_x b p1) p2 (fun (y:vname) (pp: (~ Elem y nms)) => F (FCons y b g) (unbind y e) b' (p2 y pp) )
    | FTSub g e s t p1 p2 => f8 g e s t p1 (F g e s p1) p2 
    end.

