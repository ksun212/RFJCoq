Require Import Lists.
Require Import Program.
Require Import Arith.
Require Import ZArith.
Require Import RFJ.Utils.
Require Import Definitions.Syntax.
Require Import Definitions.Names.
Require Import Definitions.Semantics.
Require Import Definitions.FJTyping.



(*---------------Big-step Semantics---------------*)

Reserved Notation "th '|-' e '⇓' e1" (at level 60).

Reserved Notation "e '⇓' e1" (at level 60).
Inductive BStepEval: expr -> expr -> Prop := 
| BEValue: forall v, isValue v -> v ⇓ v 
| BEUnOp : forall (c:UnOp) (w : expr) (v: expr) (pf : isCompat c v), 
    w ⇓ v -> (ExpUnOp c w) ⇓ (udelta c v pf)
| BEBinOp : forall (c:BinOp) (e1 e2: expr) (v1 v2: expr) (pf : isCompat2 c v1 v2),
    e1 ⇓ v1 -> e2 ⇓ v2 -> (ExpBinOp c e1 e2) ⇓ (bdelta c v1 v2 pf)
| BEInvok: forall C e m v es e1 e2 e', 
    e1 ⇓ (ExpNew C es) -> e2 ⇓ v -> 
    mbody(m, C) = e->
    (subBV_at 1 (ExpNew C es) (subBV v e)) ⇓ e' -> 
    (ExpMethodInvoc e1 m e2) ⇓ e'
| BEAccess: forall e C es Fs i ei fi f, 
    e ⇓ (ExpNew C es) -> 
    Reffields C Fs ->
    nth_error Fs i = Some fi ->
    nth_error es i = Some ei-> 
    f = (ref fi) -> 
    (ExpFieldAccess e f) ⇓ ei
| BENew: forall C es es',
    Forall2 BStepEval es es' -> 
    (ExpNew C es) ⇓ (ExpNew C es')
| BELet: forall ex ex' e e', 
    ex ⇓ ex' -> (subBV ex' e) ⇓ e' -> 
    (ExpLet ex e) ⇓ e'
where "e '⇓' e1" := (BStepEval e e1).


Definition BStepEval_ind':= 
   fun (P : expr -> expr -> Prop)
  (f1: (forall v : expr, isValue v -> P v v)) 
  (f2: (forall (c : UnOp) (w v : expr) (pf : isCompat c v),
   w ⇓ v -> P w v -> P (ExpUnOp c w) (udelta c v pf)))
  (f: (forall (c : BinOp) (e1 e2 v1 v2 : expr) (pf : isCompat2 c v1 v2),
   e1 ⇓ v1 ->
   P e1 v1 ->
   e2 ⇓ v2 -> P e2 v2 -> P (ExpBinOp c e1 e2) (bdelta c v1 v2 pf)))
  (f4: (forall (C : ClassName) (e : expr) 
  (m : MethodName) (v : expr) (es : [expr]) 
  (e1 e2 e' : expr),
e1 ⇓ ExpNew C es ->
P e1 (ExpNew C es) ->
e2 ⇓ v ->
P e2 v ->
mbody( m, C)= e ->
subBV_at 1 (ExpNew C es) (subBV v e) ⇓ e' ->
P (subBV_at 1 (ExpNew C es) (subBV v e)) e' ->
P (ExpMethodInvoc e1 m e2) e'))
  (f5: forall (e : expr) (C : ClassName) (es : [expr]) 
     (Fs : [RefFieldDecl]) (i : nat) (ei : expr) 
     (fi : RefFieldDecl) (f : var),
   e ⇓ ExpNew C es ->
   P e (ExpNew C es) ->
   Reffields C Fs ->
   nth_error Fs i = Some fi ->
   nth_error es i = Some ei -> f = ref fi -> P (ExpFieldAccess e f) ei)
  (f6: forall (C : ClassName) (es es' : [expr]),
   Forall2 BStepEval es es' -> Forall2 P es es' -> P (ExpNew C es) (ExpNew C es'))
   (f7: forall ex ex' e e' : expr,
   ex ⇓ ex' -> P ex ex' -> subBV ex' e ⇓ e' -> P (subBV ex' e) e' -> P (ExpLet ex e) e')
   => 
    fix F (e1 : expr) (e2 : expr) (e0 : BStepEval e1 e2) :=
        match e0 in (BStepEval e1 e2) return (P e1 e2) with
        |BEValue v p1 => f1 v p1
        |BEUnOp c w v pf p1 => f2 c w v pf p1 (F w v p1)
        |BEBinOp c e1 e2 v1 v2 pf p1 p2 => f c e1 e2 v1 v2 pf p1 (F e1 v1 p1) p2 (F e2 v2 p2)
        |BEInvok C e m v es e1 e2 e' p1 p2 p3 p4 => f4 C e m v es e1 e2 e' p1 (F e1 (ExpNew C es) p1) p2 (F e2 v p2) p3 p4 (F (subBV_at 1 (ExpNew C es) (subBV v e)) e' p4)
        |BEAccess e C es Fs i ei fi f p1 p2 p3 p4 p5 => f5 e C es Fs i ei fi f p1 (F e (ExpNew C es) p1) p2 p3 p4 p5
        |BENew C es es' p1 => f6 C es es' p1 ((fix list_Forall_ind (es1 : [expr]) (es2 : [expr]) 
        (map : Forall2 (BStepEval) es1 es2): 
        Forall2 (P) es1 es2 :=
        match map with
        | Forall2_nil _ => Forall2_nil (P)
        | (@Forall2_cons _ _ _ ex cx ees ccs H1 H2) => Forall2_cons ex cx (F ex cx H1) (list_Forall_ind ees ccs H2)
    end) es es' p1)
        |BELet ex ex' e e' p1 p2 => f7 ex ex' e e' p1 (F ex ex' p1) p2 (F (subBV ex' e) e' p2)
        end.

  