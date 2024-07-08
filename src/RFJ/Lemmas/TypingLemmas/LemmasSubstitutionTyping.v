Require Import Arith.
Require Import Lists. 

Require Import Definitions.Syntax.
Require Import Definitions.Names.
Require Import Definitions.FJTyping.
Require Import Definitions.SubDenotation.

Require Import Definitions.Typing.
 
Require Import Definitions.Semantics. 
Require Import Definitions.CTSanity.

Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasFJTyping.
Require Import Lemmas.BasicLemmas.LemmasSubstitution.
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasEnvironments.
Require Import Lemmas.BasicLemmas.LemmasWF.
Require Import Lemmas.BasicLemmas.LemmasWFNarrow.
Require Import Lemmas.BasicLemmas.LemmasWFWeaken.
Require Import Lemmas.BasicLemmas.LemmasWF.
Require Import Lemmas.BasicLemmas.LemmasWFNarrow.
Require Import Lemmas.BasicLemmas.LemmasWFSubstitution.
Require Import Lemmas.TypingLemmas.LemmasTyping.
Require Import Lemmas.TypingLemmas.LemmasWeakenTyp.
Require Import Lemmas.BasicLemmas.LemmasExactness.
Require Import Lemmas.BasicLemmas.LemmasTypeSubstitution. 
Require Import Lemmas.LogicalLemmas.LemmasDenotesEnv. 
Require Import Lemmas.LogicalLemmas.LemmasDenotesTyping. 
Require Import Lemmas.TypingLemmas.LemmasNarrowing. 
Require Import Lemmas.BasicLemmas.LemmasPrimitivesBasics. 
Require Import Lemmas.BasicLemmas.LemmasFJWeaken. 
Require Import Lemmas.BasicLemmas.LemmasCTBasics.


(*---------------The Substitution Lemmas---------------*)

Lemma ISub: forall (g:env) (g':env) (x:vname) (v_x:expr) (t_x:type) (ps:preds) (qs:preds),
        intersect (binds g) (binds g') = empty -> unique g -> unique g' 
            -> ~ in_env x g -> ~ in_env x g' -> WFEnv g
            -> isValue v_x -> Hastype g v_x t_x
            -> LImplies (concatE (Cons x t_x g) g') ps qs
            -> LImplies (concatE g (esubFV x v_x g')) (psubFV x v_x ps) (psubFV x v_x qs).
Proof. intros.
    apply SImp; intros th Hden Hps.
    inversion H.
    apply add_var_denotessenv with g g' x v_x t_x th  in Hden as Hth';auto.
    destruct Hth' as [th']. destruct H8. destruct H10. destruct H11.
    rewrite <- H12.  rewrite <- H12 in Hps.
    inversion H7. apply H13;auto.
    apply fv_subset_binds with t_x;auto.

    (*prove g' has nothing to do with the denotation of t_x:v_x*)
    apply extend_denotess with g (esubFV x v_x g');auto. eapply typing_wf;eauto.
    intros.
    apply typing_denotes' with g;auto.
    apply typing_wf with v_x;auto. 
Qed.


Lemma ISub2: forall (g:env) (g':env) (x x':vname) (v_x v_x':expr) (t_x t_x':type) (ps:preds) (qs:preds),
        intersect (binds g) (binds g') = empty -> unique g -> unique g' 
            -> ~ in_env x g -> ~ in_env x g' -> WFEnv g 
            -> ~ in_env x' g -> ~ in_env x' g' -> x' <> x
            -> isValue v_x -> Hastype g v_x t_x 
            -> isValue v_x' -> Hastype g v_x' (tsubBV v_x t_x')
            -> LImplies (concatE (Cons x' (openT_at 0 x t_x') (Cons x t_x g)) g') ps qs
            -> LImplies (concatE g (esubFV x v_x (esubFV  x' v_x' g'))) (psubFV x v_x (psubFV x' v_x' ps)) (psubFV x v_x (psubFV x' v_x' qs)).
Proof. intros.
    apply SImp; intros th Hden Hps.
    inversion H12.
    assert (exists th', DenotesEnv (concatE (Cons x' (openT_at 0 x t_x') (Cons x t_x g)) g') th' /\ 
    (forall e, csubst th' e = csubst th (subFV x v_x (subFV x' v_x' e))) /\        
    (forall t, ctsubst th' t = ctsubst th (tsubFV x v_x (tsubFV x' v_x' t))) /\ 
    (forall ps, cpsubst th' ps = cpsubst th (psubFV x v_x (psubFV x' v_x' ps)))) as Hth'.
    apply add_var_denotessenv2;auto.
    apply fv_subset_binds with t_x;auto. 
    apply extend_denotess with g (esubFV x v_x (esubFV x' v_x' g'));auto. eapply typing_wf;eauto.
    intros.
    apply typing_denotes' with g;auto.
    apply typing_wf with v_x;auto.
    apply typing_wf with v_x';auto.
    apply fv_subset_binds with (tsubBV v_x t_x');auto.
    apply extend_denotess with g (esubFV x v_x (esubFV x' v_x' g'));auto. eapply typing_wf;eauto.
    intros.
    apply typing_denotes' with g;auto.
    destruct Hth' as [th']. destruct H17. destruct H18. destruct H19.
    rewrite <- H20.  rewrite <- H20 in Hps.
    apply H13;auto.
Qed.


Lemma subst_subtype2' : (
  forall (g'xg : env) (t : type) (t' : type),
    Subtype g'xg t t' -> ( forall (g g':env) (x x':vname) (v_x v_x':expr) (t_x t_x':type),
      g'xg = concatE (Cons x' (openT_at 0 x t_x') (Cons x t_x g)) g' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> ~ (in_env x' g) -> ~ (in_env x' g') 
            
            -> isValue v_x -> Hastype g v_x t_x -> WFEnv (concatE (Cons x' (openT_at 0 x t_x') (Cons x t_x g)) g' )
            -> g |--- v_x' : tsubBV v_x t_x' -> isValue v_x'
            -> WFtype (concatE (Cons x' (openT_at 0 x t_x') (Cons x t_x g)) g' ) t 
            -> WFtype (concatE (Cons x' (openT_at 0 x t_x') (Cons x t_x g)) g' ) t' 
            -> Subtype (concatE g (esubFV x v_x (esubFV x' v_x' g'))) (tsubFV x v_x (tsubFV x' v_x' t)) (tsubFV x v_x (tsubFV x' v_x' t') ))).
Proof.
  apply ( Subtype_ind 
  (fun (g'xg : env) (t : type) (t' : type) =>  ( forall (g g':env) (x x':vname) (v_x v_x':expr) (t_x t_x':type),
  g'xg = concatE (Cons x' (openT_at 0 x t_x') (Cons x t_x g)) g' 
        -> unique g -> unique g'
        -> intersect (binds g) (binds g') = empty
        -> ~ (in_env x g) -> ~ (in_env x g') 
        -> ~ (in_env x' g) -> ~ (in_env x' g') 
        -> isValue v_x -> Hastype g v_x t_x -> WFEnv (concatE (Cons x' (openT_at 0 x t_x') (Cons x t_x g)) g' )
        -> g |--- v_x' : tsubBV v_x t_x' -> isValue v_x'
        -> WFtype (concatE (Cons x' (openT_at 0 x t_x') (Cons x t_x g)) g' ) t 
        -> WFtype (concatE (Cons x' (openT_at 0 x t_x') (Cons x t_x g)) g' ) t' 
        -> Subtype (concatE g (esubFV x v_x (esubFV x' v_x' g'))) (tsubFV x v_x (tsubFV x' v_x' t)) (tsubFV x v_x (tsubFV x' v_x' t') ))));
  intro env; intros; subst env.
  -
    simpl; apply SBase with (union (singleton x) (union (singleton x') (union nms (union (binds g) (binds g')))));auto.
    apply truncate_wfenv in H11 as H11'; inversion H11'. inversion H18. subst x0 t g0. subst x1. subst t0. subst g1.

    intros; 
    assert (x <> y). assert (y<>x). apply not_elem_singleton;notin_solve_one. auto. assert (x' <> y). assert (y<>x'). apply not_elem_singleton;notin_solve_one. auto. assert (isLC v_x). eapply typ_islc;eauto. assert (isLC v_x').  eapply typ_islc;eauto.
    repeat rewrite <- commute_psubFV_unbindP;auto.
    assert ( Cons y (TRefn b1 PEmpty) (concatE g (esubFV x v_x (esubFV x' v_x' g')))
              = concatE g (esubFV x v_x (esubFV x' v_x' (Cons y (TRefn b1 PEmpty) g'))) )
      as Henv by reflexivity. rewrite Henv.
      unfold in_env in H19. simpl in H19. apply not_elem_names_add_elim in H19. destruct H19. 
    apply ISub2 with t_x t_x'; simpl;auto.
    apply intersect_names_add_intro_r. auto. notin_solve_one.
    constructor;auto. unfold in_env. notin_solve_one.
    unfold in_env. simpl. apply not_elem_names_add_intro. constructor;auto.
    unfold in_env. simpl. apply not_elem_names_add_intro. constructor;auto. 
    
    apply H0. notin_solve_one.   
Qed.

Lemma subst_subtype' : (
  forall (g'xg : env) (t : type) (t' : type),
    Subtype g'xg t t' -> ( forall (g g':env) (x:vname) (v_x:expr) (t_x:type),
      g'xg = concatE (Cons x t_x g) g' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> isValue v_x -> Hastype g v_x t_x -> WFEnv (concatE (Cons x t_x g) g')
            -> WFtype (concatE (Cons x t_x g) g') t 
            -> WFtype (concatE (Cons x t_x g) g') t' 
            -> Subtype (concatE g (esubFV x v_x g')) (tsubFV x v_x t) (tsubFV x v_x t') )).
Proof.
  apply ( Subtype_ind 
  (fun (g'xg : env) (t : type) (t' : type) => ( forall (g g':env) (x:vname) (v_x:expr) (t_x:type),
    g'xg = concatE (Cons x t_x g) g' 
          -> unique g -> unique g'
          -> intersect (binds g) (binds g') = empty
          -> ~ (in_env x g) -> ~ (in_env x g') 
          -> isValue v_x -> Hastype g v_x t_x -> WFEnv (concatE (Cons x t_x g) g')
          -> WFtype (concatE (Cons x t_x g) g') t 
          -> WFtype (concatE (Cons x t_x g) g') t' 
          -> Subtype (concatE g (esubFV x v_x g')) (tsubFV x v_x t) (tsubFV x v_x t') )));
  intro env; intros; subst env.
  -
    simpl; apply SBase with (names_add x (union nms (binds (concatE g g'))));auto.
    apply truncate_wfenv in H9 as H9'; inversion H9'; subst x0 t g0.
    intros; repeat rewrite <- commute_psubFV_unbindP; 
    assert ( Cons y (TRefn b1 PEmpty) (concatE g (esubFV x v_x g'))
              = concatE g (esubFV x v_x (Cons y (TRefn b1 PEmpty) g')) )
      as Henv by reflexivity; try rewrite Henv;
    try apply ISub with t_x; simpl; try apply i;
    apply not_elem_names_add_elim in H1; destruct H1;
    apply not_elem_union_elim in H12; destruct H12;
    apply not_elem_concat_elim in H13; destruct H13;
    try apply typ_islc with g t_x;
    try apply not_elem_names_add_intro;
    try apply intersect_names_add_intro_r;
    simpl; try split; intuition.
    apply H0 in H12. inversion H12. apply H20;auto.
Qed.

Lemma subst_typ_forall: forall es Ts x t_x g g' v_x, 
concatE (Cons x t_x g) g' = concatE (Cons x t_x g) g' -> unique g -> 
unique g' -> intersect (binds g) (binds g') = empty -> ~ in_env x g -> ~ in_env x g' -> 
isValue v_x -> g |--- v_x : t_x -> WFEnv (concatE (Cons x t_x g) g') ->
List.Forall2 (fun (e : expr) (t : type) =>
 forall (g0 g'0 : env) (x0 : vname) (v_x : expr) (t_x0 : type),
 concatE (Cons x t_x g) g' = concatE (Cons x0 t_x0 g0) g'0 ->
 unique g0 ->
 unique g'0 ->
 intersect (binds g0) (binds g'0) = empty ->
 ~ in_env x0 g0 ->
 ~ in_env x0 g'0 ->
 isValue v_x ->
 g0 |--- v_x : t_x0 ->
 WFEnv (concatE (Cons x0 t_x0 g0) g'0) ->
 concatE g0 (esubFV x0 v_x g'0) |--- subFV x0 v_x e : tsubFV x0 v_x t) es Ts -> 
 List.Forall2 (Hastype (concatE g (esubFV x v_x g')))
  ((fix f (es' : [expr]) : [expr] :=
      match es' with
      | nil => nil
      | (e :: es'')%list =>
          (
              (fix subFV (x0 : vname) (v_x0 e0 : expr) {struct e0} : expr :=
                 match e0 with
                 | Bc b => Bc b
                 | Ic n => Ic n
                 | BV i => BV i
                 | FV y => if x0 =? y then v_x0 else FV y
                 | ExpUnOp op e1 => ExpUnOp op (subFV x0 v_x0 e1)
                 | ExpBinOp op e1 e' => ExpBinOp op (subFV x0 v_x0 e1) (subFV x0 v_x0 e')
                 | ExpFieldAccess e1 f0 => ExpFieldAccess (subFV x0 v_x0 e1) f0
                 | ExpMethodInvoc e1 m e' => ExpMethodInvoc (subFV x0 v_x0 e1) m (subFV x0 v_x0 e')
                 | ExpNew c es0 =>
                     ExpNew c
                       ((fix f0 (es'0 : [expr]) : [expr] :=
                           match es'0 with
                           | nil => nil
                           | e1 :: es''0 => subFV x0 v_x0 e1 :: f0 es''0
                           end) es0)
                 | ExpLet e1 e2 => ExpLet (subFV x0 v_x0 e1) (subFV x0 v_x0 e2)
                 end
               with tsubFV (x0 : vname) (v_x0 : expr) (t0 : type) {struct t0} : type :=
                 match t0 with
                 | TRefn b r => TRefn b (psubFV x0 v_x0 r)
                 end
               with psubFV (x0 : vname) (v_x0 : expr) (ps0 : preds) {struct ps0} : preds :=
                 match ps0 with
                 | PEmpty => PEmpty
                 | PCons p ps => PCons (subFV x0 v_x0 p) (psubFV x0 v_x0 ps)
                 end
            for
            subFV) x v_x e :: f es'')%list
      end) es) (map (tsubFV x v_x) Ts).
Proof.
  intros.
  generalize dependent Ts.
  induction es.
  intros. destruct Ts. apply Forall2_nil. inversion H8.
  intros. destruct Ts. inversion H8.
  inversion H8. apply Forall2_cons. eapply H12;eauto.
  apply IHes;auto.
Qed.

Lemma subst_subtype_forall: forall es Ts x t_x g g' v_x Us C, 
concatE (Cons x t_x g) g' = concatE (Cons x t_x g) g' -> unique g -> 
unique g' -> intersect (binds g) (binds g') = empty -> ~ in_env x g -> ~ in_env x g' -> isLC v_x -> 
isValue v_x -> g |--- v_x : t_x -> WFEnv (concatE (Cons x t_x g) g') ->
Forall (WFtype (concatE (Cons x t_x g) g')) Ts ->
Forall (WFtype (concatE (Cons x t_x g) g'))  (map (tsubBV (ExpNew C es))  Us) -> 
Forall2 (Subtype (concatE (Cons x t_x g) g')) Ts
       (map (tsubBV (ExpNew C es)) Us) -> 
Forall2 (Subtype (concatE g (esubFV x v_x g'))) (map (tsubFV x v_x) Ts)
  (map
     (tsubBV
        (ExpNew C
           ((fix f (es' : [expr]) : [expr] :=
               match es' with
               | nil => nil
               | e :: es'' =>
                   (fix subFV (x0 : vname) (v_x0 e0 : expr) {struct e0} : expr :=
                      match e0 with
                      | Bc b => Bc b
                      | Ic n => Ic n
                      | BV i => BV i
                      | FV y => if x0 =? y then v_x0 else FV y
                      | ExpUnOp op e1 => ExpUnOp op (subFV x0 v_x0 e1)
                      | ExpBinOp op e1 e' => ExpBinOp op (subFV x0 v_x0 e1) (subFV x0 v_x0 e')
                      | ExpFieldAccess e1 f0 => ExpFieldAccess (subFV x0 v_x0 e1) f0
                      | ExpMethodInvoc e1 m e' =>
                          ExpMethodInvoc (subFV x0 v_x0 e1) m (subFV x0 v_x0 e')
                      | ExpNew c es0 =>
                          ExpNew c
                            ((fix f0 (es'0 : [expr]) : [expr] :=
                                match es'0 with
                                | nil => nil
                                | e1 :: es''0 => subFV x0 v_x0 e1 :: f0 es''0
                                end) es0)
                      | ExpLet e1 e2 => ExpLet (subFV x0 v_x0 e1) (subFV x0 v_x0 e2)
                      end
                    with tsubFV (x0 : vname) (v_x0 : expr) (t0 : type) {struct t0} : type :=
                      match t0 with
                      | TRefn b r => TRefn b (psubFV x0 v_x0 r)
                      end
                    with psubFV (x0 : vname) (v_x0 : expr) (ps0 : preds) {struct ps0} :
                        preds :=
                      match ps0 with
                      | PEmpty => PEmpty
                      | PCons p ps => PCons (subFV x0 v_x0 p) (psubFV x0 v_x0 ps)
                      end
                    for
                    subFV) x v_x e :: f es''
               end) es))) (map (tsubFV x v_x) Us)).
Proof.
  intros.
  generalize dependent Us.
  induction Ts.
  intros. destruct Us. simpl. apply Forall2_nil. inversion H11.
  intros. destruct Us. inversion H11.
  inversion H11.  inversion H10. inversion H9. apply Forall2_cons.
  assert (ExpNew C ((fix f (es' : [expr]) : [expr] :=
  match es' with
  | nil => nil
  | e :: es'' =>
  (fix subFV (x0 : vname) (v_x0 e0 : expr) {struct e0} : expr :=
  match e0 with
  | Bc b => Bc b
  | Ic n => Ic n
  | BV i => BV i
  | FV y => if x0 =? y then v_x0 else FV y
  | ExpUnOp op e1 => ExpUnOp op (subFV x0 v_x0 e1)
  | ExpBinOp op e1 e' => ExpBinOp op (subFV x0 v_x0 e1) (subFV x0 v_x0 e')
  | ExpFieldAccess e1 f0 => ExpFieldAccess (subFV x0 v_x0 e1) f0
  | ExpMethodInvoc e1 m e' =>
      ExpMethodInvoc (subFV x0 v_x0 e1) m (subFV x0 v_x0 e')
  | ExpNew c es0 =>
      ExpNew c
        ((fix f0 (es'0 : [expr]) : [expr] :=
            match es'0 with
            | nil => nil
            | e1 :: es''0 => subFV x0 v_x0 e1 :: f0 es''0
            end) es0)
  | ExpLet e1 e2 => ExpLet (subFV x0 v_x0 e1) (subFV x0 v_x0 e2)
  end
with tsubFV (x0 : vname) (v_x0 : expr) (t0 : type) {struct t0} : type :=
  match t0 with
  | TRefn b r => TRefn b (psubFV x0 v_x0 r)
  end
with psubFV (x0 : vname) (v_x0 : expr) (ps0 : preds) {struct ps0} :
    preds :=
  match ps0 with
  | PEmpty => PEmpty
  | PCons p ps => PCons (subFV x0 v_x0 p) (psubFV x0 v_x0 ps)
  end
       for
       subFV) x v_x e :: f es''
  end) es) = subFV x v_x (ExpNew C es)). reflexivity.
  rewrite H26. rewrite <- commute_tsubFV_tsubBV;auto.
  apply subst_subtype' with (concatE (Cons x t_x g) g') t_x;auto. 
  apply IHTs;auto.
Qed.



Lemma subst_subtype_forall': forall Ts x t_x g g' v_x Us y, 
concatE (Cons x t_x g) g' = concatE (Cons x t_x g) g' -> unique g -> 
unique g' -> intersect (binds g) (binds g') = empty -> ~ in_env x g -> ~ in_env x g' -> isLC v_x -> 
isValue v_x -> g |--- v_x : t_x -> WFEnv (concatE (Cons x t_x g) g') ->
Forall (WFtype (concatE (Cons x t_x g) g')) Ts ->
Forall (WFtype (concatE (Cons x t_x g) g'))  (map (openT_at 0 y) Us) -> 
Forall2 (Subtype (concatE (Cons x t_x g) g')) Ts
  (map (openT_at 0 y) Us) -> 
Forall2 (Subtype (concatE g (esubFV x v_x g'))) (map (tsubFV x v_x) Ts)
(map (tsubFV x v_x) (map (openT_at 0 y) Us)).
Proof.
  
  intros.
  generalize dependent Us.
  induction Ts.
  intros. destruct Us. simpl. apply Forall2_nil. inversion H11.
  intros. destruct Us. inversion H11.
  inversion H11.  inversion H10. inversion H9. apply Forall2_cons.
  apply subst_subtype' with (concatE (Cons x t_x g) g') t_x;auto. 
  apply IHTs;auto.
Qed.

Lemma commute_forall: forall x v_x vv Us, isLC v_x -> 
((map (tsubBV (subFV x v_x vv)) (map (tsubFV x v_x) Us)) =  (map (tsubFV x v_x) (map (tsubBV vv) Us))).
Proof.
  intros.
  induction Us.
  simpl. reflexivity.
  simpl. f_equal.
  rewrite <- commute_tsubFV_tsubBV ;auto.
  apply IHUs.
Qed.
Lemma commute_forall': forall x v_x Us y, isLC v_x -> x <> y -> map (openT_at 0 y) (map (tsubFV x v_x) Us) =
map (tsubFV x v_x) (map (openT_at 0 y) Us).
Proof.
  intros.
  induction Us.
  simpl. reflexivity.
  simpl. f_equal.
  rewrite <- commute_tsubFV_unbindT ;auto.
  apply IHUs.
Qed.
Lemma tsubFV_notin_forall: forall x v Ts, Forall (fun t => (~ Elem x (free t))) Ts -> map (tsubFV x v) Ts = Ts.
Proof.
  intros.
  induction H.
  simpl. reflexivity.
  simpl. f_equal.
  apply tsubFV_notin. auto.
  apply IHForall.
Qed.
Lemma tsubFV_intype: forall op x v_x, intype op = tsubFV x v_x (intype op).
Proof.
  intros. destruct op. simpl. reflexivity.
Qed.
Lemma tsubFV2_intype: forall op x v_x x' v_x', intype op = tsubFV x v_x (tsubFV x' v_x' (intype op)).
Proof.
  intros. destruct op. simpl. reflexivity.
Qed.
Lemma tsubFV2_intype2: forall op x v_x x' v_x', fst(intype2 op) = tsubFV x v_x (tsubFV x' v_x' (fst(intype2 op))).
Proof.
  intros. destruct op; simpl; reflexivity.
Qed.
Lemma tsubFV2_intype2': forall op x v_x x' v_x', snd(intype2 op) = tsubFV x v_x (tsubFV x' v_x' (snd(intype2 op))).
Proof.
  intros. destruct op; simpl; reflexivity.
Qed.

Lemma tsubFV_intype2: forall op x v_x, fst(intype2 op) = tsubFV x v_x (fst(intype2 op)).
Proof.
  intros. destruct op; unfold intype2; simpl; reflexivity.
Qed.
Lemma tsubFV_intype2': forall op x v_x, snd(intype2 op) = tsubFV x v_x (snd(intype2 op)).
Proof.
  intros. destruct op; unfold intype2; simpl; reflexivity.
Qed.

Lemma tsubFV_ty': forall op x v_x e, tsubFV x v_x (tsubBV e (ty' op)) = (tsubBV (subFV x v_x e) (ty' op)).
Proof.
  intros. destruct op. unfold tsubFV. unfold tsubBV. simpl. reflexivity. 
Qed.
(*tsubFV only works for expression when the type is closed. *)
Lemma subFV_rt: forall x v_x e1 e2 rt, ~ Elem x (free rt) -> isLC v_x -> (tsubFV x v_x (tsubBV_at 1 e1 (tsubBV e2 rt)) = (tsubBV_at 1 (subFV x v_x e1) (tsubBV (subFV x v_x e2) rt))).
Proof.
  intros. 
  assert (tsubFV x v_x (tsubBV_at 1 e1 (tsubBV e2 rt)) = tsubBV_at 1 (subFV x v_x e1) (tsubFV x v_x (tsubBV e2 rt))). apply commute_subFV_subBV_at. auto. rewrite H1. 
  assert (tsubFV x v_x (tsubBV e2 rt) = tsubBV (subFV x v_x e2) (tsubFV x v_x rt)). apply commute_subFV_subBV_at. auto. rewrite H2.
  assert (tsubFV x v_x rt = rt). apply tsubFV_notin. auto. rewrite H3.
  reflexivity.
Qed.

Lemma subFV_rt2: forall x x' v_x v_x' e1 e2 rt, ~ Elem x (free rt) -> ~ Elem x' (free rt) -> isLC v_x -> isLC v_x' -> (tsubFV x v_x (tsubFV x' v_x' (tsubBV_at 1 e1 (tsubBV e2 rt))) = (tsubBV_at 1 (subFV x v_x (subFV x' v_x' e1)) (tsubBV (subFV x v_x (subFV x' v_x' e2)) rt))).
Proof.
  intros. 
  assert (tsubFV x' v_x' (tsubBV_at 1 e1 (tsubBV e2 rt)) = tsubBV_at 1 (subFV x' v_x' e1) (tsubFV x' v_x' (tsubBV e2 rt))). apply commute_subFV_subBV_at. auto. rewrite H3. 
  assert (tsubFV x' v_x' (tsubBV e2 rt) = tsubBV (subFV x' v_x' e2) (tsubFV x' v_x' rt)). apply commute_subFV_subBV_at. auto. rewrite H4.
  assert (tsubFV x' v_x' rt = rt). apply tsubFV_notin. auto. rewrite H5.
  assert (tsubFV x v_x (tsubBV_at 1 (subFV x' v_x' e1) (tsubBV (subFV x' v_x' e2) rt)) = tsubBV_at 1 (subFV x v_x (subFV x' v_x' e1)) (tsubFV x v_x (tsubBV (subFV x' v_x' e2) rt))). apply commute_subFV_subBV_at. auto. rewrite H6. 
  assert (tsubFV x v_x (tsubBV (subFV x' v_x' e2) rt) = tsubBV (subFV x v_x (subFV x' v_x' e2)) (tsubFV x v_x rt)). apply commute_subFV_subBV_at. auto. rewrite H7.
  assert (tsubFV x v_x rt = rt). apply tsubFV_notin. auto. rewrite H8.
  reflexivity.
Qed.

Lemma subFV_rt': forall x v_x e1 rt, ~ Elem x (free rt) -> isLC v_x -> (tsubFV x v_x (tsubBV e1 rt)) = (tsubBV (subFV x v_x e1) (rt)).
Proof.
  intros. 
  assert (tsubFV x v_x ((tsubBV e1 rt)) = tsubBV (subFV x v_x e1) (tsubFV x v_x rt)). apply commute_subFV_subBV_at. auto. rewrite H1. 
  assert (tsubFV x v_x rt = rt). apply tsubFV_notin. auto. rewrite H2.
  reflexivity.
Qed. 

Lemma subFV_rt2': forall x x' v_x v_x' e1 rt, ~ Elem x (free rt) -> ~ Elem x' (free rt) -> isLC v_x -> isLC v_x' -> (tsubFV x v_x (tsubFV x' v_x' (tsubBV e1 rt)) = (tsubBV (subFV x v_x (subFV x' v_x' e1)) (rt))).
Proof.
  intros. 
  assert (tsubFV x' v_x' ((tsubBV e1 rt)) = tsubBV (subFV x' v_x' e1) (tsubFV x' v_x' rt)). apply commute_subFV_subBV_at. auto. rewrite H3. 
  assert (tsubFV x' v_x' rt = rt). apply tsubFV_notin. auto. rewrite H4.
  assert (tsubFV x v_x (tsubBV (subFV x' v_x' e1) rt) = tsubBV (subFV x v_x (subFV x' v_x' e1)) (tsubFV x v_x (rt))). apply commute_subFV_subBV_at. auto. rewrite H5. 
  assert (tsubFV x v_x rt = rt). apply tsubFV_notin. auto. rewrite H6.
  reflexivity.
Qed. 

Lemma ty'2_no_fv: forall op, free (ty'2 op) = empty.
Proof.
  intros.
  destruct op;simpl;auto.
Qed.
Lemma ty'_no_fv: forall op, free (ty' op) = empty.
Proof.
  intros.
  destruct op;simpl;auto.
Qed.
(*waiting class table assumptions*)
Lemma subst_typ': ( forall (g'xg : env) (e : expr) (t : type),
Hastype g'xg e t -> ( forall (g g':env) (x:vname) (v_x:expr) (t_x:type),
    g'xg = concatE (Cons x t_x g) g' 
        -> unique g -> unique g'
        -> intersect (binds g) (binds g') = empty
        -> ~ (in_env x g) -> ~ (in_env x g') 
        -> isValue v_x -> Hastype g v_x t_x -> WFEnv (concatE (Cons x t_x g) g')
        -> Hastype (concatE g (esubFV x v_x g')) (subFV x v_x e) (tsubFV x v_x t ) )).
Proof. apply ( Hastype_ind' 
  (fun (g'xg : env) (e : expr) (t : type)  => 
    forall (g g':env) (x:vname) (v_x:expr) (t_x:type),
      g'xg = concatE (Cons x t_x g) g' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> isValue v_x -> Hastype g v_x t_x -> WFEnv (concatE (Cons x t_x g) g')
            -> Hastype (concatE g (esubFV x v_x g')) (subFV x v_x e) (tsubFV x v_x t ) ));
    intro env; intros; subst env.
  - 
    apply TBC.
  - 
    apply TIC.
  -
    simpl. case_eq (x0=?x).
    + (*x0=x, real subst*)
      intros. apply beq_nat_true in H1. subst x0.
      apply boundin_concat in H. destruct H.
      * (* x is not in g'*)
      simpl in H. destruct H.
      ** (* x not is in g*)
        destruct H. subst t_x.
        rewrite tsubFV_self. simpl. case_eq (x=?x).
        intros.
        assert (WFEnv g). assert (WFEnv ((Cons x t g))). apply truncate_wfenv with g';auto. inversion H10;auto.
        assert (WFtype g t). apply typing_wf with v_x;auto. assert (WFEnv ((Cons x t g))). apply truncate_wfenv with g';auto.
        assert (~ Elem x (free t)). apply free_bound_in_env with g;auto.
        rewrite tsubFV_notin;auto.
        apply exact_type;auto.
        apply weaken_many_typ;auto. apply esubFV_unique;auto. rewrite esubFV_binds;auto.
        apply subst_wfenv with t;auto. apply value_lc;auto. apply typing_hasfjtype;auto.
        rewrite <- tsubFV_notin with t x v_x;auto. apply subst_wf with t;auto. apply value_lc;auto. apply typing_hasfjtype;auto.
        apply subst_wfenv with t;auto. apply value_lc;auto.  apply typing_hasfjtype;auto.
        
        intros. apply beq_nat_false in H1. contradiction.

      ** (* x is in g*)
        unfold in_env in H5. apply boundin_inenv in H. contradiction. 
      * (* x is in g'*)
        unfold in_env in H6. apply boundin_inenv in H. contradiction. 
    + (*x0<>x, just weaken*)
      intros.
      rewrite tsubFV_self. simpl. case_eq (x0=?x). intro. apply beq_nat_false in H1.  apply beq_nat_true in H10. rewrite H10 in H1. contradiction.
      intro. assert (WFtype (concatE g (esubFV x0 v_x g')) (tsubFV x0 v_x t)).
      assert (WFEnv g). assert (WFEnv ((Cons x0 t_x g))). apply truncate_wfenv with g';auto. inversion H11;auto.
      apply subst_wf with t_x;auto. apply value_lc;auto.  apply typing_hasfjtype;auto. 
      apply TVar;auto.  apply boundin_concat in H. destruct H.
      * 
      (* x is not in g'*)
      destruct H.
      **  (* x not is in g*)
        destruct H. apply beq_nat_false in H1. rewrite H in H1. contradiction.
      ** (*x is in g*)
        rewrite tsubFV_notin;auto. apply boundin_concat. left;auto.
        apply truncate_wfenv in H9. inversion H9. assert (WFtype g t). apply boundin_wfenv_wftype with x;auto. apply free_bound_in_env with g;auto.
      * (*x is in g'*) 
        apply boundin_concat. right. apply boundin_esubFV;auto.
  -
    simpl.
    assert (tsubFV x v_x (tsubBV e (ty' op)) = (tsubBV (subFV x v_x e) (ty' op))). apply tsubFV_ty'. rewrite H3.
    eapply TUnOP;eauto.
    +
      assert (tsubFV x v_x (intype op) = intype op). rewrite tsubFV_notin;auto. destruct op; simpl;auto. auto. rewrite <- H12.
      apply subst_subtype' with (concatE (Cons x t_x g) g') t_x;auto.
      ++
        eapply typing_wf;eauto.
      ++
        apply wf_intype;auto.
    +
      apply subFV_lc;auto.  apply value_lc. auto.
  -
    simpl.
    assert (tsubFV x v_x (tsubBV_at 1 e1 (tsubBV e2 (ty'2 op))) = tsubBV_at 1 (subFV x v_x e1) (tsubBV (subFV x v_x e2) (ty'2 op))). rewrite commute_tsubFV_tsubBV'.  rewrite commute_tsubFV_tsubBV.  rewrite tsubFV_notin. auto. rewrite ty'2_no_fv. simpl;auto. apply value_lc;auto. apply value_lc;auto. rewrite H7.
    assert True. auto.
    assert (wf_under (fst (intype2 op)) (snd (intype2 op))). eapply wf_intype2s;eauto. unfold wf_under in H17.
    eapply TBinOP;eauto.
    + 
      assert (tsubFV x v_x (fst (intype2 op)) = fst (intype2 op)). rewrite tsubFV_notin;auto. destruct op; simpl;auto. auto. rewrite <- H18.
      eapply subst_subtype';eauto. apply typing_wf with e1;auto. assert(concatE (concatE (Cons x t_x g) g') Empty = (concatE (Cons x t_x g) g')). simpl. auto. rewrite <-H19. apply weaken_many_wf_r;simpl;auto. eapply wf_intype2f;eauto. apply wfenv_unique;auto. apply intersect_empty_r. 
    +

      assert (tsubFV x v_x (snd (intype2 op)) = snd (intype2 op)). rewrite tsubFV_notin;auto. destruct op; simpl;auto. auto. rewrite <- H18.
      rewrite <- commute_tsubFV_tsubBV. apply subst_subtype' with (concatE (Cons x t_x g) g') t_x;auto.
      ++
        eapply typing_wf;eauto.
      ++
        eapply t_wf_sub_fjtype;eauto.
        apply TSub with t;auto.
        apply wf_intype2f;auto.
      ++
        apply value_lc;auto.
    +
      apply subFV_lc;auto.  apply value_lc. auto.
    + 
      apply subFV_lc;auto. apply value_lc. auto.
  -
    simpl.
    assert (tsubFV x v_x (tsubBV_at 1 e1 (tsubBV e2 rt)) = (tsubBV_at 1 (subFV x v_x e1) (tsubBV (subFV x v_x e2) rt))). apply subFV_rt. erewrite mtype_rt_no_fv. simpl;auto. eauto. apply value_lc;auto. rewrite tsubFV_self. rewrite H8.
    assert (wf_under (TRefn (TNom (TClass C)) ps) t). eapply mtype_t_wf;eauto. unfold wf_under in H17.
    simpl.  
    eapply TInvok;eauto.
    + 
      assert (ps = psubFV x v_x ps). rewrite psubFV_notin;auto. erewrite mtype_t_no_fvP; simpl;eauto. unfold psubFV in H18. (*erewrite mtype_t_no_fv; simpl;eauto. *) rewrite H18.
      fold psubFV.
      fold psubFV. 
      assert (tsubFV x v_x (TRefn (TNom (TClass C)) ps) = TRefn (TNom (TClass C)) (psubFV x v_x ps)). auto. rewrite <- H19.
      assert (tsubFV x v_x (TRefn (TNom (TClass C)) ps') = TRefn (TNom (TClass C)) (psubFV x v_x ps')). auto. rewrite <- H20.
      eapply subst_subtype';eauto. apply typing_wf with e1;auto. eapply mtype_ps_wf_g;eauto. apply wfenv_unique;auto. 
    +
      rewrite <- subFV_rt';auto.
      ++ 
        eapply subst_subtype';eauto.
        +++ 
          apply typing_wf with e2;auto.
        +++
          apply t_wf_sub_fjtype with (TRefn (TNom (TClass C)) ps);auto.
          apply TSub with (TRefn (TNom (TClass C)) ps');auto. eapply mtype_ps_wf_g;eauto. apply wfenv_unique;auto.
      ++
        erewrite mtype_t_no_fv. simpl;auto. eauto.
      ++ 
        apply value_lc;auto. 
    +
      apply subFV_lc;auto.  apply value_lc. auto.
    + 
      apply subFV_lc;auto. apply value_lc. auto.
  -
    simpl.
    assert (tsubFV x v_x (tsubBV_at 1 e1 (tsubBV e2 rt)) = (tsubBV_at 1 (subFV x v_x e1) (tsubBV (subFV x v_x e2) rt))). apply subFV_rt. erewrite mtypei_rt_no_fv. simpl;auto. eauto. apply value_lc;auto. rewrite tsubFV_self. rewrite H8.
    assert (wf_under (TRefn (TNom (TInterface C)) ps) t). eapply mtypei_t_wf;eauto. unfold wf_under in H17.
    simpl.  
    eapply TInvokI;eauto.
    + 
      assert (ps = psubFV x v_x ps). rewrite psubFV_notin;auto. erewrite mtypei_t_no_fvP; simpl;eauto. unfold psubFV in H18. (*erewrite mtype_t_no_fv; simpl;eauto. *) rewrite H18.
      fold psubFV.
      fold psubFV. 
      assert (tsubFV x v_x (TRefn (TNom (TInterface C)) ps) = TRefn (TNom (TInterface C)) (psubFV x v_x ps)). auto. rewrite <- H19.
      assert (tsubFV x v_x (TRefn (TNom (TInterface C)) ps') = TRefn (TNom (TInterface C)) (psubFV x v_x ps')). auto. rewrite <- H20.
      eapply subst_subtype';eauto. apply typing_wf with e1;auto. eapply mtypei_ps_wf_g;eauto. apply wfenv_unique;auto. 
    +
      rewrite <- subFV_rt';auto.
      ++ 
        eapply subst_subtype';eauto.
        +++ 
          apply typing_wf with e2;auto.
        +++
          apply t_wf_sub_fjtype with (TRefn (TNom (TInterface C)) ps);auto.
          apply TSub with (TRefn (TNom (TInterface C)) ps');auto. eapply mtypei_ps_wf_g;eauto. apply wfenv_unique;auto.
      ++
        erewrite mtypei_t_no_fv. simpl;auto. eauto.
      ++ 
        apply value_lc;auto. 
    +
      apply subFV_lc;auto.  apply value_lc. auto.
    + 
      apply subFV_lc;auto. apply value_lc. auto.
  -
    assert (isLC v_x). apply value_lc;auto.
    assert (~ Elem x (free (ReffieldType fi))). erewrite fieldtype_no_fv;eauto.
    simpl. rewrite tsubFV_self. rewrite commute_tsubFV_tsubBV;auto. simpl.
    rewrite tsubFV_notin;auto. (*unfold tsubBV. rewrite tsubBV_at_self. *)
    eapply Definitions.Typing.TField;eauto.
    apply subFV_lc;auto.
  -
    assert (isLC v_x). apply value_lc;auto.
    assert (WFEnv g). assert (WFEnv ((Cons x t_x g))). apply truncate_wfenv with g';auto. inversion H15;auto.
    assert (Us = (map (tsubFV x v_x) Us)). erewrite tsubFV_notin_forall. reflexivity.  apply Forall_impl with (fun t => free t = empty). intros. rewrite H16. simpl;auto. eapply fieldtype_no_fv_forall;eauto.
    rewrite tsubFV_self. 
    assert (subFV x v_x (ExpNew C es) = ExpNew C (map (subFV x v_x) es)). reflexivity. rewrite H17.
    (*assert (tsubFV x v_x (TRefn (TNom (TClass C)) (EQs es (List.map (ExpFieldAccess (BV 0)) fs))) = (TRefn (TNom (TClass C)) (EQs (map (subFV x v_x) es) (List.map (ExpFieldAccess (BV 0)) fs)))). apply tsubFV_eqs. rewrite H18. *)
    assert (tsubFV x v_x (TRefn (TNom (TClass C)) (PEmpty)) = (TRefn (TNom (TClass C)) (PEmpty))). reflexivity. rewrite H18. (*apply tsubFV_eqs. .*)
    assert (forall y,  Forall (WFtype (Cons y (TRefn (TNom (TClass C)) PEmpty) Empty)) (map (openT_at 0 y) Us)). rewrite H. eapply fieldtype_wf_forall';eauto. assert (Definitions.Semantics.Reffields C (nil ++ Fs)). simpl. auto. apply H19. 
    apply Definitions.Typing.TNew with (map (tsubFV x v_x) Ts) Fs (map (tsubFV x v_x) Us) fs;eauto. rewrite <-H16. auto. (*rewrite <- H16. auto.*)
    apply subFV_lc_forall;auto. 
    apply subst_typ_forall with t_x;auto.

    unfold subFV.
    apply subst_subtype_forall with t_x;auto.
    apply typing_wf_forall' with es;auto.
    remember (fresh (union (frees Us) (union (binds g) (union (binds g') ((singleton x)))))) as y. assert (~Elem y (union (frees Us) (union (binds g) (union (binds g') ((singleton x)))))). rewrite Heqy. apply fresh_not_elem. assert (map (tsubBV (ExpNew C es)) Us = map (tsubFV y (ExpNew C es)) (map (openT_at 0 y) Us)). apply tsubFV_unbindT_forall;notin_solve_one. rewrite H21. apply subst_wf_top_forall with (TRefn (TNom (TClass C)) PEmpty);simpl;auto. apply wfenv_unique;auto. unfold in_env. apply not_elem_concat_intro. simpl. apply not_elem_names_add_intro. constructor;auto. apply not_elem_singleton. notin_solve_one. notin_solve_one.  notin_solve_one.
    unfold isLC. simpl. apply Forall_fun. auto.
    eapply FTNew;eauto. 
    rewrite <- H.
    assert (map erase Us = map erase (map (tsubBV (ExpNew C es)) Us)).
    rewrite <- forall_erase; auto.
    rewrite H22.
    apply forall_fsubtyping with (map erase Ts) ;auto. apply forall_subtype_fsubtype with (concatE (Cons x t_x g) g');auto.
    apply typing_hasfjtype_forall;auto.
    assert ((Cons y (TRefn (TNom (TClass C)) PEmpty) (concatE (Cons x t_x g) g')) = (concatE (concatE (Cons x t_x g) g') (Cons y (TRefn (TNom (TClass C)) PEmpty) Empty))). simpl. auto. rewrite H22.
    apply weaken_many_wf_r_forall;auto. 
    apply wfenv_unique;auto.
    simpl. constructor;simpl;auto.
    assert (binds (Cons y (TRefn (TNom (TClass C)) PEmpty) Empty) = names_add y (binds (Empty))). simpl. auto. rewrite H23. apply intersect_names_add_intro_r. simpl. apply intersect_empty_r. apply not_elem_concat_intro. simpl. apply not_elem_names_add_intro. constructor;auto. apply not_elem_singleton. notin_solve_one. notin_solve_one.  notin_solve_one.
    
  -
    assert (WFEnv g). assert (WFEnv ((Cons x t_x g))). apply truncate_wfenv with g';auto. inversion H3;auto.
    eapply TSub.
    apply H0 with t_x;auto.
    apply subst_wf with t_x;auto. apply value_lc;auto. apply typing_hasfjtype;auto.
    apply subst_subtype' with (concatE (Cons x t_x g) g') t_x;auto. apply typing_wf with e;auto.
  -
    rewrite tsubFV_self.
    apply TLet with (tsubFV x v_x b) (union (singleton x) (union (union (binds g) (binds g')) nms)). apply subst_wf' with (concatE (Cons x t_x g) g') t_x;auto. apply value_lc;auto. apply typing_hasfjtype;auto. assert (WFEnv (Cons x t_x g)). apply truncate_wfenv with g';auto. inversion H4. auto. apply H1 with t_x;auto. intros. 
    assert (Cons y (tsubFV x v_x b) (concatE g (esubFV x v_x g')) = (concatE g (Cons y (tsubFV x v_x b) (esubFV x v_x g')))) by reflexivity. rewrite H13.
    assert (Cons y (tsubFV x v_x b) (esubFV x v_x g') = esubFV x v_x (Cons y b g')) by reflexivity. rewrite H14.
    assert (x<>y). assert (~Elem y (singleton x)). notin_solve_one. apply not_elem_singleton in H15. auto. 
    assert (isLC v_x). apply value_lc;auto.
    rewrite <- commute_subFV_unbind;auto. rewrite <- commute_tsubFV_unbindT;auto.
    apply H3 with t_x;auto. notin_solve_one. simpl. constructor. unfold in_env. notin_solve_one. auto.
    apply intersect_names_add_intro_r;auto. notin_solve_one. unfold in_env. simpl. apply not_elem_names_add_intro. constructor;auto.
    apply weaken_wfenv with (concatE (Cons x t_x g) g');auto. simpl. apply not_elem_union_intro. apply not_elem_names_add_intro. constructor;auto.
    notin_solve_one. notin_solve_one. apply typing_wf with e_x;auto.
Qed.
Lemma subst_typ : forall (g g':env) (x:vname) (v_x:expr) (t_x:type) (e:expr) (t:type),
    Hastype (concatE (Cons x t_x g) g') e t 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> isValue v_x -> Hastype g v_x t_x -> WFEnv (concatE (Cons x t_x g) g')
            -> Hastype (concatE g (esubFV x v_x g')) (subFV x v_x e) (tsubFV x v_x t ).
Proof. intros; pose proof subst_typ' as Htyp; 
  apply Htyp with (concatE (Cons x t_x g) g') t_x; trivial. Qed.
(* Lemma subst_typ2 : forall (g g':env) (x x':vname) (v_x v_x':expr) (t_x t_x':type) (e:expr) (t:type),
  Hastype (concatE (Cons x' t_x' (Cons x t_x g)) g') e t 
          -> unique g -> unique g'
          -> intersect (binds g) (binds g') = empty
          -> ~ (in_env x g) -> ~ (in_env x g') 
          -> isValue v_x -> Hastype g v_x t_x -> WFEnv (concatE (Cons x t_x g) g')
          -> ~ (in_env x' g) -> ~ (in_env x' g') -> x' <> x
          -> isValue v_x' -> Hastype (Cons x t_x g) v_x' t_x' -> WFEnv (concatE (Cons x' t_x' (Cons x t_x g)) g')
          -> Hastype (concatE g (esubFV x v_x (esubFV x' v_x' g'))) (subFV x v_x (subFV x' v_x' e)) (tsubFV x v_x (tsubFV x' v_x' t )).
Proof. 
  intros.
  apply subst_typ with t_x;auto.
  apply subst_typ with t_x';auto. 
  simpl. constructor;auto.
  simpl. apply intersect_names_add_intro_l;auto.
  unfold in_env. simpl. apply not_elem_names_add_intro. constructor;auto.
  apply esubFV_unique;auto.
  rewrite esubFV_binds;auto.
  unfold in_env. simpl. rewrite esubFV_binds;auto.
  apply subst_wfenv with t_x';auto. simpl. constructor;auto.
  simpl. apply intersect_names_add_intro_l;auto.
  unfold in_env. simpl. apply not_elem_names_add_intro. constructor;auto.
  apply value_lc;auto.
  apply typing_hasfjtype;auto. 
Qed. *)

Lemma subst_typ2' : forall (g g':env) (x x':vname) (v_x v_x':expr) (t_x t_x':type) (e:expr) (t:type),
  Hastype (concatE (Cons x' (openT_at 0 x t_x') (Cons x t_x g)) g') e t 
          -> unique g -> unique g'
          -> intersect (binds g) (binds g') = empty
          -> ~ (in_env x g) -> ~ (in_env x g') 
          -> isValue v_x -> Hastype g v_x t_x -> WFEnv (concatE (Cons x t_x g) g')
          -> ~ (in_env x' g) -> ~ (in_env x' g') -> x' <> x
          -> isValue v_x' -> Hastype (Cons x t_x g) v_x' (openT_at 0 x t_x') -> WFEnv (concatE (Cons x' (openT_at 0 x t_x') (Cons x t_x g)) g')
          -> Hastype (concatE g (esubFV x v_x (esubFV x' v_x' g'))) (subFV x v_x (subFV x' v_x' e)) (tsubFV x v_x (tsubFV x' v_x' t )).
Proof. 
  intros.
  apply subst_typ with t_x;auto.
  apply subst_typ with (openT_at 0 x t_x');auto. 
  simpl. constructor;auto.
  simpl. apply intersect_names_add_intro_l;auto.
  unfold in_env. simpl. apply not_elem_names_add_intro. constructor;auto. 
  apply esubFV_unique;auto.
  rewrite esubFV_binds;auto.
  unfold in_env. simpl. rewrite esubFV_binds;auto.
  apply subst_wfenv with (openT_at 0 x t_x');auto. simpl. constructor;auto.
  simpl. apply intersect_names_add_intro_l;auto.
  unfold in_env. simpl. apply not_elem_names_add_intro. constructor;auto.
  apply value_lc;auto.
  apply typing_hasfjtype;auto.
Qed.

Lemma subst_typ2'' : forall (g g':env) (x x':vname) (v_x v_x':expr) (t_x t_x' s_x:type) (e:expr) (t:type),
  Hastype (concatE (Cons x' (openT_at 0 x t_x') (Cons x t_x g)) g') e t 
          -> unique g -> unique g'
          -> intersect (binds g) (binds g') = empty
          -> ~ (in_env x g) -> ~ (in_env x g') 
          -> isValue v_x -> Hastype g v_x s_x -> Subtype g s_x t_x -> WFEnv (concatE (Cons x s_x g) g')
          -> ~ (in_env x' g) -> ~ (in_env x' g') -> x' <> x
          -> isValue v_x' -> Hastype (Cons x s_x g) v_x' (openT_at 0 x t_x') -> WFEnv (concatE (Cons x' (openT_at 0 x t_x') (Cons x s_x g)) g')
          -> WFtype g t_x 
          -> Hastype (concatE g (esubFV x v_x (esubFV x' v_x' g'))) (subFV x v_x (subFV x' v_x' e)) (tsubFV x v_x (tsubFV x' v_x' t )).
Proof. 
  intros.
  apply subst_typ with s_x;auto.
  apply subst_typ with (openT_at 0 x t_x'); auto.
  assert (concatE (Cons x' (openT_at 0 x t_x') (Cons x s_x g)) g' = concatE ((Cons x s_x g)) (concatE (Cons x' (openT_at 0 x t_x') Empty) g')). apply push. rewrite H16.
  assert (concatE (Cons x' (openT_at 0 x t_x') (Cons x t_x g)) g' = concatE ((Cons x t_x g)) (concatE (Cons x' (openT_at 0 x t_x') Empty) g')). apply push. rewrite H17 in H.  
  
  apply narrow_typ' with (concatE (Cons x t_x g) (concatE (Cons x' (openT_at 0 x t_x') Empty) g')) t_x;auto.
  apply unique_concat;auto. simpl. constructor;auto. 
  assert (binds (Cons x' (openT_at 0 x t_x') Empty) = names_add x' empty). simpl. reflexivity. rewrite H18. apply intersect_names_add_intro_l. apply intersect_empty_l. unfold in_env in H10. auto.
  apply subset_in_intersect with (union (binds (Cons x' (openT_at 0 x t_x') Empty)) (binds g')). assert (binds (Cons x' (openT_at 0 x t_x') Empty) = names_add x' empty). simpl. reflexivity. rewrite H18. apply intersect_union_intro_r;auto. apply intersect_names_add_intro_r;auto. apply intersect_empty_r. apply binds_concat.
  unfold in_env. apply not_elem_subset with (union (binds (Cons x' (openT_at 0 x t_x') Empty)) (binds g')).  apply binds_concat. assert (binds (Cons x' (openT_at 0 x t_x') Empty) = names_add x' empty). simpl. reflexivity. rewrite H18. apply not_elem_union_intro. apply not_elem_names_add_intro. constructor;auto. unfold in_env in H4. auto. 
  apply typing_wf with v_x;auto. apply truncate_wfenv in H8. inversion H8. auto.
  rewrite <-H16. auto.
  simpl. constructor;auto.
  simpl. apply intersect_names_add_intro_l;auto.
  unfold in_env. simpl. apply not_elem_names_add_intro. constructor;auto. 
  apply esubFV_unique;auto.
  rewrite esubFV_binds;auto.
  unfold in_env. simpl. rewrite esubFV_binds;auto.
  apply subst_wfenv with (openT_at 0 x t_x');auto. simpl. constructor;auto.
  simpl. apply intersect_names_add_intro_l;auto.
  unfold in_env. simpl. apply not_elem_names_add_intro. constructor;auto.
  apply value_lc;auto.
  apply typing_hasfjtype;auto. 
Qed. 
Require Import Coq.Program.Equality.
Lemma subst_typ2 : forall (g g':env) (x x':vname) (v_x v_x':expr) (t_x t_x':type) (e:expr) (t:type),
  Hastype (concatE (Cons x' (openT_at 0 x t_x') (Cons x t_x g)) g') e t 
          -> unique g -> unique g'
          -> intersect (binds g) (binds g') = empty
          -> ~ (in_env x g) -> ~ (in_env x g') 
          -> isValue v_x -> Hastype g v_x t_x -> True
          -> ~ (in_env x' g) -> ~ (in_env x' g') -> x' <> x
          -> isValue v_x' -> Hastype g v_x' (tsubBV v_x t_x') -> WFEnv (concatE (Cons x' (openT_at 0 x t_x') (Cons x t_x g)) g')
          -> WFtype g t_x 
          -> Hastype (concatE g (esubFV x v_x (esubFV x' v_x' g'))) (subFV x v_x (subFV x' v_x' e)) (tsubFV x v_x (tsubFV x' v_x' t )).
Proof. 
  intros.
  assert ((
    forall (t:type) (j:index) (y:vname) ,
      Subset (free (openT_at j y t)) (names_add y (free t)))) as ss. apply fv_open_at_elim. 
  assert (Subset (free (openT_at 0 x t_x')) (names_add x (free t_x'))) as subs. apply ss.
  unfold in_env in *.
  assert (WFEnv g). assert (WFEnv (Cons x' (openT_at 0 x t_x') (Cons x t_x g))). apply truncate_wfenv with g';auto. inversion H15;auto. inversion H19;auto. 
  assert (WFtype g t_x). apply typing_wf with v_x;auto. (* assert (WFEnv ((Cons x t g))). apply truncate_wfenv with g';auto.*)
  assert (WFtype g (tsubBV v_x t_x')). apply typing_wf with v_x';auto. (* assert (WFEnv ((Cons x t g))). apply truncate_wfenv with g';auto.*)
  assert (~ Elem x (free t_x)). apply free_bound_in_env with g;auto.
  assert (~ Elem x (free t_x')). apply not_elem_subset with (free (tsubBV v_x t_x')). apply fv_tsubBV_intro. apply free_bound_in_env with g;auto.
  assert (~ Elem x' (free t_x)). apply free_bound_in_env with g;auto.
  assert (~ Elem x' (free t_x')). apply not_elem_subset with (free (tsubBV v_x t_x')). apply fv_tsubBV_intro. apply free_bound_in_env with g;auto.
  assert (~ Elem x (fv v_x)). apply not_elem_subset with (binds g). apply fv_subset_binds with t_x;auto. auto. 
  assert (~ Elem x' (fv v_x)). apply not_elem_subset with (binds g). apply fv_subset_binds with t_x;auto. auto.
  assert (~ Elem x (fv v_x')). apply not_elem_subset with (binds g). apply fv_subset_binds with (tsubBV v_x t_x');auto. auto.
  assert (~ Elem x' (fv v_x')). apply not_elem_subset with (binds g). apply fv_subset_binds with (tsubBV v_x t_x');auto. auto.
  
  (* assert (~ Elem x (fv v_x')). apply not_elem_subset with (free (tsubBV v_x t_x')). apply fv_tsubBV_intro. apply free_bound_in_env with g;auto. *)
  assert (~ Elem x' (free t_x)). apply free_bound_in_env with g;auto. 
  (* assert (~ Elem x' (free t_x')). apply not_elem_subset with (free (tsubBV v_x t_x')). apply fv_tsubBV_intro. apply free_bound_in_env with g;auto. *)
  assert True. auto.
  (* assert (WFEnv (concatE g (esubFV x v_x (esubFV x' v_x' g')))). 
  apply wf_bind_env2 with ((concatE (Cons x' (openT_at 0 x t_x') (Cons x t_x g)) g')) t_x' t_x;auto. apply not_elem_union_intro;auto. apply not_elem_union_intro;auto. 
  apply weaken_fjtyp_top. rewrite <- erase_tsubBV_at with 0 v_x t_x'. apply typing_hasfjtype;auto. unfold in_envFJ. rewrite <- binds_erase_env. auto. 
  apply typing_hasfjtype;auto. unfold in_envFJ. 
  apply value_lc;auto. apply value_lc;auto. *)
  dependent induction H using Hastype_ind'.
  -
    simpl.
    apply TBC.
  - 
    simpl.
    apply TIC.
  -
    clear H28.
    assert (WFEnv (concatE g (esubFV x v_x (esubFV x' v_x' g')))). 
    apply wf_bind_env2 with ((concatE (Cons x' (openT_at 0 x t_x') (Cons x t_x g)) g')) t_x' t_x;auto. apply not_elem_union_intro;auto. apply not_elem_union_intro;auto. 
    apply weaken_fjtyp_top. rewrite <- erase_tsubBV_at with 0 v_x t_x'. apply typing_hasfjtype;auto. unfold in_envFJ. rewrite <- binds_erase_env. auto. 
    apply typing_hasfjtype;auto. unfold in_envFJ. 
    apply value_lc;auto. apply value_lc;auto.
    assert (WFtype (concatE g (esubFV x v_x (esubFV x' v_x' g'))) (tsubFV x v_x (tsubFV x' v_x' t))).
    eapply wf_bind_subFV2;eauto. unfold in_env in *. apply not_elem_union_intro;auto. apply not_elem_union_intro;auto. 
    apply weaken_fjtyp_top. rewrite <- erase_tsubBV_at with 0 v_x t_x'. apply typing_hasfjtype;auto. unfold in_envFJ. rewrite <- binds_erase_env. auto. 
    apply typing_hasfjtype;auto. unfold in_envFJ. 
    apply value_lc;auto. apply value_lc;auto.
    simpl. case_eq (x'=?x0).
    + (*x0=x', real subst, all other cases are contradictory*)
      
      intros. apply beq_nat_true in H30. subst x0.
      apply boundin_concat in H. destruct H.
      * (* x' is not in g'*)
      simpl in H. destruct H.
      ** (* x' not is in g*)
        destruct H. subst t.
        rewrite tsubFV_self. simpl. case_eq (x'=?x').
        intros.
        rewrite tsubFV_self. 
        apply exact_type;auto.
        rewrite subFV_notin';auto.
        assert (tsubFV x' v_x' (openT_at 0 x t_x') = (openT_at 0 x t_x')). rewrite tsubFV_notin;auto. apply not_elem_subset with (names_add x (free t_x'));auto. apply not_elem_names_add_intro. constructor;auto. rewrite H31.
        rewrite <- tsubFV_unbindT;auto. 
        apply weaken_many_typ;auto. apply esubFV_unique;auto. apply esubFV_unique;auto.  rewrite esubFV_binds;auto. rewrite esubFV_binds;auto.
        intros. apply beq_nat_false in H30. contradiction.

      ** (* x is in g*)
        destruct H.
        ***
          destruct H. subst x. subst t.
          contradiction.
        ***
        unfold in_env in H5. apply boundin_inenv in H. contradiction. 
      * (* x is in g'*)
        unfold in_env in H6. apply boundin_inenv in H. contradiction. 
    + (*x0<>x', whether x0=x?*)
      intros.
      simpl.
      case_eq (x=?x0);intros.

      ++ (*x0=x, real subst, other cases contradictory*)
      intros. apply beq_nat_true in H31. subst x0.
      apply boundin_concat in H. destruct H.
      * (* x is not in g'*)
      simpl in H. destruct H.
      ** (* x=x'*)
        destruct H. subst x.
        apply beq_nat_false in H30;contradiction.
      **
        destruct H.
        *** (* x =x *)
            destruct H. subst t. 
            rewrite tsubFV_self. simpl. case_eq (x'=?x);intros.
          ****
            apply beq_nat_false in H30. apply beq_nat_true in H31. contradiction.
          ****
            intros.
            assert (WFEnv g). assert (WFEnv (Cons x' (openT_at 0 x t_x') (Cons x t_x g))). apply truncate_wfenv with g';auto. inversion H32;auto. 
            assert (WFtype g t_x). apply typing_wf with v_x;auto. 
            assert (~ Elem x (free t_x)). apply free_bound_in_env with g;auto.
            rewrite tsubFV_self. simpl. case_eq(x=?x);intros. 
            *****
            apply exact_type;auto.
            rewrite tsubFV_notin;auto.
            rewrite tsubFV_notin;auto.
            apply weaken_many_typ;auto.
            apply esubFV_unique. apply esubFV_unique. auto.
            rewrite esubFV_binds. rewrite esubFV_binds. auto.
            assert (Subset (free t_x) (names_add x' (binds g))). unfold Subset. intros. apply elem_names_add_intro. right. assert (Subset (free t_x) (binds g)). apply free_subset_binds;auto. unfold Subset in H37. apply H37. auto.
            apply not_elem_subset with (binds g);auto. apply free_tsubFV_bounded;auto. apply fv_subset_binds with (tsubBV v_x t_x');auto.
            *****
              intros. apply beq_nat_false in H35. contradiction.
        *** (*x is in g*)
            unfold in_env in H4. apply boundin_inenv in H. contradiction.
      * (* x is in g'*)
        unfold in_env in H5. apply boundin_inenv in H. contradiction. 
      ++ (*just weaken*)
        rewrite tsubFV_self. simpl. rewrite H30.  simpl. 
        rewrite tsubFV_self. simpl. rewrite H31.  simpl. 
        assert (WFtype (concatE g (esubFV x v_x (esubFV x' v_x' g'))) (tsubFV x v_x (tsubFV x' v_x' t))).
        assert (WFEnv g). assert (WFEnv (Cons x' (openT_at 0 x t_x') (Cons x t_x g))). apply truncate_wfenv with g';auto. inversion H32;auto. auto. 
        apply TVar;auto.  apply boundin_concat in H. destruct H.
        * 
        (* x is not in g'*)
        destruct H.
        **  (* x not is in g*)
          destruct H. apply beq_nat_false in H30. subst x0. contradiction. 
        ** (*x is in g*) 
          simpl in H.  destruct H. apply beq_nat_false in H31. destruct H. subst x0. contradiction.
          assert (Subset (free t) (binds g)). apply free_subset_binds.  apply boundin_wfenv_wftype with x0;auto. 
          rewrite tsubFV_notin;auto. rewrite tsubFV_notin;auto.  apply boundin_concat. left;auto.
          assert (Subset (free t) (names_add x' (binds g))). unfold Subset. intros. apply elem_names_add_intro. right. unfold Subset in H33. apply H33. auto.
          apply not_elem_subset with (binds g);auto. apply free_tsubFV_bounded;auto. apply fv_subset_binds with (tsubBV v_x t_x');auto.
        * (*x is in g'*) 
          apply boundin_concat. right. apply boundin_esubFV;auto. apply boundin_esubFV;auto.
  -
    simpl.
    assert (tsubFV x v_x (tsubFV x' v_x' (tsubBV e (ty' op))) = (tsubBV (subFV x v_x (subFV x' v_x' e)) (ty' op))). rewrite subFV_rt2';auto. rewrite ty'_no_fv;auto.  rewrite ty'_no_fv;auto. apply value_lc;auto. apply value_lc;auto. rewrite H30.
    apply TUnOP with (tsubFV x v_x (tsubFV x' v_x' t));auto.
    +
      eapply IHHastype;eauto.
    +
      assert (intype op = tsubFV x v_x (tsubFV x' v_x' (intype op))). apply tsubFV2_intype.  rewrite H31. eapply subst_subtype2';eauto.
      eapply typing_wf;eauto.
      apply wf_intype;auto. 
    +
      apply subFV_lc;auto. apply value_lc. auto.
      apply subFV_lc;auto. apply value_lc. auto.
  -
    simpl.
    assert (tsubFV x v_x (tsubFV x' v_x' (tsubBV_at 1 e1 (tsubBV e2 (ty'2 op)))) = tsubBV_at 1 (subFV x v_x (subFV x' v_x' e1)) (tsubBV (subFV x v_x (subFV x' v_x' e2)) (ty'2 op))). rewrite subFV_rt2;auto. rewrite ty'2_no_fv;auto.  rewrite ty'2_no_fv;auto. apply value_lc;auto. apply value_lc;auto. rewrite H33.
    apply TBinOP with (tsubFV x v_x (tsubFV x' v_x' t)) (tsubFV x v_x (tsubFV x' v_x' t'));auto.
    + 
      eapply IHHastype1;eauto.
    +
      assert (fst (intype2 op) = tsubFV x v_x (tsubFV x' v_x' (fst (intype2 op)))). apply tsubFV2_intype2.  rewrite H34.  eapply subst_subtype2';eauto.
      eapply typing_wf;eauto.
      apply wf_intype2f;auto.
    +
      eapply IHHastype2;eauto.
    +
      assert (snd (intype2 op) = tsubFV x v_x (tsubFV x' v_x' (snd (intype2 op)))). apply tsubFV2_intype2'.  rewrite H34.
      rewrite <- commute_tsubFV_tsubBV. rewrite <- commute_tsubFV_tsubBV. 
      eapply subst_subtype2';eauto.
      eapply typing_wf;eauto.
      apply t_wf_sub_fjtype with (fst (intype2 op));eauto.
      apply wf_intype2s;auto.
      apply TSub with t;auto.
      apply wf_intype2f;auto. 
      apply value_lc;auto. apply value_lc;auto.
    +
      apply subFV_lc;auto. apply value_lc. auto.
      apply subFV_lc;auto. apply value_lc. auto.
    +
      apply subFV_lc;auto. apply value_lc. auto.
      apply subFV_lc;auto. apply value_lc. auto.
  -
    simpl.
    assert (tsubFV x v_x (tsubFV x' v_x' (tsubBV_at 1 e1 (tsubBV e2 rt))) = (tsubBV_at 1 (subFV x v_x (subFV x' v_x' e1)) (tsubBV (subFV x v_x (subFV x' v_x' e2)) rt))). apply subFV_rt2. erewrite mtype_rt_no_fv; simpl;eauto. erewrite mtype_rt_no_fv; simpl;eauto. apply value_lc;auto. apply value_lc;auto. rewrite tsubFV_self. rewrite tsubFV_self. rewrite H34.
    assert (wf_under (TRefn (TNom (TClass C)) ps) t). eapply mtype_t_wf;eauto. unfold wf_under in H22.
    simpl.  
    eapply TInvok;eauto.
    +
      eapply IHHastype1;eauto.
    + 
      assert (ps = psubFV x v_x (psubFV x' v_x' ps)). assert (ps = (psubFV x' v_x' ps)). rewrite psubFV_notin;auto. erewrite mtype_t_no_fvP; simpl;eauto. rewrite <-H36. rewrite psubFV_notin;auto. erewrite mtype_t_no_fvP; simpl;eauto. (* unfold psubFV in H24. *) (*erewrite mtype_t_no_fv; simpl;eauto. *) rewrite H36.
      fold psubFV.
      fold psubFV. 
      assert (tsubFV x v_x (tsubFV x' v_x' (TRefn (TNom (TClass C)) ps)) = TRefn (TNom (TClass C)) (psubFV x v_x (psubFV x' v_x' ps))). auto. rewrite <- H37.
      assert (tsubFV x v_x (tsubFV x' v_x' (TRefn (TNom (TClass C)) ps')) = TRefn (TNom (TClass C)) (psubFV x v_x (psubFV x' v_x' ps'))). auto. rewrite <- H38.
      eapply subst_subtype2';eauto.
      apply typing_wf with (e1);auto.
      
      assert(concatE (concatE (Cons x' (openT_at 0 x t_x') (Cons x t_x g)) g') Empty = (concatE (Cons x' (openT_at 0 x t_x') (Cons x t_x g)) g')). simpl. auto. rewrite <-H39. apply weaken_many_wf_r;simpl;auto. eapply mtype_ps_wf;eauto. apply wfenv_unique;auto. apply intersect_empty_r. 
    +
      assert (concatE g (esubFV x v_x (esubFV x' v_x' g'))
      |-s tsubFV x v_x (tsubFV x' v_x' t') <::
      tsubFV x v_x (tsubFV x' v_x' (tsubBV e1 t))). 

      eapply subst_subtype2';eauto.
      apply typing_wf with e2;auto.
      eapply t_wf_sub_fjtype;eauto.
      apply TSub with ( TRefn (TNom (TClass C)) ps');auto. 
      eapply mtype_ps_wf_g;eauto. apply wfenv_unique;auto.
      rewrite <- subFV_rt2';auto.
      erewrite mtype_t_no_fv;eauto. erewrite mtype_t_no_fv;eauto.
      apply value_lc;auto. apply value_lc;auto.
(* t_elem_singleton. notin_solve_one. auto. apply value_lc. auto.  *)
    +
      apply subFV_lc;auto.  apply value_lc. auto.
      apply subFV_lc;auto.  apply value_lc. auto.
    + 
      apply subFV_lc;auto. apply value_lc. auto. 
      apply subFV_lc;auto.  apply value_lc. auto.
  -
    simpl.
    assert (tsubFV x v_x (tsubFV x' v_x' (tsubBV_at 1 e1 (tsubBV e2 rt))) = (tsubBV_at 1 (subFV x v_x (subFV x' v_x' e1)) (tsubBV (subFV x v_x (subFV x' v_x' e2)) rt))). apply subFV_rt2. erewrite mtypei_rt_no_fv; simpl;eauto. erewrite mtypei_rt_no_fv; simpl;eauto. apply value_lc;auto. apply value_lc;auto. rewrite tsubFV_self. rewrite tsubFV_self. rewrite H34.
    assert (wf_under (TRefn (TNom (TInterface C)) ps) t). eapply mtypei_t_wf;eauto. unfold wf_under in H22.
    simpl.  
    eapply TInvokI;eauto.
    +
      eapply IHHastype1;eauto.
    + 
      assert (ps = psubFV x v_x (psubFV x' v_x' ps)). assert (ps = (psubFV x' v_x' ps)). rewrite psubFV_notin;auto. erewrite mtypei_t_no_fvP; simpl;eauto. rewrite <-H36. rewrite psubFV_notin;auto. erewrite mtypei_t_no_fvP; simpl;eauto. (* unfold psubFV in H24. *) (*erewrite mtype_t_no_fv; simpl;eauto. *) rewrite H36.
      fold psubFV.
      fold psubFV. 
      assert (tsubFV x v_x (tsubFV x' v_x' (TRefn (TNom (TInterface C)) ps)) = TRefn (TNom (TInterface C)) (psubFV x v_x (psubFV x' v_x' ps))). auto. rewrite <- H37.
      assert (tsubFV x v_x (tsubFV x' v_x' (TRefn (TNom (TInterface C)) ps')) = TRefn (TNom (TInterface C)) (psubFV x v_x (psubFV x' v_x' ps'))). auto. rewrite <- H38.
      eapply subst_subtype2';eauto.
      apply typing_wf with (e1);auto.
      
      assert(concatE (concatE (Cons x' (openT_at 0 x t_x') (Cons x t_x g)) g') Empty = (concatE (Cons x' (openT_at 0 x t_x') (Cons x t_x g)) g')). simpl. auto. rewrite <-H39. apply weaken_many_wf_r;simpl;auto. eapply mtypei_ps_wf;eauto. apply wfenv_unique;auto. apply intersect_empty_r. 
    +
      assert (concatE g (esubFV x v_x (esubFV x' v_x' g'))
      |-s tsubFV x v_x (tsubFV x' v_x' t') <::
      tsubFV x v_x (tsubFV x' v_x' (tsubBV e1 t))). 

      eapply subst_subtype2';eauto.
      apply typing_wf with e2;auto.
      eapply t_wf_sub_fjtype;eauto.
      apply TSub with ( TRefn (TNom (TInterface C)) ps');auto. 
      eapply mtypei_ps_wf_g;eauto. apply wfenv_unique;auto.
      rewrite <- subFV_rt2';auto.
      erewrite mtypei_t_no_fv;eauto. erewrite mtypei_t_no_fv;eauto.
      apply value_lc;auto. apply value_lc;auto.
  (* t_elem_singleton. notin_solve_one. auto. apply value_lc. auto.  *)
    +
      apply subFV_lc;auto.  apply value_lc. auto.
      apply subFV_lc;auto.  apply value_lc. auto.
    + 
      apply subFV_lc;auto. apply value_lc. auto. 
      apply subFV_lc;auto.  apply value_lc. auto.
  -
    (*non-trivial-part: fieldtype is not affected by substitution*)
    assert (isLC v_x). apply value_lc;auto.
    assert (isLC v_x'). apply value_lc;auto.
    
    assert (~ Elem x (free (ReffieldType fi))). erewrite fieldtype_no_fv;eauto.
    assert (~ Elem x' (free (ReffieldType fi))). erewrite fieldtype_no_fv;eauto.
    
    simpl. rewrite tsubFV_self. rewrite commute_tsubFV_tsubBV;auto. simpl.
    simpl. rewrite tsubFV_self. rewrite commute_tsubFV_tsubBV;auto. simpl.
    assert ((tsubFV x' v_x' (ReffieldType fi)) = ((ReffieldType fi))). rewrite tsubFV_notin;auto. rewrite H35.
    assert ((tsubFV x v_x (ReffieldType fi)) = ((ReffieldType fi))). rewrite tsubFV_notin;auto. rewrite H36.
    apply Definitions.Typing.TField with C Fs i (psubFV x v_x (psubFV x' v_x' ps ));auto. 
    apply subFV_lc;auto. apply subFV_lc;auto.
    assert (tsubFV x v_x (tsubFV x' v_x' (TRefn (TNom (TClass C)) ps)) = TRefn (TNom (TClass C)) (psubFV x v_x (psubFV x' v_x' ps ))). auto. rewrite <- H37. eapply IHHastype;eauto.
  -
    assert (HasFJtype (erase_env (concatE (Cons x' (openT_at 0 x t_x') (Cons x t_x g)) g')) (ExpNew C es) (TNom (TClass C))). eapply FTNew;eauto.  assert (map erase (map ReffieldType Fs) = map erase (map (tsubBV (ExpNew C es)) (map ReffieldType Fs))). rewrite <- forall_erase; auto. rewrite H. apply forall_fsubtyping with (map erase Ts) ;auto. apply forall_subtype_fsubtype with (concatE (Cons x' (openT_at 0 x t_x') (Cons x t_x g)) g');auto. apply typing_hasfjtype_forall;auto.
    assert (isLC v_x). apply value_lc;auto.
    assert (isLC v_x'). apply value_lc;auto.
    
    assert (WFEnv ((Cons x' (openT_at 0 x t_x') (Cons x t_x g)))). apply truncate_wfenv with g';auto. 

    assert ((map ReffieldType Fs) = (map (tsubFV x v_x) (map (tsubFV x' v_x') (map ReffieldType Fs)))).     assert ((map ReffieldType Fs) = (map (tsubFV x' v_x') (map ReffieldType Fs))). erewrite tsubFV_notin_forall;auto. apply Forall_impl with (fun t => free t = empty). intros. rewrite H36. simpl;auto. eapply fieldtype_no_fv_forall;eauto. rewrite <- H36. erewrite tsubFV_notin_forall. reflexivity. apply Forall_impl with (fun t => free t = empty). intros. rewrite H37. simpl;auto. eapply fieldtype_no_fv_forall;eauto. 
    rewrite tsubFV_self.
    rewrite tsubFV_self.
      
    (* assert (subFV x' v_x' (ExpNew C es) = ExpNew C (map (subFV x' v_x') es)). reflexivity. rewrite H36. *)
    assert (subFV x v_x (subFV x' v_x' (ExpNew C es)) = ExpNew C (map (subFV x v_x) (map (subFV x' v_x') es))). reflexivity. rewrite H37.
    
  
    assert (tsubFV x v_x (tsubFV x' v_x' (TRefn (TNom (TClass C)) (PEmpty))) = (TRefn (TNom (TClass C)) (PEmpty))). reflexivity. rewrite H38. (*apply tsubFV_eqs. .*)
    (* assert (forall y,  Forall (WFtype (Cons y (TRefn (TNom (TClass C)) PEmpty) Empty)) (map (openT_at 0 y) Us)). rewrite H. eapply fieldtype_wf_forall';eauto. assert (Definitions.Semantics.Reffields C (nil ++ Fs)). simpl. auto. apply H19.  *)
    apply Definitions.Typing.TNew with (map (tsubFV x v_x) (map (tsubFV x' v_x') Ts)) Fs (map (tsubFV x v_x) (map (tsubFV x' v_x') (map ReffieldType Fs))) (map ReffieldName Fs);eauto.
    + 
    apply subFV_lc_forall;auto.
    apply subFV_lc_forall;auto.
    +
      clear H5. clear H.
      generalize dependent es. induction Ts.
      *
        intros. destruct es. simpl. apply Forall2_nil.
        inversion H3. 
      *
        intros. destruct es. inversion H3.
        inversion H4. inversion H1. inversion H3.
        apply Forall2_cons.
        eapply H40;eauto.
        eapply IHTs;eauto.
    +
      assert (Forall (WFtype (concatE (Cons x' (openT_at 0 x t_x') (Cons x t_x g)) g')) Ts). eapply typing_wf_forall';eauto.
      assert (Forall (WFtype (concatE (Cons x' (openT_at 0 x t_x') (Cons x t_x g)) g')) (map (tsubBV (ExpNew C es)) (map ReffieldType Fs))). apply fieldtype_wf_subst_forall' with C nil;auto. apply unique_concat;auto. simpl. unfold in_env. constructor;auto. simpl. apply not_elem_names_add_intro. constructor;auto. simpl. apply intersect_names_add_intro_l;auto. apply intersect_names_add_intro_l;auto.  unfold isLC. simpl. apply Forall_fun;auto.
      clear H2. clear H35. clear H3. clear H4. clear H36.
      generalize dependent Ts. induction Fs.
      *
        intros. destruct Ts. simpl. apply Forall2_nil.
        inversion H5. 
      *
        intros. destruct Ts. inversion H5.
        inversion H5. inversion H39. inversion H40. 
        apply Forall2_cons.
        rewrite <- H37.  rewrite <- commute_tsubFV_tsubBV;auto. rewrite <- commute_tsubFV_tsubBV;auto.
        eapply subst_subtype2';eauto.
        eapply IHFs;eauto. 
  -
    assert (WFEnv g). assert (WFEnv ((Cons x' (openT_at 0 x t_x') (Cons x t_x g)))). apply truncate_wfenv with g';auto. inversion H30;auto. 
    eapply TSub.
    apply IHHastype with t_x t_x';auto.
    apply wf_bind_subFV2 with (concatE (Cons x' (openT_at 0 x t_x') (Cons x t_x g)) g') t_x' t_x;auto. unfold in_env in *. apply not_elem_union_intro;auto. apply not_elem_union_intro;auto. 
    apply weaken_fjtyp_top. rewrite <- erase_tsubBV_at with 0 v_x t_x'. apply typing_hasfjtype;auto. unfold in_envFJ. rewrite <- binds_erase_env. auto. 
    apply typing_hasfjtype;auto. unfold in_envFJ. 
    apply value_lc;auto. apply value_lc;auto.
    apply subst_subtype2' with (concatE (Cons x' (openT_at 0 x t_x') (Cons x t_x g)) g') t_x t_x';auto. apply typing_wf with e;auto.
  -
    rewrite tsubFV_self.
    rewrite tsubFV_self.
    
    apply TLet with (tsubFV x v_x (tsubFV x' v_x' b)) (union (singleton x') (union (singleton x) (union (union (binds g) (binds g')) nms))). apply wf_bind_subFV2 with (concatE (Cons x' (openT_at 0 x t_x') (Cons x t_x g)) g') t_x' t_x;auto.
    apply not_elem_union_intro;notin_solve_one.
    apply not_elem_union_intro;notin_solve_one.
    apply weaken_fjtyp_top. rewrite <- erase_tsubBV_at with 0 v_x t_x'. apply typing_hasfjtype;auto. unfold in_envFJ. rewrite <- binds_erase_env. auto.
    apply typing_hasfjtype;auto.
    apply value_lc;auto. apply value_lc;auto.
    fold subFV. eapply IHHastype;eauto.
    fold subFV. intros. assert (Cons y (tsubFV x v_x (tsubFV x' v_x' b)) (concatE g ((esubFV x v_x (esubFV x' v_x' g')))) = (concatE g (Cons y (tsubFV x v_x (tsubFV x' v_x' b)) (esubFV x v_x (esubFV x' v_x' g'))))) by reflexivity. rewrite H32.
    assert (x<>y). assert (~Elem y (singleton x)). notin_solve_one. apply not_elem_singleton in H33. auto. 
    assert (x'<>y). assert (~Elem y (singleton x')). notin_solve_one. apply not_elem_singleton in H34. auto. 
    
    assert (isLC v_x). apply value_lc;auto. assert (isLC v_x'). apply value_lc;auto.
    assert (Cons y (tsubFV x v_x (tsubFV x' v_x' b)) (esubFV x v_x (esubFV x' v_x' g')) = esubFV x v_x (esubFV x' v_x' (Cons y b g'))) by reflexivity. rewrite H37.
    rewrite <- commute_subFV_unbind;auto. rewrite <- commute_tsubFV_unbindT;auto. rewrite <- commute_subFV_unbind;auto. rewrite <- commute_tsubFV_unbindT;auto.
    apply H2 with t_x t_x';auto.
    notin_solve_one.
    constructor;unfold in_env;auto. notin_solve_one.
    apply intersect_names_add_intro_r;auto. notin_solve_one.
    apply not_elem_names_add_intro;auto.
    simpl. apply not_elem_names_add_intro;auto.
    simpl.
    apply WFEBind;auto. unfold in_env. apply not_elem_concat_intro. simpl. apply not_elem_names_add_intro;auto. constructor;auto. apply not_elem_names_add_intro;auto. constructor;auto. notin_solve_one. notin_solve_one. apply typing_wf with e_x;auto. 
Qed.
          

Lemma subst_typ_top : forall (g:env) (x:vname) (v_x:expr) (t_x:type) (e:expr) (t:type),
    Hastype (Cons x t_x g) e t 
            -> unique g -> ~ (in_env x g) 
            -> isValue v_x -> Hastype g v_x t_x -> WFEnv g
            -> Hastype g (subFV x v_x e) (tsubFV x v_x t ).
Proof. intros; assert (g = concatE g (esubFV x v_x Empty)) by reflexivity;
  rewrite H5; apply subst_typ with t_x; try apply intersect_empty_r; 
  try apply WFEBind; try apply typing_wf with v_x;
  unfold unique; intuition. Qed.

Lemma subst_subtype : 
  forall (g g':env) (x:vname) (v_x:expr) (t_x:type) (t t':type),
        Subtype (concatE (Cons x t_x g) g') t t' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> isValue v_x -> Hastype g v_x t_x -> WFEnv (concatE (Cons x t_x g) g')
            -> WFtype (concatE (Cons x t_x g) g') t 
            -> WFtype (concatE (Cons x t_x g) g') t'
            -> Subtype (concatE g (esubFV x v_x g')) (tsubFV x v_x t) (tsubFV x v_x t').
Proof. intros; pose proof subst_subtype' as Hsub; 
  apply Hsub with (concatE (Cons x t_x g) g') t_x; trivial. Qed.

Lemma subst_subtype_top : 
  forall (g:env) (x:vname) (v_x:expr) (t_x:type) (t t':type),
        Subtype (Cons x t_x g) t t' 
            -> unique g -> ~ (in_env x g) 
            -> isValue v_x -> Hastype g v_x t_x -> WFEnv g
            -> WFtype (Cons x t_x g) t 
            -> WFtype (Cons x t_x g) t'
            -> Subtype g (tsubFV x v_x t) (tsubFV x v_x t').
Proof. intros; assert (g = concatE g (esubFV x v_x Empty)) by reflexivity.
  rewrite H7; apply subst_subtype with t_x;
  simpl; auto;
  try apply intersect_empty_r; try apply WFEBind; 
  try apply typing_wf with v_x; unfold unique; intuition.
  Qed.


