Require Import Arith.
Require Import List.

Require Import Definitions.Syntax.
Require Import Definitions.Names.
Require Import Definitions.FJTyping.
Require Import Definitions.Typing.
Require Import Definitions.CTSanity.
Require Import Definitions.Semantics.


Require Import Lemmas.BasicLemmas.LemmasFJTyping.
Require Import Lemmas.BasicLemmas.LemmasFJWeaken.
Require Import Lemmas.BasicLemmas.LemmasSubstitution.
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasEnvironments.
Require Import Lemmas.BasicLemmas.LemmasFJSubstitution. 
Require Import Lemmas.BasicLemmas.LemmasWF.
Require Import Lemmas.BasicLemmas.LemmasWFNarrow.
Require Import Lemmas.BasicLemmas.LemmasWFWeaken.


(*---------------Substitution Lemmas of WF---------------*)

Lemma subst_wf' : forall (g'xg : env) (t : type),
   WFtype g'xg t -> ( forall (g g':env) (x:vname) (v_x:expr) (t_x:type),
       g'xg = concatE (Cons x t_x g) g' 
                    -> unique g -> unique g'
                    -> intersect (binds g) (binds g') = empty
                    -> ~ (in_env x g) -> ~ (in_env x g') 
                    -> isLC v_x -> HasFJtype (erase_env g) v_x (erase t_x)
                    -> WFtype (concatE g (esubFV x v_x g')) (tsubFV x v_x t) ).
Proof. apply ( WFtype_ind 
  (fun (g'xg : env) (t : type) => 
    forall (g g' : env) (x : vname) (v_x : expr) (t_x : type),
        g'xg = concatE (Cons x t_x g) g' 
              -> unique g -> unique g'
              -> intersect (binds g) (binds g') = empty
              -> ~ (in_env x g) -> ~ (in_env x g') 
              -> isLC v_x -> HasFJtype (erase_env g) v_x (erase t_x)
              -> WFtype (concatE g (esubFV x v_x g')) (tsubFV x v_x t)  )).
  - (* WFBase *) intros; destruct b; simpl;
    (apply WFBase; assumption) || (simpl in H; contradiction).
  - (* WFRefn *) intro env; intros; destruct b eqn:B; simpl; simpl in H0;
    try apply WFRefn with (names_add x (union nms (binds (concatE g g'))));
    try apply H0 with t_x;
    try (destruct ps; simpl; contradiction || discriminate); try assumption;
    (* TBool / TInt / FTV a *) try ( 
      intros; apply not_elem_names_add_elim in H11; try destruct H11;
      apply not_elem_union_elim in H12; try destruct H12;
      apply not_elem_concat_elim in H13; try destruct H13; try subst env;
      assert (FCons y (b) (erase_env (concatE g (esubFV x v_x g')))
            = concatF (erase_env g) (FCons y (b) (erase_env g')) ) as Henv
        by (subst b; rewrite erase_concat; rewrite erase_esubFV; reflexivity || assumption); 
      rewrite B in Henv; rewrite Henv;
      rewrite <- commute_psubFV_unbindP;
      try apply subst_pbool with (erase t_x);
      assert (concatF (FCons x (erase t_x) (erase_env g)) (FCons y (b) (erase_env g'))
            = FCons y (b) (erase_env (concatE (Cons x t_x g) g'))) as Henv'
        by (subst b; rewrite erase_concat; reflexivity); rewrite B in Henv'; try rewrite Henv';
      try apply H2; simpl; try split; try unfold in_envFJ; simpl;
      try apply unique_erase_env; try rewrite <- binds_erase_env;
      try apply intersect_names_add_intro_r; try rewrite <- binds_erase_env;
      try apply not_elem_names_add_intro; try apply fjtyp_islc with (erase_env g) (erase t_x);
      try split; intuition
    ).
  Qed.
Lemma subst_wf : forall (g g':env) (x:vname) (v_x:expr) (t_x:type) (t:type),
  WFtype (concatE (Cons x t_x g) g' ) t
                  -> unique g -> unique g'
                  -> intersect (binds g) (binds g') = empty
                  -> ~ (in_env x g) -> ~ (in_env x g') 
                  -> isLC v_x -> HasFJtype (erase_env g) v_x (erase t_x)
                  -> WFtype (concatE g (esubFV x v_x g')) (tsubFV x v_x t).
Proof. intros; apply subst_wf' with (concatE (Cons x t_x g) g') t_x;
  assumption || reflexivity.  Qed.

Lemma subst_wf_top : forall (g:env) (x:vname) (v_x:expr) (t_x:type) (t:type),
  WFtype (Cons x t_x g) t
                  -> unique g -> ~ (in_env x g)
                  -> isLC v_x -> HasFJtype (erase_env g) v_x (erase t_x)
                  -> WFtype g (tsubFV x v_x t).
Proof. intros; assert (g = concatE g (esubFV x v_x Empty)) by reflexivity;
  rewrite H4; apply subst_wf with t_x; simpl; 
  try apply intersect_empty_r; intuition. Qed.

Lemma subst_wfenv : forall (g g':env) (x:vname) (v_x:expr) (t_x:type),
    WFEnv (concatE (Cons x t_x g) g' )
        -> unique g -> unique g'
        -> intersect (binds g) (binds g') = empty
        -> ~ (in_env x g) -> ~ (in_env x g') 
        -> isLC v_x -> HasFJtype (erase_env g) v_x (erase t_x)
        -> WFEnv (concatE g (esubFV x v_x g')).
Proof. intro g; induction g'; simpl; intros.
  - (* Empty *) inversion H; assumption.
  - (* Cons  *) inversion H; apply WFEBind;
    try apply IHg' with t_x;
    try apply not_elem_concat_intro; 
    try rewrite esubFV_binds;
    try apply subst_wf with t_x;
    destruct H1; 
    apply intersect_names_add_elim_r in H2; destruct H2;
    unfold in_env in H4; simpl in H4;
    apply not_elem_names_add_elim in H4; destruct H4;
    trivial.
  Qed.
(*from subFV to subBV*)
Lemma wf_bind_sub: forall t' g'xg, 
  WFtype g'xg t' -> (forall x t_x t g g' e', 
  g'xg = concatE (Cons x t_x g) g' ->
  ~ Elem x (union (free t) (binds g)) -> 
  t' = (unbindT x t) -> 
  HasFJtype (erase_env g) e' (erase t_x) -> 
  isLC e' -> 
  unique g -> 
  g' = Empty -> 
  WFtype (concatE (g) g') (tsubBV e' t)).
Proof.
  intros.
  unfold unbindT in H1.
  assert ((tsubBV_at 0 e' t) = (tsubFV x e' (openT_at 0 x t))).
  apply subFV_open_at.
  notin_solve_one.
  unfold tsubBV.
  rewrite H7.
  subst g'. 
  subst g'xg. subst t'.
  assert (Empty = (esubFV x e' Empty)).
  simpl. reflexivity.
  rewrite H0.
  apply subst_wf' with ((concatE (Cons x t_x g) Empty)) t_x;auto.
  simpl. auto.
  unfold intersect. apply intersect_empty_r.
  unfold in_env. notin_solve_one.
Qed.    
  

Lemma wf_bind_sub2: forall t' g'xg, 
  WFtype g'xg t' -> (forall x x' t_x t_x' t g g' e' e'', 
  g'xg = concatE (Cons x t_x (Cons x' t_x' g)) g' ->
  ~ Elem x (union (singleton x') (union (free t) (binds g))) -> 
  ~ Elem x' (union (free (tsubBV_at 0 e' t)) (binds g)) -> 
  t' = (openT_at 1 x' (openT_at 0 x t)) -> 
  HasFJtype (FCons x' (erase t_x') (erase_env g)) e' (erase t_x) -> 
  HasFJtype (erase_env g) e'' (erase t_x') -> 
  isLC e' -> 
  isLC e'' -> 
  unique g -> 
  g' = Empty -> 
  WFtype (concatE (g) g') (tsubBV_at 1 e'' (tsubBV_at 0 e' t))).
Proof.
  intros.
  assert ((tsubBV_at 1 e'' (tsubBV_at 0 e' t)) = tsubFV x' e'' (openT_at 1 x' (tsubBV_at 0 e' t))). 
  apply subFV_open_at. notin_solve_one. rewrite H10.
  subst g'.  subst g'xg. subst t'.
  assert (Empty = (esubFV x' e'' Empty)). simpl. reflexivity. rewrite H0.
  apply subst_wf' with ((concatE (Cons x' t_x' g) Empty)) t_x';auto.
  assert ((tsubBV_at 0 e' t) = (tsubFV x e' (openT_at 0 x t))).  apply subFV_open_at. notin_solve_one. rewrite H3.
  rewrite <- commute_tsubFV_unbindT';auto.
  assert (Empty = (esubFV x e' Empty)). simpl. reflexivity. rewrite H9.
  apply subst_wf' with (concatE (Cons x t_x (Cons x' t_x' g)) Empty) t_x;simpl;auto.
  constructor;auto. unfold in_env. notin_solve_one.
  apply intersect_empty_r.
  unfold in_env. simpl. apply not_elem_names_add_intro. constructor. apply not_elem_singleton. notin_solve_one. notin_solve_one.
  apply not_elem_singleton. notin_solve_one.  simpl;auto.  
  apply intersect_empty_r. unfold in_env. notin_solve_one.
Qed.    

Lemma wf_bind_env2: forall g'xg, 
  WFEnv g'xg -> (forall x x' t_x t_x' g g' e' e'', 
  g'xg = concatE (Cons x (openT_at 0 x' t_x) (Cons x' t_x' g)) g' ->
  ~ Elem x (union (binds g')  (binds g)) -> 
  ~ Elem x' (union (binds g') (binds g)) -> 
  x' <> x -> 
  HasFJtype (FCons x' (erase t_x') (erase_env g)) e' (erase t_x) -> 
  HasFJtype (erase_env g) e'' (erase t_x') -> 
  isLC e' -> 
  isLC e'' -> 
  unique g -> 
  unique g' -> 
  intersect (binds g) (binds g') = empty -> 
  (* g' = Empty ->  *)
  WFEnv (concatE (g) (esubFV x' e'' (esubFV x e' g')))).
Proof.
  intros.
  subst g'xg. 
  apply subst_wfenv with t_x';auto.
  apply subst_wfenv with (openT_at 0 x' t_x);simpl;auto.
  unfold in_env. constructor;auto. notin_solve_one.
  apply intersect_names_add_intro_l;auto. notin_solve_one.
  unfold in_env. simpl. apply not_elem_names_add_intro. constructor. auto. notin_solve_one. unfold in_env. notin_solve_one. rewrite erase_openT_at. auto.
  apply esubFV_unique. auto. rewrite esubFV_binds. auto.
  unfold in_env. notin_solve_one.
  unfold in_env. rewrite esubFV_binds. notin_solve_one.
Qed.  

Lemma wf_bind_subFV2: forall t g'xg, 
  WFtype g'xg t -> (forall x x' t_x t_x' g g' e' e'', 
  g'xg = concatE (Cons x (openT_at 0 x' t_x) (Cons x' t_x' g)) g' ->
  ~ Elem x (union (binds g')  (binds g)) -> 
  ~ Elem x' (union (binds g') (binds g)) -> 
  x' <> x -> 
  HasFJtype (FCons x' (erase t_x') (erase_env g)) e' (erase t_x) -> 
  HasFJtype (erase_env g) e'' (erase t_x') -> 
  isLC e' -> 
  isLC e'' -> 
  unique g -> 
  unique g' -> 
  intersect (binds g) (binds g') = empty -> 
  (* g' = Empty ->  *)
  WFtype (concatE (g) (esubFV x' e'' (esubFV x e' g'))) (tsubFV x' e'' (tsubFV x e' t))).
Proof.
  intros.
  subst g'xg. 
  apply subst_wf' with ((concatE (Cons x' t_x' g) (esubFV x e' g'))) t_x';auto.
  apply subst_wf' with (concatE (Cons x (openT_at 0 x' t_x) (Cons x' t_x' g)) g') (openT_at 0 x' t_x);simpl;auto.
  unfold in_env. constructor;auto. notin_solve_one.
  apply intersect_names_add_intro_l;auto. notin_solve_one.
  unfold in_env. simpl. apply not_elem_names_add_intro. constructor. auto. notin_solve_one. unfold in_env. notin_solve_one. rewrite erase_openT_at. auto.
  apply esubFV_unique. auto. rewrite esubFV_binds. auto.
  unfold in_env. notin_solve_one.
  unfold in_env. rewrite esubFV_binds. notin_solve_one.
Qed.  

Lemma wf_bind_sub2': forall t' g'xg, 
  WFtype g'xg t' -> (forall x x' t_x t_x' t g g' e' e'', 
  g'xg = concatE (Cons x (openT_at 0 x' t_x) (Cons x' t_x' g)) g' ->
  ~ Elem x (union (binds g') (union (singleton x') (union (free t) (binds g)))) -> 
  ~ Elem x' (union (binds g') (union (free (tsubBV_at 0 e' t)) (binds g))) -> 
  t' = (openT_at 1 x' (openT_at 0 x t)) -> 
  HasFJtype (FCons x' (erase t_x') (erase_env g)) e' (erase t_x) -> 
  HasFJtype (erase_env g) e'' (erase t_x') -> 
  isLC e' -> 
  isLC e'' -> 
  unique g -> 
  unique g' -> 
  intersect (binds g) (binds g') = empty -> 
  (* g' = Empty ->  *)
  WFtype (concatE (g) (esubFV x' e'' (esubFV x e' g'))) (tsubBV_at 1 e'' (tsubBV_at 0 e' t))).
Proof.
  intros.
  assert ((tsubBV_at 1 e'' (tsubBV_at 0 e' t)) = tsubFV x' e'' (openT_at 1 x' (tsubBV_at 0 e' t))). 
  apply subFV_open_at. notin_solve_one. rewrite H11.
  subst g'xg. subst t'.
  apply subst_wf' with ((concatE (Cons x' t_x' g) (esubFV x e' g'))) t_x';auto.
  assert ((tsubBV_at 0 e' t) = (tsubFV x e' (openT_at 0 x t))).  apply subFV_open_at. notin_solve_one. rewrite H0.
  rewrite <- commute_tsubFV_unbindT';auto.
  apply subst_wf' with (concatE (Cons x (openT_at 0 x' t_x) (Cons x' t_x' g)) g') (openT_at 0 x' t_x);simpl;auto.
  constructor;auto. unfold in_env. notin_solve_one.
  apply intersect_names_add_intro_l;auto. notin_solve_one.
  unfold in_env. simpl. apply not_elem_names_add_intro. constructor. apply not_elem_singleton. notin_solve_one. notin_solve_one. unfold in_env. notin_solve_one. rewrite erase_openT_at. auto.
  apply not_elem_singleton. notin_solve_one. simpl;auto.  
  apply esubFV_unique. auto. rewrite esubFV_binds. auto.
  unfold in_env. notin_solve_one.
  unfold in_env. rewrite esubFV_binds. notin_solve_one.
Qed.    

Lemma subst_wf_forall: forall Us g g' x t_x v_x, 
unique g -> unique g' -> intersect (binds g) (binds g') = empty -> ~ in_env x g ->
~ in_env x g' -> isLC v_x -> HasFJtype (erase_env g) v_x (erase t_x) -> 
Forall (WFtype (concatE (Cons x t_x g) g')) Us -> 
Forall (WFtype (concatE g (esubFV x v_x g'))) (map (tsubFV x v_x) Us).
Proof.
  
  induction Us.
  intros. simpl. apply Forall_nil.
  intros. inversion H6. apply Forall_cons.
  apply subst_wf with t_x;auto.
  apply IHUs with t_x;auto.
Qed.
Lemma subst_wf_top_forall: forall Us g x t_x v_x, 
unique g -> ~ in_env x g ->
isLC v_x -> HasFJtype (erase_env g) v_x (erase t_x) -> 
Forall (WFtype (Cons x t_x g)) Us -> 
Forall (WFtype g) (map (tsubFV x v_x) Us).
Proof.
  
  induction Us.
  intros. simpl. apply Forall_nil.
  intros. inversion H3. apply Forall_cons.
  apply subst_wf_top with t_x;auto.
  apply IHUs with t_x;auto.
Qed.


  
Lemma wf_sub_fjtype: forall t g e1 CC, wf_under CC t -> HasFJtype (erase_env g) e1 (erase CC) -> 
WFEnv g -> isLC e1 ->
WFtype g (tsubBV e1 t).
Proof.
  intros. assert True. auto.
  assert True. auto.
  remember (fresh (union empty (union (free t) (union (binds g) empty)))) as y. assert (~Elem y (union empty (union (free t) (union (binds g) empty)))). rewrite Heqy.  apply fresh_not_elem. 
  assert (~Elem y empty). notin_solve_one. 
  assert (g = concatE g Empty). reflexivity. auto. rewrite H7. 
  unfold wf_under in H.
  apply wf_bind_sub with (openT_at 0 y t) (concatE (Cons y CC g) Empty) y CC;simpl;auto.
  assert ((Cons y CC g) = concatE g (Cons y CC Empty)). auto. rewrite H8.
  apply weaken_many_wf_r;auto. apply wfenv_unique;auto. simpl. constructor;auto.
  assert (binds (Cons y CC Empty) = names_add y (binds Empty)). auto. rewrite H9.
  apply intersect_names_add_intro_r;auto. apply intersect_empty_r;auto. notin_solve_one.
  apply not_elem_union_intro;notin_solve_one.
  apply wfenv_unique;auto.
Qed. 


(*essentially, we only prove substitution lemma for substitution, not subbv, so we need this lemma to adopt.*)
(*You can always pick ys that are fresh enough. This lemma justifies that.*)
Lemma wf_sub_fjtype2: forall t rt g e1 e2 CC, wf_under2 CC t rt -> HasFJtype (erase_env g) e1 (erase CC) -> 
(HasFJtype (erase_env (g)) e2 (erase (tsubBV_at 0 e1 t))) -> 
WFEnv g -> isLC e1 -> isLC e2 -> 
WFtype g (tsubBV_at 1 e1 (tsubBV e2 rt)).
Proof.
  intros. assert True. auto.
  assert True. auto.
  remember (fresh (union (free (tsubBV_at 0 e2 rt)) (union empty (union (binds g) empty)))) as y. assert (~Elem y (union (free (tsubBV_at 0 e2 rt)) (union empty (union (binds g) empty)))). rewrite Heqy.  apply fresh_not_elem. 
  assert (~Elem y empty). notin_solve_one. 
  remember (fresh (union (free rt) (union (singleton y) (union empty (union empty (union (binds g) empty)))))) as y'. assert (~Elem y' (union (free rt) (union (singleton y) (union empty (union empty (union (binds g) empty)))))). rewrite Heqy'.  apply fresh_not_elem.
  
  assert (g = concatE g Empty). reflexivity. auto. rewrite H10. 
  assert (y'<>y). apply not_elem_singleton. notin_solve_one.
  assert (Empty = (esubFV y e1 (esubFV y' e2 Empty))) by reflexivity. rewrite H12.
  apply wf_bind_sub2' with ((openT_at 1 y (openT_at 0 y' rt))) (concatE (Cons y' (openT_at 0 y t) (Cons y CC g)) Empty) t CC;auto.
  
  assert (concatE (Cons y' (openT_at 0 y t) (Cons y CC g)) Empty = concatE g (Cons y' (openT_at 0 y t) (Cons y CC Empty))). simpl. auto. rewrite H13.
  apply weaken_many_wf_r;auto. 
  apply wfenv_unique;auto.  simpl. constructor. unfold in_env. simpl. unfold not. intros. destruct H14;auto. constructor;auto. 
  assert (binds (Cons y' (openT_at 0 y t) (Cons y CC Empty)) = names_add y' (names_add y empty)). simpl. reflexivity. rewrite H14. apply intersect_names_add_intro_r. apply intersect_names_add_intro_r. apply intersect_empty_r. notin_solve_one. notin_solve_one. 
  simpl. apply not_elem_union_intro;simpl;auto. apply not_elem_union_intro. notin_solve_one.  apply not_elem_union_intro. notin_solve_one. notin_solve_one.
  simpl. apply not_elem_union_intro;simpl;auto. apply not_elem_union_intro;simpl;auto. notin_solve_one. notin_solve_one.
  apply weaken_fjtyp_top.
  rewrite <- erase_tsubBV_at with 0 e1 t. apply H1. unfold in_envFJ. rewrite <- binds_erase_env. notin_solve_one.
  apply wfenv_unique;auto.
  apply intersect_empty_r. 
Qed.
