Require Import Lists.
Require Import Referable.

Require Import Definitions.Syntax.
Require Import Definitions.Names.
Require Import Definitions.FJTyping.

Require Import Definitions.SubDenotation.

Require Import Definitions.Typing.
Require Import Definitions.CTSanity.
Require Import Definitions.Semantics.

Require Import Lemmas.LogicalLemmas.LemmasDenotesTyping.
Require Import Lemmas.LogicalLemmas.LemmasDenotesEnv.
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
Require Import Lemmas.LogicalLemmas.LemmasSImp.
Require Import Lemmas.TypingLemmas.LemmasWeakenTyp.
Require Import Lemmas.BasicLemmas.LemmasCTBasics.
Require Import Lemmas.TypingLemmas.LemmasTyping.
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasPrimitivesBasics.

(*---------------The Narrowing Lemmas---------------*)

Lemma exact_subtype : forall (g:env) (s:type) (t:type) (e:expr),
    Subtype g s t -> WFEnv g -> WFtype g s -> WFtype g t -> isLC e 
                  (* -> HasFJtype (erase_env g) e (erase t) *)
                  -> Subtype g (self s e) (self t e).
Proof. 
  intros.
  induction H.
  -
    pick_fresh zz.
    apply SBase with zz;auto.
    intros.
    fold (strengthen (PCons (eqlPred e) PEmpty) p2);auto.
    unfold unbindP.
    rewrite openP_at_strengthen.
    assert (LImplies (Cons y (TRefn b1 PEmpty) g)
    (openP_at 0 y (PCons (eqlPred e) p1)) (openP_at 0 y (PCons (eqlPred e) PEmpty))).
    apply ICons1.
    assert (LImplies (Cons y (TRefn b1 PEmpty) g)
    (openP_at 0 y (PCons (eqlPred e) p1))
       (openP_at 0 y p2)).
    apply ITrans with (openP_at 0  y p1).
    apply ICons2.
    apply H4.
    rewrite Heqzz in H5.
    notin_solve_one.
    apply IConj;auto.
  Qed.
Lemma INarrow : forall (g:env) (g':env) (x:vname) (s_x t_x:type)(ps qs:preds),
intersect (binds g) (binds g') = empty -> unique g -> unique g'
    -> ~ in_env x g -> ~ in_env x g' -> WFEnv g
    -> WFtype g s_x -> WFtype g t_x -> Subtype g s_x t_x
    -> LImplies (concatE (Cons x t_x g) g') ps qs
    -> LImplies (concatE (Cons x s_x g) g') ps qs.
Proof.
    intros.
    apply SImp; intros th Hden. intros.
    inversion H8. apply H10.
    apply widen_denotess with s_x; trivial.
    intros. apply  denotessubtype with g s_x;auto. trivial.
Qed.

Lemma narrow_subtyp' : (
  forall (g'xg : env) (t : type) (t' : type),
    Subtype g'xg t t' -> ( forall (g g':env) (x:vname) (s_x t_x:type),
      g'xg = concatE (Cons x t_x g) g' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> WFtype g s_x -> WFtype g t_x -> Subtype g s_x t_x 
            -> WFEnv (concatE (Cons x s_x g) g')
            -> WFtype (concatE (Cons x s_x g) g') t
            -> Subtype (concatE (Cons x s_x g) g') t t' )).
Proof.
  intros.
  induction H.
  apply SBase with (union (singleton x) (union (union (binds g) (binds g')) nms));auto.
  intros. assert (~Elem y nms). notin_solve_one. apply H11 in H13. 
  subst g0. assert ((Cons y (TRefn b1 PEmpty) (concatE (Cons x s_x g) g')) = (concatE (Cons x s_x g) (Cons y (TRefn b1 PEmpty) g'))). reflexivity. rewrite H0.
  apply INarrow with t_x;auto. simpl. 
  apply intersect_names_add_intro_r;auto. unfold in_env in H4. notin_solve_one.
  simpl. constructor. unfold in_env. notin_solve_one. auto. unfold in_env. simpl. apply not_elem_names_add_intro.
  constructor. assert (y<>x). apply not_elem_singleton. notin_solve_one. auto. unfold in_env in H5. notin_solve_one.
  apply truncate_wfenv in H9. inversion H9. auto.
Qed.
Lemma narrow_subtyp'_forall : (
  forall (g'xg : env) (ts : [type]) (ts' : [type]),
    Forall2 (Subtype g'xg) ts ts' -> ( forall (g g':env) (x:vname) (s_x t_x:type),
      g'xg = concatE (Cons x t_x g) g' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> WFtype g s_x -> WFtype g t_x -> Subtype g s_x t_x 
            -> WFEnv (concatE (Cons x s_x g) g')
            -> Forall (WFtype (concatE (Cons x s_x g) g')) ts
            -> Forall (WFtype (concatE (Cons x s_x g) g')) ts'
            -> Forall2 (Subtype (concatE (Cons x s_x g) g')) ts ts' )).
Proof.
  intros.
  generalize dependent ts'.
  induction ts. intros. destruct ts'. apply Forall2_nil.
  intros. inversion H.
  intros. destruct ts'. inversion H.
  inversion H. inversion H11. inversion H10. apply Forall2_cons;auto.
  eapply narrow_subtyp';eauto.
Qed.


Lemma narrow_typ_aux: forall es Ts x s_x t_x g0 g', (Forall2
(fun (e : expr) (t : type) =>
 forall g : env,
 unique g ->
 ~ in_env x g ->
 WFtype g s_x ->
 WFtype g t_x ->
 g |-s s_x <:: t_x ->
 forall g'0 : env,
 concatE (Cons x t_x g0) g' = concatE (Cons x t_x g) g'0 ->
 unique g'0 ->
 intersect (binds g) (binds g'0) = empty ->
 ~ in_env x g'0 -> WFEnv (concatE (Cons x s_x g) g'0) -> 
 concatE (Cons x s_x g) g'0 |--- e : t) es Ts) -> 
 unique g0 -> ~ in_env x g0 -> WFtype g0 s_x -> WFtype g0 t_x -> g0 |-s s_x <:: t_x -> unique g' -> 
 intersect (binds g0) (binds g') = empty -> ~ in_env x g' -> WFEnv (concatE (Cons x s_x g0) g') -> 
 Forall2 (Hastype (concatE (Cons x s_x g0) g')) es Ts.
Proof.
  intros.
  generalize dependent Ts.
  induction es. intros. destruct Ts. apply Forall2_nil.
  intros. inversion H.
  intros. destruct Ts. inversion H.
  inversion H. apply Forall2_cons;auto.
Qed.
Lemma narrow_typ' : ( forall (g'xg : env) (e : expr) (t : type),
    Hastype g'xg e t -> ( forall (g g':env) (x:vname) (s_x t_x:type),
        g'xg = concatE (Cons x t_x g) g' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> WFtype g s_x -> WFtype g t_x -> Subtype g s_x t_x 
            -> WFEnv (concatE (Cons x s_x g) g')
            -> Hastype (concatE (Cons x s_x g) g') e t )).
Proof. 
  intro env. intros. generalize dependent g'. generalize dependent g.  induction H using Hastype_ind';intros; subst g. 
  - (* TBC *) apply TBC.
  - (* TIC *) apply TIC.

  - (* TVar *) 
    apply truncate_wfenv in H10 as H10'; inversion H10'; subst x1 t0 g0.
    apply boundin_concat in H. destruct H.
    try destruct H; try destruct H.
    * (* x = x0 *) subst x0; subst t; 
      apply TSub with (self s_x (FV x)).
      try apply TVar. try (apply boundin_concat; left).
      simpl. left. constructor; reflexivity.
      try apply weaken_wf;auto. 
      try apply weaken_many_wf;auto.

      apply selfify_wf with s_x.
      apply weaken_wf;auto; 
      eapply weaken_many_wf;eauto.
      apply FTVar. rewrite erase_concat. apply boundinF_concatF. left. simpl. left. constructor; reflexivity.
      apply exact_subtype.
      apply weaken_many_subtype;
      try apply weaken_subtype_top;auto.
      unfold unique;auto.
      apply intersect_names_add_intro_l;auto.
      try apply weaken_wf_top;auto.
      try apply weaken_wf_top;auto.
      auto.
      try apply weaken_wf;auto. 
      try apply weaken_many_wf;auto.
      try apply weaken_wf;auto. 
      try apply weaken_many_wf;auto.
      unfold isLC. simpl;auto.
    * (* x in g  *) apply TVar; try apply boundin_concat; simpl;
      try (left; right; apply H); apply narrow_wf with t_x; assumption. 
    * (* x in g' *) apply TVar; try apply boundin_concat; simpl;
      try (right; apply H); apply narrow_wf with t_x; assumption.
  - 
    eapply TUnOP;eauto.
    apply narrow_subtyp' with (concatE (Cons x t_x g0) g') t_x;auto. apply typing_wf with e;auto.
  - 
    assert (wf_under (fst (intype2 op)) (snd (intype2 op))). eapply wf_intype2s. eauto.
    assert True. auto.
    eapply TBinOP;eauto.
    + 
      apply narrow_subtyp' with (concatE (Cons x t_x g0) g') t_x;auto. apply typing_wf with e1;auto. 
    + 
      intros. 
      apply narrow_subtyp' with (concatE (Cons x t_x g0) g') t_x;auto.
    ++
      eapply typing_wf;eauto. 
  - (* TPrm *) 
    assert (wf_under (TRefn (TNom (TClass C)) ps) t). eapply mtype_t_wf. eauto.
    eapply TInvok;eauto.
    + 
      apply narrow_subtyp' with (concatE (Cons x t_x g0) g') t_x;auto. apply typing_wf with e1;auto. 
    + 
      apply narrow_subtyp' with (concatE (Cons x t_x g0) g') t_x;auto.
      ++ 
        apply typing_wf with e2;auto.
  -
    assert (wf_under (TRefn (TNom (TInterface C)) ps) t). eapply mtypei_t_wf. eauto.
    eapply TInvokI;eauto.
    + 
      apply narrow_subtyp' with (concatE (Cons x t_x g0) g') t_x;auto. apply typing_wf with e1;auto. 
    + 
      apply narrow_subtyp' with (concatE (Cons x t_x g0) g') t_x;auto.
      ++ 
        apply typing_wf with e2;auto.
  -
    eapply TField;eauto.
  -
    (* assert (exists nms, forall y,  ~ Elem y nms -> Forall (WFtype (Cons y (TRefn (TNom (TClass C)) PEmpty) Empty)) (map (openT_at 0 y) Us)). rewrite H. eapply fieldtype_wf_forall';eauto. assert (Definitions.Semantics.Reffields C (nil ++ Fs)). simpl. auto. apply H11. destruct H11 as [nms']. rename H11 into wf1. *)

    apply TNew with Ts Fs Us fs;auto.
    +
    eapply narrow_typ_aux;eauto.
    +
    apply narrow_subtyp'_forall with (concatE (Cons x t_x g0) g') t_x;auto.
    ++
      apply typing_wf_forall' with es;auto.
      eapply narrow_typ_aux;eauto.
    ++
      rewrite H. apply fieldtype_wf_subst_forall' with C nil;auto.
      +++
        apply wfenv_unique;auto.
      +++
        unfold isLC. simpl.
        apply Forall_fun. auto.
      +++
        rewrite erase_concat. assert(erase_env (Cons x s_x g0) = FCons x (erase s_x) (erase_env g0)) by auto. rewrite H11. (*apply narrow_fjtyp with (concatF (FCons x (erase t_x) (erase_env g0)) (erase_env g')) (erase t_x);auto.*)
        eapply FTNew;eauto.
        * 
        rewrite <- H.
        apply forall_fsubtyping with (map erase Ts) ;auto. rewrite forall_erase with Us (ExpNew C es);auto. apply forall_subtype_fsubtype with (concatE (Cons x t_x g0) g');auto.
        assert(erase_env (Cons x s_x g0) = FCons x (erase s_x) (erase_env g0)) by auto. rewrite <- H16. rewrite <- erase_concat.
        apply typing_hasfjtype_forall;auto.
        eapply narrow_typ_aux;eauto.
  -
    apply TSub with s. 
    apply IHHastype;auto.
    apply narrow_wf with t_x;auto.
    eapply narrow_subtyp';eauto.
    apply typing_wf with e. apply IHHastype;auto. auto.
  -
    apply TLet with b (union (singleton x) (union (binds g0) (union (binds g') nms)));auto.
    apply narrow_wf with t_x;auto.
    intros.
    assert (Cons y b (concatE (Cons x s_x g0) g') = concatE (Cons x s_x g0) (Cons y b g')). reflexivity. rewrite H13.
    apply H2;auto. simpl. notin_solve_one. constructor;auto. unfold in_env. notin_solve_one.
    simpl. apply intersect_names_add_intro_r;auto. notin_solve_one.
    unfold in_env. simpl. apply not_elem_names_add_intro;constructor. assert (y<>x). apply not_elem_singleton. notin_solve_one. auto. unfold in_env in H11. notin_solve_one.
    simpl. apply WFEBind;auto. unfold in_env. unfold not. intros. apply binds_concat in H14. simpl in H14.
    assert (~Elem y (union (names_add x (binds g0)) (binds g'))). apply not_elem_union_intro. apply not_elem_names_add_intro. constructor. apply not_elem_singleton. notin_solve_one. notin_solve_one. notin_solve_one. contradiction.
    apply typing_wf with e_x. apply IHHastype;auto. auto.
Qed.

Lemma narrow_typ : 
  forall (g g':env) (x:vname) (s_x t_x:type) (e:expr) (t:type),
    Hastype (concatE (Cons x t_x g) g') e t
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> WFtype g s_x -> WFtype g t_x -> Subtype g s_x t_x 
            -> WFEnv (concatE (Cons x s_x g) g')
            -> Hastype (concatE (Cons x s_x g) g') e t .
Proof. intros; pose proof narrow_typ' as Htyp. 
  apply Htyp with (concatE (Cons x t_x g) g') t_x; trivial. Qed.

Lemma narrow_subtype :
  forall (g g':env) (x:vname) (s_x t_x:type) (t t':type),
    Subtype (concatE (Cons x t_x g) g') t t'
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> WFtype g s_x -> WFtype g t_x -> Subtype g s_x t_x
            -> WFEnv (concatE (Cons x s_x g) g')
            -> WFtype (concatE (Cons x s_x g) g') t 
            -> Subtype (concatE (Cons x s_x g) g') t t' .
Proof. intros; pose proof narrow_subtyp' as Hsub.
  apply Hsub with (concatE (Cons x t_x g) g') t_x; trivial. Qed.

Lemma narrow_typ_top : 
  forall (g:env) (x:vname) (s_x t_x:type) (e:expr) (t:type),
    Hastype (Cons x t_x g) e t
            -> unique g -> ~ (in_env x g) 
            -> WFtype g s_x -> WFtype g t_x -> Subtype g s_x t_x -> WFEnv g
            -> Hastype (Cons x s_x g) e t .
Proof. intros; assert (Cons x s_x g = concatE (Cons x s_x g) Empty) by reflexivity;
  rewrite H6; apply narrow_typ with t_x; 
  try apply intersect_empty_r; try apply WFEBind;
  simpl; intuition. Qed.

Lemma narrow_typ_top2 : 
  forall (g:env) (x x':vname) (s_x t_x s_x' t_x':type) (e:expr) (t:type),
    Hastype (Cons x t_x (Cons x' t_x' g)) e t
            -> unique g -> ~ (in_env x g) -> ~ (in_env x' g) -> x'<>x
            -> WFtype g s_x' -> WFtype g t_x' -> Subtype g s_x' t_x' -> Subtype (Cons x' s_x' g) s_x t_x -> WFEnv g
            -> WFtype (Cons x' s_x' g) s_x -> WFtype (Cons x' s_x' g) t_x
            -> Hastype (Cons x s_x (Cons x' s_x' g)) e t .
Proof.
  intros.
  apply narrow_typ_top with t_x;auto.
  assert (Cons x t_x (Cons x' s_x' g) = concatE (Cons x' s_x' g) (Cons x t_x Empty)). auto. rewrite H11.
  apply narrow_typ with t_x';auto.
  simpl;auto.
  assert (binds (Cons x t_x Empty) = names_add x (binds Empty)). auto. rewrite H12. apply intersect_names_add_intro_r;auto. simpl;auto. apply intersect_empty_r.
  unfold in_env. simpl. unfold not. intros. destruct H12;auto. 
  simpl. apply WFEBind;auto. 
  unfold in_env. simpl. apply not_elem_names_add_intro;constructor;auto.
  simpl. constructor;auto. 
  unfold in_env;auto. simpl. apply not_elem_names_add_intro;constructor;auto.
Qed.


Lemma narrow_subtype_top :
  forall (g:env) (x:vname) (s_x t_x:type) (t t':type),
    Subtype (Cons x t_x g) t t'
            -> unique g -> ~ (in_env x g) 
            -> WFtype g s_x -> WFtype g t_x -> Subtype g s_x t_x -> WFEnv g
            -> WFtype  (Cons x s_x g) t 
            -> WFtype  (Cons x s_x g) t'
            -> Subtype (Cons x s_x g) t  t' .
Proof. intros; assert (Cons x s_x g = concatE (Cons x s_x g) Empty) by reflexivity;
  rewrite H8; apply narrow_subtype with t_x;
  try apply intersect_empty_r; try apply WFEBind;
  simpl; intuition. Qed.

  (* -> *)

