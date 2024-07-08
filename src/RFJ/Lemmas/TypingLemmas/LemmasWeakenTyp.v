
Require Import Coq.Program.Equality.
Require Import Lists.
Require Import Lists.ListSet.

Require Import Definitions.Syntax.
Require Import Definitions.Names.
Require Import Definitions.FJTyping.

Require Import Definitions.Typing.
Require Import Definitions.SubDenotation.

Require Import Definitions.CTSanity.
Require Import Definitions.Semantics.

Require Import Lemmas.BasicLemmas.LemmasFJTyping.
Require Import Lemmas.BasicLemmas.LemmasSubstitution.
Require Import Lemmas.BasicLemmas.LemmasSyntax.
Require Import Lemmas.BasicLemmas.LemmasEnvironments.
Require Import Lemmas.BasicLemmas.LemmasWF.
Require Import Lemmas.BasicLemmas.LemmasWFNarrow.
Require Import Lemmas.BasicLemmas.LemmasCTBasics.
Require Import Lemmas.BasicLemmas.LemmasWFWeaken.
Require Import Lemmas.BasicLemmas.LemmasWF.
Require Import Lemmas.BasicLemmas.LemmasWFNarrow.
Require Import Lemmas.BasicLemmas.LemmasWFSubstitution.
Require Import Lemmas.TypingLemmas.LemmasTyping.
Require Import Lemmas.BasicLemmas.LemmasWFWeaken.
Require Import Lemmas.BasicLemmas.LemmasPrimitivesBasics.
Require Import Lemmas.LogicalLemmas.LemmasDenotes.
Require Import Lemmas.LogicalLemmas.LemmasDenotesEnv.
Require Import Lemmas.LogicalLemmas.LemmasCSubst.
Require Import Lemmas.BasicLemmas.LemmasSyntax.

(*---------------The Weakening Lemmas---------------*)

Lemma IWeak   : forall (g:env) (g':env) (ps:preds) (qs:preds) (x:vname) (t_x:type),
        intersect (binds g) (binds g') = empty -> unique g -> unique g' 
            -> ~ in_env x g -> ~ in_env x g' -> WFEnv (concatE g g')
            -> ~ Elem x (fvP ps) 
            -> ~ Elem x (fvP qs)
            -> LImplies (concatE g g') ps qs 
            -> LImplies (concatE (Cons x t_x g) g') ps qs.
Proof. intros.
  apply SImp; intros th Hden Hps.
  inversion H.
  assert (DenotesEnv (concatE g g') (remove_fromCS th x)).
  apply remove_var_denotessenv with t_x;auto.
  apply denotesenv_closed with (concatE (Cons x t_x g) g') ;auto.
  apply denotesenv_uniqueC with (concatE (Cons x t_x g) g') ;auto.
  apply denotesenv_substitutable with (concatE (Cons x t_x g) g') ;auto.
  inversion H7.
  apply H10 in H8.
  rewrite remove_cpsubst with th x qs;auto.
  apply binds_env_th in Hden. rewrite <- Hden. simpl. apply binds_concat. simpl. apply set_union_intro1. apply set_add_intro2. reflexivity.
  apply denotesenv_closed with (concatE (Cons x t_x g) g') ;auto.
  apply denotesenv_uniqueC with (concatE (Cons x t_x g) g') ;auto.
  apply denotesenv_substitutable with (concatE (Cons x t_x g) g') ;auto.
  rewrite <-remove_cpsubst with th x ps;auto.
  apply binds_env_th in Hden. rewrite <- Hden. simpl. apply binds_concat. simpl. apply set_union_intro1. apply set_add_intro2. reflexivity.
  apply denotesenv_closed with (concatE (Cons x t_x g) g') ;auto.
  apply denotesenv_uniqueC with (concatE (Cons x t_x g) g') ;auto.
  apply denotesenv_substitutable with (concatE (Cons x t_x g) g') ;auto.
Qed.
Lemma weaken_subtype' : 
(
  forall (g'g : env) (t : type) (t' : type),
    Subtype g'g t t' -> ( forall (g g':env) (x:vname) (t_x:type),
        g'g = concatE g g' -> unique g -> unique g'
                           -> intersect (binds g) (binds g') = empty
                           -> ~ (in_env x g) -> ~ (in_env x g') -> WFEnv (concatE g g')
                           -> WFtype (concatE g g') t
                           -> WFtype (concatE g g') t'
                           -> Subtype (concatE (Cons x t_x g) g') t t') ).
Proof.
  apply (Subtype_ind (fun (g'g : env) (t : type) (t' : type) => 
  forall (g g':env) (x:vname) (t_x:type),
    g'g = concatE g g' -> unique g -> unique g'
                       -> intersect (binds g) (binds g') = empty
                       -> ~ (in_env x g) -> ~ (in_env x g') -> WFEnv (concatE g g')
                       -> WFtype (concatE g g') t 
                       -> WFtype (concatE g g') t'
                       -> Subtype (concatE (Cons x t_x g) g') t t'));
  intro env; intros; subst env.
  -
    apply SBase 
      with (names_add x (union (*(union*) nms (*(union nms0 nm1))*) (binds (concatE g g')))); auto; intros. 
    apply not_elem_names_add_elim in H1; destruct H1.
    apply not_elem_union_elim in H10; destruct H10;
    apply not_elem_concat_elim in H11; destruct H11;
    assert (Cons y (TRefn b1 PEmpty) (concatE (Cons x t_x g) g') 
              = concatE (Cons x t_x g) (Cons y (TRefn b1 PEmpty) g'))
      by reflexivity; rewrite H13.
    apply IWeak;simpl;auto. 
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; trivial.
    unfold in_env; simpl;
    try apply not_elem_names_add_intro; trivial;
    try apply not_elem_concat_intro;
    try apply not_elem_union_intro; auto.

    try apply WFEBind;
    assert (WFtype (concatE g g') (TRefn b2 PEmpty)) as Hwf
      by (inversion H7; try inversion H13; try apply WFKind;
          try (apply WFBase; apply H17 || apply H19); try apply H15;
          try (apply WFVar; apply H17 || apply H21); try apply H19);
    assert (~ Elem x (binds (concatE g g')));
    try apply not_elem_concat_intro;
    try apply not_elem_union_intro; auto.
    
    assert (~ in_env x (concatE g g')). unfold in_env; simpl;apply not_elem_concat_intro;auto. 
    apply free_bound_in_env 
      with (concatE g g') (TRefn b1 p1) x in H8;auto;
    apply free_bound_in_env 
      with (concatE g g') (TRefn b2 p2) x in H9;auto.
    simpl in H7; simpl in H8; trivial;
    pose proof fv_unbind_elim as [_ [_ Hfv]];
    apply not_elem_subset with (names_add y (fvP p1));
    try apply not_elem_names_add_intro; try split; auto.

    assert (~ in_env x (concatE g g')). unfold in_env; simpl;apply not_elem_concat_intro;auto. 
    apply free_bound_in_env 
      with (concatE g g') (TRefn b1 p1) x in H8;auto;
    apply free_bound_in_env 
      with (concatE g g') (TRefn b2 p2) x in H9;auto.
    simpl in H7; simpl in H8; trivial;
    pose proof fv_unbind_elim as [_ [_ Hfv]];
    apply not_elem_subset with (names_add y (fvP p2));
    try apply not_elem_names_add_intro; try split; auto.
Qed.



Lemma forall_weanken_subtype: forall Ts Us g g' x t_x, 
unique g -> unique g' -> intersect (binds g) (binds g') = empty -> ~ in_env x g -> ~ in_env x g' -> WFEnv (concatE g g') -> 
Forall (WFtype (concatE g g')) Us -> Forall2 (Subtype (concatE g g')) Ts Us -> 
Forall (WFtype (concatE g g')) Ts -> Forall2 (Subtype (concatE (Cons x t_x g) g')) Ts Us.
Proof.
  intros.
  generalize dependent Us.
  (* generalize dependent es. *)
  
  induction Ts.
  intros. destruct Us. apply Forall2_nil. inversion H6.
  intros. destruct Us. inversion H6.
  inversion H5. inversion H6. inversion H7. 
  (* nversion H7. *)
  apply Forall2_cons.
  apply weaken_subtype' with (concatE g g');auto. 
  apply IHTs;auto.
Qed.
Lemma forall_weanken_typ': forall g g' x t_x es Ts,  
unique g -> unique g' -> intersect (binds g) (binds g') = empty -> ~ in_env x g -> ~ in_env x g' -> WFEnv (concatE g g') -> 
Forall2 (fun (e : expr) (t : type) =>
        forall (g0 g'0 : env) (x : vname) (t_x : type),
        concatE g g' = concatE g0 g'0 ->
        unique g0 ->
        unique g'0 ->
        intersect (binds g0) (binds g'0) = empty ->
        ~ in_env x g0 ->
        ~ in_env x g'0 ->
        WFEnv (concatE g0 g'0) -> concatE (Cons x t_x g0) g'0 |--- e : t)  es Ts -> 
Forall2 (Hastype (concatE (Cons x t_x g) g')) es Ts.
Proof.
  intros.
  generalize dependent Ts.
  induction es.
  intros. destruct Ts. apply Forall2_nil. inversion H5.
  intros. destruct Ts. inversion H5.
  inversion H5. 
  apply Forall2_cons. apply H9;auto.
  apply IHes;auto.
Qed.  
Lemma weaken_typ' : ( forall (g'g : env) (e : expr) (t : type),
    Hastype g'g e t -> ( forall (g g':env) (x:vname) (t_x:type),
        g'g = concatE g g' -> unique g -> unique g'
                           -> intersect (binds g) (binds g') = empty
                           -> ~ (in_env x g) -> ~ (in_env x g') -> WFEnv (concatE g g')
                           -> Hastype (concatE (Cons x t_x g) g') e t ) ).
Proof.
  apply (Hastype_ind'
  ( fun (g'g : env) (e : expr) (t : type) => 
    ( forall (g g':env) (x:vname) (t_x:type),
        g'g = concatE g g' -> unique g -> unique g'
                           -> intersect (binds g) (binds g') = empty
                           -> ~ (in_env x g) -> ~ (in_env x g') -> WFEnv (concatE g g')
                           -> Hastype (concatE (Cons x t_x g) g') e t ) ));
  intro env; intros; subst env.
  -
    apply TBC.
  -
    apply TIC.
  -
    apply TVar.
    apply boundin_weaken;auto.
    apply weaken_wf; auto.
  -
    eapply TUnOP;eauto.
    eapply weaken_subtype';eauto. apply typing_wf with e;auto. apply wf_intype;auto.
  -
    assert (wf_under (fst (intype2 op)) (snd (intype2 op))). eapply wf_intype2s. eauto. 
    eapply TBinOP;eauto.
    +
      eapply weaken_subtype';eauto. apply typing_wf with e1;auto. apply weaken_many_wf;auto. assert(concatE g Empty = g). simpl. auto. rewrite <-H14. apply weaken_many_wf_r;simpl;auto. eapply wf_intype2f;eauto. simpl. auto. apply intersect_empty_r. 
    + 
        intros.
        apply weaken_subtype' with (concatE g g');auto.
      ++
        apply typing_wf with e2;auto.
      ++
        eapply t_wf_sub_fjtype;eauto.
        apply TSub with t;auto.
        apply wf_intype2f;auto. 
  -
    assert (wf_under (TRefn (TNom (TClass C)) ps) t). eapply mtype_t_wf. eauto. 
    eapply Definitions.Typing.TInvok;eauto.
    +
      eapply weaken_subtype';eauto. apply typing_wf with e1;auto. apply weaken_many_wf;auto. assert(concatE g Empty = g). simpl. auto. rewrite <-H15. apply weaken_many_wf_r;simpl;auto. eapply mtype_ps_wf;eauto. apply intersect_empty_r. 
    + 
      eapply weaken_subtype';eauto.
      ++
        apply typing_wf with e2;auto.
      ++
        apply t_wf_sub_fjtype with (TRefn (TNom (TClass C)) ps);auto.
        apply TSub with (TRefn (TNom (TClass C)) ps');auto. eapply mtype_ps_wf_g;eauto. apply wfenv_unique;auto.
  -
    assert (wf_under (TRefn (TNom (TInterface C)) ps) t). eapply mtypei_t_wf. eauto. 
    eapply Definitions.Typing.TInvokI;eauto.
    +
      eapply weaken_subtype';eauto. apply typing_wf with e1;auto. apply weaken_many_wf;auto. assert(concatE g Empty = g). simpl. auto. rewrite <-H15. apply weaken_many_wf_r;simpl;auto. eapply mtypei_ps_wf;eauto. apply intersect_empty_r. 
    + 
      eapply weaken_subtype';eauto.
      ++
        apply typing_wf with e2;auto.
      ++
        apply t_wf_sub_fjtype with (TRefn (TNom (TInterface C)) ps);auto.
        apply TSub with (TRefn (TNom (TInterface C)) ps');auto. eapply mtypei_ps_wf_g;eauto. apply wfenv_unique;auto.
  -
    eapply Definitions.Typing.TField;eauto.
  -
    apply Definitions.Typing.TNew with Ts Fs Us fs; auto.
    +
    apply forall_weanken_typ';auto.
    +
      apply forall_weanken_subtype;auto.
      ++ 
        rewrite H. apply fieldtype_wf_subst_forall' with C nil;auto.
        +++
          apply wfenv_unique;auto.
        +++
          unfold isLC. simpl.
          apply Forall_fun. auto.
        +++
          assert (erase (self (TRefn (TNom (TClass C)) PEmpty) (ExpNew C es)) = (TNom (TClass C))). rewrite erase_self. simpl. auto. rewrite <- H6.
          apply typing_hasfjtype;auto. eapply Definitions.Typing.TNew;eauto.
      ++
        apply typing_wf_forall' with es;auto.
  -
    apply TSub with s.
    apply H0;auto.
    apply weaken_wf; auto.
    apply weaken_subtype' with (concatE g g');auto.
    apply typing_wf with e;auto.
  -
    apply TLet with b (union (singleton x) (union (union (binds g') (binds g)) nms));auto.
    apply weaken_wf;auto.
    
    intros. assert (Cons y b (concatE (Cons x t_x g) g') = (concatE (Cons x t_x g) (Cons y b g'))) by reflexivity. rewrite H11.
    apply H3;auto. notin_solve_one. simpl. constructor. unfold in_env. notin_solve_one. auto. simpl. apply intersect_names_add_intro_r;auto.
    notin_solve_one. unfold in_env. simpl. apply not_elem_names_add_intro. constructor. unfold not. intro. assert (~ Elem y (singleton x)). notin_solve_one. apply not_elem_singleton in H13. rewrite H12 in H13. contradiction.
    auto.  apply weaken_wfenv with ( concatE g g');auto. apply not_elem_union_intro;notin_solve_one. apply typing_wf with e_x;auto.
Qed.

Lemma weaken_typ : forall (g g':env) (e:expr) (t:type) (x:vname) (t_x:type),
    Hastype (concatE g g') e t 
                          -> unique g -> unique g'
                          -> intersect (binds g) (binds g') = empty
                          -> ~ (in_env x g) -> ~ (in_env x g') -> WFEnv (concatE g g')
                          -> Hastype (concatE (Cons x t_x g) g') e t.
Proof. intros; apply weaken_typ' with (concatE g g'); trivial. Qed.

Lemma weaken_subtype : 
  forall (g g':env) (t:type) (t':type) (x:vname) (t_x:type),
    Subtype (concatE g g') t t' 
                          -> unique g -> unique g'
                          -> intersect (binds g) (binds g') = empty
                          -> ~ (in_env x g) -> ~ (in_env x g') -> WFEnv (concatE g g')
                          -> WFtype (concatE g g') t
                          -> WFtype (concatE g g') t'
                          -> Subtype (concatE (Cons x t_x g) g') t t'.
Proof. intros; pose proof weaken_subtype' as Hweaken; 
  apply Hweaken with (concatE g g'); trivial. Qed.

Lemma weaken_typ_top : forall (g:env) (e:expr) (t:type) (x:vname) (t_x:type),
    Hastype g e t -> unique g -> ~ (in_env x g) -> WFEnv g
                  -> Hastype (Cons x t_x g) e t.
Proof. intros; assert (Cons x t_x g = concatE (Cons x t_x g) Empty) by reflexivity;
  rewrite H3; apply weaken_typ; 
  try apply intersect_empty_r; simpl; intuition. Qed.

Lemma weaken_subtype_top : 
  forall (g:env) (t:type) (t':type) (x:vname) (t_x:type),
    Subtype g t t'  -> unique g -> ~ (in_env x g) -> WFEnv g 
                    -> WFtype g t  -> WFtype g t'
                    -> Subtype (Cons x t_x g) t t'.
Proof. intros; assert (Cons x t_x g = concatE (Cons x t_x g) Empty) by reflexivity;
  rewrite H5; apply weaken_subtype;
  try apply intersect_empty_r; simpl; intuition. Qed.


  Lemma weaken_many_typ : forall (g g':env) (e:expr) (t:type),
  Hastype g e t -> unique g -> unique g'
                -> intersect (binds g) (binds g') = empty  
                -> WFEnv (concatE g g')
                -> Hastype (concatE g g') e t.     
Proof. intros; induction g'; simpl; try assumption; inversion H3;
simpl in H1; destruct H1;
simpl in H2; apply intersect_names_add_elim_r in H2; destruct H2;
apply IHg' in H2 as H'; try assumption;
apply weaken_typ with (concatE g g') Empty e t x t0 in H'
  || apply weaken_tv_typ with (concatE g g') Empty e t a k in H';
simpl in H'; unfold in_env; simpl; 
try (apply intersect_empty_r);
try (apply unique_concat);
try (apply not_elem_concat_intro; assumption);  
intuition. Qed.

Lemma weaken_many_subtype : 
  forall (g g':env) (t:type) (t':type),
    Subtype g t t' -> unique g -> unique g'
                   -> intersect (binds g) (binds g') = empty   
                   -> WFEnv (concatE g g')
                   -> WFtype g t 
                   -> WFtype g t'
                   -> Subtype (concatE g g') t t'.
Proof. intros; induction g'; simpl; try assumption;
  inversion H3; simpl in H1; destruct H1;
  simpl in H2; apply intersect_names_add_elim_r in H2; destruct H2;
  apply weaken_subtype_top
    || apply weaken_tv_subtype_top;
  try apply IHg'; try apply weaken_many_wf;
  try apply unique_concat; trivial. Qed.