(*This file largely follows the file with the same name in Michael H. Borkowski's mechanization of refinement types*)

Require Import Lists.ListSet.
Require Import List.
Require Import Definitions.Syntax. 
Require Import Definitions.Names.
Require Import Definitions.FJTyping.
Require Import Lemmas.BasicLemmas.LemmasFJTyping.




Lemma empty_concatE : forall (g : env),
  concatE Empty g = g.
Proof. induction g; simpl; try rewrite IHg; reflexivity. Qed.
Lemma push: forall g g' x t, 
  concatE (Cons x t g) g' = concatE g (concatE (Cons x t Empty) g').
Proof. induction g'.
  - intros. simpl. reflexivity.
  - intros. simpl. f_equal. apply IHg'. 
Qed.  
Lemma binds_concat : forall (g g' : env),
    Subset (binds (concatE g g')) (union (binds g) (binds g')) /\
    Subset (union (binds g) (binds g')) (binds (concatE g g')).
Proof. intros; induction g'; simpl; unfold Subset; split
  ; try (unfold Subset in IHg'; destruct IHg')
  ; try (apply subset_refl)
  ; intros
  ; try ( apply set_add_elim in H1; apply subset_union_names_add_r;
          apply set_add_intro; destruct H1; try apply H in H1; intuition )
  ; try ( apply set_add_intro; apply subset_union_names_add_r in H1; 
          apply set_add_elim in H1; destruct H1; try apply H0 in H1; intuition ).
  Qed.

Lemma not_elem_concat_elim : forall (x : vname) (g g' : env),
    ~ Elem x (binds (concatE g g')) -> ~ Elem x (binds g) /\ ~ Elem x (binds g').
Proof. intros; assert 
    (Subset (union (binds g) (binds g')) (binds (concatE g g'))) 
  by apply binds_concat; pose proof (not_elem_subset x); 
  apply H1 in H0; try assumption. apply not_elem_union_elim in H0; assumption.
  Qed.

Lemma not_elem_concat_intro : forall (x : vname) (g g' : env),
    ~ Elem x (binds g) -> ~ Elem x (binds g') -> ~ Elem x (binds (concatE g g')).
Proof. intros; pose proof (binds_concat g g'); destruct H1;
  pose proof (not_elem_subset x); apply H3 with (union (binds g) (binds g'));
  apply (not_elem_union_intro x (binds g) (binds g') H) in H0; 
  try assumption.
  Qed.

Lemma unique_concat : forall (g g' : env),
    unique g -> unique g' -> intersect (binds g) (binds g') = empty
             -> unique (concatE g g').
Proof. intros; induction g'; simpl; try assumption; split;
  simpl in H0; destruct H0; simpl in H1;
  apply intersect_names_add_elim_r in H1; destruct H1;
  try (apply not_elem_concat_intro with x g g' in H3 as H4 ||
       apply not_elem_concat_intro with a g g' in H3 as H4 ; assumption);
  apply IHg' in H2; assumption.
  Qed.

Lemma concat_unique : forall (g g' : env),
    unique (concatE g g') 
        -> unique g /\ unique g' /\ intersect (binds g) (binds g') = empty.
Proof. intro g; induction g'; simpl; intros.
  - (* Empty *) repeat split; try apply intersect_empty_r; apply H.
  - (* Cons  *) repeat split; destruct H;
    apply IHg' in H0; destruct H0 as [Hg [Hg' Hi]];
    apply not_elem_concat_elim in H; destruct H;
    try apply intersect_names_add_intro_r; trivial.
  Qed.

Lemma boundin_concat : forall (x:vname) (t:type) (g g':env),
  bound_in x t (concatE g g') <-> bound_in x t g \/ bound_in x t g'.
Proof. intros; induction g'; simpl; intuition. Qed.

Lemma boundin_concat_unique : forall (x:vname) (t:type) (g g':env),
  bound_in x t (concatE g g') -> intersect (binds g) (binds g') = empty -> (Elem x (binds g) /\ ~Elem x (binds g')) \/ (Elem x (binds g') /\ ~Elem x (binds g)).
Proof. intros. induction g'.
  -
    simpl in H. left. 
    constructor. apply boundin_inenv with t;auto. simpl;auto. 
  -
    simpl in H0. apply intersect_names_add_elim_r in H0. destruct H0. simpl in H. 
    destruct H.
    +
      right. 
      constructor. simpl. apply elem_names_add_intro. left. destruct H. auto.
      destruct H. subst x0. auto.
    +
      apply IHg' in H;auto. 
      destruct H.
      *
        left. destruct H. constructor;auto. 
        simpl. apply not_elem_names_add_intro;constructor;auto.
        assert (x0<>x).
        apply not_elem_elem_neq with (binds g);auto. auto. 
      *
        right. destruct H. constructor;auto.
        simpl. apply elem_names_add_intro. right;auto.  Qed.

Lemma boundin_weaken : forall (x:vname) (t:type) (g g':env) (y:vname) (t_y:type),
  bound_in x t (concatE g g') -> bound_in x t (concatE (Cons y t_y g) g').
Proof. intros; apply boundin_concat; simpl; 
  apply boundin_concat in H; intuition. Qed.

  
  (* Type Erasure and Substitution *)

Lemma erase_tsubFV : forall (x:vname) (v:expr) (t:type),
    erase (tsubFV x v t) = erase t.
Proof. intros; induction t; simpl.
  - (* TRefn *) reflexivity.
  Qed.

Lemma erase_openT_at : forall (t:type) (j:index) (x:vname),
    erase (openT_at j x t) = erase t.
Proof. induction t; intros; simpl.
  - (* TRefn *) reflexivity.
  Qed.

Lemma erase_unbind : forall (x:vname) (t:type), erase (unbindT x t) = erase t.
Proof. intros; apply erase_openT_at. Qed.

Lemma erase_tsubBV_at : forall (j:index) (v:expr) (t:type), 
    erase (tsubBV_at j v t) = erase t.
Proof. intros j v t; revert j; induction t; intros; simpl.
  - (* TRefn *) reflexivity.
  Qed.

Lemma erase_tsubBV : forall (v:expr) (t:type), erase (tsubBV v t) = erase t.
Proof. intros. apply erase_tsubBV_at. Qed.


Lemma empty_concatF : forall (g : fjenv),
  concatF FEmpty g = g.
Proof. induction g; simpl; try rewrite IHg; reflexivity. Qed.

Lemma binds_concatF : forall (g g' : fjenv),
    Subset (bindsFJ (concatF g g')) (union (bindsFJ g) (bindsFJ g')) /\
    Subset (union (bindsFJ g) (bindsFJ g')) (bindsFJ (concatF g g')).
Proof. intros; induction g'; simpl; unfold Subset; split
  ; try (unfold Subset in IHg'; destruct IHg')
  ; try (apply subset_refl)
  ; intros
  ; try ( apply set_add_elim in H1; apply subset_union_names_add_r;
          apply set_add_intro; destruct H1; try apply H in H1; intuition )
  ; try ( apply set_add_intro; apply subset_union_names_add_r in H1; 
          apply set_add_elim in H1; destruct H1; try apply H0 in H1; intuition ).
  Qed.

Lemma vbinds_concatF : forall (g g' : fjenv),
  Subset (union (bindsFJ g) (bindsFJ g')) (bindsFJ (concatF g g')).
Proof. intros; induction g'; simpl; try apply subset_refl;
  try apply subset_trans with (names_add x (union (bindsFJ g) (bindsFJ g')));
  try apply subset_union_names_add_r;
  try apply subset_add_both_intro; apply IHg'.
  Qed.

Lemma vbinds_cons_concatF : forall (g g' : fjenv) (x : vname) (t_x : fjtype),
    Subset (bindsFJ (concatF g g'))  (bindsFJ (concatF (FCons x t_x g) g')) /\
    Subset (bindsFJ (concatF (FCons x t_x g) g')) (names_add x (bindsFJ (concatF g g'))).
Proof. intros; induction g'; split; simpl;
  try apply subset_add_both_intro; try (apply subset_add_intro; apply subset_refl);
  try apply subset_refl; try apply IHg';
  apply subset_trans with (names_add x0 (names_add x (bindsFJ (concatF g g'))));
  try apply subset_add_both_intro; try apply subset_add_commute; apply IHg'.
  Qed.


Lemma not_elem_concatF_elim : forall (x : vname) (g g' : fjenv),
    ~ Elem x (bindsFJ (concatF g g')) -> ~ Elem x (bindsFJ g) /\ ~ Elem x (bindsFJ g').
Proof. intros; assert 
    (Subset (union (bindsFJ g) (bindsFJ g')) (bindsFJ (concatF g g'))) 
  by apply binds_concatF; pose proof (not_elem_subset x); 
  apply H1 in H0; try assumption. apply not_elem_union_elim in H0; assumption.
  Qed.

Lemma not_elem_concatF_intro : forall (x : vname) (g g' : fjenv),
    ~ Elem x (bindsFJ g) -> ~ Elem x (bindsFJ g') -> ~ Elem x (bindsFJ (concatF g g')).
Proof. intros; pose proof (binds_concatF g g'); destruct H1;
  pose proof (not_elem_subset x); apply H3 with (union (bindsFJ g) (bindsFJ g'));
  apply (not_elem_union_intro x (bindsFJ g) (bindsFJ g') H) in H0; 
  try assumption.
  Qed.

Lemma uniqueF_concatF : forall (g g' : fjenv),
    uniqueF g -> uniqueF g' -> intersect (bindsFJ g) (bindsFJ g') = empty
              -> uniqueF (concatF g g').
Proof. intros; induction g'; simpl; try assumption; split;
  simpl in H0; destruct H0; simpl in H1;
  apply intersect_names_add_elim_r in H1; destruct H1;
  try (apply not_elem_concatF_intro with x g g' in H3 as H4 ||
       apply not_elem_concatF_intro with a g g' in H3 as H4 ; assumption);
  apply IHg' in H2; assumption.
  Qed.

Lemma boundinF_concatF : forall (x:vname) (t:fjtype) (g g':fjenv),
  bound_inF x t (concatF g g') <-> bound_inF x t g \/ bound_inF x t g'.
Proof. intros; induction g'; simpl; intuition. Qed.

Lemma boundinF_weaken : forall (x:vname) (t:fjtype) (g g':fjenv) (y:vname) (t_y:fjtype),
  bound_inF x t (concatF g g') -> bound_inF x t (concatF (FCons y t_y g) g').
Proof. intros; apply boundinF_concatF; simpl; 
  apply boundinF_concatF in H; intuition. Qed.


Lemma erase_concat : forall (g g':env), 
    erase_env (concatE g g') = concatF (erase_env g) (erase_env g').
Proof. intro g; induction g'; simpl; try reflexivity;
  apply f_equal; apply IHg'. Qed. 

Lemma binds_erase_env : forall (g : env),
    binds g = bindsFJ (erase_env g).
Proof. induction g; simpl; try reflexivity; apply f_equal; apply IHg. Qed.

Lemma boundin_erase_env : forall (x : vname) (t : type) (g : env),
    bound_in x t g -> bound_inF x (erase t) (erase_env g).
Proof. intros; induction g; simpl in H; try contradiction; simpl;
  try destruct H; try destruct H; try subst x0; try subst t0; intuition. 
  Qed.

Lemma unique_erase_env : forall (g : env),
    unique g -> uniqueF (erase_env g).
Proof. intros; induction g; simpl; try assumption; split;
  simpl in H; destruct H; unfold in_env in H; unfold in_envFJ;
  rewrite binds_erase_env in H; try apply IHg; assumption. Qed.

(* -- -- -- -- -- -- -- -- -- -- -- --
   -- Substitutions in Environments --
   -- -- -- -- -- -- -- -- -- -- -- -- *)



Lemma esubFV_binds : forall (x:vname) (v:expr) (g:env),
    binds (esubFV x v g) = binds g.
Proof. intros; induction g; simpl; try (rewrite IHg); reflexivity. Qed.


Lemma esubFV_unique : forall (x:vname) (v:expr) (g:env),
    unique g -> unique (esubFV x v g).
Proof. intros; induction g; simpl; simpl in H; try reflexivity;
  destruct H; split; unfold in_env; try (rewrite esubFV_binds);
  apply IHg in H0; assumption. Qed.

Lemma boundin_esubFV : forall (x:vname) (t:type) (y:vname) (v:expr) (g:env),
    bound_in x t g -> bound_in x (tsubFV y v t) (esubFV y v g).
Proof. intros; induction g; simpl; simpl in H; try contradiction. 
  - destruct H; try destruct H; try subst x0; try subst t0.
    * left; auto.
    * right; apply IHg; assumption.
  (* - apply IHg; assumption. *)
  Qed. 

Lemma erase_esubFV : forall (x:vname) (v:expr) (g:env),
    erase_env (esubFV x v g) = erase_env g.
Proof. intros x v; induction g; simpl; try reflexivity;
  try rewrite erase_tsubFV; apply f_equal; apply IHg. Qed.


Lemma l1: forall es Us g, List.Forall2 (fun (e : expr) (_ : fjtype) => Subset (fv e) (bindsFJ g)) es Us -> 
List.Forall (fun (e : expr) => Subset (fv e) (bindsFJ g)) es.
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
Lemma l2: forall es g, List.Forall (fun (e : expr) => Subset (fv e) (bindsFJ g)) es -> 
Subset
  ((fix f (es' : [expr]) : set vname :=
      match es' with
      | nil => empty
      | (e :: es'')%list => union (fv e) (f es'')
      end) es) (bindsFJ g).
Proof.
  intros.
  induction es.
  apply subset_empty_l.
  inversion H.
  apply subset_union_intro_l;auto.
Qed.

Lemma fv_subset_bindsFJ : forall (g : fjenv) (e : expr) (t : fjtype),
    HasFJtype g e t -> Subset (fv e) (bindsFJ g).
Proof. intros g e t p_e_t. 
    induction p_e_t using HasFJtype_ind'
    ;simpl; 
    try (simpl in IHp_e_t; destruct IHp_e_t as [IH1 IH2]); 
    (* Bc Ic Pr *) try (split; apply subset_empty_l);
    (* FTVar *)    try (split; apply subset_sing_l || apply subset_empty_l; 
                        apply boundin_inenvFJ with b; assumption );
    (* App/AppT/Ann*) try (intuition; repeat apply subset_union_intro_l; assumption);
    try (apply subset_empty_l);
    try (apply subset_sing_l; apply boundin_inenvFJ with b; assumption).
  -
    apply l1 in H3.
    apply l2;auto.
  -
    simpl in H0;
    pose proof (fresh_varFE_not_elem  nms g e) as Hfr; destruct Hfr as [Hfv Hfr]; 
    destruct Hfr as [Hnms Hg];
    apply H0 in Hnms. 
    apply subset_union_intro_l; try assumption.
    * apply subset_add_elim with (fresh_varFE nms g e); try assumption;
      apply subset_trans with (fv  (unbind (fresh_varFE nms g e) e));
      try (apply fv_unbind_intro); assumption.
Qed.
  


Lemma fjtyp_nofv : forall (g:fjenv) (e:expr) (t:fjtype),
  HasFJtype g e t -> g = FEmpty -> fv e = empty.
Proof. intros.
apply fv_subset_bindsFJ in H. rewrite H0 in H. simpl in H. 
apply subset_empty_r in H. auto.
Qed.
Lemma fjtyp_nofv_forall : forall (es:[expr]) (ts:[fjtype]),
  Forall2 (HasFJtype FEmpty) es ts -> Forall (fun e => fv e = empty) es.
Proof.
  intros. generalize dependent ts.
  induction es. 
  -
    intros. destruct ts. apply Forall_nil. inversion H.
  -
    intros. inversion H. apply Forall_cons. apply fjtyp_nofv with FEmpty y;auto. eapply IHes;eauto.
Qed.


Lemma fvp_subset_bindsFJ : forall (g : fjenv) (ps : preds),  
    PIsBool g ps -> Subset (fvP ps) (bindsFJ g).
Proof. intros g ps p_ps_bl. induction p_ps_bl; simpl.
  - apply subset_empty_l.
  - apply subset_union_intro_l;
    pose proof (fv_subset_bindsFJ g p (TBool) H) as Hp;assumption.
  Qed.