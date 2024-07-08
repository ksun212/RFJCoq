Require Import Crush.
Require Import List.

Require Import Definitions.Syntax. 
Require Import Definitions.Names.
Require Import Definitions.FJTyping.

Require Import Lemmas.BasicLemmas.LemmasFJTyping.
Require Import Lemmas.BasicLemmas.LemmasEnvironments.



(*---------------Weakening Lemmas of FJ Typing---------------*)


Lemma aux1: forall env x t_x g g',
  env = concatF g g'->
  intersect (bindsFJ g) (bindsFJ g') = empty ->
  ~ in_envFJ x g ->
  ~ in_envFJ x g' -> 
  forall (a : expr) (b : fjtype), (forall (g g' : fjenv) (x : vname) (t_x : fjtype),
  env = concatF g g' ->
  intersect (bindsFJ g) (bindsFJ g') = empty ->
  ~ in_envFJ x g ->
  ~ in_envFJ x g' -> HasFJtype (concatF (FCons x t_x g) g') a b) ->
  HasFJtype (concatF (FCons x t_x g) g') a b.
Proof.
  intros.
  apply H3;auto.
Qed.
Lemma weaken_fjtyp' : forall (g'g : fjenv) (e : expr) (t : fjtype),
    HasFJtype g'g e t -> ( forall (g g':fjenv) (x:vname) (t_x:fjtype),
        g'g = concatF g g' -> intersect (bindsFJ g) (bindsFJ g') = empty
                           -> ~ (in_envFJ x g) -> ~ (in_envFJ x g') 
                           -> HasFJtype (concatF (FCons x t_x g) g') e t ).
Proof. apply ( HasFJtype_ind' 
  (fun (g'g : fjenv) (e : expr) (t : fjtype) => forall (g g':fjenv) (x:vname) (t_x:fjtype),
      g'g = concatF g g' -> intersect (bindsFJ g) (bindsFJ g') = empty
                         -> ~ (in_envFJ x g) -> ~ (in_envFJ x g') 
                         -> HasFJtype (concatF (FCons x t_x g) g') e t ));
  intro env; intros.
  - (* FTBC *) apply FTBC.
  - (* FTIC *) apply FTIC.
  - (* FTVar *) apply FTVar. apply boundinF_weaken; subst env; assumption.
  - (* FTUnOP *) apply FTUnOP;auto.
  - (* FTBinOP*) apply FTBinOP;auto.
  - eapply FTInvok;eauto. 
  -
    eapply FTInvokI;eauto. 
  - 
    eapply FTField;eauto.
  -
    eapply FTNew;eauto.
    assert (List.Forall2 (fun (e : expr) (t : fjtype) => (HasFJtype (concatF (FCons x t_x g) g') e t)) es Us).
    eapply Forall2_impl.
    apply aux1;eauto.
    apply H3.
    apply H8.
  -
    apply FTLet with b (names_add x (union nms (bindsFJ env))).
    apply H0;auto.
    intros. assert (FCons y b (concatF (FCons x t_x g) g') = concatF (FCons x t_x g) (FCons y b g')) by reflexivity. rewrite H8. 
    apply not_elem_names_add_elim in H7; destruct H7.
    apply not_elem_union_elim in H9; destruct H9.
    apply H2;auto.
    rewrite H3. reflexivity. simpl.
    subst env.  apply not_elem_concatF_elim in H10; destruct H10.
    try apply intersect_names_add_intro_r;auto.
    try apply not_elem_names_add_intro; intuition.
  -
    apply FTSub with s;auto.
Qed.

Lemma weaken_fjtyp : forall (g g' : fjenv) (e : expr) (t : fjtype) (x:vname) (t_x:fjtype),
  HasFJtype (concatF g g') e t -> intersect (bindsFJ g) (bindsFJ g') = empty
                              -> ~ (in_envFJ x g) -> ~ (in_envFJ x g') 
                              -> HasFJtype (concatF (FCons x t_x g) g') e t.
Proof. intros; apply weaken_fjtyp' with (concatF g g'); intuition. Qed.

Lemma weaken_fjtyp_top : forall (g : fjenv) (e : expr) (t : fjtype) (x:vname) (t_x:fjtype),
  HasFJtype g e t -> ~ (in_envFJ x g) -> HasFJtype (FCons x t_x g) e t.
Proof. intros; assert (FCons x t_x g = concatF (FCons x t_x g) FEmpty) by reflexivity;
  rewrite H1; apply weaken_fjtyp; simpl; try apply intersect_empty_r; intuition. Qed.

Lemma weaken_pbool' : forall (g'g : fjenv) (ps : preds),
    PIsBool g'g ps -> ( forall (g g':fjenv) (x:vname) (t_x:fjtype),
        g'g = concatF g g' -> intersect (bindsFJ g) (bindsFJ g') = empty
                           -> ~ (in_envFJ x g) -> ~ (in_envFJ x g') 
                           -> PIsBool (concatF (FCons x t_x g) g') ps ).
Proof. apply ( PIsBool_ind 
  (fun (g'g : fjenv) (ps : preds) => forall (g g':fjenv) (x:vname) (t_x:fjtype),
      g'g = concatF g g' -> intersect (bindsFJ g) (bindsFJ g') = empty
                         -> ~ (in_envFJ x g) -> ~ (in_envFJ x g') 
                         -> PIsBool (concatF (FCons x t_x g) g') ps ));
  intro env; intros.
  - apply PFTEmp.
  - apply PFTCons; subst env; try apply weaken_fjtyp;
    try apply H1; intuition.
  Qed.

Lemma weaken_many_fjtyp : forall (g g':fjenv) (e:expr) (t:fjtype),
    HasFJtype g e t -> uniqueF g -> uniqueF g'
                   -> intersect (bindsFJ g) (bindsFJ g') = empty
                   -> HasFJtype (concatF g g') e t.
Proof. intros; induction g'; simpl; try assumption;
  simpl in H1; destruct H1;
  simpl in H2; apply intersect_names_add_elim_r in H2; destruct H2;
  apply IHg' in H2 as H'; try assumption.
  apply weaken_fjtyp with (concatF g g') FEmpty e t x t0 in H';
  simpl in H'; unfold in_envFJ; simpl; 
  try (apply intersect_empty_r);
  try (apply uniqueF_concatF);
  try (apply not_elem_concatF_intro; assumption);  
  intuition.
  
  
  Qed.

Lemma weaken_pbool : forall (g g' : fjenv) (ps : preds) (x:vname) (t_x:fjtype),
  PIsBool (concatF g g') ps -> intersect (bindsFJ g) (bindsFJ g') = empty
                              -> ~ (in_envFJ x g) -> ~ (in_envFJ x g') 
                              -> PIsBool (concatF (FCons x t_x g) g') ps.
Proof. intros; apply weaken_pbool' with (concatF g g'); intuition. Qed.
