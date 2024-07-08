Require Import Arith.
Require Import List. 

Require Import Definitions.Syntax.
Require Import Definitions.Names.
Require Import Definitions.FJTyping.
Require Import Definitions.Typing.

Require Import Lemmas.BasicLemmas.LemmasFJTyping.
Require Import Lemmas.BasicLemmas.LemmasEnvironments.
Require Import Lemmas.BasicLemmas.LemmasFJWeaken. 



(*---------------Weakening Lemmas of WF---------------*)

Lemma weaken_wf' : forall (g'g : env) (t : type),
    WFtype g'g t -> ( forall (g g' : env) (x : vname) (t_x : type),
        g'g = concatE g g' -> intersect (binds g) (binds g') = empty
                           -> ~ (in_env x g) -> ~ (in_env x g') 
                           -> WFtype (concatE (Cons x t_x g) g') t ).
Proof. apply ( WFtype_ind 
  (fun (g'g : env) (t : type) => forall (g g':env) (x:vname) (t_x:type),
      g'g = concatE g g' -> intersect (binds g) (binds g') = empty
                         -> ~ (in_env x g) -> ~ (in_env x g') 
                         -> WFtype (concatE (Cons x t_x g) g') t  )).
  - (* WFBase *) intros; apply WFBase; assumption.
  - (* WFRefn *) intro env; intros; 
    apply WFRefn with (names_add x (union nms (binds (concatE g g')))); 
    try apply H0; try assumption; intros;
    apply not_elem_names_add_elim in H7; destruct H7;
    apply not_elem_union_elim in H8; destruct H8;
    apply not_elem_concat_elim in H9; destruct H9;
    subst env; 
    assert (FCons y (b) (erase_env (concatE (Cons x t_x g) g'))
            = concatF (FCons x (erase t_x) (erase_env g)) (FCons y (b) (erase_env g')) )
      by (rewrite erase_concat; reflexivity); rewrite H3;
    apply weaken_pbool; 
    assert (concatF (erase_env g) (FCons y (b) (erase_env g'))
            = FCons y (b) (erase_env (concatE g g')))
      by (rewrite erase_concat; reflexivity); try rewrite H11;
    try apply H2; simpl; try split; try unfold in_envFJ; simpl;
    try apply unique_erase_env; try rewrite <- binds_erase_env;
    try apply intersect_names_add_intro_r; try rewrite <- binds_erase_env;
    try apply not_elem_names_add_intro;
    apply Nat.neq_sym in H7; try split; trivial.
  Qed.

Lemma weaken_wf : forall (g g' : env) (t : type)(x : vname) (t_x : type),
    WFtype (concatE g g') t -> intersect (binds g) (binds g') = empty
                              -> ~ (in_env x g) -> ~ (in_env x g') 
                              -> WFtype (concatE (Cons x t_x g) g') t.
Proof. intros; apply weaken_wf' with (concatE g g'); trivial. Qed.

Lemma weaken_wf_top : forall (g : env) (t : type) (x : vname) (t_x : type),
    WFtype g t -> ~ (in_env x g) -> WFtype (Cons x t_x g) t.
Proof. intros; assert (Cons x t_x g = concatE (Cons x t_x g) Empty) by reflexivity;
  rewrite H1; apply weaken_wf; simpl; try apply intersect_empty_r; intuition. Qed.
Lemma weaken_wf_many : forall (g : env) (t : type) (x : vname) (t_x : type),
  WFtype g t -> ~ (in_env x g) -> WFtype (Cons x t_x g) t.
Proof. intros; assert (Cons x t_x g = concatE (Cons x t_x g) Empty) by reflexivity;
rewrite H1; apply weaken_wf; simpl; try apply intersect_empty_r; intuition. Qed.


Lemma weaken_wf_forall: forall (g g' : env)(x : vname) (t_x : type) Us,
intersect (binds g) (binds g') = empty -> 
~ (in_env x g) -> ~ (in_env x g') ->
Forall (WFtype (concatE g g')) Us -> 
Forall (WFtype (concatE (Cons x t_x g) g')) Us.
Proof.
  intros.
  induction Us.
  apply Forall_nil.
  inversion H2.
  apply Forall_cons.
  apply  weaken_wf;auto.
  apply IHUs;auto.
Qed.


Lemma weaken_wfenv: forall gg', WFEnv gg' -> 
              forall g g' y b, gg' = (concatE g g') -> ~ Elem y (union (binds g) (binds g')) ->  WFtype (concatE g g') b -> 
              WFEnv (concatE g (Cons y b g')).
Proof.
  intros.
  destruct g.
  simpl. subst gg'. apply WFEBind;auto. unfold in_env.  simpl.  rewrite empty_concatE. notin_solve_one. 
  simpl. subst gg'. apply WFEBind;auto. unfold in_env. assert (Subset (binds (concatE (Cons x t g) g')) (union (binds (Cons x t g)) (binds g'))). apply binds_concat.
  unfold not. intro. apply H0 in H3. apply H1 in H3. contradiction. 
  Qed.

  Lemma weaken_many_wf : forall (g g':env) (t:type),
  WFtype g t -> unique g -> unique g'
               -> intersect (binds g) (binds g') = empty 
               -> WFtype (concatE g g') t.
Proof. intros; induction g'; simpl; try assumption;
simpl in H1; destruct H1;
simpl in H2; apply intersect_names_add_elim_r in H2; destruct H2;
apply IHg' in H2 as H'; try assumption;
apply weaken_wf with (concatE g g') Empty t x t0 in H'
  || apply weaken_tv_wf with (concatE g g') Empty t a k0 in H';
simpl in H'; unfold in_env; simpl; 
try (apply intersect_empty_r);
try (apply unique_concat);
try (apply not_elem_concat_intro; assumption);  
intuition. Qed.

Lemma weaken_many_wf_r : forall (g g':env) (t:type),
WFtype g' t -> unique g -> unique g'
             -> intersect (binds g) (binds g') = empty 
             -> WFtype (concatE g g') t.
Proof. intros; induction g. rewrite empty_concatE. auto. simpl in H2. apply intersect_names_add_elim_l in H2; destruct H2. inversion H0. apply weaken_wf' with (concatE g g');auto.  Qed.

Lemma weaken_many_wf_r_forall : forall (g g':env) (Us:[type]),
Forall (WFtype g') Us -> unique g -> unique g'
             -> intersect (binds g) (binds g') = empty 
             -> Forall (WFtype (concatE g g')) Us.
Proof.
  intros. induction Us.
  apply Forall_nil.
  inversion H. apply Forall_cons. apply weaken_many_wf_r;auto. apply IHUs;auto.
Qed.
Lemma weaken_wf_top_forall : forall (g : env) (ts : [type]) (x : vname) (t_x : type),
    Forall (WFtype g) ts -> ~ (in_env x g) -> Forall (WFtype (Cons x t_x g)) ts.
Proof.
  intros. induction ts.
  apply Forall_nil.
  inversion H. apply Forall_cons. apply weaken_wf_top;auto. apply IHts;auto.
Qed.