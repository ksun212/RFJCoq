(*This file largely follows the file with the same name in Michael H. Borkowski's mechanization of refinement types*)

Require Import Arith.
Require Import Lists.ListSet.
Require Import List.
Require Import Definitions.Syntax.

  (* I. Basic Defs and Properties of our Name-set theory *)

Definition names := set vname.
Definition empty := empty_set vname.
Definition singleton (x:vname) := @set_add vname Nat.eq_dec x empty.

Definition names_add := @set_add vname Nat.eq_dec.
Definition names_rem := @set_remove vname Nat.eq_dec.
Definition names_mem := @set_mem vname Nat.eq_dec.
Definition union := @set_union vname Nat.eq_dec.
Definition intersect := @set_inter vname Nat.eq_dec.
Definition diff := @set_diff vname Nat.eq_dec.

Definition Elem := @set_In vname.
Definition Subset (xs : names) (ys: names) : Prop :=
    forall (x : vname), Elem x xs -> Elem x ys.

Fixpoint Elem_many nml nms {struct nml}:=
  match nml with
  | nil => True
  | n::nml' => Elem n nms /\ Elem_many nml' nms
  end.
Lemma no_elem_empty : forall (ys : names),
    (forall (x:vname), ~ Elem x ys) -> ys = empty.
Proof. intros. destruct ys.
  - reflexivity.
  - assert (List.In v (v :: ys)) by auto with *.
    apply H in H0; contradiction.
  Qed.

Lemma empty_no_elem : forall (ys : names),
    ys = empty -> forall (x : vname), ~ Elem x ys.
Proof. unfold not; intros; subst ys; unfold Elem in H0; contradiction. Qed. 

Lemma elem_sing : forall (x y : vname),
    Elem x (singleton y) <-> x = y.
Proof. intros; split; simpl; intro H.
  - destruct H; symmetry; (trivial || contradiction).
  - intuition. Qed.

Lemma not_elem_subset : forall (x : vname) (xs ys : names),
    Subset xs ys -> ~ Elem x ys -> ~ Elem x xs.
Proof. unfold Subset; unfold not; intros; intuition. Qed.
Lemma not_elem_singleton: forall (x y : vname), ~Elem x (singleton y) -> x <> y.
Proof.
  intros.
  unfold not in *.
  intros.
  assert (Elem x (singleton y)).
  apply elem_sing.
  assumption.
  apply H in  H1.
  contradiction.
Qed.

 
Lemma not_elem_names_add_intro : forall (x y : vname) (ys : names),
    x <> y /\ ~ Elem x ys -> ~ Elem x (names_add y ys).
Proof. intros. unfold not; intro. apply set_add_elim in H0. intuition. Qed.

Lemma not_elem_names_add_elim : forall (x y : vname) (ys : names),
    ~ Elem x (names_add y ys) -> x <> y /\ ~ Elem x ys.
Proof. intros. pose proof (@set_add_intro vname Nat.eq_dec x y ys) as H1.
  split; unfold not; intros; intuition. Qed. 

Lemma elem_names_add_intro : forall (x y : vname) (ys : names),
  x = y \/ Elem x ys  -> Elem x (names_add y ys).
Proof. intros. unfold Elem in *. unfold names_add. apply set_add_intro;auto.
Qed. 

Lemma elem_names_add_elem : forall (x y : vname) (ys : names),
  Elem x (names_add y ys) -> x = y \/ Elem x ys.
Proof. intros. unfold Elem in *. unfold names_add. apply set_add_elim in H;auto.
Qed. 

Lemma not_elem_elem_neq: forall (x y : vname) ns, ~Elem x (ns) -> Elem y ns -> x <> y.
Proof.
  intros. induction ns. 
  - simpl in H0. contradiction.
  - simpl in H0. destruct H0.
    + rewrite H0 in H. simpl in H. unfold not in *. intros. assert (y = x \/ Elem x ns). left. auto. apply H in H2. auto.
    + simpl in H. apply IHns;auto.  
Qed.
Lemma not_elem_union_intro : forall (x : vname) (xs ys : names),
    ~ Elem x xs -> ~ Elem x ys -> ~ Elem x (union xs ys).
Proof. unfold not; intros; apply set_union_elim in H1;
  destruct H1; apply H in H1 || apply H0 in H1; contradiction. Qed.

Lemma not_elem_union_elim : forall (x : vname) (xs ys : names),
    ~ Elem x (union xs ys) -> ~ Elem x xs /\ ~ Elem x ys.
Proof. unfold not; intros; split; intro Hx;
  apply set_union_intro1 with vname Nat.eq_dec x xs ys in Hx ||
    apply set_union_intro2 with vname Nat.eq_dec x xs ys in Hx ;  
  intuition. Qed.


Lemma not_elem_union_elim1 : forall (x : vname) (E F : names),
  ~ Elem x (union E F) -> ~ Elem x E.
Proof.
  intros.
  apply not_elem_union_elim in H.
  destruct H.
intuition. Qed.

Lemma not_elem_union_elim2 : forall (x : vname) (E F : names),
  ~ Elem x (union E F) -> ~ Elem x F.
Proof. intros.
apply not_elem_union_elim in H.
destruct H.
intuition. Qed.
Lemma subset_refl : forall (xs : names),
    Subset xs xs.
Proof. unfold Subset; trivial. Qed.


Lemma subset_trans : forall (xs ys zs : names),
    Subset xs ys -> Subset ys zs -> Subset xs zs.
Proof. unfold Subset; intros xs ys zs H1 H2 x Hxs; 
  apply H2; apply H1; assumption. Qed.

Lemma subset_trans3 : forall (xs ys zs ws : names),
    Subset xs ys -> Subset ys zs -> Subset zs ws -> Subset xs ws.
Proof. intros; apply subset_trans with zs; try apply H1;
  apply subset_trans with ys; try apply H; apply H0. Qed.

Lemma subset_trans4 : forall (xs ys zs ws vs : names),
    Subset xs ys -> Subset ys zs -> Subset zs ws -> Subset ws vs -> Subset xs vs.
Proof. intros; apply subset_trans3 with zs ws; try apply H1; try apply H2;
  apply subset_trans with ys; try apply H; apply H0. Qed. 

Lemma subset_trans5 : forall (xs ys zs ws vs us : names),
    Subset xs ys -> Subset ys zs -> Subset zs ws 
        -> Subset ws vs -> Subset vs us -> Subset xs us.
Proof. intros; apply subset_trans3 with ys zs; try apply H; try apply H0;
  apply subset_trans3 with ws vs; assumption. Qed. 

Lemma subset_empty_l : forall (xs : names),
    Subset empty xs.
Proof. unfold Subset; intros; contradiction. Qed.
Lemma subset_empty_r : forall (xs : names),
    Subset xs empty -> xs = empty.
Proof. intros. destruct xs. 
  - auto.
  -
    unfold Subset in *; intros.
    assert (Elem v (v::xs)). simpl. left;auto. apply H in H0. simpl in H0. contradiction.
Qed.

Lemma subset_sing_l : forall (x : vname) (xs : names),
    Subset (singleton x) xs <-> Elem x xs.
Proof. intros; split; unfold Subset.
  - intro. apply H; apply elem_sing; reflexivity.
  - intros; apply elem_sing in H0; subst x; assumption. Qed.

Lemma subset_sing_add : forall (x y : vname) (xs : names),
    Subset (singleton x) (names_add y xs) <-> x = y \/ Subset (singleton x) xs.
Proof. intros; split; intro.
  - apply subset_sing_l in H; apply ListSet.set_add_iff in H; destruct H;
    try (apply subset_sing_l in H); intuition.
  - apply subset_sing_l; apply ListSet.set_add_iff. destruct H;
    try (apply subset_sing_l in H); intuition. Qed.
 
Lemma subset_add_intro_l : forall (x : vname) ( xs ys : names ),
    Elem x ys -> Subset xs ys -> Subset (names_add x xs) ys.
Proof. unfold Subset; intros; apply set_add_elim in H1; destruct H1; 
    try subst x0; intuition. Qed.
    
Lemma subset_add_intro : forall (x : vname) ( xs ys : names ),
    Subset xs ys -> Subset xs (names_add x ys).
Proof. unfold Subset; intros; apply set_add_intro; apply H in H0; intuition. Qed.

Lemma subset_add_both_intro : forall (x : vname) ( xs ys : names ),
    Subset xs ys -> Subset (names_add x xs) (names_add x ys).
Proof. unfold Subset; intros. apply set_add_elim in H0; apply set_add_intro.
  destruct H0; try apply H in H0; intuition. Qed. 

Lemma subset_add_elim : forall (z : vname) (xs ys : names),
    ~ Elem z xs -> Subset xs (names_add z ys) -> Subset xs ys.
Proof. unfold Subset; intros; apply H0 in H1 as H2; apply set_add_elim in H2;
  destruct H2; (subst x; contradiction) || trivial. Qed.
 
Lemma subset_add_both_elim : forall (x : vname) ( xs ys : names ),
    ~ Elem x xs -> Subset (names_add x xs) (names_add x ys) -> Subset xs ys.
Proof. unfold Subset; intros. apply set_add_elim2 with Nat.eq_dec x.
  - apply H0. apply set_add_intro; intuition.
  - unfold not; intro; subst x; contradiction. Qed.

Lemma subset_add_commute : forall (x y : vname) (zs : names),
    Subset (names_add x (names_add y zs)) (names_add y (names_add x zs)).
Proof. unfold Subset; intros; apply set_add_intro; 
  apply set_add_elim in H; destruct H;
  try (right; apply set_add_intro2; apply H);
  apply set_add_elim in H; destruct H;
  try (left; apply H); right; apply set_add_intro1; apply H. Qed.

Lemma subset_add_to_diff : forall (xs ys : names) (y : vname),
    Subset xs (names_add y ys) -> Subset (diff xs (singleton y)) ys.
Proof. intros; unfold Subset; intros;
  apply set_diff_iff in H0; destruct H0;
  apply H in H0; apply set_add_elim in H0;
  destruct H0; try subst y; simpl in H1; intuition. Qed.

Lemma subset_diff_to_add : forall (xs ys : names) (y : vname),
    Subset (diff xs (singleton y)) ys -> Subset xs (names_add y ys).
Proof. intros; unfold Subset; intros;
  apply set_add_intro; destruct (x =? y) eqn:X;
  try apply Nat.eqb_eq in X; try (left; apply X);
  apply Nat.eqb_neq in X; right; apply H;
  apply set_diff_iff; split; simpl; intuition. Qed.

Lemma union_empty_l : forall (ys : names), 
    Subset ys (union empty ys) /\ Subset (union empty ys) ys.
Proof. unfold Subset; split; intros.
  - apply set_union_intro2; assumption.
  - apply set_union_emptyL in H; assumption. Qed.

Lemma union_empty_r : forall (ys : names), 
  Subset ys (union ys empty) /\ Subset (union ys empty) ys.
Proof. unfold Subset; split; intros.
- apply set_union_intro1; assumption.
- apply set_union_emptyR in H; assumption. Qed.
Lemma subset_union_intro_l : forall (xs ys zs : names),
    Subset xs zs -> Subset ys zs -> Subset (union xs ys) zs.
Proof. unfold Subset; intros; apply set_union_elim in H1;
  destruct H1; apply H in H1|| apply H0 in H1; assumption. Qed.

Lemma subset_union_intro_r : forall (xs zs : names),
    Subset xs (union xs zs) /\ Subset xs (union zs xs).
Proof. unfold Subset; split; intros;
  apply set_union_intro; intuition. Qed.

Lemma subset_union_assoc : forall (xs ys zs : names),
    Subset (union (union xs ys) zs) (union xs (union ys zs)) /\
    Subset (union xs (union ys zs)) (union (union xs ys) zs).
Proof. unfold Subset; split; intros; apply set_union_elim in H;
  destruct H; try (apply set_union_elim in H; destruct H);
  apply set_union_intro;
  ( left;  apply H || apply set_union_intro; (left; apply H) || (right; apply H) ) || 
  ( right; apply H || apply set_union_intro; (left; apply H) || (right; apply H) ).
  Qed.

Lemma subset_union_both : forall (xs ys xs' ys' : names),
    Subset xs xs' -> Subset ys ys' -> Subset (union xs ys) (union xs' ys').
Proof. unfold Subset; intros. apply set_union_elim in H1.
  destruct H1; apply H in H1 || apply H0 in H1.
  -  apply set_union_intro1; trivial.
  -  apply set_union_intro2; trivial. Qed.
Lemma subset_union_both' : forall (xs ys xs' ys' : names),
  Subset xs ys' -> Subset ys xs' -> Subset (union xs ys) (union xs' ys').
Proof. unfold Subset; intros. apply set_union_elim in H1.
destruct H1; apply H in H1 || apply H0 in H1.
-  apply set_union_intro2; trivial.
-  apply set_union_intro1; trivial. Qed.
Lemma subset_union_names_add_l : forall (xs ys : names) (x : vname),
    Subset (union (names_add x xs) ys) (names_add x (union xs ys)) /\
    Subset (names_add x (union xs ys)) (union (names_add x xs) ys).
Proof. unfold Subset; intros; split; intros.
  - apply set_union_elim in H. destruct H.
      * apply set_add_intro; apply set_add_elim in H; destruct H; 
        intuition; right. apply set_union_intro1; assumption.      
      * apply set_add_intro1; apply set_union_intro2; assumption.
  - apply set_add_elim in H; destruct H.
      * apply set_union_intro1; apply set_add_intro; intuition.  
      * apply set_union_elim in H; destruct H.
        apply set_union_intro1; apply set_add_intro1; assumption.
        apply set_union_intro2; assumption.  
  Qed.

Lemma subset_union_names_add_r : forall (xs ys : names) (y : vname),
    Subset (union xs (names_add y ys)) (names_add y (union xs ys)) /\
    Subset (names_add y (union xs ys)) (union xs (names_add y ys)).
Proof. unfold Subset; intros; split; intros.
  - apply set_union_elim in H. destruct H.
      * apply set_add_intro1; apply set_union_intro1; assumption.
      * apply set_add_intro; apply set_add_elim in H; destruct H; 
        intuition; right. apply set_union_intro2; assumption.
  - apply set_add_elim in H; destruct H.
      * apply set_union_intro2; apply set_add_intro; intuition.  
      * apply set_union_elim in H; destruct H.
        apply set_union_intro1; assumption. 
        apply set_union_intro2; apply set_add_intro1; assumption. 
  Qed.
Lemma subset_diff_diff: forall A B C, Subset A C -> Subset (diff A B) (diff C B).
Proof.
  unfold Subset; intros.
  apply set_diff_intro. apply set_diff_elim1 in H0. apply H in H0. auto.
  apply set_diff_elim2 in H0. auto.
Qed.
Lemma subset_union_names_add_both : forall (xs ys : names) (z : vname),
    Subset (union (names_add z xs) (names_add z ys)) (names_add z (union xs ys)).
Proof. unfold Subset; intros.
  apply set_union_elim in H; destruct H; apply set_add_elim in H;
  apply set_add_intro; intuition; right; 
  (apply set_union_intro1; assumption) || (apply set_union_intro2; assumption). Qed.

Lemma subset_union_elim: forall (xs ys zs: names), 
    Subset (union xs ys) zs -> Subset xs zs /\ Subset ys zs.
Proof. 
  unfold Subset; intros. constructor.
  intros. assert (Elem x (union xs ys)). apply set_union_intro. auto. apply H in H1. auto.
  intros. assert (Elem x (union xs ys)). apply set_union_intro. auto. apply H in H1. auto.
Qed.

Lemma intersect_empty_l : forall (xs : names), intersect empty xs = empty.
Proof. intro xs; apply no_elem_empty; unfold not; intros; 
  apply set_inter_elim in H; intuition. Qed.

Lemma intersect_empty_r : forall (xs : names), intersect xs empty = empty.
Proof. intro xs; apply no_elem_empty; unfold not; intros; 
  apply set_inter_elim in H; intuition. Qed.

Lemma intersect_names_add_intro_l : forall (x : vname) (xs ys : names),
    intersect xs ys = empty -> ~ Elem x ys -> intersect (names_add x xs) ys = empty.
Proof. intros; apply no_elem_empty; unfold not; intros.
  apply set_inter_elim in H1; destruct H1; 
  apply set_add_elim in H1; destruct H1.
  - subst x; contradiction.
  - apply set_inter_intro with vname Nat.eq_dec x0 xs ys in H1;
    ( apply empty_no_elem with (intersect xs ys) x0 in H; contradiction
      || assumption).
  Qed.


  Lemma intersect_union_intro_r : forall (xs ys zs: names),
  intersect xs ys = empty ->  intersect xs zs = empty -> intersect xs (union zs ys) = empty.
Proof. intros; apply no_elem_empty; unfold not; intros.
apply set_inter_elim in H1; destruct H1.
apply set_union_elim in H2; destruct H2.
apply set_inter_intro with vname Nat.eq_dec x xs zs in H1;auto.
apply empty_no_elem with (intersect xs zs) x in H0; contradiction.
apply set_inter_intro with vname Nat.eq_dec x xs ys in H1;auto.
apply empty_no_elem with (intersect xs ys) x in H; contradiction.
Qed.

Lemma intersect_names_add_intro_r : forall (y : vname) (xs ys : names),
    intersect xs ys = empty -> ~ Elem y xs -> intersect xs (names_add y ys) = empty.
Proof. intros; apply no_elem_empty; unfold not; intros.
  apply set_inter_elim in H1; destruct H1; 
  apply set_add_elim in H2; destruct H2.
  - subst x; contradiction.
  - apply set_inter_intro with vname Nat.eq_dec x xs ys in H1;
    ( apply empty_no_elem with (intersect xs ys) x in H; contradiction
      || assumption).
  Qed.

Lemma intersect_names_add_elim_l : forall (x : vname) (xs ys : names),
    intersect (names_add x xs) ys = empty -> intersect xs ys = empty /\ ~ Elem x ys.
Proof. intros; split. 
  - apply no_elem_empty; unfold not; intros; 
    apply set_inter_elim in H0; destruct H0.
    apply empty_no_elem with (intersect (names_add x xs) ys) x0 in H.
    apply set_add_intro1 with vname Nat.eq_dec x0 x xs in H0.
    apply set_inter_intro with vname Nat.eq_dec x0 (names_add x xs) ys in H1;
    intuition.
  - unfold not; intros.
    apply empty_no_elem with (intersect (names_add x xs) ys) x in H.
    assert (x = x) by reflexivity.
    apply set_add_intro2 with vname Nat.eq_dec x x xs in H1. 
    apply set_inter_intro with vname Nat.eq_dec x (names_add x xs) ys in H0;
    intuition.
  Qed.  

Lemma intersect_names_add_elim_r : forall (y : vname) (xs ys : names),
    intersect xs (names_add y ys) = empty -> intersect xs ys = empty /\ ~ Elem y xs.
Proof. intros; split. 
  - apply no_elem_empty; unfold not; intros; 
    apply set_inter_elim in H0; destruct H0.
    apply empty_no_elem with (intersect xs (names_add y ys)) x in H.
    apply set_add_intro1 with vname Nat.eq_dec x y ys in H1.
    apply set_inter_intro with vname Nat.eq_dec x xs (names_add y ys) in H0;
    intuition.
  - unfold not; intros.
    apply empty_no_elem with (intersect xs (names_add y ys)) y in H.
    assert (y = y) by reflexivity.
    apply set_add_intro2 with vname Nat.eq_dec y y ys in H1.
    apply set_inter_intro with vname Nat.eq_dec y xs (names_add y ys) in H0;
    intuition.
  Qed.
Lemma intersect_singleton: forall x xs,  ~Elem x xs -> intersect xs (singleton x) = empty.
Proof. 
  intros. induction xs.
  apply intersect_empty_l.
  simpl. case_eq(Nat.eq_dec a x). intros. simpl in H. unfold not in H. assert (a = x \/ Elem x xs). left;auto. apply H in H1. contradiction. 
  intros. apply IHxs. simpl in H. unfold not in H. unfold not. intros. assert (a = x \/ Elem x xs). right;auto. apply H in H2. contradiction.
Qed.
Lemma subset_in_intersect : forall (xs ys zs : names),
    intersect xs zs = empty -> Subset ys zs -> intersect xs ys = empty.
Proof. intros; apply no_elem_empty; unfold not; intros. 
  apply set_inter_elim in H1; destruct H1; apply H0 in H2.
  assert (Elem x (intersect xs zs)) by (apply set_inter_intro; assumption);
  rewrite H in H3; intuition. Qed.

Lemma subset_union_diff : forall (xs ys zs : names),
    Subset (union (diff xs zs) (diff ys zs)) (diff (union xs ys) zs) /\
    Subset (diff (union xs ys) zs) (union (diff xs zs) (diff ys zs)).  
Proof. unfold Subset; intros; split; intros.
  - apply set_union_elim in H; destruct H; 
    apply set_diff_iff in H; destruct H; apply set_diff_iff; split;
    try ((apply set_union_intro1; apply H) || (apply set_union_intro2; apply H)); intuition. 
  - apply set_diff_iff in H; destruct H;
    apply set_union_elim in H; destruct H;
    apply (set_diff_intro Nat.eq_dec x xs zs) in H 
      || apply (set_diff_intro Nat.eq_dec x ys zs) in H; try assumption;
    (apply set_union_intro1; apply H) || (apply set_union_intro2; apply H).
  Qed.

Lemma intersect_commute: forall (a:set nat) (b:set nat), set_inter Nat.eq_dec a b = empty -> set_inter Nat.eq_dec b a = empty. 
Proof.
  intros.
  apply no_elem_empty. intros.
  apply empty_no_elem with (set_inter Nat.eq_dec a b) x in H.
  unfold not in *. intros.
  apply set_inter_elim in H0. destruct H0.
  assert (Elem x (set_inter Nat.eq_dec a b)). apply set_inter_intro;auto. auto.
Qed.

Lemma add_eq_empty: forall (a:nat) (b:set nat), set_add Nat.eq_dec a b = nil -> False. 
Proof.
  intros. 
  induction b. simpl in H. inversion H.
  simpl in H. case_eq (Nat.eq_dec a a0). intros. rewrite H0 in H. inversion H. intros. rewrite H0 in H. inversion H.
Qed.
  
Lemma union_eq_empty: forall a b, union a b = empty -> a = empty /\ b = empty. 
Proof.
  intros. generalize dependent a. induction b. 
  - intros. simpl in H. rewrite H. constructor;auto.
  - intros.  simpl in H. apply add_eq_empty in H. contradiction. 
Qed.

Lemma union_eq_empty_intro: forall a b,  a = empty /\ b = empty -> union a b = empty . 
Proof.
  intros. destruct H. subst a. subst b.
  simpl. auto. 
Qed.

Lemma subset_empty_intro: forall xs ys, Subset xs ys -> ys = empty -> xs = empty. 
Proof.
  intros. subst ys.
  apply no_elem_empty. intros.
  unfold Subset in H. unfold not. intros.
  apply H in H0. simpl in H0. contradiction. 
Qed.

  (* II. Name-sets of free variables *)

Fixpoint fv (e0:expr) : names := 
    match e0 with
    | (Bc _)          => empty
    | (Ic _)          => empty
    | (BV _)          => empty
    | (FV x)          => singleton x
    | (ExpUnOp op e)     => fv e
    | (ExpBinOp op e1 e2)=> union (fv e1) (fv e2)
    | (ExpMethodInvoc e1 m e2)=> union (fv e1) (fv e2)
    | (ExpFieldAccess e1 f) => fv e1
    | (ExpNew c es) => (fix f (es': [expr]) := match es' with | nil => empty | e::es''=> union (fv e) (f es'') end) es
    | (ExpLet   ex e)    => union (fv ex) (fv e)
    end

with free (t0:type) : names :=
    match t0 with
    | (TRefn b   rs)     => fvP rs
    end

with fvP (ps0:preds) : names :=
    match ps0 with
    | PEmpty       => empty
    | (PCons p ps) => union (fv p) (fvP ps)
    end. 

Fixpoint frees ts: names := 
  match ts with
  | nil => empty
  | t:: ts' => union (free t) (frees ts')
  end.


Fixpoint fvs ts: names := 
  match ts with
  | nil => empty
  | t:: ts' => union (fv t) (fvs ts')
  end.

    (* III. Free variables under substiution etc *)
Lemma forall_fv: forall l j y, 
Forall (fun e : expr => forall (j : index) (y : vname), Subset (fv e) (fv (open_at j y e))) l ->
Subset ((fix f (es': [expr]) := match es' with | nil => empty | e::es''=> union (fv e) (f es'') end) l) 
((fix f (es': [expr]) := match es' with | nil => empty | e::es''=> union (fv e) (f es'') end) ((fix f (es': [expr]) := match es' with | nil => nil | e::es''=> (open_at j y e) :: (f es'') end) l)).
Proof.
  intros.
  induction l.
  apply subset_empty_l.
  inversion H.
  apply subset_union_both.
  apply H2.
  apply IHl.
  apply H3.
Qed.
Lemma fv_open_at_intro : ( forall (e:expr) (j:index) (y:vname) ,
    Subset (fv e) (fv (open_at j y e))  ) /\ ((
  forall (t:type) (j:index) (y:vname) ,
    Subset (free t) (free (openT_at j y t)) ) /\ (
  forall (ps:preds) (j:index) (y:vname) ,
    Subset (fvP ps) (fvP (openP_at j y ps)) )).
Proof. 
  apply ( syntax_mutind'
  ( fun e : expr => forall (j:index) (y:vname) ,
    Subset (fv e) (fv (open_at j y e))  )
  ( fun t : type => forall (j:index) (y:vname) ,
    Subset (free t) (free (openT_at j y t)) )
  ( fun ps : preds => forall (j:index) (y:vname) ,
    Subset (fvP ps) (fvP (openP_at j y ps)) ))

    ;intros;simpl
       ; try (apply subset_empty_l)
       ; try (apply forall_fv;auto)
       ; try (apply subset_refl)
       ; (* one IH *) try ( apply H)
       ; (* two IH *) try ( apply subset_union_both; apply H || apply H0 )
       ; (* 3 IH *) try ( apply subset_union_both; 
                          apply H || apply subset_union_both; trivial). 

  Qed.
  
Lemma fv_unbind_intro : (forall (e:expr) (y:vname) ,
    Subset (fv e) (fv (unbind y e))  ) * ((
  forall (t:type) (y:vname) ,
    Subset (free t) (free (unbindT y t)) ) * (
  forall (ps:preds) (y:vname) ,
    Subset (fvP ps) (fvP (unbindP y ps)) )).
Proof. unfold unbind; unfold unbindT; unfold unbindP; repeat split; 
  intros; apply fv_open_at_intro. Qed. 

Lemma forall_fv2: forall l y j,
Forall (fun e : expr => forall (j : index) (y : vname), Subset (fv (open_at j y e)) (names_add y (fv e))) l -> 
Subset ((fix f (es' : [expr]) : set vname := match es' with
                                        | nil => empty
                                        | e :: es'' => union (fv e) (f es'')
                                        end)
     ((fix f (es' : [expr]) : [expr] := match es' with
                                        | nil => nil
                                        | e :: es'' => open_at j y e :: f es''
                                        end) l))
  (names_add y
     ((fix f (es' : [expr]) : set vname := match es' with
                                           | nil => empty
                                           | e :: es'' => union (fv e) (f es'')
                                           end) l)).
Proof.
  intros.
  induction l.
  apply subset_empty_l.
  assert (Subset
  (union (fv (open_at j y a))
     ((fix f (es' : [expr]) : set vname := match es' with
                                           | nil => empty
                                           | e :: es'' => union (fv e) (f es'')
                                           end)
        ((fix f (es' : [expr]) : [expr] := match es' with
                                           | nil => nil
                                           | e :: es'' => open_at j y e :: f es''
                                           end) l)))
  (union (names_add y (fv a))
     (names_add y
        ((fix f (es' : [expr]) : set vname := match es' with
                                              | nil => empty
                                              | e :: es'' => union (fv e) (f es'')
                                              end) l)))).
  inversion H.
  apply subset_union_both;auto.
  assert (Subset (union (names_add y (fv a))
  (names_add y
     ((fix f (es' : [expr]) : set vname := match es' with
                                           | nil => empty
                                           | e :: es'' => union (fv e) (f es'')
                                           end) l))) ((names_add y )
                                           (union (fv a)
                                              ((fix f (es' : [expr]) : set vname := match es' with
                                                                                    | nil => empty
                                                                                    | e :: es'' => union (fv e) (f es'')
                                                                                    end) l)))).
  apply subset_union_names_add_both.
  eapply subset_trans .
  apply H0.
  apply H1.
Qed.
  
Lemma fv_open_at_elim : ( forall (e:expr) (j:index) (y:vname) ,
    Subset (fv (open_at j y e)) (names_add y (fv e)) ) /\ ((
  forall (t:type) (j:index) (y:vname) ,
    Subset (free (openT_at j y t)) (names_add y (free t))) /\ (
  forall (ps:preds) (j:index) (y:vname) ,
    Subset (fvP (openP_at j y ps)) (names_add y (fvP ps)))).
Proof.
  apply ( syntax_mutind'
  ( fun e : expr => forall (j:index) (y:vname) ,
    Subset (fv (open_at j y e)) (names_add y (fv e)) )
  ( fun t : type => forall (j:index) (y:vname) ,
    Subset (free (openT_at j y t)) (names_add y (free t)))
  ( fun ps : preds => forall (j:index) (y:vname) ,
    Subset (fvP (openP_at j y ps)) (names_add y (fvP ps))));
  simpl; intros
       ; try (apply subset_empty_l)
       ; try (apply forall_fv2)
       ; (* one IH *) try ( apply H )
       ; (* two IH *) try ( apply subset_trans 
              with (union (names_add y (fv e)) (names_add y (fv e0))) ||
              apply subset_trans 
              with (union (names_add y (fv e1)) (names_add y (fv e2))) ||
            apply subset_trans  
              with (union (names_add y (fv e)) (names_add y (free t))) ||
            apply subset_trans 
              with (union (names_add y (free tx)) (names_add y (free t))) ||
            apply subset_trans 
              with (union (names_add y (fv p)) (names_add y (fvP ps)));
          try apply subset_union_both; 
          try apply subset_union_names_add_both; apply H || apply H0).
       - (* BV *) destruct (j =? i); simpl;
          apply subset_empty_l || apply subset_sing_l; simpl; left; reflexivity.
       - (* FV *) destruct (Nat.eq_dec y x); apply subset_sing_l;
          simpl; left; reflexivity.
  Qed. 

Lemma fv_unbind_elim : ( forall (e:expr) (y:vname) ,
    Subset (fv (unbind y e)) (names_add y (fv e)) ) * ((
  forall (t:type) (y:vname) ,
    Subset (free (unbindT y t)) (names_add y (free t))) * (
  forall (ps:preds) (y:vname) ,
    Subset (fvP (unbindP y ps)) (names_add y (fvP ps)))).
Proof. unfold unbind; unfold unbindT; unfold unbindP; repeat split; 
  intros; apply fv_open_at_elim. Qed. 
 
Lemma fv_subFV_elim : ( forall (e:expr) (x:vname) (v:expr),
    Subset (fv (subFV x v e)) (union (diff (fv e) (singleton x)) (fv v))  ) /\ ((
  forall (t:type) (x:vname) (v:expr),
    Subset (free (tsubFV x v t)) (union (diff (free t) (singleton x)) (fv v)) ) /\ (
  forall (ps:preds) (x:vname) (v:expr),
    Subset (fvP (psubFV x v ps)) (union (diff (fvP ps) (singleton x)) (fv v)) )).
Proof. 
  apply ( syntax_mutind'
  ( fun e : expr => forall (x:vname) (v:expr),
    Subset (fv (subFV x v e)) (union (diff (fv e) (singleton x)) (fv v))  )
  ( fun t : type => forall (x:vname) (v:expr),
    Subset (free (tsubFV x v t)) (union (diff (free t) (singleton x)) (fv v)) )
  ( fun ps : preds => forall (x:vname) (v:expr) ,
    Subset (fvP (psubFV x v ps)) (union (diff (fvP ps) (singleton x)) (fv v)) ))
  ; intros; simpl
  ; try (apply subset_empty_l)
  ; (* one IH *) try ( apply H)
  ; (* two IH *) try ( unfold Subset; intros; 
    apply set_union_elim in H1; destruct H1; 
    apply H in H1 || apply H0 in H1;
    apply set_union_elim in H1; destruct H1; apply set_union_intro; 
    intuition; left; 
    apply set_diff_intro; apply set_diff_iff in H1; destruct H1;
    try assumption; apply set_union_intro; intuition ).
  - destruct (x0 =? x) eqn:E; simpl; 
    apply Nat.eqb_eq in E || apply Nat.eqb_neq in E; 
    symmetry in E || apply Nat.neq_sym in E;
    destruct (Nat.eq_dec x x0) eqn:D; try contradiction.
    * apply union_empty_l. 
    * apply subset_sing_l; apply set_union_intro1; simpl; intuition.
  -
    induction l.
    apply subset_empty_l.
    inversion H.
    remember ((fix f (es' : [expr]) : set vname :=
    match es' with
    | nil => empty
    | e :: es'' => union (fv e) (f es'')
    end) l) as fvs. 
    assert (Subset ((union (diff (fvs) (singleton x)) (fv v)))  (union (diff (union (fv a) fvs) (singleton x)) (fv v))).
    apply subset_union_both. apply subset_diff_diff.  apply subset_union_intro_r. apply subset_refl.
    assert (Subset ((union (diff (fv a) (singleton x)) (fv v)))  (union (diff (union (fv a) fvs) (singleton x)) (fv v))).
    apply subset_union_both. apply subset_diff_diff.  apply subset_union_intro_r. apply subset_refl.
    apply subset_trans with (union (union (diff (union (fv a) fvs) (singleton x)) (fv v)) (union (diff (union (fv a) fvs) (singleton x)) (fv v))).
    apply subset_union_both. apply subset_trans with (union (diff (fv a) (singleton x)) (fv v)). apply H2. apply H5. 
    apply subset_trans with (union (diff fvs (singleton x)) (fv v)). apply IHl. apply H3. apply H4.
    apply subset_union_intro_l. apply subset_refl. apply subset_refl. 
  Qed.

Lemma free_tsubFV_bounded : forall (x:vname) (v_x:expr) (t:type) (ys : names),
    Subset (fv v_x) ys -> Subset (free t) (names_add x ys)
        -> Subset (free (tsubFV x v_x t)) ys.
Proof. intros; apply subset_trans with (union (diff (free t) (singleton x)) (fv v_x));
  try apply fv_subFV_elim; apply subset_union_intro_l; try apply H;
  unfold Subset; intros; apply set_diff_iff in H1; destruct H1;
  apply H0 in H1; apply set_add_elim in H1; destruct H1;
  (apply elem_sing in H1; contradiction) || assumption.
  Qed. 

Lemma fv_strengthen_elim : forall (ps qs : preds),
    Subset ( fvP (strengthen ps qs)) (union (fvP ps) (fvP qs)).
Proof. intros; induction ps; simpl.
  - apply subset_union_intro_r; apply subset_refl.
  - apply subset_trans with (union (fv p) (union (fvP ps) (fvP qs))).
    * apply subset_union_both; try apply subset_refl; apply IHps.
    * apply subset_union_assoc.
  Qed.

Lemma fv_strengthen_intro : forall (ps qs : preds),
    Subset (union (fvP ps) (fvP qs)) ( fvP (strengthen ps qs)) .
Proof. intros; induction ps; simpl.
  - apply subset_union_intro_l; try apply subset_empty_l; apply subset_refl.
  - apply subset_trans with (union (fv p) (union (fvP ps) (fvP qs))).
    * apply subset_union_assoc.
    * apply subset_union_both; try apply subset_refl; apply IHps.     
  Qed.

(*-------------------------------------------------------------------------
----- | IV. TYPING ENVIRONMENTS
-------------------------------------------------------------------------*)

Inductive env : Set :=  
    | Empty                         
    | Cons  (x : vname) (t : type) (g : env).
Fixpoint Cons_many ys ts e := 
  match ys, ts with
  | y::ys', t::ts' => Cons y t (Cons_many ys' ts' e) 
  | _, _ => e
  end.
Fixpoint Cons_many_many ys ts e := 
  match ys, ts with
  | y::ys', t::ts' => Cons_many ys ts e::(Cons_many_many ys' ts' e) 
  | _, _ => e::nil
  end.
  
Fixpoint binds (g : env) : names :=
    match g with
    | Empty         => empty
    | (Cons  x t g) => names_add x (binds g)
    end.



Definition in_env (x : vname) (g : env) : Prop := Elem x (binds g).

Fixpoint unique (g0 : env) : Prop :=
    match g0 with
    | Empty         => True
    | (Cons  x t g) => ~ in_env x g /\ unique g
    end.    

Lemma binds_subset : forall (g : env), Subset (binds g) (binds g).
Proof. unfold Subset; induction g; simpl.
  - trivial.
  - apply subset_add_both_intro; assumption.
  Qed.
Lemma in_env_Cons : forall (x y : vname) (t : type) (g : env),
  ~ in_env x (Cons y t g) -> x <> y /\ ~ in_env x g.
Proof. unfold in_env; simpl; intros; split; unfold not.
  - intro. apply set_add_intro2 with _ Nat.eq_dec x y (binds g) in H0; contradiction.
  - intro. apply set_add_intro1 with _ Nat.eq_dec x y (binds g) in H0; contradiction.
  Qed.


Fixpoint bound_in (x : vname) (t : type) (g0 : env) : Prop := 
    match g0 with
    | Empty          => False
    | (Cons  y t' g) => (x = y /\ t = t') \/ bound_in x t g
    end.

Lemma boundin_inenv : forall (x:vname) (t:type) (g:env),
  bound_in x t g -> Elem x (binds g) (*in_env x g *).
Proof. intros. induction g; simpl in H; simpl; try contradiction;
try (apply set_add_intro); try (destruct H); try (apply IHg in H); intuition. 
Qed.

(* 
  --- V. SYSTEM F's TYPING ENVIRONMENTS *)

Inductive fjenv := 
    | FEmpty                      
    | FCons  (x : vname) (t : fjtype) (g : fjenv).

Fixpoint bindsFJ (g : fjenv) : names :=
    match g with
    | FEmpty         => empty
    | (FCons  x t g) => names_add x (bindsFJ g)
    end.


Definition in_envFJ (x : vname) (g : fjenv) : Prop := Elem x (bindsFJ g).

Fixpoint uniqueF (g0 : fjenv) : Prop :=
    match g0 with
    | FEmpty         => True
    | (FCons  x t g) => ~ in_envFJ x g /\ uniqueF g
    end.    

Lemma bindsFJ_subset : forall (g : fjenv), Subset (bindsFJ g) (bindsFJ g).
Proof. unfold Subset; induction g; simpl.
  - trivial.
  - apply subset_add_both_intro; assumption.
  Qed.
  (* - apply subset_add_intro; assumption. Qed. *)
  

Lemma in_envFJ_FCons : forall (x y : vname) (t : fjtype) (g : fjenv),
  ~ in_envFJ x (FCons y t g) -> x <> y /\ ~ in_envFJ x g.
Proof. unfold in_envFJ; simpl; intros; split; unfold not.
  - intro. apply set_add_intro2 with _ Nat.eq_dec x y (bindsFJ g) in H0; contradiction.
  - intro. apply set_add_intro1 with _ Nat.eq_dec x y (bindsFJ g) in H0; contradiction.
  Qed.

Fixpoint bound_inF (x : vname) (t : fjtype) (g0 : fjenv) : Prop := 
    match g0 with
    | FEmpty          => False
    | (FCons  y t' g) => (x = y /\ t = t') \/ bound_inF x t g
    end.

 
Lemma boundin_inenvFJ : forall (x:vname) (t:fjtype) (g:fjenv),
    bound_inF x t g -> Elem x (bindsFJ g) (*in_envFJ x g *).
Proof. intros. induction g; simpl in H; simpl; try contradiction;
  try (apply set_add_intro); try (destruct H); try (apply IHg in H); intuition. 
  Qed.



Fixpoint erase_env (g0 : env) : fjenv :=
    match g0 with
    | Empty         => FEmpty
    | (Cons  x t g) => FCons  x (erase t) (erase_env g)
    end.
Lemma erase_empty: FEmpty = erase_env Empty.
Proof. auto. Qed. 
(*---------------------------------------------------------------------------
----- | VI. NAME SETS and FRESH NAMES
---------------------------------------------------------------------------*)

Definition fresh (xs:names) : vname  :=  1 + List.list_max xs.

Lemma fresh_above_all : forall (x:vname) (xs:names),
    Elem x xs -> x < fresh xs.
Proof. intro x. induction xs as[|y ys IH].
  - simpl; intuition.
  - intro H; simpl in H. 
    destruct H; unfold fresh; simpl; apply Nat.lt_succ_r.
      * subst x.  apply Nat.le_max_l.
      * apply IH in H. unfold fresh in H; simpl in H. 
        apply Nat.le_succ_l in H; apply le_S_n in H.
        transitivity (List.list_max ys); (apply H || apply Nat.le_max_r).
  Qed.

Lemma above_fresh_not_elem : forall (y:vname) (xs : names), 
    fresh xs <= y -> ~ Elem y xs.
Proof. unfold not. intros. apply fresh_above_all in H0. apply Nat.lt_nge in H0.
  contradiction. Qed.

Lemma fresh_not_elem : forall (xs : names), ~ Elem (fresh xs) xs.
Proof. intro xs. apply above_fresh_not_elem; trivial. Qed.
  
Definition fresh_varF (xs : names) (g : fjenv) : vname := 
  max (fresh xs) (fresh (bindsFJ g)).

Lemma above_fresh_varF_not_elem : forall (y:vname) (xs : names) (g : fjenv),
    fresh_varF xs g <= y   ->   ~ Elem    y xs /\ ~ in_envFJ y g.
Proof. split; unfold in_envFJ; apply above_fresh_not_elem; (*unfold fresh_varF in H. *)
  transitivity (fresh_varF xs g); try assumption;        
  apply Nat.le_max_l || apply Nat.le_max_r. Qed.

Lemma fresh_varF_not_elem : forall (xs : names) (g : fjenv),
    ~ Elem (fresh_varF xs g) xs /\ ~ in_envFJ (fresh_varF xs g) g.
Proof. intros. apply above_fresh_varF_not_elem; trivial. Qed. 
  
Definition fresh_var_excludingF (xs:names) (g:fjenv) (y:vname) :=  
    max (fresh_varF xs g) (1+y).

Lemma fresh_var_excludingF_not_elem : forall (xs:names) (g:fjenv) (y:vname),
    ~ (fresh_var_excludingF xs g y) = y        /\
    ~ Elem    (fresh_var_excludingF xs g y) xs /\ 
    ~ in_envFJ (fresh_var_excludingF xs g y) g.
Proof. split; unfold fresh_var_excludingF.
  - unfold not. intro. assert (1 + y <= max (fresh_varF xs g) (1 + y) ).
    apply Nat.le_max_r. rewrite H in H0. apply Nat.lt_nge in H0. intuition.
  - apply above_fresh_varF_not_elem; unfold fresh_varF;
    apply Nat.le_max_l || apply Nat.le_max_r. Qed.

Definition fresh_varFE (xs : names) (g : fjenv) (e : expr) : vname :=
  max (fresh_varF xs g) ((fresh (fv e))).

Lemma above_fresh_varFE_not_elem : forall (y:vname) (xs:names) (g:fjenv) (e:expr),
  fresh_varFE xs g e <= y ->  ~ Elem    y (fv e)  /\
                              ~ Elem    y xs      /\ 
                              ~ in_envFJ y g       .
Proof. 
  split.
  apply above_fresh_not_elem.
  transitivity (fresh_varFE xs g e).
  unfold fresh_varFE; try (apply Nat.le_max_r); assumption. assumption.
  apply above_fresh_varF_not_elem.
  transitivity (fresh_varFE xs g e).
  unfold fresh_varFE; try (apply Nat.le_max_l). assumption.
  Qed.

Lemma fresh_varFE_not_elem : forall (xs:names) (g:fjenv) (e:expr),
    ~ Elem    (fresh_varFE xs g e) (fv e)  /\
    ~ Elem    (fresh_varFE xs g e) xs      /\ 
    ~ in_envFJ (fresh_varFE xs g e) g       .
Proof. intros; apply  above_fresh_varFE_not_elem; trivial. Qed.
  
Definition fresh_var (xs : names) (g : env) : vname := 
  max (fresh xs) (fresh (binds g)).

Lemma above_fresh_var_not_elem : forall (y:vname) (xs : names) (g : env),
    fresh_var xs g <= y   ->   ~ Elem    y xs /\ ~ in_env y g.
Proof. split; unfold in_env; apply above_fresh_not_elem; 
  transitivity (fresh_var xs g); try assumption;        
  apply Nat.le_max_l || apply Nat.le_max_r. Qed.

Lemma fresh_var_not_elem : forall (xs : names) (g : env),
    ~ Elem (fresh_var xs g) xs /\ ~ in_env (fresh_var xs g) g.
Proof. intros. apply above_fresh_var_not_elem; trivial. Qed. 
  
Definition fresh_var_excluding (xs:names) (g:env) (y:vname) :=  
    max (fresh_var xs g) (1+y).

Lemma fresh_var_excluding_not_elem : forall (xs:names) (g:env) (y:vname),
    ~ (fresh_var_excluding xs g y) = y        /\
    ~ Elem    (fresh_var_excluding xs g y) xs /\ 
    ~ in_env  (fresh_var_excluding xs g y) g.
Proof. split; unfold fresh_var_excluding.
  - unfold not. intro. assert (1 + y <= max (fresh_var xs g) (1 + y) ).
    apply Nat.le_max_r. rewrite H in H0. apply Nat.lt_nge in H0. intuition.
  - apply above_fresh_var_not_elem; unfold fresh_var;
    apply Nat.le_max_l || apply Nat.le_max_r. Qed.

Definition fresh_varE (xs : names) (g : env) (e : expr) : vname :=
  max (fresh_var xs g) (fresh (fv e)).

Lemma above_fresh_varE_not_elem : forall (y:vname) (xs:names) (g:env) (e:expr),
  fresh_varE xs g e <= y ->  ~ Elem   y (fv e)  /\
                             ~ Elem   y xs      /\ 
                             ~ in_env y g       .
Proof. split.
  apply above_fresh_not_elem.
  transitivity (fresh_varE xs g e).
  apply Nat.le_max_r.
  apply H.
  split.
  apply above_fresh_not_elem.
  transitivity (fresh_varE xs g e).
  transitivity (fresh_var xs g).
  apply Nat.le_max_l.
  apply Nat.le_max_l.
  apply H.
  apply above_fresh_not_elem.
  transitivity (fresh_varE xs g e).
  transitivity (fresh_var xs g).
  apply Nat.le_max_r.
  apply Nat.le_max_l.
  apply H.
Qed.

Lemma fresh_varE_not_elem : forall (xs:names) (g:env) (e:expr),
    ~ Elem   (fresh_varE xs g e) (fv e)  /\
    ~ Elem   (fresh_varE xs g e) xs      /\ 
    ~ in_env (fresh_varE xs g e) g       .
Proof. intros; apply  above_fresh_varE_not_elem; trivial. Qed. 

Definition fresh_varT (xs : names) (g : env) (t : type) : vname :=
  max (fresh_var xs g) (fresh (free t)).

Lemma above_fresh_varT_not_elem : forall (y:vname) (xs:names) (g:env) (t:type),
  fresh_varT xs g t <= y ->  ~ Elem   y (free   t) /\
                             ~ Elem   y xs      /\ 
                             ~ in_env y g       .
Proof. split; try split; try
  ( apply above_fresh_not_elem; 
    transitivity (fresh_varT xs g t); try (apply Nat.le_max_r); try (apply Nat.le_max_l); assumption );
  try  apply above_fresh_not_elem; 
  try transitivity ((fresh_var xs g)) ; try (apply Nat.le_max_l); try (apply Nat.le_max_r); try assumption;
  try transitivity ((fresh_varT xs g t)) ; try (apply Nat.le_max_l); try (apply Nat.le_max_r); try assumption.
  Qed.

Lemma fresh_varT_not_elem : forall (xs:names) (g:env) (t:type),
    ~ Elem   (fresh_varT xs g t) (free   t) /\
    ~ Elem   (fresh_varT xs g t) xs      /\ 
    ~ in_env (fresh_varT xs g t) g       .
Proof. intros; apply  above_fresh_varT_not_elem; trivial. Qed.


Fixpoint concatE (g g'0 : env) : env :=
    match g'0 with
    | Empty          => g
    | (Cons  x t g') => Cons  x t (concatE g g')
    end.

Fixpoint concatF (g g'0 : fjenv) : fjenv :=
  match g'0 with
  | FEmpty          => g
  | (FCons  x t g') => FCons  x t (concatF g g')
  end.
  
Fixpoint esubFV (x:vname) (v:expr) (g0:env) : env :=
  match g0 with 
  | Empty           => Empty
  | (Cons  z t_z g) => Cons z (tsubFV x v t_z) (esubFV x v g)
  end.
Ltac gather_vars_with F :=
  let rec gather V :=
    match goal with
    | H: ?S |- _ =>
      let FH := constr:(F H) in
      match V with
      | empty => gather FH
      | context [FH] => fail 1
      | _ => gather (union FH V)
      end
    | _ => V
    end in
  let L := gather (empty) in eval simpl in L.

Ltac gather_vars :=
  let A := gather_vars_with (fun x : names => x) in
  let B := gather_vars_with (fun x : vname => singleton x) in
  let C := gather_vars_with (fun x : env => binds x) in
  let D := gather_vars_with (fun x : fjenv => bindsFJ x) in
  let E := gather_vars_with (fun x : type => free x) in
  let F := gather_vars_with (fun x : expr => fv x) in

  constr: (union (union (union (union (union A B) C) D) E) F).

(* * The tactic [pick_fresh] pick a fresh variable in the context *)
Tactic Notation "pick_fresh" ident(x) :=
  let l := gather_vars in remember l as x.

Arguments not_elem_union_elim1 [x E F].
Arguments not_elem_union_elim2 [x E F].
  
Ltac notin_solve_target_from x E H :=
 
  match type of H with 
  | ~ Elem x E => constr:(H)
  | ~ Elem x (union ?F ?G) =>  
      let H' :=

        match F with 
        | context [E] => 
        constr:(not_elem_union_elim1 H)
        (* let a := match F with _ => idtac F end in constr:(not_elem_union_elim1 H) *)
        | _ => match G with 
          | context [E] => constr:(not_elem_union_elim2 H)
          | _ => fail 20
          end
        end in
      notin_solve_target_from x E H' 
  end.

Ltac notin_solve_target x E :=
  match goal with 
  | H: ~ Elem x ?L |- _ =>
    match L with context[E] =>
      let F := notin_solve_target_from x E H in
      apply F 
    end
  (* | H: x <> ?y |- _ => 
      match E with \{y} => 
        apply (notin_singleton_l H)
      end *)
  end.

Ltac notin_solve_one :=
  match goal with
  | |- ~ Elem ?x ?E => 
    notin_solve_target x E
  end.







