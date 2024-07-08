Require Import Referable.
Require Import List.
Require Import Crush.
Require Import Lists.ListSet.
Require Import Lists.
Require Import ZArith.
Require Import RFJ.Tactics.
Require Import Coq.Program.Equality.
Require Import Lia.

Require Import Definitions.Syntax. 
Require Import Definitions.Names.
Require Import Definitions.Semantics.
Require Import Definitions.FJTyping.

Require Import Definitions.Typing.
Require Import Definitions.CTSanity.
Require Import Definitions.Semantics.
Require Import Definitions.SubDenotation.


Require Import Lemmas.TypingLemmas.Preservation_Progress.


Theorem type_soundness : forall (e e':expr) (t:type),
    EvalsTo e e' -> Hastype Empty e t -> isValue e' \/  exists e'', Step e' e''.
Proof. intros e e' t ev_e_e'; induction ev_e_e'.
  - (* Refl *) intro p_e_t; apply progress with t; apply p_e_t.
  - (* AddStep *) intro p_e1_t; apply IHev_e_e'; 
    apply preservation with e1; trivial. Qed.
