Require Import Coq.Unicode.Utf8 Arith Bool Ring Setoid String.
Require Import Coq.Lists.ListSet.
Require Import Coq.Sets.Powerset.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Lists.List.
Require Import Classical_Prop.
Require Import Classical_Pred_Type.
Require Import Coq.Numbers.BinNums.
(* Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ClassicalFacts. *)
Import ListNotations.




Ltac inv H := inversion H; subst; clear H.
Ltac unf :=
  repeat match goal with
    | [ H : exists _, _ |- _ ] => inv H
    | [ H : _ /\ _ |- _ ] => inv H
    | [ H : _ <-> _ |- _ ] => inv H
  end.

Ltac cla H := assert (H \/ ~H); try (destruct (classic H); auto; fail).
Ltac clac H := destruct (classic H).

Ltac ctor := econstructor.
Ltac introc H := intro H; clear H.
Ltac eex := repeat (eexists; eauto).