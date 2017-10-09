Load svl.

Inductive Set_GFormula :=
| GFormPrecise : Set_Formula -> Set_GFormula
| GFormImprecise : forall phi, Satisfiable phi -> Set_GFormula.
Inductive Set_GContract :=
| GContract : Set_GFormula -> Set_GFormula -> Set_GContract.
Inductive Set_GMethod :=
| GMethod : Set_Type -> Set_MethodName -> Set_Type -> Set_Ident -> Set_GContract -> Set_Stmt -> Set_GMethod.
Inductive Set_GProgram :=
| GProgram : (list Set_GMethod) -> Set_Stmt -> Set_GProgram.

Inductive Static : Set_GFormula -> Set_Formula -> Prop :=
| StaticPrecise : forall phi, Static (GFormPrecise phi) phi
| StaticImprecise : forall phi sat, Static (GFormImprecise phi sat) phi
.

Lemma FormTrueSat : Satisfiable FormTrue. Proof. exists VarEnvFresh. ctor. Qed.
Definition Unknown := GFormImprecise FormTrue FormTrueSat.

(* conversion *)
Inductive ConvertFormula : Set_Formula -> Set_GFormula -> Prop :=
| ConvFormula : forall phi, ConvertFormula phi (GFormPrecise phi)
.
Inductive ConvertContract : Set_Contract -> Set_GContract -> Prop :=
| ConvContract : forall phi1 phi2 gphi1 gphi2,
  ConvertFormula phi1 gphi1 ->
  ConvertFormula phi2 gphi2 ->
  ConvertContract (Contract phi1 phi2) (GContract gphi1 gphi2)
.
Inductive ConvertMethod : Set_Method -> Set_GMethod -> Prop :=
| ConvMethod : forall c gc T1 m T2 i r,
  ConvertContract c gc ->
  ConvertMethod (Method T1 m T2 i c r) (GMethod T1 m T2 i gc r)
.
Inductive LiftList  { T U : Type } (P : T -> U -> Prop) : list T -> list U -> Prop :=
| LiftListEmpty : @LiftList T U P [] []
| LiftListCons : forall x1 x2 l1 l2, P x1 x2 -> @LiftList T U P l1 l2 -> @LiftList T U P (x1 :: l1) (x2 :: l2)
.

Inductive ConvertProgram : Set_Program -> Set_GProgram -> Prop :=
| ConvProgram : forall m1 m2 s,
  LiftList ConvertMethod m1 m2 ->
  ConvertProgram (Program m1 s) (GProgram m2 s)
.


(* interpretation *)
Definition Set_PFormula := Set_Formula -> Prop. (* power set *)
Definition PFormSubset (pphi1 pphi2 : Set_PFormula) := forall phi, pphi1 phi -> pphi2 phi.
Definition PFormEqual (pphi1 pphi2 : Set_PFormula) := PFormSubset pphi1 pphi2 /\ PFormSubset pphi2 pphi1.
Lemma PFormSubsetRefl : forall p, PFormSubset p p.
Proof.
  intro. intro. auto.
Qed.
Lemma PFormEqualRefl : forall p, PFormEqual p p.
Proof.
  intro. split; apply PFormSubsetRefl.
Qed.
Definition MakePFormSingleton (phi : Set_Formula) : Set_PFormula := fun phi' => phi' = phi.
Definition PFormSingleton phi pphi : Prop := PFormEqual pphi (MakePFormSingleton phi).
Definition MakePFormIdeal (phi : Set_Formula) : Set_PFormula := fun phi' => Implies phi' phi /\ Satisfiable phi'.
Definition PFormIdeal phi pphi : Prop := PFormEqual pphi (MakePFormIdeal phi).
Definition PFormNonEmpty (pphi : Set_PFormula) : Prop := exists phi, pphi phi.


Inductive Gamma : Set_GFormula -> Set_PFormula -> Prop :=
| GammaPrecise : forall phi (pphi : Set_PFormula),
  PFormSingleton phi pphi ->
  Gamma (GFormPrecise phi) pphi
| GammaImprecise : forall phi sat (pphi : Set_PFormula),
  PFormIdeal phi pphi ->
  Gamma (GFormImprecise phi sat) pphi
.

Hint Unfold PFormSubset.
Hint Unfold PFormEqual.
Hint Unfold PFormSingleton.
Hint Unfold PFormIdeal.
Hint Unfold MakePFormSingleton.
Hint Unfold MakePFormIdeal.
Hint Resolve PFormSubsetRefl.
Hint Resolve PFormEqualRefl.
Hint Resolve ImpliesRefl.
Hint Constructors Gamma.
Hint Constructors Static.

Lemma GammaImpliesStatic : forall gphi pphi phi, Static gphi phi -> Gamma gphi pphi -> forall phi', pphi phi' -> Implies phi' phi.
Proof.
  intro. intro. intro. intro st. intro ga. intro. intro pp.
  inv ga; inv st.
  - inv H. apply H0 in pp. inv pp. auto.
  - inv H. apply H0 in pp. apply pp.
Qed.

Lemma GammaContainsStatic : forall gphi pphi phi, Static gphi phi -> Gamma gphi pphi -> pphi phi.
Proof.
  intro. intro. intro. intro st. intro ga.
  inv ga; inv st.
  - inv H. apply H1. ctor.
  - inv H. apply H1. auto.
Qed.

Definition MorePreciseThan (gphi1 gphi2 : Set_GFormula) := exists pphi1 pphi2, Gamma gphi1 pphi1 /\ Gamma gphi2 pphi2 /\ PFormSubset pphi1 pphi2.
Definition MaxMorePreciseThan : (Set_GFormula -> Prop) -> (Set_GFormula -> Prop) := fun pred gphi =>
  pred gphi /\ (∀ gphi', pred gphi' -> MorePreciseThan gphi' gphi).
Definition MinMorePreciseThan : (Set_GFormula -> Prop) -> (Set_GFormula -> Prop) := fun pred gphi =>
  pred gphi /\ (∀ gphi', pred gphi' -> MorePreciseThan gphi gphi').
Definition GFormEqual (gphi1 gphi2 : Set_GFormula) := MorePreciseThan gphi1 gphi2 /\ MorePreciseThan gphi2 gphi1.

Definition GContractMorePreciseThan (gc1 gc2 : Set_GContract) := exists a1 a2 b1 b2, gc1 = GContract a1 b1 /\ gc2 = GContract a2 b2 /\ MorePreciseThan a1 a2 /\ MorePreciseThan b1 b2.
Definition GMethodMorePreciseThan (gm1 gm2 : Set_GMethod) := exists T1 m T2 i c1 c2 s, gm1 = GMethod T1 m T2 i c1 s /\ gm2 = GMethod T1 m T2 i c2 s /\ GContractMorePreciseThan c1 c2.
Definition GProgramMorePreciseThan (gp1 gp2 : Set_GProgram) := exists m1 m2 s, gp1 = GProgram m1 s /\ gp2 = GProgram m2 s /\ LiftList GMethodMorePreciseThan m1 m2.

Definition Alpha (pphi : Set_PFormula) (gphi : Set_GFormula) :=
  MinMorePreciseThan (fun gphi => exists pphi', Gamma gphi pphi' /\ PFormSubset pphi pphi') gphi.

Lemma PartialGC1 : forall pphi gphi, Alpha pphi gphi -> exists pphi', Gamma gphi pphi' /\ PFormSubset pphi pphi'.
Proof.
  intros.
  inv H. inv H0.
  eex.
Qed.

Lemma PartialGC2 : forall pphi gphi, Alpha pphi gphi -> forall gphi' pphi', Gamma gphi' pphi' -> PFormSubset pphi pphi' -> MorePreciseThan gphi gphi'.
Proof.
  intros.
  inv H. inv H2.
  apply H3. clear H3.
  eex.
Qed.

Definition PartialGC3 (F : Set_PFormula -> Set_PFormula -> Prop) := forall gphi pphi, Gamma gphi pphi -> forall pphi', F pphi pphi' -> exists gphi', Alpha pphi' gphi'.
Definition WeakPartialGC3 (F : Set_PFormula -> Set_PFormula -> Prop) := forall gphi pphi, Gamma gphi pphi -> forall pphi', F pphi pphi' -> PFormNonEmpty pphi' -> exists gphi', Alpha pphi' gphi'.


(* lifting *)

Definition MakeLiftPredicate1 (P : Set_Formula -> Prop) (gphi1 : Set_GFormula) :=
  exists phi1 pphi1, Gamma gphi1 pphi1 /\ pphi1 phi1 /\ P phi1.
Definition MakeLiftPredicate2 (P : Set_Formula -> Set_Formula -> Prop) (gphi1 gphi2 : Set_GFormula) :=
  exists phi1 pphi1 phi2 pphi2, Gamma gphi1 pphi1 /\ Gamma gphi2 pphi2 /\ pphi1 phi1 /\ pphi2 phi2 /\ P phi1 phi2.

Definition LiftPredicate1 (P : Set_Formula -> Prop) (gP : Set_GFormula -> Prop) :=
  forall gphi1, MakeLiftPredicate1 P gphi1 <-> gP gphi1.
Definition LiftPredicate2 (P : Set_Formula -> Set_Formula -> Prop) (gP : Set_GFormula -> Set_GFormula -> Prop) :=
  forall gphi1 gphi2, MakeLiftPredicate2 P gphi1 gphi2 <-> gP gphi1 gphi2.
Definition LiftPredicateApprox1 (P : Set_Formula -> Prop) (gP : Set_GFormula -> Prop) :=
  forall gphi1, MakeLiftPredicate1 P gphi1 -> gP gphi1.
Definition LiftPredicateApprox2 (P : Set_Formula -> Set_Formula -> Prop) (gP : Set_GFormula -> Set_GFormula -> Prop) :=
  forall gphi1 gphi2, MakeLiftPredicate2 P gphi1 gphi2 -> gP gphi1 gphi2.

Hint Unfold MakeLiftPredicate1.
Hint Unfold MakeLiftPredicate2.
Hint Unfold LiftPredicate1.
Hint Unfold LiftPredicate2.
Hint Unfold LiftPredicateApprox1.
Hint Unfold LiftPredicateApprox2.

Definition EvalGFormula rho gphi := exists phi, Static gphi phi /\ EvalFormula rho phi.

Lemma LiftingEvalGFormula : forall rho, LiftPredicate1 (EvalFormula rho) (EvalGFormula rho).
Proof.
  intro. intro.
  unfold EvalGFormula.
  split; intro hyp.
  - inv hyp. unf.
    inv H.
    * eex. inv H1. apply H in H0. inv H0. assumption.
    * exists phi. split; auto.
      inv H1. apply H in H0; eauto. inv H0. auto.
  - unf.
    inv H0.
    * eex.
    * eex.
Qed.

Lemma ImpliesSatisfiable : forall phi1 phi2, Implies phi1 phi2 -> Satisfiable phi1 -> Satisfiable phi2.
Proof.
  intro. intro. intro im. intro sa.
  inv sa.
  eex.
Qed.

Inductive GImplies : Set_GFormula -> Set_GFormula -> Prop :=
| GImpliesPrecise : forall phi1 gphi2 phi2,
  Static gphi2 phi2 ->
  Implies phi1 phi2 ->
  GImplies (GFormPrecise phi1) gphi2
| GImpliesImprecise : forall phi phi1 gphi2 phi2 (sat : Satisfiable phi1),
  Satisfiable phi ->
  Implies phi phi1 ->
  Static gphi2 phi2 ->
  Implies phi phi2 ->
  GImplies (GFormImprecise phi1 sat) gphi2
.

Hint Constructors GImplies.

Lemma LiftingGImplies : LiftPredicate2 Implies GImplies.
Proof.
  intro. intro.
  split; intro hyp.
  - inv hyp. unf.
    inv H.
    * apply H3 in H1. inv H1.
      inv H0.
      + apply H in H2. inv H2. ctor; eauto.
      + inv H. apply H0 in H2. inv H2. ctor; auto. eapply ImpliesTrans; eauto.
    * inv H3. apply H in H1. inv H1.
      inv H0.
      + apply H1 in H2. inv H2.
        eauto.
      + apply H1 in H2. inv H2. ctor.
        --apply H6.
        --assumption.
        --ctor.
        --eapply ImpliesTrans. eapply H4. assumption.
  - inv hyp.
    * inv H; eex.
    * inv H1; eex.
Qed.

(* lifting functions *)

Definition MakePLiftFunction1 (F : Set_Formula -> Set_Formula -> Prop) (pphi1 pphi' : Set_PFormula) : Prop :=
  forall phi', (exists phi1, F phi1 phi' /\ pphi1 phi1) <-> pphi' phi'.
Definition MakePLiftFunction2 (F : Set_Formula -> Set_Formula -> Set_Formula -> Prop) (pphi1 pphi2 pphi' : Set_PFormula) : Prop :=
  forall phi', (exists phi1 phi2, F phi1 phi2 phi' /\ pphi1 phi1 /\ pphi2 phi2) <-> pphi' phi'.
Definition PLiftFunction1 (F : Set_Formula -> Set_Formula -> Prop) (pF : Set_PFormula -> Set_PFormula -> Prop) :=
  forall pphi1 pphi', pF pphi1 pphi' <-> MakePLiftFunction1 F pphi1 pphi'.
Definition PLiftFunction2 (F : Set_Formula -> Set_Formula -> Set_Formula -> Prop) (pF : Set_PFormula -> Set_PFormula -> Set_PFormula -> Prop) :=
  forall pphi1 pphi2 pphi', pF pphi1 pphi2 pphi' <-> MakePLiftFunction2 F pphi1 pphi2 pphi'.

Definition MakeLiftFunction1 (F : Set_Formula -> Set_Formula -> Prop) (gphi1 gphi' : Set_GFormula) : Prop :=
  exists pF, PLiftFunction1 F pF /\
  exists pphi1, Gamma gphi1 pphi1 /\
  exists pphi', pF pphi1 pphi' /\ Alpha pphi' gphi'.
Definition MakeGPLiftFunction1 (gF : Set_GFormula -> Set_GFormula -> Prop) (pphi1 pphi' : Set_PFormula) : Prop :=
  exists gp1, Alpha pphi1 gp1 /\
  exists gp', gF gp1 gp' /\ Gamma gp' pphi'.
Definition MakeLiftFunction2 (F : Set_Formula -> Set_Formula -> Set_Formula -> Prop) (gphi1 gphi2 gphi' : Set_GFormula) : Prop :=
  exists pF, PLiftFunction2 F pF /\
  exists pphi1, Gamma gphi1 pphi1 /\
  exists pphi2, Gamma gphi2 pphi2 /\
  exists pphi', pF pphi1 pphi2 pphi' /\ Alpha pphi' gphi'.
Definition LiftFunction1 (F : Set_Formula -> Set_Formula -> Prop) (gF : Set_GFormula -> Set_GFormula -> Prop) :=
  forall gphi1 gphi', gF gphi1 gphi' <-> MakeLiftFunction1 F gphi1 gphi'.
Definition LiftFunction2 (F : Set_Formula -> Set_Formula -> Set_Formula -> Prop) (gF : Set_GFormula -> Set_GFormula -> Set_GFormula -> Prop) :=
  forall gphi1 gphi2 gphi', gF gphi1 gphi2 gphi' <-> MakeLiftFunction2 F gphi1 gphi2 gphi'.

Definition LiftFunctionApprox1 (F : Set_Formula -> Set_Formula -> Prop) (gF : Set_GFormula -> Set_GFormula -> Prop) :=
  forall gphi1 gphi', MakeLiftFunction1 F gphi1 gphi' -> exists gphi'', gF gphi1 gphi'' /\ MorePreciseThan gphi' gphi''.
Definition LiftFunctionApprox2 (F : Set_Formula -> Set_Formula -> Set_Formula -> Prop) (gF : Set_GFormula -> Set_GFormula -> Set_GFormula -> Prop) :=
  forall gphi1 gphi2 gphi', MakeLiftFunction2 F gphi1 gphi2 gphi' -> exists gphi'', gF gphi1 gphi2 gphi'' /\ MorePreciseThan gphi' gphi''.

Hint Unfold MakePLiftFunction1.
Hint Unfold MakePLiftFunction2.
Hint Unfold PLiftFunction1.
Hint Unfold PLiftFunction2.
Hint Unfold MakeLiftFunction1.
Hint Unfold MakeLiftFunction2.
Hint Unfold LiftFunction1.
Hint Unfold LiftFunction2.
Hint Unfold LiftFunctionApprox1.
Hint Unfold LiftFunctionApprox2.

Inductive GFormAndSat : Set_GFormula -> Set_GFormula -> Set_GFormula -> Prop :=
| GFormAndSatPrecise : forall phi1 phi2,
  Satisfiable (FormAnd phi1 phi2) ->
  GFormAndSat (GFormPrecise phi1) (GFormPrecise phi2) (GFormPrecise (FormAnd phi1 phi2))
| GFormAndSatImprecise : forall gphi1 gphi2 phi1 phi2 sat gphi,
  Static gphi1 phi1 ->
  Static gphi2 phi2 ->
  ((~ exists phi, gphi1 = GFormPrecise phi) \/ (~ exists phi, gphi2 = GFormPrecise phi)) ->
  GFormEqual gphi (GFormImprecise (FormAnd phi1 phi2) sat) ->
  GFormAndSat gphi1 gphi2 gphi
.

Hint Constructors EvalFormula.

Lemma ImpliesAnd : forall p1 p2 p1' p2', Implies p1 p1' -> Implies p2 p2' -> Implies (FormAnd p1 p2) (FormAnd p1' p2').
Proof.
  intro. intro. intro. intro. intro im1. intro im2. intro. intro ef. inv ef. auto.
Qed.

Lemma PFormSubsetTrans : forall pp1 pp2 pp3, PFormSubset pp1 pp2 -> PFormSubset pp2 pp3 -> PFormSubset pp1 pp3.
Proof.
  auto.
Qed.

Hint Resolve ImpliesAnd.
Hint Resolve PFormSubsetTrans.

Lemma PFormSingletonDet : forall phi pphi1 pphi2, PFormSingleton phi pphi1 -> PFormSingleton phi pphi2 -> PFormEqual pphi1 pphi2.
Proof.
  intro. intro. intro. intro ga1. intro ga2.
  inv ga1. inv ga2.
  split; eapply PFormSubsetTrans; eauto.
Qed.

Lemma PFormIdealDet : forall phi pphi1 pphi2, PFormIdeal phi pphi1 -> PFormIdeal phi pphi2 -> PFormEqual pphi1 pphi2.
Proof.
  intro. intro. intro. intro ga1. intro ga2.
  inv ga1. inv ga2.
  split; eapply PFormSubsetTrans; eauto.
Qed.

Lemma GammaDet : forall gphi pphi1 pphi2, Gamma gphi pphi1 -> Gamma gphi pphi2 -> PFormEqual pphi1 pphi2.
Proof.
  intro. intro. intro. intro ga1. intro ga2.
  inv ga1; inv ga2.
  - eapply PFormSingletonDet; eauto.
  - eapply PFormIdealDet; eauto.
Qed.

Lemma GammaTotal : forall gp, exists pp, Gamma gp pp.
Proof.
  intros.
  destruct gp; eex.
Qed.

Hint Unfold GFormEqual.



Lemma MorePreciseThanRefl : forall gp, MorePreciseThan gp gp.
Proof.
  intro. reduce.
  assert (g := GammaTotal gp). unf.
  eex.
Qed.

Lemma GFormEqualRefl : forall gp, GFormEqual gp gp.
Proof.
  intro. split; apply MorePreciseThanRefl.
Qed.

Hint Resolve MorePreciseThanRefl.
Hint Resolve GFormEqualRefl.

Lemma GFormEqualSymm : forall gphi1 gphi2, GFormEqual gphi1 gphi2 -> GFormEqual gphi2 gphi1.
Proof.
  intro. intro. intro eq. inv eq. auto.
Qed.



Lemma FormEqualRefl : forall p, FormEqual p p.
Proof. intros. split; auto. Qed.

Hint Resolve FormEqualRefl.

Definition GSatisfiable (gp : Set_GFormula) := exists p, Static gp p /\ Satisfiable p.
Definition GSatisfiableAlt (gp : Set_GFormula) := exists pp p, Gamma gp pp /\ pp p /\ Satisfiable p.
Lemma GSatisfiableAltEq : forall gp, GSatisfiable gp <-> GSatisfiableAlt gp.
Proof.
  intro. split; intro sat; inv sat; unf.
  - assert (tot := GammaTotal gp). unf.
    exists x0. exists x.
    split; auto. split; auto.
    inv H; inv H0.
    * apply H2. auto.
    * apply H2. auto.
  - inv H; apply H1 in H0.
    * inv H0. eex.
    * eex.
Qed.

Lemma StaticTotal : forall gp, exists p, Static gp p.
Proof.
  intro.
  destruct gp; eex.
Qed.

Lemma GFormEqualSameGamma : forall gphi1 gphi2, GFormEqual gphi1 gphi2 -> forall pphi, Gamma gphi1 pphi -> Gamma gphi2 pphi.
Proof.
  intro. intro. intro eq. intro. intro ga.
  inv eq. inv H. inv H0. unf.
  eapply GammaDet in H; eauto.
  eapply GammaDet in H1; eauto.
  eapply GammaDet in ga; eauto.
  inv ga. inv H1. inv H.
  assert (PFormEqual x0 pphi) as eq. split.
    eapply PFormSubsetTrans; eauto.
    eapply PFormSubsetTrans; eauto.
  inv H2.
  - ctor. inv H. ctor.
    * eapply PFormSubsetTrans; eauto.
    * eapply PFormSubsetTrans; eauto.
  - ctor. inv H. ctor.
    * eapply PFormSubsetTrans; eauto.
    * eapply PFormSubsetTrans; eauto.
Qed.

Lemma AlphaNotEmpty : forall pphi gphi, Alpha pphi gphi -> exists phi, pphi phi.
Proof.
  intro. intro. intro al.
  inv al. unf.
  apply NNPP. intro c.
  assert (C1 := H0 (GFormPrecise FormTrue)).
  assert (C2 := H0 (GFormPrecise (FormAnd FormTrue FormTrue))).
  lapply C1. Focus 2. eex. intro. intro cc. contradict c. eex. intro c1.
  lapply C2. Focus 2. eex. intro. intro cc. contradict c. eex. intro c2.
  inv c1. inv c2. unf.
  eapply GammaDet in H1; eauto. inv H1.
  inv H3. inv H10. inv H4. inv H11.
  assert (exists phi, Static gphi phi). inv H; eex. unf. rename x4 into phi.
  assert (phi = FormTrue) as c1.
    eapply (PFormSubsetTrans x0) in H1; eauto. eapply (PFormSubsetTrans x1) in H1; eauto.
    inv H12; inv H5.
      inv H12. eapply (PFormSubsetTrans (MakePFormSingleton phi)) in H1; eauto. specialize (H1 phi). lapply H1; auto.
      inv H12. eapply (PFormSubsetTrans (MakePFormIdeal phi)) in H1; eauto. specialize (H1 phi). lapply H1; auto.
  assert (phi = (FormAnd FormTrue FormTrue)) as c2.
    eapply (PFormSubsetTrans x1) in H4; eauto.
    inv H12; inv H5.
      inv H12. eapply (PFormSubsetTrans (MakePFormSingleton FormTrue)) in H4; eauto. specialize (H4 FormTrue). lapply H4; auto.
      inv H12. eapply (PFormSubsetTrans (MakePFormIdeal FormTrue)) in H4; eauto. specialize (H4 FormTrue). lapply H4; auto.
  congruence.
Qed.

Lemma GImpliesRefl : forall gp, GImplies gp gp.
Proof.
  intro. apply LiftingGImplies.
  reduce.
  assert (tot := GammaTotal gp). unf.
  assert (sta := StaticTotal gp). unf.
  eapply GammaContainsStatic in H0; eauto.
  eex.
Qed.

Lemma StaticDet : forall gp p1 p2, Static gp p1 -> Static gp p2 -> p1 = p2.
Proof.
  intro. intro. intro. intro st1. intro st2.
  inv st1; inv st2; auto.
Qed.

Definition MoreImpliesThan (gphi1 gphi2 : Set_GFormula) := forall gp, GImplies gp gphi1 -> GImplies gp gphi2.
Definition MoreImpliesThanAlt (gphi1 gphi2 : Set_GFormula) := forall p1 p2, Static gphi1 p1 -> Static gphi2 p2 -> Implies p1 p2.
Definition MoreImpliesThanAlt2 (gphi1 gphi2 : Set_GFormula) := forall pp1 pp2, Gamma gphi1 pp1 -> Gamma gphi2 pp2 -> forall p1, pp1 p1 -> exists p2, pp2 p2 /\ Implies p1 p2.
Definition IsPrecise gp := exists p, gp = GFormPrecise p.

Definition EqualPrecise gp1 gp2 := exists p1 p2, gp1 = GFormPrecise p1 /\ gp2 = GFormPrecise p2 /\ FormEqual p1 p2.
Definition XMorePreciseThan gp1 gp2 := MorePreciseThan gp1 gp2 \/ EqualPrecise gp1 gp2 \/ (~ GSatisfiable gp1 /\ ~ IsPrecise gp2).

Lemma MoreImpliesThanAltEq : forall gp1 gp2, MoreImpliesThan gp1 gp2 <-> MoreImpliesThanAlt gp1 gp2.
Proof.
  intro. intro. split; intro hyp.
  - intro. intro. intro st1. intro st2.
    inv st1.
    * specialize (hyp (GFormPrecise p1) (GImpliesRefl _)).
      inv hyp.
      eapply StaticDet in st2; eauto. subst.
      assumption.
    * lapply (hyp (GFormPrecise p1)).
      + intro c. inv c.
        eapply StaticDet in st2; eauto. subst.
        assumption.
      + ctor; eauto.
  - intro. intro gi.
    assert (tot := StaticTotal gp1). unf.
    assert (tot := StaticTotal gp2). unf.
    specialize (hyp x x0 H H0).
    inv gi.
    * eapply StaticDet in H; eauto. subst.
      ctor; eauto. eapply ImpliesTrans; eauto.
    * eapply StaticDet in H; eauto. subst.
      ctor; eauto. eapply ImpliesTrans; eauto.
Qed.

Lemma MoreImpliesThanAlt2Eq : forall gp1 gp2, MoreImpliesThan gp1 gp2 <-> MoreImpliesThanAlt2 gp1 gp2.
Proof.
  intro. intro. split; intro hyp.
  - intro. intro. intro g1. intro g2. intro. intro px1.
    inv g1.
    * specialize (hyp (GFormPrecise phi) (GImpliesRefl _)).
      inv hyp.
      apply H in px1. inv px1.
      eex. eapply GammaContainsStatic; eauto.
    * apply H in px1. inv px1.
      assert (tot := StaticTotal gp2). unf.
      exists x.
      split. eapply GammaContainsStatic; eauto.
      lapply (hyp (GFormPrecise phi)).
      + intro c. inv c.
        eapply StaticDet in H2; eauto. subst.
        eapply ImpliesTrans; eauto.
      + ctor; eauto.
  - intro. intro gi.
    apply LiftingGImplies in gi.
    apply LiftingGImplies.
    inv gi. unf.
    assert (tot := GammaTotal gp2). unf.
    specialize (hyp x2 x3 H0 H3 x1 H2). unf.
    exists x. exists x0. exists x4. exists x3.
    split; auto.
    split; auto.
    split; auto.
    split; auto.
    eapply ImpliesTrans; eauto.
Qed.

Lemma MorePreciseMoreImplies : forall gp1 gp2, MorePreciseThan gp1 gp2 -> MoreImpliesThan gp1 gp2.
Proof.
  intro. intro. intro mpt.
  intro. intro imp.
  apply LiftingGImplies.
  apply LiftingGImplies in imp.
  unfold MakeLiftPredicate2 in *. unf.
  unfold MorePreciseThan in *. unf.
  eapply GammaDet in H0; eauto.
  exists x. exists x0. exists x1. exists x4.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  apply H7. apply H0. assumption.
Qed.

Lemma MorePreciseXMorePrecise : forall gp1 gp2, MorePreciseThan gp1 gp2 -> XMorePreciseThan gp1 gp2.
Proof.
  intro. intro. intro mpt.
  ctor.
  apply mpt.
Qed.

Lemma XMorePreciseMoreImplies : forall gp1 gp2, XMorePreciseThan gp1 gp2 -> MoreImpliesThan gp1 gp2.
Proof.
  intro. intro. intro mpt.
  inv mpt. apply MorePreciseMoreImplies. assumption.
  inv H.
  - inv H0. unf.
    apply MoreImpliesThanAltEq.
    reduce.
    inv H. inv H1.
    apply H0.
    assumption.
  - unf.
    apply MoreImpliesThanAltEq.
    reduce.
    contradict H.
    eex.
Qed.

Lemma MoreImpliesMorePreciseImprecise : forall gp1 p2 sat, GSatisfiable gp1 -> MoreImpliesThan gp1 (GFormImprecise p2 sat) -> MorePreciseThan gp1 (GFormImprecise p2 sat).
Proof.
  intro. intro. intro. intro satx. intro mpt.
  assert (tot := StaticTotal gp1). unf.
  apply MoreImpliesThanAltEq in mpt. reduce in mpt.
  specialize (mpt x p2 H).
  apply GSatisfiableAltEq in satx.
  inv satx. unf.
  exists x0. eexists.
  split. auto.
  split. eauto.
  intro. intro xx.
  lapply mpt; auto. intro c.
  split.
  - intro. intro ef. apply c.
    inv H0; inv H.
    * apply H2 in xx. inv xx.
      assumption.
    * apply H2 in xx. apply xx.
      assumption.
  - inv H0.
    * apply H2 in H1. inv H1.
      apply H2 in xx. inv xx.
      assumption.
    * apply H2 in xx. apply xx.
Qed.

(* about the "Satisfiable p": Without that, any (? /\ x) ~/\ (? /\ y) wouldn't be defined
  Reasoning: Concretizations of both operands are individually "/\"ed
          => unsatisfiable formulas arise
          => abstraction of that is undefined
 *)
Lemma LiftingGPhiAnd : LiftFunction2 (fun p1 p2 p => FormAnd p1 p2 = p /\ Satisfiable p) GFormAndSat.
Proof.
  intro. intro. intro.
  split; intro hyp.
  - inv hyp.
    * eexists. split. eex.
      eexists. split. eauto.
      eexists. split. eauto.
      exists (MakePFormSingleton (FormAnd phi1 phi2)).
      split.
      + split.
        --intro ee. unf.
          inv H1. inv H3.
          auto.
        --inv H. eex. inv H. eauto.
      + reduce.
        split. eex.
        intro. intro ee. unf.
        eex.
    * eexists. split. eex.
      inv H; inv H0.
      + apply or_not_and in H1. contradict H1. eex.
      + eexists. split. eauto.
        eexists. split. eauto.
        exists (fun phi' => (∃ phi0 phi3 : Set_Formula, (FormAnd phi0 phi3 = phi' ∧ Satisfiable phi') ∧ MakePFormSingleton phi1 phi0 ∧ MakePFormIdeal phi2 phi3)).
        split. reduce. split; auto.
        reduce.
        split.
        --eexists.
          split. apply GFormEqualSymm in H2. eapply GFormEqualSameGamma in H2; eauto.
          inv H2. reduce. unf.
          inv H2. inv H5.
          split; auto.
        --intros. unf.
          reduce. exists (MakePFormIdeal (FormAnd phi1 phi2)). eex.
            apply GFormEqualSymm in H2.
            eapply GFormEqualSameGamma; eauto.
          inv H.
          **apply except.
            inv H0. eapply PFormSubsetTrans in H; try eapply H3.
            assert (C1 := H (FormAnd phi1 phi2)).
            assert (C2 := H (FormAnd phi1 (FormAnd FormTrue phi2))).
            lapply C1. intro c1. Focus 2. eex.
            lapply C2. intro c2. Focus 2. exists phi1. exists (FormAnd FormTrue phi2). split.
              split; auto. inversion sat. inv H0. eex.
              split; auto. split.
                intro. intro. inv H0. auto.
                inv sat1. eex.
            inv c1. inv c2. apply RecFormAndR in H5. auto.
          **inv H0.
            intro. intro mpfi. inv mpfi.
            apply H4. clear H4. eapply PFormSubsetTrans in H; try apply H3. clear H3. (* eliminate x *)
            reduce. split; auto.
            intro. intro ef. apply H0 in ef.
            specialize (H (FormAnd phi1 phi2)). lapply H.
            ++intro mpfi. apply mpfi in ef. assumption.
            ++eex.
      + eexists. split. eauto.
        eexists. split. eauto.
        exists (fun phi' => (∃ phi0 phi3 : Set_Formula, (FormAnd phi0 phi3 = phi' ∧ Satisfiable phi') ∧ MakePFormIdeal phi1 phi0 ∧ MakePFormSingleton phi2 phi3)).
        split. reduce. split; auto.
        reduce.
        split.
        --eexists.
          split. apply GFormEqualSymm in H2. eapply GFormEqualSameGamma in H2; eauto.
          inv H2. reduce. unf.
          inv H2. inv H5.
          split; auto.
        --intros. unf.
          reduce. exists (MakePFormIdeal (FormAnd phi1 phi2)). eex.
            apply GFormEqualSymm in H2.
            eapply GFormEqualSameGamma; eauto.
          inv H.
          **apply except.
            inv H0. eapply PFormSubsetTrans in H; try eapply H3.
            assert (C1 := H (FormAnd phi1 phi2)).
            assert (C2 := H (FormAnd (FormAnd FormTrue phi1) phi2)).
            lapply C1. intro c1. Focus 2. eex.
            lapply C2. intro c2. Focus 2. exists (FormAnd FormTrue phi1). exists phi2. split.
              split; auto. inversion sat. inv H0. eex.
              split; auto. split.
                intro. intro. inv H0. auto.
                inv sat1. eex.
            inv c1. inv c2. apply RecFormAndR in H5. auto.
          **inv H0.
            intro. intro mpfi. inv mpfi.
            apply H4. clear H4. eapply PFormSubsetTrans in H; try apply H3. clear H3. (* eliminate x *)
            reduce. split; auto.
            intro. intro ef. apply H0 in ef.
            specialize (H (FormAnd phi1 phi2)). lapply H.
            ++intro mpfi. apply mpfi in ef. assumption.
            ++eex.
      + eexists. split. eauto.
        eexists. split. eauto.
        exists (fun phi' => (∃ phi0 phi3 : Set_Formula, (FormAnd phi0 phi3 = phi' ∧ Satisfiable phi') ∧ MakePFormIdeal phi1 phi0 ∧ MakePFormIdeal phi2 phi3)).
        split. reduce. split; auto.
        reduce.
        split.
        --eexists.
          split. apply GFormEqualSymm in H2. eapply GFormEqualSameGamma in H2; eauto.
          inv H2. reduce. unf.
          inv H2. inv H5.
          split; auto.
        --intros. unf.
          reduce. exists (MakePFormIdeal (FormAnd phi1 phi2)). eex.
            apply GFormEqualSymm in H2.
            eapply GFormEqualSameGamma; eauto.
          inv H.
          **apply except.
            inv H0. eapply PFormSubsetTrans in H; try eapply H3.
            assert (C1 := H (FormAnd phi1 phi2)).
            assert (C2 := H (FormAnd (FormAnd FormTrue phi1) phi2)).
            lapply C1. intro c1. Focus 2. eex.
            lapply C2. intro c2. Focus 2. exists (FormAnd FormTrue phi1). exists phi2. split.
              split; auto. inversion sat. inv H0. eex.
              split; auto. split.
                intro. intro. inv H0. auto.
                inv sat1. eex.
            inv c1. inv c2. apply RecFormAndR in H5. auto.
          **inv H0.
            intro. intro mpfi. inv mpfi.
            apply H4. clear H4. eapply PFormSubsetTrans in H; try apply H3. clear H3. (* eliminate x *)
            reduce. split; auto.
            intro. intro ef. apply H0 in ef.
            specialize (H (FormAnd phi1 phi2)). lapply H.
            ++intro mpfi. apply mpfi in ef. assumption.
            ++eex.
  - inv hyp. unf.
    clac (¬ (∃ phi, gphi1 = GFormPrecise phi) ∨ ¬ (∃ phi : Set_Formula, gphi2 = GFormPrecise phi)).
    * assert (exists phi1, Static gphi1 phi1) as c1. inv H1; eex.
      assert (exists phi2, Static gphi2 phi2) as c2. inv H2; eex.
      assert (exists phi, x2 phi) as sat. eapply AlphaNotEmpty; eauto. unf.
      apply H0 in H3. clear H0.
      assert (mpli := H3).
      apply H3 in H5. clear H3.
      unf.
      assert (Satisfiable (FormAnd x5 x4)) as sat.
        eapply (GammaImpliesStatic gphi1) in H3; eauto.
        eapply (GammaImpliesStatic gphi2) in H8; eauto.
        eapply (ImpliesAnd x6 x7) in H8; eauto.
        inv H9. eex.
      apply (GFormAndSatImprecise gphi1 gphi2 x5 x4 sat); try assumption.
      (* proof GFormEqual *)
      reduce in mpli.
      reduce in H4. unf.
      split.
      + apply H5. eexists. split. eauto.
        intro. intro c. apply mpli in c. unf.
        reduce. split; auto.
        apply ImpliesAnd; eapply GammaImpliesStatic; eauto.
      + inv H0.
        --apply except.
          assert (mpli1 := mpli (FormAnd x5 x4)). inv mpli1.
            lapply H0. Focus 2. eex; eapply GammaContainsStatic; eauto.
            intro c1.
          assert (exists phi, phi <> (FormAnd x5 x4) /\ x2 phi) as mpli2.
            inv H1; inv H2; inversion H6; inversion H7; subst. (* Gamma and Static *)
              contradict H. apply and_not_or. split; intro c; contradict c; eex.
              exists (FormAnd x5 (FormAnd FormTrue x4)). split.
                intro c. inv c. apply RecFormAndR in H13. auto.
                apply mpli. eexists. eexists. split. split; eauto. inv sat. inv H2. eex. split.
                  eapply GammaContainsStatic; eauto.
                  apply H1. reduce. split.
                    intro. intro. inv H2. auto.
                    inv sat2. eex.
              exists (FormAnd (FormAnd FormTrue x5) x4). split.
                intro c. inv c. apply RecFormAndR in H13. auto.
                apply mpli. eexists. eexists. split. split; eauto. inv sat. inv H2. eex. split.
                  apply H12. reduce. split.
                    intro. intro. inv H2. auto.
                    inv sat2. eex.
                  eapply GammaContainsStatic; eauto.
              exists (FormAnd (FormAnd FormTrue x5) x4). split.
                intro c. inv c. apply RecFormAndR in H13. auto.
                apply mpli. eexists. eexists. split. split; eauto. inv sat. inv H2. eex. split.
                  apply H12. reduce. split.
                    intro. intro. inv H2. auto.
                    inv sat4. eex.
                  eapply GammaContainsStatic; eauto.
          unf.
          apply H10 in c1.
          apply H10 in H14.
          apply H4 in c1.
          apply H4 in H14.
          inv c1. inv H14.
          congruence.
        --reduce. eex.
          intro. intro mpfix. inv mpfix.
          apply H4. split; auto.
          intro. intro ef. apply H0 in ef.
          specialize (mpli (FormAnd x5 x4)). inv mpli. lapply H12.
          **intro c. apply H10 in c. apply H4 in c. apply c. assumption.
          **eex; eapply GammaContainsStatic; eauto.
    * intuition. apply NNPP in H5. apply NNPP in H6.
      unf. inv H1. inv H2. apply H0 in H3. clear H0.
      reduce in H3.
      assert (al := H4).
      inv H4. unf.
      inv H. (* Gamma gphi' x5 *)
      + assert (exists phi, x2 phi) as nonempty.
          eapply AlphaNotEmpty; eauto.
        unf.
        assert (x6 = FormAnd x4 x3 /\ Satisfiable x6) as xx.
          apply H3 in H. unf. apply H5 in H. apply H1 in H8. inv H. inv H8. auto.
        unf. subst.
        apply H4 in H.
        apply H2 in H. inv H.
        ctor. assumption.
      + apply except.
        specialize (H0 (GFormPrecise (FormAnd x4 x3))).
        lapply H0.
        --intro c. inv c. unf. inv H. inv H6. inv H7. inv H9.
          eapply (PFormSubsetTrans x6) in H; eauto. eapply (PFormSubsetTrans (MakePFormIdeal phi)) in H; eauto.
          reduce in H.
          assert (C1 := H phi).
          assert (C2 := H (FormAnd phi FormTrue)).
          lapply C1; auto. intro c1.
          lapply C2. Focus 2. reduce. split.
            intro. intro. inv H9. assumption.
            inv sat1. eex.
            intro c2.
          subst. inv c2. apply RecFormAndL in H11. auto.
        --eex. intro. intro xx. apply H3 in xx. unf.
          reduce.
          apply H5 in H6. apply H1 in H8. inv H6. inv H8.
          auto.
Qed.

Lemma SubstExprVarExprDet : forall x e ee e1 e2, SubstExprVarExpr x e ee e1 -> SubstExprVarExpr x e ee e2 -> e1 = e2.
Proof.
  intro. intro. induction ee; intro; intro; intro sfve1; intro sfve2.
  - inv sfve1. inv sfve2. auto.
  - inv sfve1; inv sfve2; auto; congruence.
  - inv sfve1. inv sfve2.
    eapply IHee1 in H5; eauto.
    eapply IHee2 in H6; eauto.
    subst. auto.
Qed.

Lemma SubstFormVarExprDet : forall x e phi phi1 phi2, SubstFormVarExpr x e phi phi1 -> SubstFormVarExpr x e phi phi2 -> phi1 = phi2.
Proof.
  intro. intro. induction phi; intro; intro; intro sfve1; intro sfve2.
  - inv sfve1. inv sfve2. auto.
  - inv sfve1. inv sfve2.
    eapply SubstExprVarExprDet in H5; eauto.
    eapply SubstExprVarExprDet in H6; eauto.
    subst. auto.
  - inv sfve1. inv sfve2.
    eapply IHphi1 in H3; eauto.
    eapply IHphi2 in H5; eauto.
    subst. auto.
Qed.

Lemma SubstExprVarExprId : forall x e e1 e2, ~ FreeVarExpr x e1 -> SubstExprVarExpr x e e1 e2 -> e1 = e2.
Proof.
  intro. intro. induction e1; intro; intro fv; intro su.
  - inv su. auto.
  - inv su.
    * contradict fv. ctor.
    * auto.
  - inv su.
    eapply IHe1_1 in H5; try (intro c; contradict fv; ctor; auto; fail).
    eapply IHe1_2 in H6; try (intro c; contradict fv; ctor; auto; fail).
    subst.
    auto.
Qed.

Lemma SubstFormVarExprId : forall x e phi1 phi2, ~ FreeVarForm x phi1 -> SubstFormVarExpr x e phi1 phi2 -> phi1 = phi2.
Proof.
  intro. intro. induction phi1; intro; intro fv; intro su.
  - inv su. auto.
  - inv su.
    eapply SubstExprVarExprId in H5; try (intro c; contradict fv; ctor; auto; fail).
    eapply SubstExprVarExprId in H6; try (intro c; contradict fv; ctor; auto; fail).
    subst.
    auto.
  - inv su.
    eapply IHphi1_1 in H3; try (intro c; contradict fv; ctor; auto; fail).
    eapply IHphi1_2 in H5; try (intro c; contradict fv; ctor; auto; fail).
    subst.
    auto.
Qed.

Inductive VarEnvWithout : Set_Var -> Set_VarEnv -> Set_VarEnv -> Prop :=
| VEWF : forall x, VarEnvWithout x VarEnvFresh VarEnvFresh
| VEW0 : forall x x' v rho rho',
  VarEnvWithout x rho rho' ->
  x <> x' ->
  VarEnvWithout x (VarEnvMapping x' v rho) (VarEnvMapping x' v rho')
| VEW1 : forall x x' v rho rho',
  VarEnvWithout x rho rho' ->
  x = x' ->
  VarEnvWithout x (VarEnvMapping x' v rho) rho'
.

Hint Constructors VarEnvWithout.

Lemma VarEnvWithoutTotal : forall x rho, exists rho', VarEnvWithout x rho rho'.
Proof.
  induction rho.
  - eex.
  - unf.
    clac (s = x).
    * subst.
      eex.
    * eex.
Qed.

Lemma VarEnvWithoutNonEval : forall x rho rho', VarEnvWithout x rho rho' -> ~ exists v, EvalVar rho' x v.
Proof.
  induction rho; intro; intro vew; inv vew.
  - intro c. unf. inv H.
  - apply IHrho in H4. intro c. contradict H4. unf. inv H; try congruence. eex.
  - apply IHrho in H4. assumption.
Qed.

Lemma VarEnvWithoutDet : forall x rho rho1 rho2, VarEnvWithout x rho rho1 -> VarEnvWithout x rho rho2 -> rho1 = rho2.
Proof.
  induction rho; intro; intro; intro fv1; intro fv2;
  inv fv1; inv fv2; auto; try congruence.
  eapply IHrho in H4; eauto. subst. auto.
Qed.

Lemma EvalExprSimplerRho : forall x e rho v,
   ¬ FreeVarExpr x e ->
   EvalExpr rho e v ->
  exists rho', VarEnvWithout x rho rho' /\ EvalExpr rho' e v.
Proof.
  induction e; intro; intro; intro fv; intro ee.
  - assert (tot := VarEnvWithoutTotal x rho). unf.
    eex. inv ee. ctor.
  - clac (s = x).
    * subst.
      contradict fv. ctor.
    * generalize rho ee H. clear.
      induction rho; intro ee; intro ne; inv ee; inv H1.
      + assert (tot := VarEnvWithoutTotal x rho). unf.
        exists (VarEnvMapping s v x0).
        split.
          ctor; auto.
          ctor. ctor.
      + eapply IHrho in ne; auto. Focus 2. ctor. auto.
        unf.
        clac (s0 = x).
        --subst. eex.
        --inv H1. eex. ctor. ctor; auto.
  - inv ee.
    apply IHe1 in H3. Focus 2. intro c. contradict fv. ctor. auto.
    apply IHe2 in H5. Focus 2. intro c. contradict fv. ctor. auto.
    unf.
    eapply VarEnvWithoutDet in H1; eauto. subst.
    eex. ctor; eauto.
Qed.

Lemma EvalFormulaSimplerRho : forall rho x phi,
   ¬ FreeVarForm x phi ->
   EvalFormula rho phi ->
  exists rho', VarEnvWithout x rho rho' /\ EvalFormula rho' phi.
Proof.
  induction phi; intro fv; intro ef.
  - assert (tot := VarEnvWithoutTotal x rho). unf.
    eex.
  - inv ef.
    eapply EvalExprSimplerRho in H3. Focus 2. intro c. contradict fv. ctor. eauto.
    eapply EvalExprSimplerRho in H4. Focus 2. intro c. contradict fv. ctor. eauto.
    unf.
    eapply VarEnvWithoutDet in H1; eauto. subst.
    eex.
  - inv ef.
    apply IHphi1 in H2. Focus 2. intro c. contradict fv. ctor. auto.
    apply IHphi2 in H3. Focus 2. intro c. contradict fv. ctor. auto.
    unf.
    eapply VarEnvWithoutDet in H1; eauto. subst.
    eex.
Qed.

Lemma EvalExprEvalFreeVar : forall rho e v, EvalExpr rho e v -> forall x, FreeVarExpr x e -> exists v, EvalVar rho x v.
Proof.
  induction e; intro; intro ev; intro; intro fv; inv fv.
  - inv ev. eex.
  - inv ev. inv H1.
    * eapply IHe1; eauto.
    * eapply IHe2; eauto.
Qed.

Lemma EvalFormulaEvalFreeVar : forall rho phi, EvalFormula rho phi -> forall x, FreeVarForm x phi -> exists v, EvalVar rho x v.
Proof.
  induction phi; intro ev; intro; intro fv; inv fv.
  - inv ev. inv H1.
    * eapply EvalExprEvalFreeVar in H4; eauto.
    * eapply EvalExprEvalFreeVar in H5; eauto.
  - inv ev. inv H1.
    * eapply IHphi1 in H3; eauto.
    * eapply IHphi2 in H4; eauto.
Qed.

Lemma ImpliesFreeVarForm : forall phi1 phi2, Satisfiable phi1 -> Implies phi1 phi2 -> forall x, FreeVarForm x phi2 -> FreeVarForm x phi1.
Proof.
  intro. intro. intro sat. intro im. intro. intro fv2.
  apply NNPP. intro fv1.
  inv sat.
  eapply EvalFormulaSimplerRho in H; eauto. unf.
  apply im in H1.
  eapply EvalFormulaEvalFreeVar in H1; eauto.
  eapply VarEnvWithoutNonEval in H.
  auto.
Qed.

(*monotone subst*)
Lemma MonotoneSubstFormVarExpr_Helper1 : ∀ x e phi1 phi2 phi1' phi2',
  SubstFormVarExpr x e phi1 phi1' -> SubstFormVarExpr x e phi2 phi2' ->
  Satisfiable phi1 ->
  Implies phi1 phi2 -> Implies phi1' phi2'.
Proof.
  intro. intro. intro. intro. intro. intro.
  intro sfve1. intro sfve2. intro sat.
  intro im.
  intro. intro ef.
  clac (FreeVarForm x phi1).
  - eapply MonotoneSubstFormVarExpr_HelperForm in H; eauto. unf.
    eapply SubstFormSemantics in ef; eauto.
    eapply im in ef.
    eapply SubstFormSemantics; eauto.
  - assert (~ FreeVarForm x phi2) as fv.
      intro c. contradict H. eapply ImpliesFreeVarForm in im; eauto.
    eapply SubstFormVarExprId in sfve1; eauto.
    eapply SubstFormVarExprId in sfve2; eauto.
    subst.
    apply im. auto.
Qed.

Definition InfiniteSet (S : Set) := forall (l : list S), ~ forall (s : S), In s l.

Lemma Set_VarInfinite : InfiniteSet Set_Var.
Proof.
  unfold InfiniteSet.
  intros. intro c.
  assert (forall l : list Set_Var, exists le, forall i, In (VarIdent i) l -> String.length i < le) as len.
    induction l0. exists 0. intros. inv H.
    unf. destruct a.
      exists x. intros. inv H0; try congruence. apply H; auto.
      exists (max x (S (String.length s))). intros. unfold lt in *. inv H0.
        inv H1. apply Nat.le_max_r.
        apply H in H1. eapply Nat.le_trans; eauto. apply Nat.le_max_l.
      exists x. intros. inv H0; try congruence. apply H; auto.
  specialize (len l).
  unf.
  assert (forall le, exists s : string, String.length s = le) as ex.
    induction le.
      exists EmptyString. auto.
      unf. exists (String Ascii.zero x0). auto.
  specialize (ex x).
  unf.
  specialize (H x0).
  lapply H; auto.
  apply Nat.lt_irrefl.
Qed.

Lemma NotFreeVarForm : forall phi, exists x, ~ FreeVarForm x phi.
Proof.
  intro.
  apply not_all_ex_not.
  intro c.
  assert (ub := FreeVarFormUpperBound phi). unf.
  assert (forall x0, In x0 x) as inf. intro. apply H. apply c.
  contradict inf.
  apply Set_VarInfinite.
Qed.

Lemma SubstFormVarExprSatisfiable : ∀ x e phi phi',
  SubstFormVarExpr x e phi phi' -> Satisfiable phi' -> Satisfiable phi.
Proof.
  intro. intro. intro. intro. intro sfv. intro sat.
  inv sat.
  clac (FreeVarForm x phi).
  - eapply MonotoneSubstFormVarExpr_HelperForm in H0; eauto. unf.
    eapply SubstFormSemantics in sfv; eauto.
    apply sfv in H.
    eex.
  - apply SubstFormVarExprId in sfv; auto.
    subst.
    eex.
Qed.

Lemma MonotoneSubstFormVarExpr_Helper2 : ∀ x e phi1 phi2 phi1' phi2',
  SubstFormVarExpr x e phi1 phi1' -> SubstFormVarExpr x e phi2 phi2' ->
  ~ Satisfiable phi1 ->
  Implies phi1 phi2 -> Implies phi1' phi2'.
Proof.
  intro. intro. intro. intro. intro. intro. intro sfv1. intro sfv2. intro sat. intro im.
  assert (~ Satisfiable phi1') as sat'.
    intro c. contradict sat.
    apply SubstFormVarExprSatisfiable in sfv1; auto.
  intro. intro ef. contradict sat'. eex.
Qed.

Lemma MonotoneSubstFormVarExpr : ∀ x e phi1 phi2 phi1' phi2',
  SubstFormVarExpr x e phi1 phi1' -> SubstFormVarExpr x e phi2 phi2' ->
  Implies phi1 phi2 -> Implies phi1' phi2'.
Proof.
  intros.
  clac (Satisfiable phi1).
  - eapply MonotoneSubstFormVarExpr_Helper1; eauto.
  - eapply MonotoneSubstFormVarExpr_Helper2; eauto.
Qed.

Hint Constructors SubstExprVarExpr.
Hint Constructors SubstFormVarExpr.

Lemma SubstExprVarExprTotal : forall x e e1, exists e2, SubstExprVarExpr x e e1 e2.
Proof.
  induction e1.
  - eex.
  - clac (s = x); subst; eex.
  - unf. eex.
Qed.

Lemma SubstFormVarExprTotal : forall x e phi, exists phi', SubstFormVarExpr x e phi phi'.
Proof.
  induction phi.
  - eex.
  - assert (se1 := SubstExprVarExprTotal x e s0).
    assert (se2 := SubstExprVarExprTotal x e s1).
    unf.
    eex.
  - unf.
    eex.
Qed.

Lemma PFormSubsetSingleton : forall p (pp : Set_PFormula) phi, pp p -> PFormSubset pp (MakePFormSingleton phi) -> PFormSingleton phi pp.
Proof.
  intro. intro. intro. intro psat. intro pfs.
  split; auto.
  reduce in pfs.
  reduce. inv H.
  assert (p = phi). apply pfs; auto.
  subst.
  assumption.
Qed.

Lemma MorePreciseThanPrecise : forall gp phi, MorePreciseThan gp (GFormPrecise phi) <-> gp = GFormPrecise phi.
Proof.
  intro. intro.
  split; intro mpt.
  * reduce in mpt. unf.
    inv H0. inv H3. eapply (PFormSubsetTrans x) in H0; eauto.
    inv H; inv H3.
    - eapply (PFormSubsetTrans (MakePFormSingleton phi0)) in H0; eauto.
      specialize (H0 phi0).
      lapply H0; eauto. intro c. inv c.
      auto.
    - apply except.
      eapply (PFormSubsetTrans (MakePFormIdeal phi0)) in H0; eauto.
      assert (C1 := H0 phi0).
      assert (C2 := H0 (FormAnd phi0 FormTrue)).
      lapply C1. Focus 2. eex.
      intro c1.
      lapply C2. Focus 2. split.
          intro. intro c. inv c. assumption.
          inv sat. eex.
      intro c2.
      inv c1. inv c2.
      apply RecFormAndL in H3. auto.
  * subst. auto.
Qed.

Lemma MorePreciseThanImprecise : forall p1 p2 s1 s2,
  Implies p1 p2 <-> MorePreciseThan (GFormImprecise p1 s1) (GFormImprecise p2 s2).
Proof.
  intros.
  split; intro hyp.
  - eexists. eexists. split; eauto. split; eauto.
    intro. intro mpfi. inv mpfi.
    ctor; eauto.
    eapply ImpliesTrans; eauto.
  - reduce in hyp. unf.
    inv H. inv H0.
    inv H1. inv H3.
    lapply (H4 p1); auto. intro c.
    apply H2 in c. apply H in c. apply c.
Qed.

Definition SatisfiableCodomain (f : Set_Formula -> Set_Formula -> Prop) := forall phi1 phi2, f phi1 phi2 -> Satisfiable phi2.
Definition IdealDomainNonSingularCodomain (f : Set_Formula -> Set_Formula -> Prop) := forall phi1 phi2, Satisfiable phi1 -> f phi1 phi2 -> exists phi1' phi2', Satisfiable phi1' /\ f phi1' phi2' /\ Implies phi1' phi1 /\ phi2 <> phi2'.

Inductive PrimitiveLift : (Set_Formula -> Set_Formula -> Prop) -> (Set_GFormula -> Set_GFormula -> Prop) :=
| PrimitiveLiftPrecise : forall (P : Set_Formula -> Set_Formula -> Prop) phi1 phi2,
  P phi1 phi2 ->
  PrimitiveLift P (GFormPrecise phi1) (GFormPrecise phi2)
| PrimitiveLiftPreciseUnsat : forall (P : Set_Formula -> Set_Formula -> Prop) phi1 phi2 sat1,
  P phi1 phi2 ->
  ~ Satisfiable phi2 ->
  PrimitiveLift P (GFormImprecise phi1 sat1) (GFormPrecise phi2)
| PrimitiveLiftImprecise : forall (P : Set_Formula -> Set_Formula -> Prop) phi1 phi2 sat1 sat2 gphi,
  P phi1 phi2 ->
  GFormEqual (GFormImprecise phi2 sat2) gphi ->
  PrimitiveLift P (GFormImprecise phi1 sat1) gphi
.

Hint Constructors PrimitiveLift.

Lemma MakePLiftFunction1Total : forall f p, exists p', MakePLiftFunction1 f p p'.
Proof.
  intros.
  exists (fun phi' => ∃ phi1 : Set_Formula, f phi1 phi' ∧ p phi1).
  split; auto.
Qed.

Lemma MonotoneMakePLiftFunction1 : forall f p1 p1' p2 p2',
  MakePLiftFunction1 f p1 p1' -> MakePLiftFunction1 f p2 p2' -> PFormSubset p1 p2 -> PFormSubset p1' p2'.
Proof.
  intro. intro. intro. intro. intro. intro mp1. intro mp2. intro pf. intro. intro pp.
  apply mp1 in pp. unf. apply pf in H1. apply mp2. eex.
Qed.


Definition MonotoneGFunction1 (gF : Set_GFormula -> Set_GFormula -> Prop) := forall gp1 gp2,
  MorePreciseThan gp1 gp2 -> forall gp1', gF gp1 gp1' -> exists gp2', gF gp2 gp2' /\ MorePreciseThan gp1' gp2'.
Definition IMonotoneGFunction1 (gF : Set_GFormula -> Set_GFormula -> Prop) := forall gp1 gp2,
  MoreImpliesThan gp1 gp2 -> forall gp1', gF gp1 gp1' -> exists gp2', gF gp2 gp2' /\ MoreImpliesThan gp1' gp2'.
Definition XMonotoneGFunction1 (gF : Set_GFormula -> Set_GFormula -> Prop) := forall gp1 gp2,
  XMorePreciseThan gp1 gp2 -> forall gp1', gF gp1 gp1' -> exists gp2', gF gp2 gp2' /\ XMorePreciseThan gp1' gp2'.

Definition CustomMonotoneGFunction1 (Pin Pout gF : Set_GFormula -> Set_GFormula -> Prop) := forall gp1 gp2,
  Pin gp1 gp2 -> forall gp1', gF gp1 gp1' -> exists gp2', gF gp2 gp2' /\ Pout gp1' gp2'.

Print PartialGC3.
Lemma MonotoneLiftFunction1 : forall f gf,
  LiftFunction1 f gf -> WeakPartialGC3 (MakePLiftFunction1 f) -> MonotoneGFunction1 gf.
Proof.
  intro. intro. intro lf. intro pg. intro. intro. intro mpt. intro. intro gff.
  apply lf in gff.
  reduce in gff. unf.
  apply H0 in H2. clear x H0.
  reduce in mpt. unf.
  eapply GammaDet in H1; eauto.
  assert (mpl := MakePLiftFunction1Total f x2). unf.
  assert (MakePLiftFunction1 f x x1) as mpli. intro. specialize (H2 phi'). symmetry in H2. rewrite H2. split; intro c; unf; eex; apply H1; assumption.
  clear H2 H1 x0.
  assert (PFormSubset x1 x3) as mon.
    eapply MonotoneMakePLiftFunction1; eauto.
  assert (∃ gphi', Alpha x3 gphi') as ex.
    eapply pg; eauto.
    apply AlphaNotEmpty in H3. unf. apply mon in H1. eex.
  unf.
  exists x0.
  split.
  - apply lf.
    reduce.
    eexists. split. eex.
    eexists. split. eauto.
    eexists. split. eauto.
    assumption.
  - assert (AA := H1). apply PartialGC1 in H1.
    unf.
    eapply PartialGC2; eauto.
Qed.

(* key diff with MPT (which only has this property for refl. case) *)
Lemma MoreImpliesThanFalse : forall gp p, Satisfiable p \/ MoreImpliesThan (GFormPrecise p) gp.
Proof.
  intro. intro.
  clac (Satisfiable p); auto.
  apply or_intror.
  apply MoreImpliesThanAltEq.
  intro. intro. intro st1. intro st2. intro. intro ef.
  inv st1.
  contradict H. eex.
Qed.

Definition GUnknown (gp : Set_GFormula) := exists p sat, gp = GFormImprecise p sat /\ FormEqual p FormTrue.
Definition GUnknownAlt (gp : Set_GFormula) := exists pp, Gamma gp pp /\ forall p, pp p <-> Satisfiable p.
Lemma GUnknownAltEq : forall gp, GUnknown gp <-> GUnknownAlt gp.
Proof.
  intro. split; intro sat; inv sat; unf.
  - eexists. split; eauto.
    intro. split; intro hyp.
    * apply hyp.
    * reduce. split; auto. intro. intro ef. apply H1. auto.
  - inv H0.
    * apply except.
      assert (x FormTrue) as X1. apply H1. exists VarEnvFresh. auto.
      assert (x (FormAnd FormTrue FormTrue)) as X2. apply H1. exists VarEnvFresh. auto.
      apply H in X1. apply H in X2.
      inv X1. inv X2.
    * exists phi.
      exists sat.
      split; auto.
      split; intro; intro hyp. auto.
      assert (Satisfiable FormTrue) as satx. eex.
      apply H1 in satx. apply H in satx. inv satx.
      apply H0. auto.
Qed.

Lemma MorePreciseThanNotSatisfiable : forall gp1 gp2, ~ GSatisfiable gp1 -> MorePreciseThan gp1 gp2 -> gp1 = gp2.
Proof.
  intro. intro. intro sat. intro eq.
  inv eq. unf.
  apply NNPP. intro c.
  contradict sat.
  rewrite GSatisfiableAltEq.
  exists x.
  assert (st := StaticTotal gp1). unf. assert (G := H). eapply GammaContainsStatic in G; eauto.
  exists x1. split; auto. split; auto.
  inv H;
  apply H3 in G; inv G. Focus 2. assumption.
  clear H1. (* Static *)
  assert (x phi) as go. apply H3. auto.
  apply H2 in go.
  inv H0.
  + apply except.
    apply H in go. inv go.
    contradict c. auto.
  + apply H in go. inv go.
    assumption.
Qed.


Definition IsMaxImprecise (gp : Set_GFormula) := forall gp', MorePreciseThan gp gp' -> GFormEqual gp gp'.
Lemma IsMaxImpreciseCases : forall gp, IsMaxImprecise gp <-> (GSatisfiable gp -> GUnknown gp).
Proof.
  intro. split; intro hyp.
  - intro sat.
    apply GSatisfiableAltEq in sat.
    assert (Satisfiable FormTrue) as sat'. exists VarEnvFresh. auto.
    lapply (hyp (GFormImprecise FormTrue sat')).
    * intro. inv H.
      destruct gp.
      + apply MorePreciseThanPrecise in H1. inv H1.
      + apply MorePreciseThanImprecise in H0.
        apply MorePreciseThanImprecise in H1.
        eex.
    * inv sat. unf.
      eexists. eexists.
      split; eauto.
      split; eauto.
      intro. intro xx. ctor. intro. auto.
      inv H.
      + apply H1 in H0. apply H1 in xx. inv H0. inv xx. assumption.
      + apply H1 in xx. inv xx. assumption.
  - intro. intro mpt.
    split; auto.
    clac (GSatisfiable gp).
    * assert (sat := H). apply hyp in H.
      inv H. unf.
      destruct gp'.
      + apply MorePreciseThanPrecise in mpt. inv mpt.
      + apply MorePreciseThanImprecise. intro. intro ef.
        apply H1. auto.
    * apply MorePreciseThanNotSatisfiable in mpt; auto.
      subst. auto.
Qed.

Lemma MorePreciseThanGSatisfiable : forall gp1 gp2, MorePreciseThan gp1 gp2 -> GSatisfiable gp1 -> GSatisfiable gp2.
Proof.
  intro. intro. intro mpt. intro sat.
  apply GSatisfiableAltEq in sat. apply GSatisfiableAltEq.
  inv sat. unf.
  inv mpt. unf.
  eex. apply H5. eapply GammaDet in H; eauto.
  apply H. auto.
Qed.

(* 
Definition SafelyDomainEnlargedGFunction1 (gf1 gf2 : Set_GFormula -> Set_GFormula -> Prop) :=
  forall gp1 gp', gf2 gp1 gp' <-> (GSatisfiable gp1 -> gf1 gp1 gp').
 *)
 
Definition LocallyMonotoneGFunction1 (gF : Set_GFormula → Set_GFormula -> Prop) gp1 gpr :=
    ∀ gp1' : Set_GFormula, MorePreciseThan gp1 gp1' →
    ∃ gpr' : Set_GFormula, gF gp1' gpr' ∧ MorePreciseThan gpr gpr'.
Definition DomainEnlargedGFunction1 (gf1 gf2 : Set_GFormula -> Set_GFormula -> Prop) :=
  forall gp1 gp', (gf2 gp1 gp' -> (gf1 gp1 gp' \/ LocallyMonotoneGFunction1 gf2 gp1 gp'))
               /\ (gf1 gp1 gp' -> gf2 gp1 gp').

Lemma MonotoneDomainEnlargedGFunction1 : forall gf1 gf2,
  DomainEnlargedGFunction1 gf1 gf2 -> MonotoneGFunction1 gf1 -> MonotoneGFunction1 gf2.
Proof.
  intro. intro. intro sdef. intro mon.
  intro. intro. intro mpt. intro. intro gg.
  apply sdef in gg.
  inv gg.
  - eapply mon in H; eauto. unf. eex.
    eapply sdef.
    assumption.
  - apply H in mpt.
    assumption.
Qed.
 

(* 
gsubst monotony ctr example

(x = 3)[4/x] = (4 = 3)
? * (x = 3)[4/x] = (4 = 3)
?[4/x] = ? 

mon in terms of implied by more?
mon as in XMonotone? Note that this also chains since unsat. gformulas are already max. precise!
*)

Lemma MorePreciseThanImprecise2 : forall gp p sat, MorePreciseThan gp (GFormImprecise p sat)
  <-> exists p', Static gp p' /\ Satisfiable p' /\ Implies p' p.
Proof.
  intro. intro. intro.
  split.
  * intro mpt.
    inv mpt. unf.
    inv H0.
    inv H.
    - assert (x phi) as xx. apply H0. auto.
      apply H2 in xx. apply H3 in xx.
      inv xx.
      eex.
    - eex.
      assert (x phi) as xx. apply H0. auto.
      apply H2 in xx. apply H3 in xx. 
      apply xx.
  * intro ee. unf.
    assert (tot := GammaTotal gp). unf.
    exists x0. eexists.
    split; eauto.
    split; eauto.
    intro. intro xx.
    assert (yy := xx).
    eapply GammaImpliesStatic in xx; eauto.
    split.
    - eapply ImpliesTrans; eauto.
    - inv H1; inv H0.
      + apply H3 in yy. inv yy.
        assumption.
      + apply H3 in yy. apply yy.
Qed.

Lemma GFormEqualSameStatic : forall g1 g2, GFormEqual g1 g2 -> forall p1 p2, Static g1 p1 -> Static g2 p2 -> FormEqual p1 p2.
Proof.
  intro. intro. intro ge. intro. intro. intro st1. intro st2.
  inv ge.
  inv st1.
  - apply MorePreciseThanPrecise in H0. inv H0. inv st2.
    auto.
  - apply MorePreciseThanImprecise2 in H0. unf.
    eapply (StaticDet g2 p2 x) in st2; eauto. subst.
    split; auto.
    destruct g2.
    * apply MorePreciseThanPrecise in H. inv H.
    * apply MorePreciseThanImprecise in H. inv H0.
      assumption.
Qed.

Hint Unfold XMorePreciseThan.

Lemma XMonotonePrimitiveLift : forall f, MonotoneDef f -> Monotone f -> XMonotoneGFunction1 (PrimitiveLift f).
Proof.
  intro. intro mond. intro mon. intro. intro. intro mpt. intro. intro pl.
  destruct gp2.
  - inv mpt.
    * apply MorePreciseThanPrecise in H. subst.
      eex.
    * inv H.
      + inv H0. unf. inv H.
        assert (exists p2 p2', f x p2 /\ Static gp1' p2' /\ FormEqual p2 p2') as ee1.
          inv pl. eex.
        unf.
        assert (exists p2, f x0 p2) as ee1.
          eapply mond; eauto. apply H0.
        unf.
        assert (FormEqual x1 x3) as eq.
          split; eapply mon; eauto; apply H0.
        exists (GFormPrecise x3). split; auto.
        apply or_intror. apply or_introl.
        assert (FormEqual x2 x3) as eqs.
          eex; intro; intro ef.
            apply eq. apply H3. assumption.
            apply H3. apply eq. assumption.
        eex.
        inv H1; auto. inv pl.
      + unf. contradict H1. eex.
  - inv mpt.
    + apply MorePreciseThanImprecise2 in H. unf.
      assert (exists p2 p2', f x p2 /\ Static gp1' p2' /\ FormEqual p2 p2') as ee1.
        inv pl; inv H.
          eex.
          eex.
          assert (tot := StaticTotal gp1'). unf. eapply GFormEqualSameStatic in H3; eauto.
      unf.
      assert (im := H2).
      assert (exists p2', f phi p2') as ee2.
        unf.
        eapply mond in im; eauto.
      unf.
      eapply mon in im; eauto.
      clac (Satisfiable x2).
      * exists (GFormImprecise x2 H6).
        split. ctor; eauto.
        clac (Satisfiable x1).
        --apply or_introl. apply MorePreciseThanImprecise2. eex. intro. intro ef. apply im. apply H5. assumption.
        --apply or_intror. apply or_intror. split.
          **intro c. contradict H7. inv c. unf. eapply StaticDet in H3; eauto. subst. assumption.
          **intro c. inv c. inv H8.
      * exists (GFormPrecise x2).
        split. ctor; eauto.
        apply or_intror. apply or_introl.
        assert (~ Satisfiable x1) as unsat.
          intro c. contradict H6. inv c. apply H5 in H6. apply im in H6. eex.
        inv H3. Focus 2. contradict unsat. assumption.
        eex; intro; intro ef.
        --apply im. apply H5. assumption.
        --contradict H6. eex.
    + inv H.
      * inv H0. unf. inv H.
      * unf.
        destruct gp1. Focus 2. contradict H. eex.
        inv pl.
        assert (~ Satisfiable s0) as unsat.
          intro c. contradict H. eex.
        assert (exists p2, f phi p2) as ee1.
          eapply mond; eauto. intro. intro ef. contradict unsat. eex.
        unf.
        clac (Satisfiable x).
        --exists (GFormImprecise x H2).
          split.
          **ctor; eauto.
          **reduce.
            clac (Satisfiable phi2).
            ++apply or_introl.
              apply MorePreciseThanImprecise2. eex.
              eapply mon; eauto.
              intro. intro ef. contradict unsat. eex.
            ++apply or_intror. apply or_intror.
              split.
              --- intro c. contradict H4.
                  inv c. unf. inv H5. assumption.
              --- intro c. inv c. inv H5.
        --exists (GFormPrecise x).
          split. ctor; auto.
          apply or_intror. apply or_introl.
          assert (~ Satisfiable phi2).
          intro c. contradict H2. inv c. exists x0.
          eapply mon. eapply H3. eapply H0. intro. intro ef. contradict unsat. eex. assumption.
          eex; intro; intro ef.
          **contradict H4. eex.
          **contradict H2. eex.
Qed.

Section GSemantics.

Variable p : Set_GProgram.

Definition LookupGMethodAmbig : Set_MethodName -> Set_GMethod -> Prop := fun n m =>
match p with
| GProgram ms _ => In m ms /\ (match m with GMethod _ n' _ _ _ _ => n' = n end)
end.
Definition LookupGMethod : Set_MethodName -> Set_GMethod -> Prop := fun n m =>
  LookupGMethodAmbig n m /\ (∀ m', LookupGMethodAmbig n m' -> m = m').

Definition GFormAnd (phi1 : Set_Formula) :=
  PrimitiveLift (fun phi2 phir => FormAnd phi1 phi2 = phir).

Lemma XMonotoneGFormAnd : forall p, XMonotoneGFunction1 (GFormAnd p).
Proof.
  intro. apply XMonotonePrimitiveLift.
  - intro. intro. intro fa. intro. intro im.
    eex.
  - intro. intro. intro. intro. intro fa1. intro fa2. intro im.
    subst.
    auto.
Qed.

Definition SubstGFormVarExpr x e :=
  PrimitiveLift (SubstFormVarExpr x e).

Lemma XMonotoneSubstGFormVarExpr : forall x e, XMonotoneGFunction1 (SubstGFormVarExpr x e).
Proof.
  intro. intro. apply XMonotonePrimitiveLift.
  - intro. intro. intro fa. intro. intro im.
    apply SubstFormVarExprTotal.
  - intro. intro. intro. intro. intro fa1. intro fa2. intro im.
    eapply MonotoneSubstFormVarExpr; eauto.
Qed.

(* approximation with desirable properties *)
Definition GCallMaxImplies (x : Set_Var) (phi phi1' phi2' gr : Set_GFormula) : Prop :=
  exists P,
  (P = (IsPrecise phi /\ IsPrecise phi1' /\ IsPrecise phi2')) /\
  (P -> exists phi', 
        MaxImplies (fun phi' =>
            (forall x', FreeVarForm x' phi' -> x = x') /\
            GImplies (GFormPrecise phi') phi1' /\
            (exists g', GFormAnd phi' phi2' g' /\ GImplies g' phi)
          ) phi'
     /\ gr = GFormPrecise (FormAnd phi' (FormCompOp CompOpEq (ExprVar x) (ExprVar x)))) /\
  (~ P -> exists phi',
        Static phi1' phi'
     /\ exists sat, gr = GFormImprecise (FormAnd phi' (FormCompOp CompOpEq (ExprVar x) (ExprVar x))) sat).

Lemma XMonHelper1 : forall p1 p2, FormEqual p1 p2 -> forall g, GImplies g (GFormPrecise p1) -> GImplies g (GFormPrecise p2).
Proof.
  intro. intro. intro eq. intro. intro im.
  inv im; ctor; eauto.
  - inv H. intro. intro ef. apply eq. apply H0. assumption.
  - inv H1. intro. intro ef. apply eq. apply H2. assumption.
Qed.

Lemma FormEqualSymm : forall p1 p2, FormEqual p1 p2 -> FormEqual p2 p1.
Proof.
  intro. intro. intro fe.
  split; apply fe.
Qed.


Lemma SatisfiableAdditionalEqualityHelper2 : forall rho e v, EvalExpr rho e v -> forall x, FreeVarExpr x e -> exists v, EvalVar rho x v.
Proof.
  induction e; intro; intro ef; intro; intro fvf.
  - inv fvf.
  - inv ef. inv fvf. eex.
  - inv ef. inv fvf. inv H1.
    * eapply IHe1; eauto.
    * eapply IHe2; eauto.
Qed.

Lemma SatisfiableAdditionalEqualityHelper : forall rho phi, EvalFormula rho phi -> forall x, FreeVarForm x phi -> exists v, EvalVar rho x v.
Proof.
  induction phi; intro ef; intro; intro fvf.
  - inv fvf.
  - inv ef. inv fvf.
    inv H1.
    * eapply SatisfiableAdditionalEqualityHelper2 in H3; eauto.
    * eapply SatisfiableAdditionalEqualityHelper2 in H4; eauto.
  - inv ef. inv fvf.
    inv H1.
    * eapply IHphi1; eauto.
    * eapply IHphi2; eauto.
Qed.

Lemma SatisfiableAdditionalEquality : forall phi, Satisfiable phi -> forall x, Satisfiable (FormAnd phi (FormCompOp CompOpEq (ExprVar x) (ExprVar x))).
Proof.
  intro. intro sat. intro.
  inv sat.
  clac (exists v, EvalVar x0 x v).
  - unf.
    exists x0.
    ctor.
    * eauto.
    * ctor; try (ctor; eauto).
      unfold CompOpEq.
      apply Zbool.Zeq_is_eq_bool.
      auto.
  - exists (VarEnvMapping x Z0 x0).
    ctor. Focus 2. ctor; try (ctor; ctor; eauto).
    assert (fv := FreeVarFormList phi). unf.
    assert (~ In x x1) as not_in_it.
      intro c. apply H1 in c. eapply SatisfiableAdditionalEqualityHelper in c; eauto.
    eapply (ObservablyIdenticalVarEnvEvalFormula x1); eauto.
    * intro. intro inn. intro.
      split; intro ev.
      + inv ev.
        --apply not_in_it in inn. inv inn.
        --assumption.
      +ctor; auto.
       intro c. subst. apply not_in_it in inn. inv inn.
    * intro. intro fvf. apply H1. assumption.
Qed.

Lemma XMonotoneGCallMaxImplies1 : forall x phi1' phi2', XMonotoneGFunction1 (fun phi => GCallMaxImplies x phi phi1' phi2').
Proof.
  intro. intro. intro.
  intro. intro. intro mpt. intro. intro f.
  destruct gp2.
  - inv mpt.
    * apply MorePreciseThanPrecise in H. subst.
      eex.
    * inv H.
      + inv H0. unf. inv H.
        exists gp1'.
        split; auto.
        inv f. unf. ctor. split. eauto.
        clac (IsPrecise phi1' ∧ IsPrecise phi2').
        --clear H1. split. Focus 2. intro c. contradict c. split. eex. assumption.
          introc asd.
          lapply H. Focus 2. split. eex. assumption.
          intro c.
          unf. exists x2. split; auto.
          inv H3. unf. split.
          **split; auto. split; auto. eex.
            eapply XMonHelper1; eauto.
          **intros. unf. apply H5.
            split; auto. split; auto. eex.
            apply FormEqualSymm in H0.
            eapply XMonHelper1; eauto.
        --clear H. split. intro c. contradict H2. apply c.
          introc asd.
          lapply H1. Focus 2. intro c. contradict H2. apply c.
          intro c.
          assumption.
      + unf. contradict H1. eex.
  - inv mpt.
    * apply MorePreciseThanImprecise2 in H. unf.
      assert (tot := StaticTotal phi1'). unf.
      assert (Satisfiable (FormAnd x1 (FormCompOp CompOpEq (ExprVar x) (ExprVar x)))) as satis.
        admit. (* that's a method precond *)
      exists (GFormImprecise (FormAnd x1 (FormCompOp CompOpEq (ExprVar x) (ExprVar x))) satis).
      split.
      + eexists. split. eauto.
        split; intro c. inv c. inv H3. inv H5.
        eex.
      + clac (GSatisfiable gp1').
        --apply or_introl.
          apply MorePreciseThanImprecise2.
          inv f. clac x2; intuition; unf.
          **exists (FormAnd x3 (FormCompOp CompOpEq (ExprVar x) (ExprVar x))).
            split; auto.
            split. inv H3. unf. inv H3. assumption.
            apply ImpliesAnd; auto.
            inv H6. unf. inv H7. eapply StaticDet in H1; eauto. subst.
            assumption.
          **eex.
            eapply StaticDet in H1; eauto. subst.
            apply ImpliesAnd; auto.
        --apply or_intror. apply or_intror.
          split; auto.
          intro c. inv c. inv H4.
    * inv H.
      + inv H0. unf. inv H.
      + assert (tot := StaticTotal phi1'). unf.
        assert (Satisfiable (FormAnd x0 (FormCompOp CompOpEq (ExprVar x) (ExprVar x)))) as satis.
          admit. (* that's a method precond *)
        exists (GFormImprecise (FormAnd x0 (FormCompOp CompOpEq (ExprVar x) (ExprVar x))) satis).
        split.
        ++eexists. split. eauto.
          split; intro c. inv c. inv H0. inv H4.
          eex.
        ++clac (GSatisfiable gp1').
          --apply or_introl.
            apply MorePreciseThanImprecise2.
            inv f. clac x1; intuition; unf.
            **eexists.
              split; eauto.
              split. inv H0. unf. inv H0. assumption.
              apply ImpliesAnd; auto.
              inv H5. unf. inv H6. eapply StaticDet in H; eauto. subst.
              assumption.
            **eex.
              eapply StaticDet in H; eauto. subst.
              apply ImpliesAnd; auto.
          --apply or_intror. apply or_intror.
            split; auto.
            intro c. inv c. inv H3.
Admitted.

Lemma CMonotoneGCallMaxImplies2 : forall x phi phi2', CustomMonotoneGFunction1 MorePreciseThan MoreImpliesThan (fun phi1' => GCallMaxImplies x phi phi1' phi2').
Proof.
  intro. intro. intro.
  intro. intro. intro mpt. intro. intro f.
  destruct gp2.
  - apply MorePreciseThanPrecise in mpt. subst.
    eex. intro. auto.
  - apply MorePreciseThanImprecise2 in mpt. unf.
    assert (Satisfiable (FormAnd phi0 (FormCompOp CompOpEq (ExprVar x) (ExprVar x)))) as satis.
      admit.
    exists (GFormImprecise (FormAnd phi0 (FormCompOp CompOpEq (ExprVar x) (ExprVar x))) satis).
    split.
    * eexists. split. eauto.
      split; intro c. inv c. inv H3. inv H4. inv H3.
      eex.
    * apply MoreImpliesThanAltEq. intro. intro. intro st. intro st'. inv st'.
      inv f. clac x1; intuition; unf.
      + inv st.
        apply ImpliesAnd; auto.
        inv H4. unf. inv H5. eapply StaticDet in H0; eauto. subst.
        eapply ImpliesTrans; eauto.
      + inv st.
        apply ImpliesAnd; auto.
        eapply StaticDet in H0; eauto. subst.
        assumption.
Admitted.

Lemma CMonotoneGCallMaxImplies3 : forall x phi phi1', CustomMonotoneGFunction1 MorePreciseThan MoreImpliesThan (fun phi2' => GCallMaxImplies x phi phi1' phi2').
Proof.
  intro. intro. intro.
  intro. intro. intro mpt. intro. intro f.
  destruct gp2.
  - apply MorePreciseThanPrecise in mpt. subst.
    eex. intro. auto.
  - apply MorePreciseThanImprecise2 in mpt. unf.
    assert (tot := StaticTotal phi1'). unf.
    assert (Satisfiable (FormAnd x1 (FormCompOp CompOpEq (ExprVar x) (ExprVar x)))) as satis.
      admit.
    exists (GFormImprecise (FormAnd x1 (FormCompOp CompOpEq (ExprVar x) (ExprVar x))) satis).
    split.
    * eexists. split. eauto.
      split; intro c. inv c. inv H3. inv H4. inv H5. inv H4.
      eex.
    * apply MoreImpliesThanAltEq. intro. intro. intro st. intro st'. inv st'.
      inv f. clac x2; intuition; unf.
      + inv st.
        apply ImpliesAnd; auto.
        inv H5. unf. inv H6. eapply StaticDet in H1; eauto. subst.
        assumption.
      + inv st.
        apply ImpliesAnd; auto.
        eapply StaticDet in H1; eauto. subst.
        auto.
Admitted.


Inductive GWP : Set_Stmt -> Set_GFormula -> Set_GFormula -> Prop :=
| GWpSkip : ∀ gphi,
  GWP StmtSkip gphi gphi
| GWpAssert : ∀ gphi gphi' phia,
  GFormAnd phia gphi gphi' ->
  GWP (StmtAssert phia) gphi gphi'
| GWpVarAssign : ∀ (gphi gphi' gg : Set_GFormula) (x : Set_Var) (e : Set_Expr),
  (~ exists i, x = VarOldIdent i) ->
  SubstGFormVarExpr x e gphi gphi' ->
  GFormAnd (FormCompOp CompOpEq e e) gphi' gg -> (* impl. detail: additional precond. to ensure evaluation *)
  GWP (StmtVarAssign x e) gphi gg

| GWpCall : ∀ (phi phi1 phi2 phi1' phi2' phi2'' : Set_GFormula) (x y : Set_Var) (i : Set_Ident) (m : Set_MethodName) (_T1 _T2 : Set_Type) (_s : Set_Stmt) gr,
  (~ exists i, y = VarOldIdent i) ->
  x <> y ->
  x <> VarResult ->
  LookupGMethod m (GMethod _T1 m _T2 i (GContract phi1 phi2) _s) ->
  SubstGFormVarExpr (VarIdent i) (ExprVar x) phi1 phi1' ->
  SubstGFormVarExpr (VarOldIdent i) (ExprVar x) phi2 phi2'' ->
  SubstGFormVarExpr VarResult (ExprVar y) phi2'' phi2' ->
  GCallMaxImplies x phi phi1' phi2' gr ->
  GWP (StmtCall y m x) phi gr

| GWpSeq : ∀ (s1 s2 : Set_Stmt) (phi1 phi2 phi3 : Set_GFormula),
  GWP s2 phi3 phi2 ->
  GWP s1 phi2 phi1 ->
  GWP (StmtSeq s1 s2) phi3 phi1
.

Hint Constructors GWP.

Definition GFunction1OperandSat (gf : Set_GFormula -> Set_GFormula -> Prop) :=
  forall gp gr, gf gp gr -> GSatisfiable gr -> GSatisfiable gp.

Lemma GWpSkipXMonotone : XMonotoneGFunction1 (GWP StmtSkip).
Proof.
  intro. intro. intro mpt. intro. intro f.
  inv f.
  eex.
Qed.

Lemma GWpAssertXMonotone : forall p, XMonotoneGFunction1 (GWP (StmtAssert p)).
Proof.
  intro.
  intro. intro. intro mpt. intro. intro f.
  inv f.
  eapply XMonotoneGFormAnd in H0; eauto.
  unf. eex.
Qed.

Lemma GImpliesGSatisfiable : forall g1 g2, GImplies g1 g2 -> GSatisfiable g1 -> GSatisfiable g2.
Proof.
  intro. intro. intro gi. intro sat.
  inv gi; inv sat; unf.
  - inv H2.
    inv H3. apply H0 in H1. eex.
  - inv H4.
    inv H. apply H2 in H3. eex.
Qed.

(* note: following is proof for monotone w.r.t. WP parameter; monotone w.r.t. pre- & postcondition are covered by XMonotoneGCallMaxImplies2/3 *)
Lemma GWpCallXMonotone : forall y m x, XMonotoneGFunction1 (GWP (StmtCall y m x)).
Proof.
  intro. intro. intro.
  intro. intro. intro mpt. intro. intro f.
  inv f.
  eapply XMonotoneGCallMaxImplies1 in H11; eauto. unf.
  eex.
Qed.

Lemma GWpVarAssignXMonotone : forall x e, XMonotoneGFunction1 (GWP (StmtVarAssign x e)).
Proof.
  intro. intro.
  intro. intro. intro mpt. intro. intro f.
  inv f.
  eapply XMonotoneSubstGFormVarExpr in H2; eauto. unf.
  eapply XMonotoneGFormAnd in H5; eauto. unf.
  eex.
Qed.

Lemma GWpSeqXMonotone : forall s1 s2,
  XMonotoneGFunction1 (GWP s1) -> XMonotoneGFunction1 (GWP s2) -> XMonotoneGFunction1 (GWP (StmtSeq s1 s2)).
Proof.
  intro. intro. intro x1. intro x2.
  intro. intro. intro mpt. intro. intro f.
  inv f.
  eapply x2 in H1; eauto. unf.
  eapply x1 in H4; eauto. unf.
  eex.
Qed.

Theorem GWpXMonotone : forall s, XMonotoneGFunction1 (GWP s).
Proof.
  induction s.
  - apply GWpSkipXMonotone.
  - apply GWpVarAssignXMonotone.
  - apply GWpCallXMonotone.
  - apply GWpAssertXMonotone.
  - apply GWpSeqXMonotone; assumption.
Qed.

Lemma FormEqualForward : forall f, Monotone f -> forall x1 x2 x1' x2', f x1 x1' -> f x2 x2' -> FormEqual x1 x2 -> FormEqual x1' x2'.
Proof.
  intro. intro mon.
  intro. intro. intro. intro.
  intro f1. intro f2. intro eq.
  split; eapply mon; eauto; apply eq.
Qed.

Lemma MorePreciseThanTrans : forall p1 p2 p3, MorePreciseThan p1 p2 -> MorePreciseThan p2 p3 -> MorePreciseThan p1 p3.
Proof.
  intro. intro. intro. intro m1. intro m2.
  unfold MorePreciseThan in *. unf.
  eapply GammaDet in H1; eauto.
  eex.
  intro. intro xx.
  apply H5. apply H1. apply H3. assumption.
Qed.
Lemma GFormEqualTrans : forall p1 p2 p3, GFormEqual p1 p2 -> GFormEqual p2 p3 -> GFormEqual p1 p3.
Proof.
  intro. intro. intro. intro m1. intro m2.
  unfold GFormEqual in *. unf.
  split; eapply MorePreciseThanTrans; eauto.
Qed.

Definition GDeterministic (f : Set_GFormula -> Set_GFormula -> Prop) := forall phi1' phi2' phi1 phi2, f phi1' phi1 -> f phi2' phi2 -> GFormEqual phi1' phi2' -> (GFormEqual phi1 phi2 \/ ~ GSatisfiable phi1 /\ ~ GSatisfiable phi2).
Lemma PrimitiveLiftDet : forall f, Deterministic f -> Monotone f -> GDeterministic (PrimitiveLift f).
Proof.
  intro. intro det. intro mon. intro. intro. intro. intro. intro p1. intro p2. intro eq.
  inv p1; inv p2.
  - inv eq.
    apply MorePreciseThanPrecise in H1. inv H1.
    assert (s := det _ _ _ H H0). subst.
    auto.
  - apply except.
    inv eq.
    apply MorePreciseThanPrecise in H3. inv H3.
  - apply except.
    inv eq.
    apply MorePreciseThanPrecise in H3. inv H3.
  - apply except.
    inv eq.
    apply MorePreciseThanPrecise in H2. inv H2.
  - apply or_intror.
    split; intro c; inv c; unf; inv H4; congruence.
  - apply except.
    eapply GFormEqualSameStatic in eq; eauto.
    eapply FormEqualForward in eq; eauto.
    contradict H0.
    clear H2. inv sat2. eex. apply eq. eauto.
  - apply except.
    inv eq.
    apply MorePreciseThanPrecise in H2. inv H2.
  - apply except.
    eapply GFormEqualSameStatic in eq; eauto.
    eapply FormEqualForward in eq; eauto.
    contradict H2.
    clear H0. inv sat2. eex. apply eq. eauto.
  - ctor.
    eapply GFormEqualSameStatic in eq; eauto.
    eapply FormEqualForward in eq; eauto.
    apply GFormEqualSymm in H0.
    eapply GFormEqualTrans; eauto.
    eapply GFormEqualTrans in H2; eauto.
    split; eapply MorePreciseThanImprecise; apply eq.
Qed.

Lemma SubstGFormVarExprDet : forall x e, GDeterministic (SubstGFormVarExpr x e).
Proof.
  intro. intro.
  apply PrimitiveLiftDet.
  - intro. intros.
    eapply SubstFormVarExprDet; eauto.
  - intro. intros. eapply MonotoneSubstFormVarExpr; eauto.
Qed.

Lemma GFormAndDet : forall phi, GDeterministic (GFormAnd phi).
Proof.
  intro.
  apply PrimitiveLiftDet.
  - intro. intros.
    subst.
    auto.
  - intro. intros.
    subst.
    eapply ImpliesAnd; auto.
Qed.


Lemma LookupGMethodDet : forall m m1 m2, LookupGMethod m m1 -> LookupGMethod m m2 -> m1 = m2.
Proof.
  intro. intro. intro. intro l1. intro l2.
  unfold LookupGMethod in *. unf.
  apply H0 in H1. auto.
Qed.

Check SubstFormVarExprSatisfiable.
Lemma SubstGFormVarExprGSatisfiable : ∀ x e phi phi', SubstGFormVarExpr x e phi phi' → GSatisfiable phi' → GSatisfiable phi.
Proof.
  intro. intro. intro. intro. intro s. intro sat.
  inv sat. inv H.
  inv s; inv H0; try (eex; fail).
  eapply SubstFormVarExprSatisfiable in H; eauto.
  eex.
Qed.

Lemma XGFormEqualSamePrec : forall a b, (GFormEqual a b ∨ ¬ GSatisfiable a ∧ ¬ GSatisfiable b) -> (IsPrecise a <-> IsPrecise b).
Proof.
  intros. inv H.
  - inv H0.
    split; intro c; inv c.
    * apply MorePreciseThanPrecise in H1. subst. eex.
    * apply MorePreciseThanPrecise in H. subst. eex.
  - unf.
    split; intro c; inv c.
    * destruct b.
      + eex.
      + contradict H1. eex.
    * destruct a.
      + eex.
      + contradict H. eex.
Qed.

Lemma NotGSatisfiable : forall g, ¬ GSatisfiable g -> exists p, g = GFormPrecise p /\ ~ Satisfiable p.
Proof.
  intros.
  destruct g.
  - eex.
    intro c.
    contradict H.
    eex.
  - contradict H.
    eex.
Qed.

Definition MonotonePred (p : Set_Formula -> Prop) := forall p1 p2, Implies p1 p2 -> p p1 -> p p2.

(* validity *)

Definition GFreeVarForm x gp := exists p, Static gp p /\ FreeVarForm x p.

Definition ValidGMethod : Set_GMethod -> Prop := fun m =>
match m with
| GMethod _ _ _ i c s =>
  match c with
  | GContract phi1 phi2 =>
    (forall x', GFreeVarForm x' phi1 -> x' = (VarIdent i)) /\
    (forall x', GFreeVarForm x' phi2 -> x' = (VarOldIdent i) \/ x' = VarResult) /\
    (exists phi'' phi', GWP s phi2 phi'' /\ SubstGFormVarExpr (VarOldIdent i) (ExprVar (VarIdent i)) phi'' phi' /\ GImplies phi1 phi') /\
    GImplies phi2 (GFormPrecise (FormCompOp CompOpEq (ExprVar VarResult) (ExprVar VarResult)))
  end
end.

Definition ValidGProgram : Set_GProgram -> Prop := fun p =>
match p with
| GProgram ms s =>
  (exists phi, GWP s (GFormPrecise FormTrue) phi /\ GImplies (GFormPrecise FormTrue) phi) /\
  (forall m, In m ms -> ValidGMethod m)
end.

(* static gradual guarantee *)

Lemma GImpliesMorePreciseThan : forall g1 g2 gr, MorePreciseThan g1 g2 -> GImplies g1 gr -> GImplies g2 gr.
Proof.
  intros.
  apply LiftingGImplies. apply LiftingGImplies in H0.
  inv H. inv H0. unf. eapply GammaDet in H1; eauto. eex. apply H3. apply H1. assumption.
Qed.

Theorem StaticGradGuarantee : forall gp1 gp2, GProgramMorePreciseThan gp1 gp2 -> ValidGProgram gp1 -> ValidGProgram gp2.
Proof.
  intro. intro. intro mpt. intro val.
  inv mpt. unf.
  inv val. ctor; auto. clear H.
  generalize x x0 H0 H1. clear. induction x; intro; intro li; intro fa; intro; intro inn.
    inv li. inv inn.
  destruct x0; inv inn.
  - lapply (fa a). Focus 2. ctor. auto.
    intro va. clear fa IHx.
    assert (GMethodMorePreciseThan a m) as mpt.
      inv li. assumption.
    clear li.
    inv mpt. unf.
    inv H0. unf.
    inv va. unf.
    split.
      intro. intro fv. apply H0.
      destruct x9.
        apply MorePreciseThanPrecise in H. subst. assumption.
        apply MorePreciseThanImprecise2 in H. unf. inv fv. inv H8. inv H10. eapply ImpliesFreeVarForm in H9; eauto. eex.
    split.
      intro. intro fv. apply H3.
      destruct x11.
        apply MorePreciseThanPrecise in H1. subst. assumption.
        apply MorePreciseThanImprecise2 in H1. unf. inv fv. inv H8. inv H10. eapply ImpliesFreeVarForm in H9; eauto. eex.
    split.
      eapply GWpXMonotone in H4; eauto. unf.
      eapply XMonotoneSubstGFormVarExpr in H2; eauto. unf.
      exists x12. exists x13.
      repeat split; try assumption.
      apply XMorePreciseMoreImplies in H9. apply H9.
      eapply GImpliesMorePreciseThan; eauto.
    eapply GImpliesMorePreciseThan; eauto.
  - inv li.
    eapply IHx; eauto.
    intro. intro inn. apply fa. intuition.
Qed.


(* DYNAMICS *)

(* diff (note: swapped parameter order compated to paper) *)

Definition AntiMonotone (f : Set_Formula -> Set_Formula -> Prop) := ∀ (phi1 phi2 phi1' phi2' : Set_Formula),
       f phi1 phi1' → f phi2 phi2'
       → Implies phi1 phi2 → Implies phi2' phi1'.

(* DIFF: can be approximation. the worse, the more runtime checks *)
Definition DefDiff (diff : Set_Formula -> Set_Formula -> Set_Formula -> Prop) : Prop :=
  forall pd pa, exists pb, diff pd pa pb.
Definition ValidDiff (diff : Set_Formula -> Set_Formula -> Set_Formula -> Prop) : Prop :=
  forall pd pa pb, diff pd pa pb -> Implies (FormAnd pd pb) pa /\ Implies pa pb.
Definition MonotoneDiff (diff : Set_Formula -> Set_Formula -> Set_Formula -> Prop) : Prop :=
  forall pd, Monotone (diff pd) /\ AntiMonotone (fun x => diff x pd).

Definition LiftDiff (diff : Set_Formula -> Set_Formula -> Set_Formula -> Prop)
                     (gpd gpa gpb : Set_GFormula) : Prop :=
  exists pd, Static gpd pd /\ PrimitiveLift (diff pd) gpa gpb.

Parameter diff : Set_Formula -> Set_Formula -> Set_Formula -> Prop.
Axiom diffValid : DefDiff diff /\ ValidDiff diff /\ MonotoneDiff diff.
Lemma diffExists : exists d, DefDiff d /\ ValidDiff d /\ MonotoneDiff d.
Proof.
  exists (fun a b c => b = c).
  repeat split.
  - intro. intro. eex.
  - subst. intro. intro ef. inv ef. assumption.
  - subst. auto.
  - intro. intro. intro. intro. intro. intro s. subst. intro s. subst. auto.
  - intro. intros. subst. auto.
Qed.

Definition gdiff := LiftDiff diff.

Lemma gdiffTotal : forall pd pa, exists pb, gdiff pd pa pb.
Proof.
  intros.
  assert (tot := StaticTotal pd). unf.
  assert (tot := StaticTotal pa). unf.
  assert (exists pb, diff x x0 pb) as ee. apply diffValid. unf.
  destruct pa; inv H0.
  - eex.
  - assert (Satisfiable x1) as sat.
      assert (val := diffValid). unf. eapply H3 in H1. unf.
      inv sat0. eex.
    exists (GFormImprecise x1 sat).
    ctor. split. eauto.
    ctor; eauto.
Qed.

Lemma diffWeakens : forall p1 p2 p3, diff p1 p2 p3 -> Implies p2 p3.
Proof.
  intro. intro. intro. intro gd. apply diffValid in gd.
  unf. assumption.
Qed.

Lemma gdiffWeakens : forall p1 p2 p3, gdiff p1 p2 p3 -> forall rho, EvalGFormula rho p2 -> EvalGFormula rho p3.
Proof.
  intro. intro. intro. intro gd. intro. intro ef.
  inv gd. unf. inv H1.
  - inv ef. unf. inv H2. ctor. split; eauto.
    eapply diffWeakens; eauto.
  - inv ef. unf. inv H3. ctor. split; eauto.
    eapply diffWeakens; eauto.
  - inv ef. unf. inv H3.
    assert (tot := StaticTotal p3). unf.
    ctor. split; eauto.
    eapply GFormEqualSameStatic in H2; eauto. apply H2.
    eapply diffWeakens; eauto.
Qed.

Lemma diffConjunction : forall p1 p2 p3, diff p1 p2 p3 -> Implies (FormAnd p1 p3) p2.
Proof.
  intro. intro. intro. intro gd. apply diffValid in gd.
  unf. assumption.
Qed.

Lemma gdiffConjunction : forall p1 p2 p3, gdiff p1 p2 p3 -> forall rho, EvalGFormula rho p1 -> EvalGFormula rho p3 -> EvalGFormula rho p2.
Proof.
  intro. intro. intro. intro gd. intro. intro ef1. intro ef2.
  inv gd. unf. inv H1.
  - inv ef1. inv ef2. unf. inv H3. eapply StaticDet in H0; eauto. subst. ctor. split; eauto.
    eapply diffConjunction; eauto.
  - inv ef1. inv ef2. unf. inv H4. eapply StaticDet in H0; eauto. subst. ctor. split; eauto.
    eapply diffConjunction; eauto.
  - inv ef1. inv ef2. unf. eapply StaticDet in H0; eauto. subst. ctor. split; eauto.
    eapply GFormEqualSameStatic in H2; eauto. apply H2 in H5.
    eapply diffConjunction; eauto.
Qed.

(* GSP: can be approximation. the worse, the more runtime checks *)
Definition DefGSPCall (gspc : Set_Var -> Set_MethodName -> Set_Var -> Set_GFormula -> Set_GFormula -> Prop) : Prop :=
  forall y m x pa pb, GWP (StmtCall y m x) pb pa -> exists pb, gspc y m x pa pb.
Definition ValidGSPCall (gspc : Set_Var -> Set_MethodName -> Set_Var -> Set_GFormula -> Set_GFormula -> Prop) : Prop :=
  forall y m x pa pb, gspc y m x pa pb -> (forall pa', GWP (StmtCall y m x) pb pa' -> GImplies pa pa') /\ (forall pb', GWP (StmtCall y m x) pb' pa -> MoreImpliesThan pb' pb).
Definition MonotoneGSPCall (gspc : Set_Var -> Set_MethodName -> Set_Var -> Set_GFormula -> Set_GFormula -> Prop) : Prop :=
  forall y m x, MonotoneGFunction1 (gspc y m x).

Parameter GSPCall : Set_Var -> Set_MethodName -> Set_Var -> Set_GFormula -> Set_GFormula -> Prop.
Axiom GSPCallValid : DefGSPCall GSPCall /\ ValidGSPCall GSPCall /\ MonotoneGSPCall GSPCall.
Lemma gspExists : exists d, DefGSPCall d /\ ValidGSPCall d /\ MonotoneGSPCall d.
Proof.
  exists (fun y m x pa pb => pb = Unknown /\ exists pa', GWP (StmtCall y m x) pb pa' /\ GImplies pa pa').
  repeat split.
  - intro. intro. intro. intro. intro. intro gw. exists Unknown. split; auto.
    apply (GWpXMonotone _ _ Unknown) in gw.
    * unf. eex.
      apply XMorePreciseMoreImplies in H1.
      apply H1.
      apply GImpliesRefl.
    * clac (GSatisfiable pb).
      + apply MorePreciseXMorePrecise.
        apply MorePreciseThanImprecise2.
        inv H. unf.
        eex.
        intro. intro. ctor.
      + apply or_intror. apply or_intror.
        split. auto.
        intro c. inv c. inv H0.
  - unf. intros.
    (* monotone/deteministic *)
    admit.
  - unf. intros.
    reduce.
    destruct gp.
    * ctor. ctor.
      intro. intros. ctor.
    * ctor. eauto. eauto. ctor.
      intro. intros. ctor.
  - intro. intro. intro. intro. intro. intro mpt. intro. intros.
    unf.
    eexists. repeat split.
    * eex.
      eapply GImpliesMorePreciseThan; eauto.
    * auto.
Admitted.

Inductive StackGWP : list Set_Stmt -> Set_GFormula -> list Set_GFormula -> Prop :=
| StackGWpMain : ∀ (s : Set_Stmt) (phi : Set_GFormula) (phi' : Set_GFormula),
  GWP s phi phi' ->
  StackGWP [s] phi [phi']
| StackGWpCall : ∀ (s s' _s : Set_Stmt) (S : list Set_Stmt) (phi _phi1 phi2 phi' : Set_GFormula) (phi'' : list Set_GFormula) (x y : Set_Var) _i (m : Set_MethodName) (_T1 _T2 : Set_Type),
  LookupGMethod m (GMethod _T1 m _T2 _i (GContract _phi1 phi2) _s) ->
  GWP s phi2 phi' ->
  FirstStmt s' (StmtCall y m x) ->
  StackGWP (s' :: S) phi phi'' ->
  StackGWP (s :: s' :: S) phi (phi' :: phi'')
.

Lemma ConsStmtDomain : forall s, (exists a b, ConsStmt s a b) <-> s <> StmtSkip.
Proof.
  induction s; split; intro hyp;
  try congruence.
  - unf.
    inv H0.
    congruence.
  - eex.
    ctor.
    * congruence.
    * intros.
      congruence.
  - eex.
    ctor.
    * congruence.
    * intros.
      congruence.
  - eex.
    ctor.
    * congruence.
    * intros.
      congruence.
  - clac (s1 = StmtSkip).
    * subst.
      eex.
    * apply IHs1 in H.
      clear IHs1 IHs2.
      unf.
      eex.
Qed.

Inductive GStep : Set_State -> option Set_State -> Prop :=
| GStepLocal : ∀ p' (s s' : Set_Stmt) (rho rho' : Set_VarEnv) (S : Set_Stack),
  Step
    p' (*irrelevant for local steps*)
    (StackCons (StackFrame rho' s') S)
    (StackCons (StackFrame rho s) S) ->
  @GStep
    (StackCons (StackFrame rho' s') S)
    (Some (StackCons (StackFrame rho s) S))
| GStepCall : ∀ (r : Set_Stmt) (phi : Set_GFormula) (rho rho' : Set_VarEnv) (S : Set_Stack) (x y : Set_Var) (i : Set_Ident) (v : Set_Val) (m : Set_MethodName) (_T1 _T2 : Set_Type) (_phi : Set_GFormula) gg gg' S1 S2,
  (* additional check *)
  GWP r _phi gg ->
  gdiff phi gg gg' ->
  EvalGFormula rho' gg' ->

  LookupGMethod m (GMethod _T1 m _T2 i (GContract phi _phi) r) ->
  EvalVar rho x v ->
  rho' = VarEnvMapping (VarOldIdent i) v (VarEnvMapping (VarIdent i) v VarEnvFresh) ->
  EvalGFormula rho' phi ->
  ConsStmt S1 S2 (StmtCall y m x) ->
  GStep
    (StackCons (StackFrame rho S1) S)
    (Some (StackCons (StackFrame rho' r) (StackCons (StackFrame rho S1) S)))
| GStepCallErr : ∀ (r : Set_Stmt) (phi : Set_GFormula) (rho rho' : Set_VarEnv) (S : Set_Stack) (x y : Set_Var) (i : Set_Ident) (v : Set_Val) (m : Set_MethodName) (_T1 _T2 : Set_Type) (_phi : Set_GFormula) gg gg' S1 S2,
  (* additional check *)
  GWP r _phi gg ->
  gdiff phi gg gg' ->
  ~ EvalGFormula rho' gg' ->

  LookupGMethod m (GMethod _T1 m _T2 i (GContract phi _phi) r) ->
  EvalVar rho x v ->
  rho' = VarEnvMapping (VarOldIdent i) v (VarEnvMapping (VarIdent i) v VarEnvFresh) ->
  EvalGFormula rho' phi ->
  ConsStmt S1 S2 (StmtCall y m x) ->
  GStep
    (StackCons (StackFrame rho S1) S)
    None
| GStepCallFinish : ∀ (_r : Set_Stmt) (phi : Set_GFormula) (rho rho' : Set_VarEnv) (S : Set_Stack) (x y : Set_Var) (i : Set_Ident) (v  : Set_Val) (m : Set_MethodName) (T _T : Set_Type) (_phi : Set_GFormula) gg ggs gg' gg'' gg''' Sr Ss S1 S2,
  (* additional check *)
  StateExtract S Sr Ss ->
  StackGWP (S2 :: Ss) (GFormPrecise FormTrue) (gg :: ggs) ->
  GWP (StmtCall y m x) gg gg'' ->
  GSPCall y m x gg'' gg''' ->
  gdiff gg''' gg gg' ->
  EvalGFormula (VarEnvMapping y v rho) gg' ->

  LookupGMethod m (GMethod T m _T i (GContract _phi phi) _r) ->
  EvalVar rho' VarResult v ->
  EvalGFormula rho' phi ->
  ConsStmt S1 S2 (StmtCall y m x) ->
  GStep
    (StackCons (StackFrame rho' StmtSkip) (StackCons (StackFrame rho S1) S))
    (Some (StackCons (StackFrame (VarEnvMapping y v rho) S2) S))
| GStepCallFinishErr : ∀ (_r : Set_Stmt) (phi : Set_GFormula) (rho rho' : Set_VarEnv) (S : Set_Stack) (x y : Set_Var) (i : Set_Ident) (v  : Set_Val) (m : Set_MethodName) (T _T : Set_Type) (_phi : Set_GFormula) gg ggs gg' gg'' gg''' Sr Ss S1 S2,
  (* additional check *)
  StateExtract S Sr Ss ->
  StackGWP (S2 :: Ss) (GFormPrecise FormTrue) (gg :: ggs) ->
  GWP (StmtCall y m x) gg gg'' ->
  GSPCall y m x gg'' gg''' ->
  gdiff gg''' gg gg' ->
  ~ EvalGFormula (VarEnvMapping y v rho) gg' ->

  LookupGMethod m (GMethod T m _T i (GContract _phi phi) _r) ->
  EvalVar rho' VarResult v ->
  EvalGFormula rho' phi ->
  ConsStmt S1 S2 (StmtCall y m x) ->
  GStep
    (StackCons (StackFrame rho' StmtSkip) (StackCons (StackFrame rho S1) S))
    None
.

(* soundness *)

(* WP of next step satisfied *)
Definition LocallyValidGState : Set_State -> Prop := fun pi => exists rho s S phi' phi,
  pi = StackCons (StackFrame rho s) S /\
  GWP s phi' phi /\
  EvalGFormula rho phi /\
  (s = StmtSkip -> (S = StackEmpty \/ (exists s' _S rho' y m x _T1 _T2 i _phi1 phi2 _s,
                     S = StackCons (StackFrame rho' s') _S
                  /\ FirstStmt s' (StmtCall y m x)
                  /\ LookupGMethod m (GMethod _T1 m _T2 i (GContract _phi1 phi2) _s)
                  /\ EvalGFormula rho phi2)))
.

Definition FinalGState : Set_State -> Prop := fun pi => 
  pi = StackEmpty \/
  (exists rho, pi = StackCons (StackFrame rho StmtSkip) StackEmpty).

Axiom GValidity : ValidGProgram p.

Inductive ValidGStateEx : Set_GFormula -> Set_State -> Prop :=
| ValidGStateBase : forall phi' phi rho s,
  GWP s phi' phi ->
  EvalGFormula rho phi ->
  ValidGStateEx phi' (StackCons (StackFrame rho s) StackEmpty)
| ValidGStateCons : forall phi' phi rho rho' s s' S m x i v _y _T1 _T2 _r _phi1 phi2,
  GWP s' phi2 phi ->
  EvalGFormula rho' phi ->
  FirstStmt s (StmtCall _y m x) ->
  LookupGMethod m (GMethod _T1 m _T2 i (GContract _phi1 phi2) _r) ->
  EvalVar rho x v ->
  EvalVar rho' (VarOldIdent i) v ->
  ValidGStateEx phi' (StackCons (StackFrame rho s) S) ->
  ValidGStateEx phi' (StackCons (StackFrame rho' s') (StackCons (StackFrame rho s) S))
.

Definition ValidGState := ValidGStateEx (GFormPrecise FormTrue).

Definition ValidGStateClassic : Set_State -> Prop := fun pi => exists rhos ss phis,
  StateExtract pi rhos ss /\
  StackGWP ss (GFormPrecise FormTrue) phis /\
  Forall2 EvalGFormula rhos phis
.

Lemma ValidGStateClassicness : forall pi, ValidGState pi -> ValidGStateClassic pi.
Proof.
  induction pi; intro vs; inv vs.
  - exists [rho]. exists [s0]. exists [phi].
    split. ctor. ctor.
    split. ctor. assumption.
    ctor. assumption.
    ctor.
  - apply IHpi in H8.
    unfold ValidGStateClassic in *.
    unf.
    exists (rho' :: x0).
    exists (s' :: x1).
    exists (phi :: x2).
    split. ctor. assumption.
    split.
    * inv H0. inv H.
      + ctor; eauto.
        ctor. assumption.
      + ctor. Focus 2. eauto.
        eauto. eauto.
        ctor; eauto.
    * ctor; auto.
Qed.

Lemma ValidGStateClassicnessRev : forall pi, ValidGStateClassic pi -> ValidGState pi.
Proof.
  induction pi; intro vs; inv vs.
  - unf. inv H0. inv H.
  - unf. inv H0. inv H.
    * inv H6. inv H2. ctor; eauto.
    * lapply IHpi.
      + intro c. inv H2.
        assert (va := c).
        inv c.
        --inv H6. ctor. eauto. eauto. eauto. eauto. admit. admit. apply va.
        --inv H6. ctor. eauto. eauto. eauto. eauto. admit. admit. apply va.
      + inv H2. ctor. eex.
Admitted.

Lemma StateExtractTotal : forall s, exists a b, StateExtract s a b.
Proof.
  induction s.
  - eex. ctor.
  - unf.
    destruct s. eex. ctor.
    eauto.
Qed.

Lemma StackWPTopSkip : forall s ss a aa c, StackGWP (s :: ss) c (a :: aa) <-> exists b, GWP s b a /\ StackGWP (StmtSkip :: ss) c (b :: aa).
Proof.
  intro. intro. intro. intro.
  split; intro hyp.
  - inv hyp.
    * eex. ctor. ctor.
    * eex. ctor; eauto.
  - unf.
    inv H1.
    * inv H4. ctor. assumption.
    * inv H7. ctor; eauto.
Qed.

Lemma ConsStmtGWP : forall s12 s1 s2, ConsStmt s12 s2 s1 -> forall a c, GWP s12 c a <-> exists b, GWP s2 c b /\ GWP s1 b a.
Proof.
  induction s12; intro; intro; intro co; inv co; intro; intro; split; intro gw;
  unf;
  try (congruence; fail);
  try (eex; fail).
  - inv H2.
    assumption.
  - inv H2.
    assumption.
  - inv H2.
    assumption.
  - inv gw.
    eapply IHs12_1 in H5; eauto.
    unf.
    eex.
  - inv H0.
    ctor; eauto.
    eapply IHs12_1; eauto.
  - inv gw.
    eex.
  - ctor; eauto.
Qed.

Lemma StackWPTopConsStmt : forall s s1 s2 ss a aa c, ConsStmt s s1 s2 ->
  StackGWP (s :: ss) c (a :: aa) <-> exists b, GWP s2 b a /\ StackGWP (s1 :: ss) c (b :: aa).
Proof.
  intro. intro. intro. intro. intro. intro. intro. intro cons.
  split; intro hyp.
  - inv hyp.
    * eapply ConsStmtGWP in H2; eauto. unf.
      eex. ctor. assumption.
    * eapply ConsStmtGWP in H5; eauto. unf.
      eex. ctor; eauto.
  - unf.
    inv H1.
    * ctor.
      generalize s s1 s2 c a x H0 H4 cons. clear.
      induction s; intro; intro; intro; intro; intro; intro yy; intro xx; intro con.
      + inv con.
        congruence.
      + inv con.
        inv xx.
        assumption.
      + inv con.
        inv xx.
        assumption.
      + inv con.
        inv xx.
        assumption.
      + inv con.
        --specialize (H0 s1 s2).
          congruence.
        --inv xx.
          ctor; eauto.
        --ctor; eauto.
    * ctor; eauto.
      generalize s s1 s2 phi2 a x H0 H7 cons. clear.
      induction s; intro; intro; intro; intro; intro; intro yy; intro xx; intro con.
      + inv con.
        congruence.
      + inv con.
        inv xx.
        assumption.
      + inv con.
        inv xx.
        assumption.
      + inv con.
        inv xx.
        assumption.
      + inv con.
        --specialize (H0 s1 s2).
          congruence.
        --inv xx.
          ctor; eauto.
        --ctor; eauto.
Qed.

Lemma FirstStmtCons : forall s12 s1, (s12 <> StmtSkip \/ s1 <> StmtSkip) -> FirstStmt s12 s1 -> exists s2, ConsStmt s12 s2 s1.
Proof.
  induction s12; intro; intro sk; intro fi.
  - inv sk.
    * congruence.
    * inv fi.
      congruence.
  - inv fi.
    eex.
    ctor; congruence.
  - inv fi.
    eex.
    ctor; congruence.
  - inv fi.
    eex.
    ctor; congruence.
  - inv fi.
    * contradict H.
      eex.
    * clac (s12_1 = StmtSkip).
      + subst.
        inv H2.
        eex.
      + apply IHs12_1 in H2; auto.
        unf.
        eex.
Qed.

Proposition ValidGStateTopMost : ∀ pi p sf,
  ValidGStateEx p (StackCons sf pi) ->
  exists p', ValidGStateEx p' (StackCons sf StackEmpty).
Proof.
  induction pi; intros.
  - eex.
  - inv H.
    eex. ctor; eauto.
Qed.

Lemma PrimitiveLiftStatic : forall f g1 g2, PrimitiveLift f g1 g2 -> exists p1 p2 p2', Static g1 p1 /\ Static g2 p2 /\ FormEqual p2 p2' /\ f p1 p2'.
Proof.
  intro. intro. intro. intro pl.
  inv pl.
  - eex.
  - eex.
  - assert (tot := StaticTotal g2). unf.
    eapply GFormEqualSameStatic in H0; eauto.
    exists phi1. exists x. exists phi2.
    repeat split; auto; apply H0.
Qed.ObservablyIdenticalVarEnvEvalFormula

Lemma GProgress : ∀ (pi : Set_State),
  ValidGState pi ->
  ~ FinalGState pi ->
  (exists pi', GStep pi pi').
Proof.
  destruct pi as [ | frame]; intro valid; intro not_final.
  - contradict not_final.
    reduce.
    auto.
  - destruct frame as [rho s].
    induction s.
    * destruct pi.
      + contradict not_final.
        reduce.
        eauto.
      + clear not_final.
        inv valid. inv H3.
        apply ValidGStateClassicness in H10. inv H10. unf.
        inv H0.
        destruct x2; try (inv H; fail).
        apply StackWPTopSkip in H. unf.
        apply FirstStmtCons in H5. Focus 2. apply or_intror. congruence. unf.

        eapply ConsStmtGWP in H; eauto. unf.

        assert (exists g, GSPCall _y m x s g) as def.
          apply GSPCallValid in H5. assumption.
        unf.
        assert (tot := gdiffTotal x4 x3). unf.
        assert (exists v, EvalVar rho VarResult v) as resDef.
          admit. (* validity criterion: each ex. path needs return statement => will be initialized... *)
        unf.
        clac (EvalGFormula (VarEnvMapping _y x6 rho0) x5).
        --eexists; eapply GStepCallFinish.
          Focus 1. eauto.
          Focus 2. eauto.
          Focus 2. eauto.
          Focus 2. eauto.
          Focus 2. eauto.
          Focus 2. eauto.
          Focus 2. eauto.
          Focus 2. eauto.
          Focus 2. eauto.
          eapply StackWPTopSkip. eex.
        --eexists; eapply GStepCallFinishErr.
          Focus 1. eauto.
          Focus 2. eauto.
          Focus 2. eauto.
          Focus 2. eauto.
          Focus 2. eauto.
          Focus 2. eauto.
          Focus 2. eauto.
          Focus 2. eauto.
          Focus 2. eauto.
          eapply StackWPTopSkip. eex.
    * clear not_final.
      apply ValidGStateTopMost in valid. unf.
      inv H.
      inv H3.
      assert (EvalFormula rho (FormCompOp CompOpEq s0 s0)) as ev.
        inv H7; inv H4; inv H.
          inv H0. inv H3. assumption.
          inv H3. inv H4. assumption.
          eapply GFormEqualSameStatic in H0; eauto. apply H0 in H4. inv H4. assumption.
      inv ev.
      eexists.
      eapply GStepLocal.
      eapply StepVarAssign.
      apply H6.
    * clear not_final.
      apply ValidGStateTopMost in valid. unf.
      inv H.
      inv H3.

      assert (va := GValidity). unfold ValidGProgram in va.
        assert (lookup := H7).
        inv lookup. unfold LookupGMethodAmbig in H.
        destruct p. unf.
        apply H10 in H1. inv H1. unf.

      assert (tot := gdiffTotal phi1 x1). unf.
      clear H3 H0 H H14.
      assert (EvalFormula rho (FormCompOp CompOpEq (ExprVar s1) (ExprVar s1))) as ev.
        inv H13. clac x4; intuition; unf; inv H4.
          inv H13. inv H4. inv H21. assumption.
          inv H13. inv H4. inv H14. assumption.
      assert (exists v, EvalVar rho s1 v).
        inv ev. inv H20. eex.
      clear ev.
      unf.

      assert (EvalGFormula (VarEnvMapping (VarOldIdent i) x4 (VarEnvMapping (VarIdent i) x4 VarEnvFresh)) phi1) as ef.
        apply PrimitiveLiftStatic in H8.
        apply PrimitiveLiftStatic in H9.
        apply PrimitiveLiftStatic in H12.
        unf. ctor. split. eauto.
        apply SwapVarEnvEvalFormula; try congruence.
        assert (subst := H20).
        eapply SubstFormSemantics in H20; eauto. Focus 2. ctor. eauto.
        assert (EvalFormula rho x12) as eff.
          inv H13. clac x14; intuition; unf.
            inv H20. unf. inv H27. eapply StaticDet in H9; eauto. subst. apply H37. inv H4. unf. inv H4. inv H27. assumption.
            eapply StaticDet in H9; eauto. subst. inv H4. unf. inv H4. inv H27. assumption.
        apply H12 in eff. (* FormEqual *)
        apply H20 in eff. clear H20.
        rewrite (ObservablyIdenticalVarEnvEvalFormula [(VarIdent i)]); eauto.
          intro gx. intro ingx. inv ingx; try (intuition; fail). intro v. split; intro ev; inv ev; try (intuition; fail); ctor.
          intro gx. intro fv. ctor. symmetry. apply H11. eex.

      clac (EvalGFormula (VarEnvMapping (VarOldIdent i) x4 (VarEnvMapping (VarIdent i) x4 VarEnvFresh)) x3).
      
      + eexists.
        eapply GStepCall.
          Focus 4. eauto.
          Focus 5. eauto.
          Focus 6. ctor; congruence.
          eauto.
          eauto.
          Focus 2. eauto.
          Focus 2. eauto.
          eauto.
      + eexists.
        eapply GStepCallErr.
          Focus 4. eauto.
          Focus 5. eauto.
          Focus 6. ctor; congruence.
          eauto.
          eauto.
          Focus 2. eauto.
          Focus 2. eauto.
          eauto.
    * clear not_final.
      apply ValidGStateTopMost in valid. unf.
      inv H.
      inv H3.
      eexists.
      eapply GStepLocal.
      eapply StepAssert.
      inv H4. unf.
      inv H0.
      + inv H1. inv H2. assumption.
      + inv H1. inv H2. assumption.
      + eapply GFormEqualSameStatic in H3; eauto. apply H3 in H2. inv H2. assumption.
    * admit. (* by design *)
Admitted.

Lemma StateExtractDet : forall s a1 a2 b1 b2, StateExtract s a1 b1 -> StateExtract s a2 b2 -> a1 = a2 /\ b1 = b2.
Proof.
  induction s; intro; intro; intro; intro; intro s1; intro s2; inv s1; inv s2.
  - auto.
  - eapply IHs in H3; eauto. unf. subst.
    auto.
Qed.

Proposition GPreservation : ∀ (pi pi' : Set_State),
  GStep pi (Some pi') ->
  ValidGState pi ->
  ValidGState pi'.
Proof.
  intro. intro. intro step. intro valid.
  inv step; subst.
  - generalize s' rho' s rho valid H1. clear. induction s'; intro; intro; intro; intro; intro step; inv step.
    * apply RecStack1 in H4. intuition.
    * symmetry in H3. apply RecStack1 in H3. intuition.
    * apply ValidGStateClassicnessRev.
      apply ValidGStateClassicness in valid. inv valid. unf. inv H1.
      destruct x1. inv H3.
      rewrite StackWPTopSkip in H; eauto. unf.
      inv H. inv H3.
      eex. ctor. eauto.
      ctor; auto.
      apply PrimitiveLiftStatic in H6. unf.
      apply PrimitiveLiftStatic in H10. unf. inv H7. unf. eapply StaticDet in H4; eauto. eapply StaticDet in H; eauto. subst. apply H10 in H13. inv H13.
      eex. apply H3 in H15.
      eapply SubstFormSemantics; eauto.
    * apply RecStack1 in H4. intuition.
    * apply RecStack1 in H4. intuition.
    * apply ValidGStateClassicnessRev.
      apply ValidGStateClassicness in valid. inv valid. unf. inv H1.
      destruct x1. inv H3.
      rewrite StackWPTopSkip in H; eauto. unf.
      inv H. inv H3.
      eex. ctor. eauto.
      ctor; auto.
      apply PrimitiveLiftStatic in H4. unf. inv H6. unf. eapply StaticDet in H; eauto. subst. apply H3 in H6. inv H6.
      eex.
    * apply RecStack1 in H4. intuition.
    * apply ValidGStateClassicnessRev.
      apply ValidGStateClassicness in valid. inv valid. unf. inv H0.
      destruct x1. inv H2.
      rewrite StackWPTopConsStmt in H; eauto. unf.
      inv H.
      eex.
      ctor. assumption.
    * apply RecStack1 in H4. intuition.
    * admit. (* inductively *)
  - ctor; eauto.
    * eapply gdiffConjunction in H1; eauto.
    * eapply ConsStmtFirst. eauto.
    * ctor.
  - inv valid. inv H14.
    apply ValidGStateClassicness in H21. inv H21. unf. inv H9. 
    apply ValidGStateClassicnessRev.
    destruct x3. inv H12.
    rewrite StackWPTopConsStmt in H; eauto. unf.
    eexists. eexists. eexists.
    split. ctor. eauto.
    split. eauto.
    inv H12. ctor; auto.

    eapply StateExtractDet in H0; eauto. unf. subst.
    assert (gg = x1). admit. (* StackGWP deterministic *)
    assert (gg'' = s). admit. (* GWP deterministic *)
    subst.

    eapply gdiffConjunction; eauto.
    apply GSPCallValid in H3. unf. apply H9 in H.
    admit. (* by def (same as non-gradual...) *)
Admitted.

End GSemantics.

Lemma LookupGMethodCoincidesWithLookupMethodAmbig : forall p p', ConvertProgram p p' ->
  forall m T1 T2 m' i phi1 phi2 s,
            LookupMethodAmbig p m (Method T1 m' T2 i (Contract phi1 phi2) s) <->
            LookupGMethodAmbig p' m (GMethod T1 m' T2 i (GContract (GFormPrecise phi1) (GFormPrecise phi2)) s).
Proof.
  intro. intro. intro co.
  inv co.
  intro. intro. intro. intro. intro. intro. intro. intro.
  generalize m1 m2 H. clear m1 m2 H.
  induction m1; intro m2; intro li; inv li;
  split; intro lm; inv lm; inv H.
  * destruct x2.
    (* typ *) destruct T1. destruct T2. destruct s1. destruct s3.
    inv H1.
    inv H0. inv H2. inv H5.
    repeat ctor; auto.
  * ctor; auto.
    apply in_cons.
    apply IHm1; auto.
    ctor; auto.
  * destruct a.
    (* typ *) destruct T1. destruct T2. destruct s1. destruct s3.
    inv H1.
    inv H0. inv H4. inv H5.
    repeat ctor; auto.
  * ctor; auto.
    apply in_cons.
    apply IHm1 in H3. symmetry in H3. apply H3.
    ctor; auto.
Qed.

Lemma LookupGMethodAmbigPrecise : forall p p', ConvertProgram p p' ->
  forall m T1 T2 m' i gphi1 gphi2 s,
    LookupGMethodAmbig p' m (GMethod T1 m' T2 i (GContract gphi1 gphi2) s) ->
    exists phi1 phi2, gphi1 = (GFormPrecise phi1) /\ gphi2 = (GFormPrecise phi2).
Proof.
  intro. intro. intro co.
  inv co.
  intro. intro. intro. intro. intro. intro. intro. intro.
  generalize m1 m2 H. clear m1 m2 H.
  induction m1; intro m2; intro li; inv li; intro lm.
  - inv lm. inv H.
  - inv lm. inv H.
    * inv H1. inv H2. inv H4. inv H5.
      eex.
    * eapply IHm1; eauto.
      ctor; auto.
Qed.

Lemma LookupGMethodCoincidesWithLookupMethod : forall p p', ConvertProgram p p' ->
  forall m T1 T2 m' i phi1 phi2 s,
            LookupMethod p m (Method T1 m' T2 i (Contract phi1 phi2) s) ->
            LookupGMethod p' m (GMethod T1 m' T2 i (GContract (GFormPrecise phi1) (GFormPrecise phi2)) s).
Proof.
  intro. intro. intro co.
  intro. intro. intro. intro. intro. intro. intro. intro.
  intro lm. inv lm.
  ctor.
  - eapply LookupGMethodCoincidesWithLookupMethodAmbig; eauto.
  - intro. intro lo.
    destruct m'0. destruct s4.
    assert (lox := lo). eapply LookupGMethodAmbigPrecise in lox; eauto. unf.
    eapply LookupGMethodCoincidesWithLookupMethodAmbig in lo; eauto.
    apply H0 in lo. inv lo.
    (* typ *) destruct T1. destruct T2. destruct s0. destruct s2.
    auto.
Qed.

Theorem GWpCoincidesWithWp : forall p p', ConvertProgram p p' -> forall s p1 p2, WP p s p1 p2 -> GWP p' s (GFormPrecise p1) (GFormPrecise p2).
Proof.
  intro. intro. intro co.
  induction s; intro; intro; intro wp; inv wp.
  - ctor.
  - ctor.
    * assumption.
    * ctor. eauto.
    * ctor. auto.
  - eapply LookupGMethodCoincidesWithLookupMethod in H5; eauto.
    ctor; eauto.
    * ctor. eauto.
    * ctor. eauto.
    * ctor. eauto.
    * eexists. split. eauto.
      split.
      + introc x. eexists. split; eauto.
        repeat split.
        --apply H11.
        --ctor. ctor. apply H11.
        --eexists. ctor. ctor. eauto. ctor. ctor. apply H11.
        --intro. intro aa. unf. apply H11.
          split. assumption.
          split. inv H1. inv H12. assumption.
          inv H8. inv H9. inv H8. assumption.
      + intro nope. contradict nope. eex.
  - ctor. ctor. auto.
  - ctor.
    * apply IHs2. eauto.
    * apply IHs1. auto.
Qed.

Theorem GStepCoincidesWithStep : forall p p', ValidProgram p p -> ConvertProgram p p' -> forall s1 s2, Step p s1 s2 -> GStep p' s1 (Some s2).
Proof.
  intro. intro. intro va. intro co.
  induction s1; intro; intro st; inv st.
  - ctor. ctor.
  - ctor. ctor. assumption.
  - ctor. ctor. assumption.
  - assert (ValidMethod p (Method _T1 m _T2 i (Contract phi _phi) r)) as vam.
      reduce in va. inv H1. reduce in H. destruct p. unf. apply H5 in H1. assumption.
    inv vam. unf.
    unf. rename H5 into WPexists.
    assert (tot := gdiffTotal (GFormPrecise phi) (GFormPrecise x0)). unf. rename H5 into tot.

    ctor.
    Focus 6. eauto.
    Focus 4. eapply LookupGMethodCoincidesWithLookupMethod in H1; eauto.
    Focus 5. exists phi. eauto.
    Focus 5. eauto.
    Focus 4. assumption.
    Focus 1. eapply GWpCoincidesWithWp; eauto.
    Focus 1. eauto.
    eapply gdiffWeakens; eauto.
    (* implied by precondition *)
    apply H9 in H4.
    ctor. split; eauto.
    eapply SubstFormSemantics in H4; eauto.
    Focus 2. ctor. ctor. congruence. ctor.
    assert (fvu := FreeVarFormUpperBound x0). unf.
    eapply (ObservablyIdenticalVarEnvEvalFormula x3); eauto.
    clear. intro. intro inn. intro.
    split; intro ev; inv ev.
    * ctor.
    * ctor. assumption. ctor. assumption. assumption.
    * ctor.
    * inv H5. contradict H4. auto. ctor. assumption. assumption.
  - admit. (* analogous to above *)
  - ctor. ctor; eauto.
Admitted.

(* dynamic gradual guarantee *)

Lemma GProgramMorePreciseThanLookup : forall gp1 gp2, GProgramMorePreciseThan gp1 gp2
    -> forall T1 m m0 T2 i p1 p2 s, LookupGMethod gp1 m (GMethod T1 m0 T2 i (GContract p1 p2) s)
    -> exists p1' p2', LookupGMethod gp2 m (GMethod T1 m0 T2 i (GContract p1' p2') s) /\ MorePreciseThan p1 p1' /\ MorePreciseThan p2 p2'.
Proof.
  intro. intro. intro mpt. intro. intro. intro. intro. intro. intro. intro. intro. intro lo.
  inv mpt. unf.
  generalize x x0 H0 lo. clear.
  induction x; intro; intro li; intro lo.
  - apply except. inv lo. inv H. inv H1.
  - inv li. inv lo. inv H. inv H2.
    * inv H1. unf. inv H4. unf. inv H1. inv H. eexists. eexists. repeat split.
      + ctor.
        (* typ *) destruct x0. destruct x4. destruct T1. destruct T2. 
        eauto.
      + admit. (* no ambiguity... *)
      + ctor. eauto.
      + assumption.
    * eapply IHx in H3.
      + unf. eex.
        --inv H2. inv H4. intuition.
        --admit. (* no ambiguity... *)
      + ctor. ctor; auto.
        intro. intro lo. apply H0. inv lo. ctor; intuition.
Admitted.

Lemma MoreImpliesThanTrans : forall a b c, MoreImpliesThan a b -> MoreImpliesThan b c -> MoreImpliesThan a c.
Proof.
  intros.
  intro. intro g.
  apply H0. apply H.
  assumption.
Qed.

Theorem DynamicGradGuarantee : forall gp1 gp2, GProgramMorePreciseThan gp1 gp2 -> forall pi pi', GStep gp1 pi (Some pi') -> GStep gp2 pi (Some pi').
Proof.
  intro. intro. intro mpt. intro. intro. intro st.
  inv st.
  - ctor.
    inv H1.
    * ctor.
    * ctor. assumption.
    * ctor. assumption.
    * apply RecStack1 in H5. inv H5.
    * symmetry in H6. apply RecStack1 in H6. inv H6.
    * ctor; eassumption.
  - eapply GProgramMorePreciseThanLookup in H3; eauto. unf.
    apply MorePreciseXMorePrecise in H7. eapply GWpXMonotone in H0; eauto. unf.
    assert (exists xx, GWP gp2 r x1 xx /\ XMorePreciseThan x2 xx). admit. (* lemmas not yet connected to theorem *) unf.
    assert (exists x0x x3x xx, Static x0 x0x /\ Static x3 x3x /\ diff x0x x3x xx) as dd.
      assert (tot := StaticTotal x0). unf.
      assert (tot := StaticTotal x3). unf.
      assert (DefDiff diff) as def. apply diffValid.
      specialize (def x4 x5). unf.
      eex.
    unf.
    inv H1. unf.
    apply MorePreciseMoreImplies in H3. apply MoreImpliesThanAltEq in H3. specialize (H3 _ _ H1 H12).
    
    destruct x3; inv H10.
    * ctor.
      Focus 4. eauto.
      Focus 5. eauto.
      Focus 5. inv H6. unf. eapply StaticDet in H1; eauto. subst. apply H3 in H13. eex.
      Focus 4. eauto.
      Focus 1. eauto.
      Focus 1. ctor. split; eauto.
      Focus 1.
        ctor. split; eauto. apply diffValid in H14. apply H14. clear H14.
        apply XMorePreciseMoreImplies in H9. apply XMorePreciseMoreImplies in H11. eapply MoreImpliesThanTrans in H11; eauto.
        apply PrimitiveLiftStatic in H15. unf. apply diffValid in H16. unf.
        apply MoreImpliesThanAltEq in H11. specialize (H11 _ x5 H13). apply H11; auto.
        apply H15. ctor.
          inv H6. unf. eapply StaticDet in H1; eauto. subst. assumption.
          apply H14. inv H2. unf. eapply StaticDet in H10; eauto. subst. assumption.
      Focus 1. eauto.
    * ctor.
      Focus 4. eauto.
      Focus 5. eauto.
      Focus 5. inv H6. unf. eapply StaticDet in H1; eauto. subst. apply H3 in H13. eex.
      Focus 4. eauto.
      Focus 1. eauto.
      Focus 1. ctor. split; eauto.
      Focus 1.
        ctor. split; eauto. apply diffValid in H14. apply H14. clear H14.
        apply XMorePreciseMoreImplies in H9. apply XMorePreciseMoreImplies in H11. eapply MoreImpliesThanTrans in H11; eauto.
        apply PrimitiveLiftStatic in H15. unf. apply diffValid in H16. unf.
        apply MoreImpliesThanAltEq in H11. specialize (H11 _ x5 H13). apply H11; auto.
        apply H15. ctor.
          inv H6. unf. eapply StaticDet in H1; eauto. subst. assumption.
          apply H14. inv H2. unf. eapply StaticDet in H10; eauto. subst. assumption.
      Focus 1. eauto.
  - eapply GProgramMorePreciseThanLookup in H6; eauto. unf.
    assert (exists gg' ggs', StackGWP gp2 (S2 :: Ss) (GFormPrecise FormTrue) (gg' :: ggs') /\ XMorePreciseThan gg gg'). admit. (* lemmas not yet connected to theorem *) unf.
    assert (exists xx, GWP gp2 (StmtCall y m x) x2 xx /\ XMorePreciseThan gg'' xx). admit. (* lemmas not yet connected to theorem *) unf.
    assert (exists ggx, GSPCall y m x x4 ggx /\ MoreImpliesThan gg''' ggx). admit. (* lemmas not yet connected to theorem *) unf.

    assert (exists x5x x2x xx, Static x5 x5x /\ Static x2 x2x /\ diff x5x x2x xx) as dd.
      assert (tot := StaticTotal x5). unf.
      assert (tot := StaticTotal x2). unf.
      assert (DefDiff diff) as def. apply diffValid.
      specialize (def x6 x7). unf.
      eex.
    unf.

    destruct x2; inv H16.
    * ctor.
      Focus 7. eauto.
      Focus 7. eauto.
      Focus 8. eauto.
      Focus 1. eauto.
      Focus 1. eauto.
      Focus 1. eauto.
      Focus 1. eauto.
      Focus 3. apply MorePreciseMoreImplies in H11. apply MoreImpliesThanAltEq in H11. inv H8. unf. assert (t1 := StaticTotal x1). unf. specialize (H11 _ _ H8 H16). apply H11 in H19. eex.
      Focus 1. ctor. split; eauto.
      Focus 1.
        ctor. split; eauto.
        apply diffValid in H20. apply H20. clear H20.
        apply XMorePreciseMoreImplies in H13. apply XMorePreciseMoreImplies in H15.
        apply MoreImpliesThanAltEq in H13.
        assert (tot := StaticTotal gg). unf. eapply H13; eauto.
        inv H5. unf.
        inv H4. unf. apply PrimitiveLiftStatic in H21. unf. eapply StaticDet in H5; eauto. eapply StaticDet in H16; eauto. subst.
        apply diffValid in H24. apply H24. clear H24.
        ctor.
          admit. (* SP supposed to hold by def *)
          apply H22. assumption.
    * ctor.
      Focus 7. eauto.
      Focus 7. eauto.
      Focus 8. eauto.
      Focus 1. eauto.
      Focus 1. eauto.
      Focus 1. eauto.
      Focus 1. eauto.
      Focus 3. apply MorePreciseMoreImplies in H11. apply MoreImpliesThanAltEq in H11. inv H8. unf. assert (t1 := StaticTotal x1). unf. specialize (H11 _ _ H8 H16). apply H11 in H19. eex.
      Focus 1. ctor. split; eauto.
      Focus 1.
        ctor. split; eauto.
        apply diffValid in H20. apply H20. clear H20.
        apply XMorePreciseMoreImplies in H13. apply XMorePreciseMoreImplies in H15.
        apply MoreImpliesThanAltEq in H13.
        assert (tot := StaticTotal gg). unf. eapply H13; eauto.
        inv H5. unf.
        inv H4. unf. apply PrimitiveLiftStatic in H21. unf. eapply StaticDet in H5; eauto. eapply StaticDet in H16; eauto. subst.
        apply diffValid in H24. apply H24. clear H24.
        ctor.
          admit. (* SP supposed to hold by def *)
          apply H22. assumption.
Admitted.
