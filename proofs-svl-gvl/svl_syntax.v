Load imports.

Inductive Set_Type :=
| TypeInt : Set_Type.
Definition Set_MethodName := string.
Definition Set_Val := Z.
Definition Set_Ident := string.
Inductive Set_Var :=
| VarResult : Set_Var
| VarIdent : Set_Ident -> Set_Var
| VarOldIdent : Set_Ident -> Set_Var.
Definition Set_BinOp := Set_Val -> Set_Val -> option Set_Val.
Definition Set_CompOp := Set_Val -> Set_Val -> bool.
Definition CompOpEq : Set_Val -> Set_Val -> bool := Zbool.Zeq_bool.

Definition DefaultValue (T : Set_Type) : Set_Val :=
  match T with
  | TypeInt => Z0
  end.

Inductive Set_Expr :=
| ExprVal : Set_Val -> Set_Expr
| ExprVar : Set_Var -> Set_Expr
| ExprBinOp : Set_BinOp -> Set_Expr -> Set_Expr -> Set_Expr.
Inductive Set_Formula :=
| FormTrue : Set_Formula
| FormCompOp : Set_CompOp -> Set_Expr -> Set_Expr -> Set_Formula
| FormAnd : Set_Formula -> Set_Formula -> Set_Formula.
Inductive Set_Stmt :=
| StmtSkip : Set_Stmt
| StmtVarAssign : Set_Var -> Set_Expr -> Set_Stmt
| StmtCall : Set_Var -> Set_MethodName -> Set_Var -> Set_Stmt
| StmtAssert : Set_Formula -> Set_Stmt
(* | StmtDeclare : Set_Type -> Set_Var -> Set_Stmt *)
| StmtSeq : Set_Stmt -> Set_Stmt -> Set_Stmt.
Inductive Set_Contract :=
| Contract : Set_Formula -> Set_Formula -> Set_Contract.
Inductive Set_Method :=
| Method : Set_Type -> Set_MethodName -> Set_Type -> Set_Ident -> Set_Contract -> Set_Stmt -> Set_Method.
Inductive Set_Program :=
| Program : (list Set_Method) -> Set_Stmt -> Set_Program.


(*dyn sem*)
Inductive Set_VarEnv :=
| VarEnvFresh : Set_VarEnv
| VarEnvMapping : Set_Var -> Set_Val -> Set_VarEnv -> Set_VarEnv.
Inductive EvalVar : Set_VarEnv -> Set_Var -> Set_Val -> Prop :=
| EVarHead : ∀ (rho : Set_VarEnv) (x : Set_Var) (v : Set_Val), EvalVar (VarEnvMapping x v rho) x v
| EVarTail : ∀ (rho : Set_VarEnv) (x : Set_Var) (v : Set_Val) (x' : Set_Var) (v' : Set_Val), x <> x' -> EvalVar rho x v -> EvalVar (VarEnvMapping x' v' rho) x v.
Inductive Set_StackFrame :=
| StackFrame : Set_VarEnv -> Set_Stmt -> Set_StackFrame.
Inductive Set_Stack :=
| StackEmpty : Set_Stack
| StackCons : Set_StackFrame -> Set_Stack -> Set_Stack.
Definition Set_State := Set_Stack.

Inductive EvalExpr : Set_VarEnv -> Set_Expr -> Set_Val -> Prop :=
| EExprVal : ∀ (rho : Set_VarEnv) (v : Set_Val), EvalExpr rho (ExprVal v) v
| EExprVar : ∀ (rho : Set_VarEnv) (x : Set_Var) (v : Set_Val),
  EvalVar rho x v ->
  EvalExpr rho (ExprVar x) v
| EExprBinOp : ∀ (rho : Set_VarEnv) (op : Set_BinOp) (e1 : Set_Expr) (e2 : Set_Expr) (v1 : Set_Val) (v2 : Set_Val) (v : Set_Val),
  EvalExpr rho e1 v1 ->
  EvalExpr rho e2 v2 ->
  op v1 v2 = Some v ->
  EvalExpr rho (ExprBinOp op e1 e2) v.

Inductive EvalFormula : Set_VarEnv -> Set_Formula -> Prop :=
| EFormTrue : ∀ (rho : Set_VarEnv), EvalFormula rho FormTrue
| EFormCompOp : ∀ (rho : Set_VarEnv) (op : Set_CompOp) (e1 : Set_Expr) (e2 : Set_Expr) (v1 : Set_Val) (v2 : Set_Val),
  EvalExpr rho e1 v1 ->
  EvalExpr rho e2 v2 ->
  op v1 v2 = true ->
  EvalFormula rho (FormCompOp op e1 e2)
| EFormAnd : ∀ (rho : Set_VarEnv) (phi1 : Set_Formula) (phi2 : Set_Formula),
  EvalFormula rho phi1 ->
  EvalFormula rho phi2 ->
  EvalFormula rho (FormAnd phi1 phi2).

(* implication *)

Definition Evaluable : Set_Expr -> Prop :=
  fun e => exists (rho : Set_VarEnv) v, EvalExpr rho e v.
Definition Satisfiable : Set_Formula -> Prop :=
  fun phi => exists (rho : Set_VarEnv), EvalFormula rho phi.
Definition Implies : Set_Formula -> Set_Formula -> Prop :=
  fun phi1 phi2 => ∀ (rho : Set_VarEnv), EvalFormula rho phi1 -> EvalFormula rho phi2.
Definition MaxImplies : (Set_Formula -> Prop) -> (Set_Formula -> Prop) := fun pred phi =>
  pred phi /\ (∀ phi', pred phi' -> Implies phi' phi).
Definition MinImplies : (Set_Formula -> Prop) -> (Set_Formula -> Prop) := fun pred phi =>
  pred phi /\ (∀ phi', pred phi' -> Implies phi phi').
Definition FormEqual (phi1 phi2 : Set_Formula) := Implies phi1 phi2 /\ Implies phi2 phi1.

Lemma ImpliesRefl : forall phi, Implies phi phi.
Proof.
  intro. intro. auto.
Qed.
Lemma ImpliesTrans : forall phi1 phi2 phi3, Implies phi1 phi2 -> Implies phi2 phi3 -> Implies phi1 phi3.
Proof.
  intro. intro. intro. intro im1. intro im2. intro. intro ef. auto.
Qed.


Lemma RecFormAndL : ∀ p1 p2, ~ FormAnd p1 p2 = p1.
Proof.
  induction p1; congruence.
Qed.
Lemma RecFormAndR : ∀ p2 p1, ~ FormAnd p1 p2 = p2.
Proof.
  induction p2; congruence.
Qed.

Inductive SubstExprVarExpr : Set_Var -> Set_Expr -> Set_Expr -> Set_Expr -> Prop :=
| SubstFormVarExprVal : ∀ (x : Set_Var) (e : Set_Expr) (v : Set_Val), SubstExprVarExpr x e (ExprVal v) (ExprVal v)
| SubstFormVarExprVarHit : ∀ (x : Set_Var) (e : Set_Expr), SubstExprVarExpr x e (ExprVar x) e
| SubstFormVarExprVarMiss : ∀ (x : Set_Var) (e : Set_Expr) (x' : Set_Var), x <> x' -> SubstExprVarExpr x e (ExprVar x') (ExprVar x')
| SubstFormVarExprBinOp : ∀ (x : Set_Var) (e : Set_Expr) (op : Set_BinOp) (e1 e2 e1' e2' : Set_Expr),
  SubstExprVarExpr x e e1 e1' ->
  SubstExprVarExpr x e e2 e2' ->
  SubstExprVarExpr x e (ExprBinOp op e1 e2) (ExprBinOp op e1' e2')
.
Inductive SubstFormVarExpr : Set_Var -> Set_Expr -> Set_Formula -> Set_Formula -> Prop :=
| SubstFormVarExprTrue : ∀ (x : Set_Var) (e : Set_Expr), SubstFormVarExpr x e FormTrue FormTrue
| SubstFormVarExprCompOp : ∀ (x : Set_Var) (e : Set_Expr) (op : Set_CompOp) (e1 e2 e1' e2' : Set_Expr),
  SubstExprVarExpr x e e1 e1' ->
  SubstExprVarExpr x e e2 e2' ->
  SubstFormVarExpr x e (FormCompOp op e1 e2) (FormCompOp op e1' e2')
| SubstFormVarExprAnd : ∀ (x : Set_Var) (e : Set_Expr) (phi1 phi2 phi1' phi2' : Set_Formula),
  SubstFormVarExpr x e phi1 phi1' ->
  SubstFormVarExpr x e phi2 phi2' ->
  SubstFormVarExpr x e (FormAnd phi1 phi2) (FormAnd phi1' phi2')
.
Inductive FreeVarExpr : Set_Var -> Set_Expr -> Prop :=
| FreeVarExprVar : ∀ (x : Set_Var), FreeVarExpr x (ExprVar x)
| FreeVarExprBinOp : ∀ (x : Set_Var) (op : Set_BinOp) (e1 e2 : Set_Expr),
  FreeVarExpr x e1 \/ FreeVarExpr x e2 ->
  FreeVarExpr x (ExprBinOp op e1 e2)
.
Inductive FreeVarForm : Set_Var -> Set_Formula -> Prop :=
| FreeVarFormCompOp : ∀ (x : Set_Var) (op : Set_CompOp) (e1 e2 : Set_Expr),
  FreeVarExpr x e1 \/ FreeVarExpr x e2 ->
  FreeVarForm x (FormCompOp op e1 e2)
| FreeVarFormAnd : ∀ (x : Set_Var) (phi1 phi2 : Set_Formula),
  FreeVarForm x phi1 \/ FreeVarForm x phi2 ->
  FreeVarForm x (FormAnd phi1 phi2)
.

Definition EImplies (e1 e2 : Set_Expr) := forall rho v, EvalExpr rho e1 v -> EvalExpr rho e2 v.
Definition EEqual (e1 e2 : Set_Expr) := EImplies e1 e2 /\ EImplies e2 e1.



Lemma EvalVarDet : ∀ rho x v1 v2, EvalVar rho x v1 -> EvalVar rho x v2 -> v1 = v2.
Proof.
  induction rho; intro; intro; intro; intro; intro.
  - inv H.
  - clac (s = x).
    * subst.
      inv H0; intuition.
      inv H; intuition.
    * inv H0; intuition.
      inv H; intuition.
      eapply IHrho; eauto.
Qed.

Lemma EvalExprDet : ∀ rho e v1 v2, EvalExpr rho e v1 -> EvalExpr rho e v2 -> v1 = v2.
Proof.
  intro.
  induction e; intro; intro; intro ee1; intro ee2.
  - inv ee1. inv ee2. auto.
  - inv ee1. inv ee2. eapply EvalVarDet; eauto.
  - inv ee1. inv ee2.
    assert (v0 = v4) as IH1. apply IHe1; auto.
    assert (v3 = v5) as IH2. apply IHe2; auto.
    subst.
    rewrite H6 in H9. inv H9. auto.
Qed.

Lemma SubstExprSemantics : 
  ∀ x e e1 e2, SubstExprVarExpr x e e1 e2 ->
  ∀ rho v, EvalExpr rho e v ->
  ∀ ve, EvalExpr (VarEnvMapping x v rho) e1 ve <-> EvalExpr rho e2 ve.
Proof.
  induction e1; intro; intro subst; intro; intro; intro ev; intro; split; intro ee.
  - inv subst.
    inv ee. ctor.
  - inv subst.
    inv ee. ctor.
  - inv subst.
    * inv ee. inv H1; intuition.
    * inv ee. inv H1; intuition.
      ctor. assumption.
  - inv subst.
    * assert (v = ve). eapply EvalExprDet; eauto.
      subst.
      ctor. ctor.
    * inv ee.
      ctor. ctor; auto.
  - inv subst. inv ee. ctor; eauto.
    * eapply IHe1_1; eauto.
    * eapply IHe1_2; eauto.
  - inv subst. inv ee. ctor; eauto.
    * rewrite IHe1_1; eauto.
    * rewrite IHe1_2; eauto.
Qed.

Lemma SubstFormSemantics :
  ∀ x e phi1 phi2, SubstFormVarExpr x e phi1 phi2 ->
  ∀ rho v, EvalExpr rho e v ->
  EvalFormula (VarEnvMapping x v rho) phi1 <-> EvalFormula rho phi2.
Proof.
  intro. intro. intro. intro. intro subst. intro. intro. intro eev.
  generalize phi1 phi2 subst. clear subst phi1 phi2.
  induction phi1; intro; intro subst; split; intro ef.
  - inv subst. ctor.
  - inv subst. ctor.
  - inv subst. inv ef. ctor; eauto; eapply SubstExprSemantics; eauto.
  - inv subst. inv ef. ctor; eauto; eapply SubstExprSemantics; eauto.
  - inv subst. inv ef. ctor; eauto.
    * apply IHphi1_1; assumption.
    * apply IHphi1_2; assumption.
  - inv subst. inv ef. ctor; eauto.
    * rewrite (IHphi1_1 phi1'); assumption.
    * rewrite (IHphi1_2 phi2'); assumption.
Qed.

Lemma MonotoneFormAnd : ∀ phi1 phi2 phi1' phi2', Implies phi1 phi2 -> Implies phi1' phi2' -> Implies (FormAnd phi1 phi1') (FormAnd phi2 phi2').
Proof.
  intro. intro. intro. intro. intro ima. intro imb.
  intro. intro ef.
  inv ef.
  apply ima in H2.
  apply imb in H3.
  constructor; assumption.
Qed.

Lemma ObservablyIdenticalVarEnvEvalExpr : forall rho1 rho2 (xs : list Set_Var),
  (∀ x, In x xs -> ∀ v, EvalVar rho1 x v <-> EvalVar rho2 x v) ->
  ∀ e, (∀ x, FreeVarExpr x e → In x xs) -> ∀ v, EvalExpr rho1 e v <-> EvalExpr rho2 e v.
Proof.
  intro. intro. 
  induction xs.
  - introc TMP.
    induction e; intro fv; intro.
    * split; intro evl; inv evl; ctor.
    * specialize (fv s).
      assert (In s []) as T. apply fv. ctor.
      inv T.
    * assert (∀ v : Set_Val, EvalExpr rho1 e1 v ↔ EvalExpr rho2 e1 v) as T1.
        apply IHe1. intro. intro fve. apply fv. ctor. auto.
      clear IHe1.
      assert (∀ v : Set_Val, EvalExpr rho1 e2 v ↔ EvalExpr rho2 e2 v) as T2.
        apply IHe2. intro. intro fve. apply fv. ctor. auto.
      clear IHe2.
      split; intro ee; inv ee;
      specialize (T1 v1);
      specialize (T2 v2);
      ctor; eauto;
      intuition.
  - intro freval.
    induction e; intro fv; intro.
    * split; intro evl; inv evl; ctor.
    * specialize (fv s).
      assert (In s (a :: xs)) as T. apply fv. ctor. clear fv.
      inv T.
      + assert (EvalVar rho1 s v ↔ EvalVar rho2 s v) as T. apply freval. ctor. auto.
        split; intro ee; inv ee;
        ctor;
        intuition.
      + assert (∀ e : Set_Expr, (∀ x : Set_Var, FreeVarExpr x e → In x xs) → ∀ v : Set_Val, EvalExpr rho1 e v ↔ EvalExpr rho2 e v) as IH.
          apply IHxs. intro. intro i. intro. apply freval. intuition.
        clear IHxs.
        apply IH.
        intro. intro fve. inv fve. assumption.
    * clear IHxs.
      assert (∀ v : Set_Val, EvalExpr rho1 e1 v ↔ EvalExpr rho2 e1 v) as T1.
        apply IHe1. intro. intro fve. apply fv. ctor. auto.
      clear IHe1.
      assert (∀ v : Set_Val, EvalExpr rho1 e2 v ↔ EvalExpr rho2 e2 v) as T2.
        apply IHe2. intro. intro fve. apply fv. ctor. auto.
      clear IHe2.
      split; intro ee; inv ee;
      specialize (T1 v1);
      specialize (T2 v2);
      ctor; eauto;
      intuition.
Qed.



Lemma ObservablyIdenticalVarEnvEvalFormula : forall (xs : list Set_Var) rho1 rho2,
  (∀ x, In x xs -> ∀ v, EvalVar rho1 x v <-> EvalVar rho2 x v) ->
  ∀ phi, (∀ x, FreeVarForm x phi → In x xs) -> (EvalFormula rho1 phi <-> EvalFormula rho2 phi).
Proof.
  intro. intro. intro. intro ev.
  induction phi.
  - introc TMP.
    split; ctor.
  - intro fv.
    assert (∀ v, (EvalExpr rho1 s0 v <-> EvalExpr rho2 s0 v)) as Hy1.
      eapply ObservablyIdenticalVarEnvEvalExpr; eauto.
      intros. apply fv. ctor. auto.
    assert (∀ v, (EvalExpr rho1 s1 v <-> EvalExpr rho2 s1 v)) as Hy2.
      eapply ObservablyIdenticalVarEnvEvalExpr; eauto.
      intros. apply fv. ctor. auto.
    split; intro ef; inv ef.
    * ctor; eauto; try rewrite Hy1 in *; try rewrite Hy2 in *; auto.
    * ctor; eauto; try rewrite Hy1; try rewrite Hy2; auto.
  - clear ev.
    intro fv.
    assert (EvalFormula rho1 phi1 ↔ EvalFormula rho2 phi1) as Hy1.
      apply IHphi1.
      intros. apply fv. ctor. auto.
    assert (EvalFormula rho1 phi2 ↔ EvalFormula rho2 phi2) as Hy2.
      apply IHphi2.
      intros. apply fv. ctor. auto.
    split; intro ef; inv ef.
    * ctor; eauto; try rewrite Hy1 in *; try rewrite Hy2 in *; auto.
    * ctor; eauto; try rewrite Hy1; try rewrite Hy2; auto.
Qed.


Lemma MonotoneSubstFormVarExpr_HelperExpr : ∀ x e rho e1 e2 v',
  SubstExprVarExpr x e e1 e2 → EvalExpr rho e2 v' → FreeVarExpr x e1 → ∃ v : Set_Val, EvalExpr rho e v.
Proof.
  induction e1; intro; intro;
  intro subst; intro ee; intro fve.
  - inv fve.
  - inv fve.
    inv subst.
    * eexists. eauto.
    * congruence.
  - inv subst.
    inv ee.
    inv fve.
    inv H1.
    * eapply IHe1_1 in H; eauto.
    * eapply IHe1_2 in H; eauto.
Qed.

Lemma MonotoneSubstFormVarExpr_HelperForm : ∀ x e rho phi1 phi1',
  SubstFormVarExpr x e phi1 phi1' → EvalFormula rho phi1' → FreeVarForm x phi1 → ∃ v : Set_Val, EvalExpr rho e v.
Proof.
  induction phi1; intro;
  intro subst; intro ef; intro fvf;
  inv fvf.
  - inv subst.
    inv ef.
    inv H1.
    * eapply MonotoneSubstFormVarExpr_HelperExpr in H; eauto.
    * eapply MonotoneSubstFormVarExpr_HelperExpr in H; eauto.
  - inv subst.
    inv ef.
    inv H1.
    * eapply IHphi1_1 in H; eauto.
    * eapply IHphi1_2 in H; eauto.
Qed.

Lemma FreeVarExprList : ∀ e, exists l, ∀ x, FreeVarExpr x e <-> In x l.
Proof.
  induction e.
  - exists [].
    split; intros; inv H.
  - exists [s].
    split; intros; inv H.
    * ctor. auto.
    * ctor.
    * inv H0.
  - unf.
    exists (x ++ x0).
    split; intros.
    * apply in_or_app.
      inv H1.
      inv H4.
      + apply H0 in H1. auto.
      + apply H in H1. auto.
    * apply in_app_or in H1.
      ctor.
      inv H1.
      + rewrite H. auto.
      + rewrite H0. auto.
Qed.

Lemma FreeVarFormList : ∀ phi, exists l, ∀ x, FreeVarForm x phi <-> In x l.
Proof.
  induction phi.
  - exists [].
    split; intros; inv H.
  - assert (e1 := FreeVarExprList s0).
    assert (e2 := FreeVarExprList s1).
    unf.
    exists (x ++ x0).
    split; intros.
    * apply in_or_app.
      inv H1.
      inv H4.
      + apply H0 in H1. auto.
      + apply H in H1. auto.
    * apply in_app_or in H1.
      ctor.
      inv H1.
      + rewrite H. auto.
      + rewrite H0. auto.
  - unf.
    exists (x ++ x0).
    split; intros.
    * apply in_or_app.
      inv H1.
      inv H4.
      + apply H0 in H1. auto.
      + apply H in H1. auto.
    * apply in_app_or in H1.
      ctor.
      inv H1.
      + rewrite H. auto.
      + rewrite H0. auto.
Qed.

Lemma FreeVarExprUpperBound : ∀ e, exists l, ∀ x, FreeVarExpr x e -> In x l.
Proof.
  induction e.
  - exists [].
    intros.
    inv H.
  - exists [s].
    intros.
    inv H.
    ctor.
    auto.
  - unf.
    exists (x ++ x0).
    intros.
    inv H1.
    intuition.
Qed.

Lemma FreeVarFormUpperBound : ∀ phi, exists l, ∀ x, FreeVarForm x phi -> In x l.
Proof.
  induction phi.
  - exists [].
    intros.
    inv H.
  - assert (e1 := FreeVarExprUpperBound s0).
    assert (e2 := FreeVarExprUpperBound s1).
    unf.
    exists (x ++ x0).
    intros.
    inv H1.
    intuition.
  - unf.
    exists (x ++ x0).
    intros.
    inv H1.
    intuition.
Qed.


Definition Deterministic (f : Set_Formula -> Set_Formula -> Prop) := forall phi phi1 phi2, f phi phi1 -> f phi phi2 -> phi1 = phi2.
Definition Monotone (f : Set_Formula -> Set_Formula -> Prop) := ∀ (phi1 phi2 phi1' phi2' : Set_Formula),
       f phi1 phi1' → f phi2 phi2'
       → Implies phi1 phi2 → Implies phi1' phi2'.
Definition MonotoneDef (f : Set_Formula -> Set_Formula -> Prop) := ∀ (phi1 phi1' : Set_Formula),
       f phi1 phi1' → forall phi2, Implies phi1 phi2 → exists phi2', f phi2 phi2'.

Definition MonotoneFull f := MonotoneDef f /\ Monotone f.


Inductive FirstStmt : Set_Stmt -> Set_Stmt -> Prop :=
| FirstStmtAtomic : ∀ (s : Set_Stmt), (~ exists s1 s2, StmtSeq s1 s2 = s) -> FirstStmt s s
| FirstStmtSeq : ∀ (s s1 s2 : Set_Stmt), FirstStmt s1 s -> FirstStmt (StmtSeq s1 s2) s.


Inductive StateExtract : Set_State -> list Set_VarEnv -> list Set_Stmt -> Prop :=
| StateExtractEmpty : StateExtract StackEmpty [] []
| StateExtractCons : ∀ S rhos ss rho s,
  StateExtract S rhos ss ->
  StateExtract (StackCons (StackFrame rho s) S) (rho :: rhos) (s :: ss)
.

Section Semantics.

Variable p : Set_Program.

Definition LookupMethodAmbig : Set_MethodName -> Set_Method -> Prop := fun n m =>
match p with
| Program ms _ => In m ms /\ (match m with Method _ n' _ _ _ _ => n' = n end)
end.
Definition LookupMethod : Set_MethodName -> Set_Method -> Prop := fun n m =>
  LookupMethodAmbig n m /\ (∀ m', LookupMethodAmbig n m' -> m = m').

Inductive Step : Set_State -> Set_State -> Prop :=
| StepSkip : ∀ (s : Set_Stmt) (rho : Set_VarEnv) (S : Set_Stack),
  Step
    (StackCons (StackFrame rho (StmtSeq StmtSkip s)) S)
    (StackCons (StackFrame rho s) S)
| StepAssert : ∀ (rho : Set_VarEnv) (S : Set_Stack) (phi : Set_Formula),
  EvalFormula rho phi ->
  Step
    (StackCons (StackFrame rho (StmtAssert phi)) S)
    (StackCons (StackFrame rho StmtSkip) S)
| StepVarAssign : ∀ (rho : Set_VarEnv) (S : Set_Stack) (x : Set_Var) (e : Set_Expr) (v : Set_Val),
  EvalExpr rho e v ->
  Step
    (StackCons (StackFrame rho (StmtVarAssign x e)) S)
    (StackCons (StackFrame (VarEnvMapping x v rho) StmtSkip) S)
| StepCall : ∀ (r : Set_Stmt) (phi : Set_Formula) (rho rho' : Set_VarEnv) (S : Set_Stack) (x y : Set_Var) (i : Set_Ident) (v : Set_Val) (m : Set_MethodName) (_T1 _T2 : Set_Type) (_phi : Set_Formula),
  LookupMethod m (Method _T1 m _T2 i (Contract phi _phi) r) ->
  EvalVar rho x v ->
  rho' = VarEnvMapping (VarOldIdent i) v (VarEnvMapping (VarIdent i) v VarEnvFresh) ->
  EvalFormula rho' phi ->
  Step
    (StackCons (StackFrame rho (StmtCall y m x)) S)
    (StackCons (StackFrame rho' r) (StackCons (StackFrame rho (StmtCall y m x)) S))
| StepCallFinish : ∀ (_r : Set_Stmt) (phi : Set_Formula) (rho rho' : Set_VarEnv) (S : Set_Stack) (x y : Set_Var) (i : Set_Ident) (v  : Set_Val) (m : Set_MethodName) (T _T : Set_Type) (_phi : Set_Formula),
  LookupMethod m (Method T m _T i (Contract _phi phi) _r) ->
  EvalVar rho' VarResult v ->
  EvalFormula rho' phi ->
  Step
    (StackCons (StackFrame rho' StmtSkip) (StackCons (StackFrame rho (StmtCall y m x)) S))
    (StackCons (StackFrame (VarEnvMapping y v rho) StmtSkip) S)
| StepSeq : ∀ (s1 : Set_Stmt) (s1' : Set_Stmt) (s2 : Set_Stmt) (rho : Set_VarEnv) (rho' : Set_VarEnv) (S : Set_Stack),
  s1 <> StmtSkip
  ->
  Step
    (StackCons (StackFrame rho s1) S)
    (StackCons (StackFrame rho' s1') S)
  ->
  Step
    (StackCons (StackFrame rho (StmtSeq s1 s2)) S)
    (StackCons (StackFrame rho' (StmtSeq s1' s2)) S)
| StepSeqEnter : ∀ sf (s1 : Set_Stmt) (s1' : Set_Stmt) (s2 : Set_Stmt) (rho : Set_VarEnv) (rho' : Set_VarEnv) (S : Set_Stack),
  Step
    (StackCons (StackFrame rho s1) S)
    (StackCons sf (StackCons (StackFrame rho' s1') S))
  ->
  Step
    (StackCons (StackFrame rho (StmtSeq s1 s2)) S)
    (StackCons sf (StackCons (StackFrame rho' (StmtSeq s1' s2)) S))
| StepSeqExit : ∀ sf (s1 : Set_Stmt) (s1' : Set_Stmt) (s2 : Set_Stmt) (rho : Set_VarEnv) (rho' : Set_VarEnv) (S : Set_Stack),
  Step
    (StackCons sf (StackCons (StackFrame rho s1) S))
    (StackCons (StackFrame rho' s1') S)
  ->
  Step
    (StackCons sf (StackCons (StackFrame rho (StmtSeq s1 s2)) S))
    (StackCons (StackFrame rho' (StmtSeq s1' s2)) S)
.


(* stat sem *)

Inductive WP : Set_Stmt -> Set_Formula -> Set_Formula -> Prop :=
| WpSkip : ∀ (phi : Set_Formula),
  WP StmtSkip phi phi
| WpAssert : ∀ (phi phia : Set_Formula),
  WP (StmtAssert phia) phi (FormAnd phia phi)
| WpVarAssign : ∀ (phi phi' : Set_Formula) (x : Set_Var) (e : Set_Expr),
  (~ exists i, x = VarOldIdent i) ->
  SubstFormVarExpr x e phi phi' ->
  WP (StmtVarAssign x e) phi (FormAnd (FormCompOp CompOpEq e e) phi') (* impl. detail: additional precond. to ensure evaluation *)
| WpCall : ∀ (phi phi1 phi2 phi1' phi2' phi2'' phi' : Set_Formula) (x y : Set_Var) (i : Set_Ident) (m : Set_MethodName) (_T1 _T2 : Set_Type) (_s : Set_Stmt),
  (~ exists i, y = VarOldIdent i) ->
  x <> y ->
  x <> VarResult ->
  LookupMethod m (Method _T1 m _T2 i (Contract phi1 phi2) _s) ->
  SubstFormVarExpr (VarIdent i) (ExprVar x) phi1 phi1' ->
  SubstFormVarExpr (VarOldIdent i) (ExprVar x) phi2 phi2'' ->
  SubstFormVarExpr VarResult (ExprVar y) phi2'' phi2' ->
  MaxImplies (fun phi' =>
    (forall x', FreeVarForm x' phi' -> x = x') /\
    Implies phi' phi1' /\
    Implies (FormAnd phi' phi2') phi
  ) phi' ->
  WP (StmtCall y m x) phi (FormAnd phi' (FormCompOp CompOpEq (ExprVar x) (ExprVar x)))
| WpSeq : ∀ (s1 s2 : Set_Stmt) (phi1 phi2 phi3 : Set_Formula),
  WP s2 phi3 phi2 ->
  WP s1 phi2 phi1 ->
  WP (StmtSeq s1 s2) phi3 phi1
.

Inductive StackWP : list Set_Stmt -> Set_Formula -> list Set_Formula -> Prop :=
| StackWpMain : ∀ (s : Set_Stmt) (phi : Set_Formula) (phi' : Set_Formula),
  WP s phi phi' ->
  StackWP [s] phi [phi']
| StackWpCall : ∀ (s s' _s : Set_Stmt) (S : list Set_Stmt) (phi _phi1 phi2 phi' : Set_Formula) (phi'' : list Set_Formula) (x y : Set_Var) _i (m : Set_MethodName) (_T1 _T2 : Set_Type),
  LookupMethod m (Method _T1 m _T2 _i (Contract _phi1 phi2) _s) ->
  WP s phi2 phi' ->
  FirstStmt s' (StmtCall y m x) ->
  StackWP (s' :: S) phi phi'' ->
  StackWP (s :: s' :: S) phi (phi' :: phi'')
.


(* validity *)

Definition ValidMethod : Set_Method -> Prop := fun m =>
match m with
| Method _ _ _ i c s =>
  match c with
  | Contract phi1 phi2 =>
    (forall x', FreeVarForm x' phi1 -> x' = (VarIdent i)) /\
    (forall x', FreeVarForm x' phi2 -> x' = (VarOldIdent i) \/ x' = VarResult) /\
    (exists phi'' phi', WP s phi2 phi'' /\ SubstFormVarExpr (VarOldIdent i) (ExprVar (VarIdent i)) phi'' phi' /\ Implies phi1 phi') /\
    Implies phi2 (FormCompOp CompOpEq (ExprVar VarResult) (ExprVar VarResult))
  end
end.

Definition ValidProgram : Set_Program -> Prop := fun p =>
match p with
| Program ms s =>
  (exists phi, WP s FormTrue phi /\ Implies FormTrue phi) /\
  (forall m, In m ms -> ValidMethod m)
end.

Definition ValidStateClassic : Set_State -> Prop := fun pi => exists rhos ss phis,
  StateExtract pi rhos ss /\
  StackWP ss FormTrue phis /\
  Forall2 EvalFormula rhos phis
.

Inductive ValidStateEx : Set_Formula -> Set_State -> Prop :=
| ValidStateBase : forall phi' phi rho s,
  WP s phi' phi ->
  EvalFormula rho phi ->
  ValidStateEx phi' (StackCons (StackFrame rho s) StackEmpty)
| ValidStateCons : forall phi' phi rho rho' s s' S m x i v _y _T1 _T2 _r _phi1 phi2,
  WP s' phi2 phi ->
  EvalFormula rho' phi ->
  FirstStmt s (StmtCall _y m x) ->
  LookupMethod m (Method _T1 m _T2 i (Contract _phi1 phi2) _r) ->
  EvalVar rho x v ->
  EvalVar rho' (VarOldIdent i) v ->
  ValidStateEx phi' (StackCons (StackFrame rho s) S) ->
  ValidStateEx phi' (StackCons (StackFrame rho' s') (StackCons (StackFrame rho s) S))
.

Definition ValidState := ValidStateEx FormTrue.

(* WP of next step satisfied *)
Definition LocallyValidState : Set_State -> Prop := fun pi => exists rho s S phi' phi,
  pi = StackCons (StackFrame rho s) S /\
  WP s phi' phi /\
  EvalFormula rho phi /\
  (s = StmtSkip -> (S = StackEmpty \/ (exists s' _S rho' y m x _T1 _T2 i _phi1 phi2 _s,
                     S = StackCons (StackFrame rho' s') _S
                  /\ FirstStmt s' (StmtCall y m x)
                  /\ LookupMethod m (Method _T1 m _T2 i (Contract _phi1 phi2) _s)
                  /\ EvalFormula rho phi2)))
.

Lemma ValidStateClassicness : forall pi, ValidState pi -> ValidStateClassic pi.
Proof.
  induction pi; intro vs; inv vs.
  - exists [rho]. exists [s0]. exists [phi].
    split. ctor. ctor.
    split. ctor. assumption.
    ctor. assumption.
    ctor.
  - apply IHpi in H8.
    unfold ValidStateClassic in *.
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

Lemma LookupMethodDet : forall m m1 m2, LookupMethod m m1 -> LookupMethod m m2 -> m1 = m2.
Proof.
  intro. intro. intro. intro l1. intro l2.
  unfold LookupMethod in *. unf.
  apply H0 in H1. auto.
Qed.

Lemma LocalValidity : ∀ pi : Set_State, ValidState pi -> LocallyValidState pi.
Proof.
  intro pi.
  intro valid.
  unfold LocallyValidState in *.
  inv valid.
  - eex.
  - eex.
    intro ss. subst.
    inv H.
    apply or_intror.
    eex.
Qed.

Axiom Validity : ValidProgram p.

(* soundness *)

Definition FinalState : Set_State -> Prop := fun pi => 
  pi = StackEmpty \/
  (exists rho, pi = StackCons (StackFrame rho StmtSkip) StackEmpty).


Definition UsedVarForm (x : Set_Var) (phi : Set_Formula) := ~ ∀ rho, EvalFormula rho phi -> ∀ v, EvalFormula (VarEnvMapping x v rho) phi.
Definition UsedVarExpr (x : Set_Var) (e : Set_Expr) := ~ ∀ rho ve, EvalExpr rho e ve -> ∀ v, EvalExpr (VarEnvMapping x v rho) e ve.

Definition Z1 : Z := Zpos 1.


Lemma UsedVarExprVar : forall e, UsedVarExpr e (ExprVar e).
Proof.
  intros. intro.
  specialize (H (VarEnvMapping e Z0 VarEnvFresh) Z0).
  lapply H.
  - intro c.
    specialize (c Z1).
    inv c. inv H2. congruence.
  - ctor. ctor.
Qed.

(* dyn sem helper *)

Inductive InitializeVars : list Set_Var -> Set_VarEnv -> Set_VarEnv -> Prop :=
| InitializeVarsEmpty : forall rho, InitializeVars [] rho rho
| InitializeVarsCons : forall x xs rho rho',
  InitializeVars xs rho rho' ->
  InitializeVars (x :: xs) rho (VarEnvMapping x Z0 rho')
.
Lemma InitializeVarsExists : forall xs rho, exists rho', InitializeVars xs rho rho'.
Proof.
  induction xs; intro.
  - eexists. ctor.
  - specialize (IHxs rho).
    unf.
    eexists. ctor. eauto.
Qed.

Lemma NoUsedVarExprIsConst : ∀ e, (∀ x : Set_Var, ~ UsedVarExpr x e) -> ∀ v1 v2 rho1 rho2, EvalExpr rho1 e v1 -> EvalExpr rho2 e v2 -> v1 = v2.
Proof.
  intros.
  assert (exists xs, forall x, FreeVarExpr x e -> In x xs) as fvs.
    generalize e. clear.
    induction e.
      exists []. intros. inv H.
      exists [s]. intros. inv H. ctor. auto.
      unf. exists (app x x0). intro. specialize (H x1). specialize (H0 x1).
      intro fve. inv fve. intuition.
  unf.
  assert (ee1 := InitializeVarsExists x rho1).
  assert (ee2 := InitializeVarsExists x rho2).
  unf.
  assert (EvalExpr x1 e v1) as e1.
    generalize x x1 H4. clear x H4 H2 H3. induction x; intros.
      inv H4. assumption.
      inv H4. specialize (H a). apply NNPP in H. apply H. apply IHx. assumption.
  assert (EvalExpr x0 e v2) as e2.
    generalize x x0 H3. clear x H4 H2 H3. induction x; intros.
      inv H3. assumption.
      inv H3. specialize (H a). apply NNPP in H. apply H. apply IHx. assumption.
  clear H0 H1.

  apply (ObservablyIdenticalVarEnvEvalExpr x1 x0 x) in e1; auto.
    eapply EvalExprDet; eauto.
  intros.
  generalize x x0 x1 H3 H4 H1. clear.
  induction x; intro; intro; intro iv1; intro iv2; intro inx; inv inx.
  - inv iv1. inv iv2.
    split; intro ev; inv ev; try congruence; ctor.
  - inv iv1. inv iv2.
    eapply IHx in H4; eauto.
    clac (a = x2).
    * subst.
      split; intro ev; inv ev; try congruence; ctor.
    * split; intro ev; inv ev ; try congruence; ctor; auto;
      apply H4; auto.
Qed.

(* Lemma ObservablyIdenticalVarEnvEvalExprEx : forall rho1 rho2 (xs : list Set_Var),
  (∀ x, In x xs -> ∀ v, EvalVar rho1 x v <-> EvalVar rho2 x v) ->
  ∀ e, (∀ x, UsedVarExpr x e → In x xs) -> ∀ v1 v2, EvalExpr rho1 e v1 -> EvalExpr rho2 e v2 -> v1 = v2.
Proof.
  intro. intro. 
  induction xs.
  - introc TMP.
    intro. intro uv. intro.
    assert (∀ x : Set_Var, ~ UsedVarExpr x e) as uve.
      intro. intro uve. apply uv in uve. inv uve.
    clear uv.
    intros.
    eapply NoUsedVarExprIsConst; eauto.
  - intros.
    assert (forall rho, EvalExpr rho e v)

    induction e; intro fv; intro.
  
    * split; intro evl; inv evl; ctor.
    * specialize (fv s).
      assert (In s []) as T. apply fv. apply UsedVarExprVar.
      inv T.
    * assert (∀ v : Set_Val, EvalExpr rho1 e1 v ↔ EvalExpr rho2 e1 v) as T1.
        apply IHe1. intro. intro fve. apply fv. ctor. auto.
      clear IHe1.
      assert (∀ v : Set_Val, EvalExpr rho1 e2 v ↔ EvalExpr rho2 e2 v) as T2.
        apply IHe2. intro. intro fve. apply fv. ctor. auto.
      clear IHe2.
      split; intro ee; inv ee;
      specialize (T1 v1);
      specialize (T2 v2);
      ctor; eauto;
      intuition.
  - intro freval.
    induction e; intro fv; intro.
    * split; intro evl; inv evl; ctor.
    * specialize (fv s).
      assert (In s (a :: xs)) as T. apply fv. ctor. clear fv.
      inv T.
      + assert (EvalVar rho1 s v ↔ EvalVar rho2 s v) as T. apply freval. ctor. auto.
        split; intro ee; inv ee;
        ctor;
        intuition.
      + assert (∀ e : Set_Expr, (∀ x : Set_Var, FreeVarExpr x e → In x xs) → ∀ v : Set_Val, EvalExpr rho1 e v ↔ EvalExpr rho2 e v) as IH.
          apply IHxs. intro. intro i. intro. apply freval. intuition.
        clear IHxs.
        apply IH.
        intro. intro fve. inv fve. assumption.
    * clear IHxs.
      assert (∀ v : Set_Val, EvalExpr rho1 e1 v ↔ EvalExpr rho2 e1 v) as T1.
        apply IHe1. intro. intro fve. apply fv. ctor. auto.
      clear IHe1.
      assert (∀ v : Set_Val, EvalExpr rho1 e2 v ↔ EvalExpr rho2 e2 v) as T2.
        apply IHe2. intro. intro fve. apply fv. ctor. auto.
      clear IHe2.
      split; intro ee; inv ee;
      specialize (T1 v1);
      specialize (T2 v2);
      ctor; eauto;
      intuition.
Qed. *)


Lemma UsedVarExprEvaluable : ∀ e x, UsedVarExpr x e -> Evaluable e.
Proof.
  unfold UsedVarExpr.
  intro. intro. intro uv.
  clac (Evaluable e); auto.
  contradict uv.
  intro. intro. intro ee.
  contradict H.
  eexists. eexists. eauto.
Qed.

Lemma UsedVarFormSatisfiable : ∀ phi x, UsedVarForm x phi -> Satisfiable phi.
Proof.
  unfold UsedVarForm.
  intro. intro. intro uv.
  clac (Satisfiable phi); auto.
  contradict uv.
  intro. intro. intro ef.
  contradict H.
  eexists. eauto.
Qed.

Lemma UsedVarExprFree : ∀ x e, UsedVarExpr x e -> FreeVarExpr x e.
Proof.
  unfold UsedVarExpr.
  induction e; intro uv.
  - contradict uv.
    intro. intro. intro ee. intro.
    inv ee.
    ctor.
  - clac (x = s).
    * subst. ctor.
    * contradict uv.
      intro. intro. intro ee. intro.
      inv ee.
      ctor. ctor; auto.
  - ctor.
    apply not_all_ex_not in uv. inv uv.
    apply not_all_ex_not in H. inv H.
    apply not_all_ex_not in H0. inv H0.
    apply not_all_ex_not in H. inv H.
    inv x2.
    assert (~ EvalExpr (VarEnvMapping x x3 x0) e1 v1 \/ ~ EvalExpr (VarEnvMapping x x3 x0) e2 v2) as ee.
      apply not_and_or.
      intro ee. inv ee.
      contradict H0. ctor; eauto.
    clear H0.
    inv ee.
    * apply or_introl.
      apply IHe1.
      repeat (apply ex_not_not_all; eexists; eauto).
    * apply or_intror.
      apply IHe2.
      repeat (apply ex_not_not_all; eexists; eauto).
Qed.

Lemma UsedVarFormFree : ∀ x phi, UsedVarForm x phi -> FreeVarForm x phi.
Proof.
  unfold UsedVarForm.
  induction phi; intro uv.
  - contradict uv.
    intro. intro. intro. ctor.
  - ctor.
    apply not_all_ex_not in uv. inv uv.
    apply not_all_ex_not in H. inv H.
    apply not_all_ex_not in H0. inv H0.
    inv x1.
    assert (~ EvalExpr (VarEnvMapping x x2 x0) s0 v1 \/ ~ EvalExpr (VarEnvMapping x x2 x0) s1 v2) as ee.
      apply not_and_or.
      intro ee. inv ee.
      contradict H. ctor; eauto.
    clear H.
    inv ee.
    * apply or_introl.
      apply UsedVarExprFree.
      repeat (apply ex_not_not_all; eexists; eauto).
    * apply or_intror.
      apply UsedVarExprFree.
      repeat (apply ex_not_not_all; eexists; eauto).
  - ctor.
    apply not_all_ex_not in uv. inv uv.
    apply not_all_ex_not in H. inv H.
    apply not_all_ex_not in H0. inv H0.
    inv x1.
    assert (~ EvalFormula (VarEnvMapping x x2 x0) phi1 \/ ~ EvalFormula (VarEnvMapping x x2 x0) phi2) as ee.
      apply not_and_or.
      intro ee. inv ee.
      contradict H. ctor; eauto.
    clear H.
    inv ee.
    * apply or_introl.
      apply IHphi1.
      repeat (apply ex_not_not_all; eexists; eauto).
    * apply or_intror.
      apply IHphi2.
      repeat (apply ex_not_not_all; eexists; eauto).
Qed.

(* Lemma SubstExprVarExprId : ∀ x e e1 e2,
  ~ UsedVarExpr x e1 ->
  SubstExprVarExpr x e e1 e2 ->
  EqualExpr e1 e2.
Proof.
  intro. intro. intro. intro. intro uv. intro subst. intro. intro.
  apply NNPP in uv.
  split; intro ee.
  - eapply SubstExprSemantics in subst.
    * apply subst.
      eapply uv in ee.
      eauto.
    * eauto.


  induction e1; intro; intro fv; intro subst.
  - inv subst.
    split; auto.
  - inv subst; try (split; auto; fail).
    contradict fv.
    intro c.
    specialize (c (VarEnvMapping s Z0 VarEnvFresh) Z0).
    lapply c; clear c.
    * intro c.
      specialize (c Z1).
      inv c. inv H1. congruence.
    * ctor. ctor.
  - inv subst.
    apply NNPP in fv.
    assert (EqualExpr e1_1 e1') as eq1.
      eapply IHe1_1; auto.
      intro c. apply c.
      intro. intro. intro ee. intro.
Admitted. *)

(* Lemma SubstFormVarExprId : ∀ x e phi phi',
  ~ UsedVarForm x phi ->
  SubstFormVarExpr x e phi phi' ->
  EqualForm phi phi'.
Proof.
Admitted.
(*   induction phi; intro; intro fv; intro subst.
  - inv subst.
    auto.
  - inv subst.
    apply SubstExprVarExprId in H5.
    apply SubstExprVarExprId in H6.
    subst.
    auto.
    * intro fve.
      contradict fv.
      ctor. auto.
    * intro fve.
      contradict fv.
      ctor. auto.
  - inv subst.
    apply IHphi1 in H3.
    apply IHphi2 in H5.
    subst.
    auto.
    * intro fve.
      contradict fv.
      ctor. auto.
    * intro fve.
      contradict fv.
      ctor. auto.
Qed. *) *)

(* Lemma ImpliesFreeVarExpr : forall e1 e2, ImpliesExpr e1 e2 -> forall x, UsedVarExpr x e2 -> UsedVarExpr x e1.
Proof.
  unfold UsedVarExpr.
  intros.
  intro c.
  contradict H0.
  intros.

  unfold UsedVarExpr.
  induction e1; intro; 
  intro; intro; intro uv;
  intro c; contradict uv;
  intro; intro; intro ee; intro.
  - apply H.
    ctor.
  - clac (s = x).
    * subst. inv ee.
      ctor. ctor; auto.
      contradict c.
      apply ex_not_not_all. eexists.
      apply ex_not_not_all. eexists.
      apply ex_not_not_all. eexists. admit.
      
       *)
    

(* Lemma ImpliesFreeVarForm : forall phi1 phi2, Implies phi1 phi2 -> forall x, FreeVarForm x phi2 -> FreeVarForm x phi1.
Proof.
  intro. intro. intro im.
  apply NNPP. intro c.
  apply not_all_ex_not in c.
  unf.
  apply not_all_ex_not in H.
  unf.
  SearchPattern (~ _ -> _).
  apply not_implies in H.
  induction phi1;
  intro; intro; intro; intro uv.
  - generalize phi2 H uv.
  - intro c.
    contradict uv.
    intro. intro ef. intro.
    apply H.
    apply c.
    ctor.
  - intro c.
    contradict uv.
    intro. intro ef. intro.
    apply H.

  intro; intro; induction phi1; intro; intro; intro.
  - intro s1; intro s2; intro im. *)

(* 
Lemma MonotoneSubstFormVarExpr : ∀ x e phi1 phi2 phi1' phi2',
  SubstFormVarExpr x e phi1 phi1' -> SubstFormVarExpr x e phi2 phi2' ->
  Implies phi1 phi2 -> Implies phi1' phi2'.
Proof.
  intros.
  assert (∀ rho v, (FreeVarForm x phi1 -> EvalExpr rho e v) → EvalFormula (VarEnvMapping x v rho) phi1 ↔ EvalFormula rho phi1') as s1.
    admit. (* apply SubstFormSemantics. assumption. *)
  assert (∀ rho v, (FreeVarForm x phi2 -> EvalExpr rho e v) → EvalFormula (VarEnvMapping x v rho) phi2 ↔ EvalFormula rho phi2') as s2.
    admit. (* apply SubstFormSemantics. assumption. *)
  intro. intro ef.
  clac (FreeVarForm x phi1).
  - Search Implies.

eapply MonotoneSubstFormVarExpr_HelperForm in H; eauto.
    apply 

  - clear H H0.
    unf.
    specialize (s1 rho x0).
    specialize (s2 rho x0).
    intuition.
  - clear s1 s2.
    apply SubstFormVarExprId in H. apply H in ef.
    apply H1 in ef.
    apply SubstFormVarExprId in H0. apply H0 in ef.
    assumption.
    * intro c.
      apply UsedVarFormFree in c.
      Check MonotoneSubstFormVarExpr_HelperForm.
      eapply MonotoneSubstFormVarExpr_HelperForm in c; eauto.
      admit.
    * intro c.
      apply UsedVarFormFree in c.
      eapply MonotoneSubstFormVarExpr_HelperForm in c; eauto.

eapply not_ex_all_not in H2.

  
  Check SubstFormSemantics.
  apply SubstFormSemantics.

Lemma MonotoneSubstExprVarExpr : ∀ x e e1 e2 e1' e2',
  SubstExprVarExpr x e e1 e1' -> SubstExprVarExpr x e e2 e2' ->
  ImpliesExpr e1 e2 -> ImpliesExpr e1' e2'.
Proof.
  intros.
  Check SubstExprSemantics.
  eapply SubstExprSemantics in H.

  induction e1; intro; intro; intro;
  intro s1; intro s2; intro im;
  intro; intro; intro ee.
  - inv s1. inv ee.
    eapply SubstExprVarExprId in s2.
    * apply s2.
      apply im.
      ctor.
    * assert (forall rho, EvalExpr rho e2 v) as ee.
        intro. apply im. ctor.
      clear im.
      intro c. apply c. clear c.
      intros.
      assert (ve = v).
        eapply EvalExprDet; eauto.
      subst.
      apply ee.
  - clac (x = s).
    * subst.
      inv s1; try congruence.
      
      
    
  
Lemma MonotoneSubstFormVarExpr : ∀ x e phi1 phi2 phi1' phi2',
  SubstFormVarExpr x e phi1 phi1' -> SubstFormVarExpr x e phi2 phi2' ->
  Implies phi1 phi2 -> Implies phi1' phi2'.
Proof.
  intro; intro; intro; intro; intro; intro.
  intro s1; intro s2; intro im.
  intro. intro ef.
  clac (UsedVarForm x phi1).
  - assert (exists v, EvalExpr rho e v) as eev. (* x free in p1 /\ x substituted with e from p1 to p2 /\ p2 evals in rho -> e evals in rho *)
      eapply MonotoneSubstFormVarExpr_HelperForm in s1; eauto.
      apply UsedVarFormFree. assumption.
    inv eev.
    eapply SubstFormSemantics in s1; eauto.
    apply s1 in ef. clear s1.
    apply im in ef. clear im.
    eapply SubstFormSemantics; eauto.
  - apply SubstFormVarExprId in s1; try assumption.
    apply s1 in ef.
    apply im in ef.

  

Lemma MonotoneWP : ∀ s phi1 phi2 phi1' phi2',
  WP s phi1 phi1' -> WP s phi2 phi2' ->
  Implies phi1 phi2 -> Implies phi1' phi2'.
Proof.
  induction s; intro; intro; intro; intro;
  intro wp1; intro wp2; intro im;
  inv wp1; inv wp2.
  - assumption.
  - intro. intro ef.
    inv ef.
    ctor; auto.
     *)



Lemma SwapVarEnvEvalVar : ∀ x1 x2,
  x1 <> x2 -> ∀ v1 v2 rho x v,
  EvalVar (VarEnvMapping x1 v1 (VarEnvMapping x2 v2 rho)) x v ->
  EvalVar (VarEnvMapping x2 v2 (VarEnvMapping x1 v1 rho)) x v.
Proof.
  intro. intro. intro neq. intro. intro. intro. intro. intro. intro ev.
  inv ev.
  - ctor; auto. ctor.
  - inv H5.
    * ctor.
    * ctor; auto. ctor; auto.
Qed.

Lemma SwapVarEnvEvalExpr : ∀ x1 x2,
  x1 <> x2 -> ∀ v1 v2 rho e v,
  EvalExpr (VarEnvMapping x1 v1 (VarEnvMapping x2 v2 rho)) e v ->
  EvalExpr (VarEnvMapping x2 v2 (VarEnvMapping x1 v1 rho)) e v.
Proof.
  intro. intro. intro neq. intro. intro. intro.
  induction e; intro; intro ev; inv ev.
  - ctor.
  - ctor. apply SwapVarEnvEvalVar; assumption.
  - ctor; eauto.
Qed.

Lemma SwapVarEnvEvalFormula : ∀ x1 x2,
  x1 <> x2 -> ∀ v1 v2 rho phi,
  EvalFormula (VarEnvMapping x1 v1 (VarEnvMapping x2 v2 rho)) phi ->
  EvalFormula (VarEnvMapping x2 v2 (VarEnvMapping x1 v1 rho)) phi.
Proof.
  intro. intro. intro neq. intro. intro. intro.
  induction phi; intro ev; inv ev.
  - ctor.
  - ctor; eauto; apply SwapVarEnvEvalExpr; assumption.
  - ctor; eauto.
Qed.

Lemma RecStack1 : ∀ (pi : Set_State) sf, ~ StackCons sf pi = pi.
Proof.
  induction pi; congruence.
Qed.
Lemma RecStack2 : ∀ (pi : Set_State) sf1 sf2, ~ StackCons sf1 (StackCons sf2 pi) = pi.
Proof.
  induction pi; congruence.
Qed.

Lemma StepPopOnlyWithSkip : ∀ (pi : Set_State) r' s' r1 s1 r2 s2,
  Step (StackCons (StackFrame r' s') (StackCons (StackFrame r1 s1) pi))
                                     (StackCons (StackFrame r2 s2) pi) ->
  s' = StmtSkip.
Proof.
  intro. intro.
  induction s'; intro; intro; intro; intro; intro step.
  - auto.
  - contradict step. generalize s1 s2. clear.
    unfold not. induction s1; intro; intro step; inv step;
    try (apply RecStack1 in H6; auto).
    eapply IHs1_1 in H0.
    auto.
  - contradict step. generalize s3 s2. clear.
    unfold not. induction s3; intro; intro step.
    * inv step. apply RecStack2 in H7. auto.
    * inv step. apply RecStack2 in H7. auto.
    * inv step. apply RecStack2 in H7. auto.
    * inv step. apply RecStack2 in H7. auto.
    * inv step.
      + apply RecStack2 in H7. auto.
      + eapply IHs3_1 in H0. auto.
  - contradict step. generalize s1 s2. clear.
    unfold not. induction s1; intro; intro step; inv step;
    try (apply RecStack1 in H5; auto).
    eapply IHs1_1 in H0.
    auto.
  - contradict step. generalize s1 s2. clear.
    unfold not. induction s1; intro; intro step; inv step;
    try (apply RecStack1 in H6; auto);
    try (apply RecStack2 in H5; auto).
    eapply IHs1_1 in H0.
    auto.
Qed.

(* static sem *)



Lemma SubstExprFreeVar : ∀ x e e1 e2,
  SubstExprVarExpr x e e1 e2 -> ∀ x1,
  FreeVarExpr x1 e1 ->
  ((x <> x1 /\ FreeVarExpr x1 e2) \/ (x = x1 /\ forall x2, FreeVarExpr x2 e -> FreeVarExpr x2 e2)).
Proof.
  intro. intro.
  induction e1; intro; intro subst; intro; intro fv.
  - inv subst. inv fv.
  - inv subst.
    * inv fv. auto.
    * inv fv. ctor. ctor; auto. ctor.
  - inv subst.
    inv fv. inv H1.
    * eapply (IHe1_1 e1') in H; auto.
      inv H; unf.
      + ctor. ctor; auto. ctor. auto.
      + apply or_intror. ctor; auto.
        intro. intro fv. apply H1 in fv. ctor. auto.
    * eapply (IHe1_2 e2') in H; auto.
      inv H; unf.
      + ctor. ctor; auto. ctor. auto.
      + apply or_intror. ctor; auto.
        intro. intro fv. apply H1 in fv. ctor. auto.
Qed.

Lemma SubstFormFreeVar : ∀ x e phi1 phi2,
  SubstFormVarExpr x e phi1 phi2 -> ∀ x1,
  FreeVarForm x1 phi1 ->
  ((x <> x1 /\ FreeVarForm x1 phi2) \/ (x = x1 /\ forall x2, FreeVarExpr x2 e -> FreeVarForm x2 phi2)).
Proof.
  intro. intro.
  induction phi1; intro; intro subst; intro; intro fv.
  - inv subst. inv fv.
  - inv subst. inv fv. inv H1.
    * eapply SubstExprFreeVar in H; eauto.
      inv H; unf.
      + ctor. ctor; auto. ctor. auto.
      + apply or_intror. ctor; auto.
        intro. intro fv. apply H1 in fv. ctor. auto.
    * eapply SubstExprFreeVar in H; eauto.
      inv H; unf.
      + ctor. ctor; auto. ctor. auto.
      + apply or_intror. ctor; auto.
        intro. intro fv. apply H1 in fv. ctor. auto.
  - inv subst. inv fv. inv H1.
    * eapply (IHphi1_1 phi1') in H; eauto.
      inv H; unf.
      + ctor. ctor; auto. ctor. auto.
      + apply or_intror. ctor; auto.
        intro. intro fv. apply H1 in fv. ctor. auto.
    * eapply (IHphi1_2 phi2') in H; eauto.
      inv H; unf.
      + ctor. ctor; auto. ctor. auto.
      + apply or_intror. ctor; auto.
        intro. intro fv. apply H1 in fv. ctor. auto.
Qed.

(* end *)

Lemma ProgressHelper : ∀ (pi : Set_State),
  LocallyValidState pi ->
  ~ FinalState pi ->
  (exists pi', Step pi pi').
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
        inv valid.
        unf.
        inv H0.
        intuition; try congruence.
        unf.
        inv H.
        inv H0.
        generalize x0 H2. clear x0 H2 H1.
        induction x0; intros; inv H2.
        **assert (exists v, EvalVar x VarResult v) as exx.
            assert (val := Validity). unfold ValidProgram in val.
            unfold LookupMethod in H3. unfold LookupMethodAmbig in H3.
            destruct p. unf. apply H0 in H3. inv H3.
            apply H8 in H5. inv H5. inv H13. eex.
          inv exx.
          eexists; eapply StepCallFinish; eauto.
        **apply IHx0_1 in H4.
          unf.
          inversion H; subst.
          ++eexists.
            eapply StepSeqExit.
            eauto.
          ++eexists.
            eapply StepSeqExit.
            eauto.
    * clear not_final.
      inv valid.
      unf.
      clear H3.
      inv H0.
      inv H.
      inv H1.
      inv H4.
      eexists.
      eapply StepVarAssign.
      eauto.
    * clear not_final.
      inv valid.
      unf.
      clear H3.
      inv H0.
      inv H.
      inv H1.
      inv H13.
      unf.
      inv H10.
      inv H16.
      eexists.
      eapply StepCall; eauto.

      assert (lookup := H7).
      clear H5 H6 H11 H12 H17 H18.
      assert (EvalExpr x (ExprVar s1) v1) as ee. ctor. assumption.
      apply SwapVarEnvEvalFormula; try congruence.
      assert (subst := H8).
      eapply SubstFormSemantics in H8; eauto.
      apply H in H3. symmetry in H8. rewrite H8 in H3. clear H8.
      rewrite (ObservablyIdenticalVarEnvEvalFormula [(VarIdent i)]); eauto.
      --intro gx. intro ingx. inv ingx; try (intuition; fail).
        intro v. split; intro ev; inv ev; try (intuition; fail); ctor.
      --assert (va := Validity). unfold ValidProgram in va.
        inv lookup. unfold LookupMethodAmbig in H2.
        destruct p. unf.
        apply H10 in H6. inv H6.
        intro xx. intro fv. apply H11 in fv. ctor. congruence.
    * clear not_final.
      inv valid.
      unf.
      clear H3.
      inv H0.
      inv H.
      inv H1.
      eexists.
      eapply StepAssert.
      assumption.
    * clear not_final IHs2.
      clac (s1 = StmtSkip).
      + subst.
        eexists.
        eapply StepSkip.
      + assert (∃ pi' : Set_State, Step (StackCons (StackFrame rho s1) pi) pi').
          apply IHs1.
            inv valid. unf. inv H1. clear H4.
            inv H0.
            unfold LocallyValidState.
            eex. intros. subst. congruence.
          unfold not. intro fs. inv fs; try congruence.
          unf. inv H1. congruence.
        clear IHs1 valid.
        unf. destruct x.
          inv H1.
        destruct s.
        clac (x = pi).
        --subst.
          exists (StackCons (StackFrame s (StmtSeq s0 s2)) pi).
          constructor; assumption.
        --inversion H1; try congruence; subst.
          **eexists. eapply StepSeqEnter. eauto.
          **eexists. eapply StepSeqEnter. eauto.
          **apply StepPopOnlyWithSkip in H3.
            congruence.
Qed.

Proposition Progress : ∀ (pi : Set_State),
  ValidState pi ->
  ~ FinalState pi ->
  (exists pi', Step pi pi').
Proof.
  intros.
  apply ProgressHelper; auto.
  apply LocalValidity.
  auto.
Qed.

Inductive Invariant : Set_State -> Prop :=
| InvariantBase : forall rho s, Invariant (StackCons (StackFrame rho s) StackEmpty)
| InvariantCons : forall rho rho' s s' S m x i v _y _T1 _T2 _c _r,
  FirstStmt s (StmtCall _y m x) ->
  LookupMethod m (Method _T1 m _T2 i _c _r) ->
  EvalVar rho x v ->
  EvalVar rho' (VarOldIdent i) v ->
  Invariant (StackCons (StackFrame rho s) S) ->
  Invariant (StackCons (StackFrame rho' s') (StackCons (StackFrame rho s) S))
.

Lemma StepLocalityLocal1 : ∀ s s' rho rho',
  Step (StackCons (StackFrame rho s) StackEmpty) (StackCons (StackFrame rho' s') StackEmpty) ->
  ∀ pi, Step (StackCons (StackFrame rho s) pi) (StackCons (StackFrame rho' s') pi).
Proof.
  induction s; intro; intro; intro; intro step; intro;
  inv step;
  ctor; auto.
Qed.

Lemma StepLocalityLocal2 : ∀ s s' rho rho' pi,
  Step (StackCons (StackFrame rho s) pi) (StackCons (StackFrame rho' s') pi) ->
  Step (StackCons (StackFrame rho s) StackEmpty) (StackCons (StackFrame rho' s') StackEmpty).
Proof.
  induction s; intros;
  inv H;
  try (ctor; auto; fail).
  - symmetry in H5. apply RecStack1 in H5. inv H5.
  - symmetry in H5. apply RecStack1 in H5. inv H5.
  - symmetry in H5. apply RecStack1 in H5. inv H5.
  - apply RecStack1 in H8. inv H8.
  - symmetry in H5. apply RecStack1 in H5. inv H5.
  - symmetry in H5. apply RecStack1 in H5. inv H5.
  - ctor; auto. eapply IHs1; eauto.
  - apply RecStack1 in H6. inv H6.
  - symmetry in H5. apply RecStack1 in H5. inv H5.
Qed.

Lemma StepLocalityLocal : ∀ s s' rho rho' pi,
  Step (StackCons (StackFrame rho s) pi) (StackCons (StackFrame rho' s') pi) <->
  Step (StackCons (StackFrame rho s) StackEmpty) (StackCons (StackFrame rho' s') StackEmpty).
Proof.
  split; intro step.
  - eapply StepLocalityLocal2; eauto.
  - eapply StepLocalityLocal1; eauto.
Qed.

Lemma PreservationLocal : ∀ s s' rho rho',
  Step (StackCons (StackFrame rho s) StackEmpty) (StackCons (StackFrame rho' s') StackEmpty) -> forall p,
  (exists phi,  WP s  p phi  /\ EvalFormula rho  phi) ->
  (exists phi', WP s' p phi' /\ EvalFormula rho' phi').
Proof.
  induction s; intro; intro; intro; intro step; intro; intro valid;
  unf;
  rename H0 into wp;
  rename H1 into ev;
  inv wp; inv step.
  - inv ev.
    eexists.
    repeat ctor.
    eapply SubstFormSemantics; eauto.
  - inv ev.
    eexists.
    repeat ctor.
    assumption.
  - inv H4.
    eexists.
    split; eauto.
  - eapply IHs1 in H8.
    Focus 2. eexists. split; eauto.
    unf.
    eexists.
    split; eauto.
    ctor; eauto.
Qed.

Proposition PreservationEnter : ∀ y m x s rho rho',
  Step (StackCons (StackFrame rho (StmtCall y m x)) StackEmpty) 
       (StackCons (StackFrame rho' s) (StackCons (StackFrame rho (StmtCall y m x)) StackEmpty)) ->
  (exists phi' phi2 _T1 _T2 i _phi1 v,
            (LookupMethod m (Method _T1 m _T2 i (Contract _phi1 phi2) s)) /\
            EvalVar rho x v /\
            EvalVar rho' (VarOldIdent i) v /\
            WP s phi2 phi' /\ EvalFormula rho' phi').
Proof.
  intro; intro; intro; intro; intro; intro; intro step.
  inv step.
  assert (exists p, WP s _phi p /\ forall rho, EvalVar rho (VarOldIdent i) v -> EvalVar rho (VarIdent i) v -> EvalFormula rho phi -> EvalFormula rho p) as ex.
    assert (val := Validity). unfold ValidProgram, LookupMethod, LookupMethodAmbig in *.
    destruct p. unf. apply H0 in H3.
    inv H3. unf.
    eexists.
    split. eauto.
    intro. intro ev1. intro ev2. intro ef.
    apply H12 in ef.
    eapply SubstFormSemantics in H6; eauto.
    Focus 2. ctor. eauto.
    apply H6 in ef.
    assert (fvl := FreeVarFormUpperBound x1). unf.
    eapply ObservablyIdenticalVarEnvEvalFormula; eauto.
    intro. intro inx. intro.
    split; intro evar.
      clac (x4 = VarOldIdent i).
        subst. assert (v0 = v). eapply EvalVarDet in evar; eauto. subst. ctor.
        ctor; auto.
      inv evar; auto.
  unf.
  eexists. eexists. eexists. eexists. eexists. eexists. eexists.
  split. eauto.
  split. eauto.
  split. ctor.
  split. eauto.
  apply H1.
  - ctor.
  - ctor; try congruence. ctor.
  - assumption.
Qed.

Lemma StepLocalityEnter : ∀ s s' s'' rho rho' rho'' pi,
  Step (StackCons (StackFrame rho s) pi) (StackCons (StackFrame rho' s') (StackCons (StackFrame rho'' s'') pi)) <->
  Step (StackCons (StackFrame rho s) StackEmpty) (StackCons (StackFrame rho' s') (StackCons (StackFrame rho'' s'') StackEmpty)).
Proof.
  induction s; split; intro step; inv step;
  try (symmetry in H4; apply RecStack2 in H4; inv H4; fail);
  try (symmetry in H5; apply RecStack1 in H5; inv H5; fail);
  try (symmetry in H6; apply RecStack1 in H6; inv H6; fail).
  - ctor; eauto.
  - ctor; eauto.
  - ctor. apply IHs1 in H0. assumption.
  - ctor. apply IHs1. assumption.
Qed.

Proposition PreservationExit : ∀ y m x s rho rho' rho'' _phi1 phi2 i _T1 _T2 v,
  Step (StackCons (StackFrame rho'' StmtSkip) (StackCons (StackFrame rho (StmtCall y m x)) StackEmpty))
       (StackCons (StackFrame rho' StmtSkip) StackEmpty) ->
  EvalVar rho x v -> EvalVar rho'' (VarOldIdent i) v ->
  LookupMethod m (Method _T1 m _T2 i (Contract _phi1 phi2) s) -> forall p,
  (exists phi, WP (StmtCall y m x) p phi /\ EvalFormula rho phi) ->
  EvalFormula rho' p.
Proof.
  intro. intro. intro. intro. intro. intro. intro. intro. intro. intro. intro. intro. intro.
  intro step. intro ev1. intro ev2. intro lookup. intro.
  intro pre.
  unf.
  inv step.
  eapply LookupMethodDet in lookup; eauto. inv lookup.
  inv H0.
  eapply LookupMethodDet in H4; eauto. inv H4.
  inv H16. apply H. (*MaxImplies*)
  ctor.
  - inv H1.
    eapply (ObservablyIdenticalVarEnvEvalFormula [x]); eauto.
    * intro gx. intro ingx. inv ingx; try (intuition; fail).
      intro vx. split; intro ev.
      + inv ev; try congruence.
      + ctor; assumption.
    * intro xx. intro fvf. apply H in fvf. subst. ctor. auto.
  - (* first subst *)
    assert (EvalExpr (VarEnvMapping y v0 rho) (ExprVar y) v0) as tmp.
      ctor. ctor.
    eapply SubstFormSemantics in H15; eauto.
    symmetry in H15.
    rewrite H15.
    clear H15 tmp.
    (* second subst *)
    assert (exists vv, EvalExpr (VarEnvMapping VarResult v0 (VarEnvMapping y v0 rho)) (ExprVar x) vv /\ EvalVar rho'' (VarOldIdent i) vv) as tmp.
      inv H1. inv H14. exists v1. inv H15.
      split.
        ctor. ctor; try congruence. ctor; congruence.
        eapply EvalVarDet in ev1; eauto.
        subst. assumption.
    inv tmp. inv H2.
    eapply SubstFormSemantics in H12; eauto.
    symmetry in H12.
    rewrite H12. clear H12.
    (* obs. eq. *)
    eapply (ObservablyIdenticalVarEnvEvalFormula [(VarOldIdent i); VarResult]); eauto.
    * inv H3. inv H13; try congruence. inv H17; try congruence.
      intro gx. intro ingx. intro vv.
      split; intro ev.
      + inv ev; auto.
        inv ingx; try congruence.
        inv H2; try (intuition; fail).
        inv H19; congruence.
      + inv ingx.
        --eapply EvalVarDet in H4; eauto. subst. ctor.
        --inv H2; try (intuition; fail).
          ctor; try congruence.
          eapply EvalVarDet in H9; eauto. subst. ctor.
    * intro. intro fvf.
      assert (va := Validity).
      unfold ValidProgram in va.
      rename H8 into lookup. inv lookup. unfold LookupMethodAmbig in *.
      destruct p. unf. apply H14 in H12.
      inv H12. apply H19 in fvf. inv fvf; intuition.
Qed.

Lemma StepLocalityExit : ∀ s'' s s' rho rho' rho'' pi,
  Step (StackCons (StackFrame rho s) (StackCons (StackFrame rho'' s'') pi)) (StackCons (StackFrame rho' s') pi) <->
  Step (StackCons (StackFrame rho s) (StackCons (StackFrame rho'' s'') StackEmpty)) (StackCons (StackFrame rho' s') StackEmpty).
Proof.
  induction s''; split; intro step; inv step;
  try (apply RecStack1 in H5; inv H5; fail);
  try (apply RecStack2 in H5; inv H5; fail);
  try (apply RecStack2 in H4; inv H4; fail);
  auto.
  - ctor; eauto.
  - ctor; eauto.
  - ctor. apply IHs''1 in H0. assumption.
  - ctor. apply IHs''1. assumption.
Qed.

Proposition ValidStateLocality : ∀ p rho' s' rho s pi,
  ValidStateEx p (StackCons (StackFrame rho' s') (StackCons (StackFrame rho s) pi)) <->
  ValidStateEx p (StackCons (StackFrame rho s) pi) /\
  (exists m phi _phi _y _x _T1 _T2 _i _r v, FirstStmt s (StmtCall _y m _x) /\ LookupMethod m (Method _T1 m _T2 _i (Contract _phi phi) _r) /\
  EvalVar rho' (VarOldIdent _i) v /\
  EvalVar rho _x v /\
  ValidStateEx phi (StackCons (StackFrame rho' s') StackEmpty)).
Proof.
  split; intro vs.
  - inv vs.
    split; auto.
    eex.
    ctor; eauto.
  - unf.
    inv H5.
    ctor; eauto.
Qed.

Proposition ValidStateTopMost : ∀ p sf pi,
  ValidStateEx p (StackCons sf pi) ->
  exists p', ValidStateEx p' (StackCons sf StackEmpty).
Proof.
  intros.
  destruct pi.
  - eex.
  - destruct sf. destruct s. apply ValidStateLocality in H.
    unf.
    eex.
Qed.

Proposition PreservationLocalEx : ∀ pi sf sf',
  Step (StackCons sf pi) (StackCons sf' pi) -> forall p,
  (ValidStateEx p (StackCons sf pi)) ->
  (ValidStateEx p (StackCons sf' pi)).
Proof.
  intro. intro. intro. intro step. intro. intro valid.
  destruct sf. destruct sf'.
  apply StepLocalityLocal in step.
  destruct pi.
  - inv valid.
    eapply PreservationLocal in step.
    Focus 2. eex.
    unf.
    ctor; eauto.
  - destruct s3. apply ValidStateLocality in valid.
    apply ValidStateLocality.
    split. apply valid.
    apply proj2 in valid.
    unf.
    assert (step' := step).
    eapply PreservationLocal in step.
    Focus 2. inv H4. eex.
    unf.
    eex.
    * inv H4.
      generalize s0 x0 s2 phi H9 H1 step'. clear. induction s0; intro; intro; intro; intro wp; intro ev; intro step; inv step; auto.
      + inv wp.
        eapply not_ex_all_not in H2.
        ctor; eauto.
      + inv wp.
        eapply IHs0_1 in H6; eauto.
    * ctor; eauto.
Qed.

Lemma PreservationEnterExHelper : ∀ s0 rho sf' sf'' pi,
  Step (StackCons (StackFrame rho s0) pi) (StackCons sf' (StackCons sf'' pi)) -> forall p,
  (ValidStateEx p (StackCons (StackFrame rho s0) StackEmpty)) ->
  (StackFrame rho s0) = sf'' /\
  exists rho' s2 y m x,
  sf' = (StackFrame rho' s2) /\
  FirstStmt s0 (StmtCall y m x) /\
  exists _T1 _T2 x' _phi phi,
  LookupMethod m (Method _T1 m _T2 x' (Contract _phi phi) s2) /\
  ValidStateEx phi (StackCons sf' StackEmpty) /\
  exists v, EvalVar rho x v /\ EvalVar rho' (VarOldIdent x') v.
Proof.
  induction s0; intro; intro; intro; intro; intro step; intro; intro valid; inv step;
  try (symmetry in H2; apply RecStack2 in H2; inv H2; fail);
  try (symmetry in H3; apply RecStack2 in H3; inv H3; fail);
  try (symmetry in H4; apply RecStack1 in H4; inv H4; fail);
  try (symmetry in H5; apply RecStack1 in H5; inv H5; fail).
  - split. auto.
    eexists. eexists. eexists. eexists. eexists. eexists. eexists.
    split. ctor. intro c. unf. inv H0. 
    eexists. eexists. eexists. eexists. eexists.
    split. eauto.
    split. Focus 2. eex. ctor.

    assert (val := Validity).
    unfold ValidProgram, LookupMethod, LookupMethodAmbig in *. destruct p. unf. apply H0 in H3. inv H3. unf. ctor.
    eauto.
    apply H12 in H9. eapply SubstFormSemantics in H6. apply H6 in H9. Focus 2. ctor. ctor; try congruence. ctor.
    assert (fvf := FreeVarFormUpperBound x0). unf.
    eapply ObservablyIdenticalVarEnvEvalFormula; eauto.
    intros. split; intro ev; inv ev; ctor; auto.
    * ctor; auto.
    * inv H21; congruence.
  - inv valid. inv H3.
    eapply IHs0_1 in H0.
    Focus 2. ctor; eauto.
    unf.
    inv H.
    split. auto.
    eexists. eexists. eexists. eexists. eexists.
    split. eauto.
    split. ctor. eauto.
    eexists. eexists. eexists. eexists. eexists.
    split; eauto.
Qed.

Lemma PreservationEnterEx : ∀ sf sf' sf'' pi,
  Step (StackCons sf pi) (StackCons sf' (StackCons sf'' pi)) -> forall p,
  (ValidStateEx p (StackCons sf pi)) ->
  (ValidStateEx p (StackCons sf' (StackCons sf'' pi))).
Proof.
  intro. destruct sf. generalize s0 s. clear.
  intro; intro; intro; intro; intro; intro step; intro; intro valid;
  destruct sf'; destruct sf''.
  destruct pi.
  - eapply PreservationEnterExHelper in step; eauto.
    unf. inv H. inv H0.
    eapply ValidStateLocality.
    split; auto.
    eex.
  - destruct s5. apply ValidStateLocality in valid.
    unf.
    eapply PreservationEnterExHelper in step; eauto.
    unf. inv H4. inv H6.
    eapply ValidStateLocality.
    split. inv H5. ctor; eauto.
    eex.
Qed.

Lemma FirstStmtDet : forall s s1 s2, FirstStmt s s1 -> FirstStmt s s2 -> s1 = s2.
Proof.
  induction s; intro; intro; intro fs1; intro fs2; inv fs1; inv fs2; auto.
  - contradict H. eex.
  - contradict H. eex.
Qed.
(* 
Lemma PreservationExitExHelper : ∀ s0 rho sf sf' pi,
  Step (StackCons sf' (StackCons (StackFrame rho s0) pi)) (StackCons sf pi) -> forall p,
  (ValidStateEx p (StackCons (StackFrame rho s0) StackEmpty)) ->
  exists rho' rho'' s2 y m x,
  sf' = (StackFrame rho'' StmtSkip) /\
  sf = (StackFrame rho' StmtSkip) /\
  FirstStmt s0 (StmtCall y m x) /\
  exists _T1 _T2 x' _phi phi,
  LookupMethod m (Method _T1 m _T2 x' (Contract _phi phi) s2) /\
  ValidStateEx phi (StackCons sf' StackEmpty) /\
  exists v, EvalVar rho x v /\ EvalVar rho' (VarOldIdent x') v.

  (ValidStateEx p (StackCons sf' (StackCons sf'' StackEmpty))) ->
  (ValidStateEx p (StackCons sf StackEmpty)).
Proof.
  intro. destruct sf''. generalize s0 s. clear.
  induction s0; intro; intro; intro; intro; intro step; intro; intro valid;
  inv step;
  try (apply RecStack1 in H3; inv H3; fail);
  try (apply RecStack2 in H3; inv H3; fail);
  try (apply RecStack2 in H2; inv H2; fail).
  - inv valid.
    inv H5. inv H10.
    admit.
  - inv valid. inv H11. inv H3.
    ctor.
    ctor; eauto.
    ctor.

    destruct sf'. apply ValidStateLocality in valid. unf.
    destruct pi.
    * inv H. inv H9.
      eapply IHs0_1 in H0.
      + inv H0. ctor; eauto. ctor; eauto.
      + inv H6. inv H2. ctor; eauto. ctor; eauto.
    * destruct s2. apply ValidStateLocality in H. unf.
      apply ValidStateLocality.
      split; auto. clear H5.
      eexists. eexists. eexists. eexists. eexists. eexists. eexists. eexists. eexists. eexists.
      split. eauto.
 *)

Lemma StepExitDoesntAlterOldVariable : forall s s' rho rho' sf i v phi1 phi2,
  WP s phi1 phi2 ->
  Step (StackCons sf (StackCons (StackFrame rho s) StackEmpty)) (StackCons (StackFrame rho' s') StackEmpty) ->
  EvalVar rho (VarOldIdent i) v ->
  EvalVar rho' (VarOldIdent i) v.
Proof.
  induction s; intro; intro; intro; intro; intro; intro; intro; intro; intro wp; intro step; intro ev; inv step.
  - inv wp.
    ctor; eauto.
  - inv wp.
    eapply IHs1 in H0; eauto.
Qed.

Lemma PreservationExitEx : ∀ sf'' sf sf' pi,
  Step (StackCons sf' (StackCons sf'' pi)) (StackCons sf pi) -> forall p,
  (ValidStateEx p (StackCons sf' (StackCons sf'' pi))) ->
  (ValidStateEx p (StackCons sf pi)).
Proof.
  intro. destruct sf''. generalize s0 s. clear.
  induction s0; intro; intro; intro; intro; intro step; intro; intro valid;
  inversion step; subst;
  try (apply RecStack1 in H3; inv H3; fail);
  try (apply RecStack2 in H3; inv H3; fail);
  try (apply RecStack2 in H2; inv H2; fail).
  - inv valid.
    inv H5. inv H10.
    clear H1.
    eapply LookupMethodDet in H2; eauto. inv H2.
    apply StepLocalityExit in step.
    destruct pi.
    * inv H14.
      eapply PreservationExit in step; eauto.
      ctor; eauto. ctor.
    * inv H14.
      eapply PreservationExit in step; eauto.
      ctor; eauto. ctor.
      ctor; eauto.
      inv H3. intro c. contradict H2. eex.
  - clear IHs0_2.
    destruct sf'.
    apply StepLocalityExit in H0.
    apply ValidStateLocality in valid. unf.

    destruct pi.
    * inv H. inv H9.
      eapply IHs0_1 in H0.
      + inv H0. ctor; eauto. ctor; eauto.
      + inv H6. inv H2. ctor; eauto. ctor; eauto.
    * destruct s2. apply ValidStateLocality in H. unf.
      inv H11. inv H14.
      apply ValidStateLocality.
      split; auto.
      eexists. eexists. eexists. eexists. eexists. eexists. eexists. eexists. eexists. eexists.
      split. eauto.
      split. eauto.
      assert (EvalVar rho' (VarOldIdent x16) x18) as ev.
        apply (StepExitDoesntAlterOldVariable s0_1 s1' s rho' (StackFrame s0 s1) x16 x18 phi2 phi); auto.
      split. apply ev.
      split. assumption.

      eapply IHs0_1 in H0.
      + inv H0. ctor; eauto. ctor; eauto.
      + inv H6. inv H2. ctor; eauto. ctor; eauto.
Qed.

Proposition Preservation : ∀ (pi pi' : Set_State),
  Step pi pi' -> forall p,
  (ValidStateEx p pi) ->
  (ValidStateEx p pi').
Proof.
  intro. intro. intro step. intro.
  intro valid.
  inversion step; subst;
  try (eapply PreservationLocalEx in step; eauto; fail);
  try (eapply PreservationEnterEx in step; eauto; fail);
  try (eapply PreservationExitEx in step; eauto; fail).
Qed.

End Semantics.




