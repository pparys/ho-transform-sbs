Require Import List.
Import ListNotations.
Require Import Nat.
Require Import Omega.
Require Import Program.
Load ListLemmata.
Load TypeCast.

(***********************************************************************************************)
(* PART 1: Definitions of type, term, grammar, etc.                                            *)
(***********************************************************************************************)

Inductive type := 
  | Arr : list type -> type.

Definition Ground := Arr [].

Fixpoint ArgsOfType t := match t with Arr T => T end.

Inductive ElementOfList {A} (a : A) : list A -> Type :=
  | FirstEl tail : ElementOfList a (a :: tail)
  | NextEl first tail : ElementOfList a tail -> ElementOfList a (first :: tail).

Inductive term Nn Vv : type -> Set :=
  | Nontermi : forall t, ElementOfList t Nn -> term Nn Vv t
  | Var : forall t, ElementOfList t Vv -> term Nn Vv t
  | And : list (term Nn Vv Ground) -> term Nn Vv Ground
  | Or : list (term Nn Vv Ground) -> term Nn Vv Ground
  | App : forall t T, term Nn Vv (Arr (t :: T)) -> term Nn Vv t -> term Nn Vv (Arr T).

Inductive rule Nn t := 
  | RuleCons : term Nn (ArgsOfType t) Ground -> rule Nn t.

Definition TermOfRule {Nn t} (rule : rule Nn t) : term Nn (ArgsOfType t) Ground :=
  match rule with RuleCons _ _ M => M end.

Inductive rules_ind NnAll : list type -> Set := 
  | EmptyRules : rules_ind NnAll []
  | ConsRules : forall t Nn_tail, rule NnAll t -> rules_ind NnAll Nn_tail 
      -> rules_ind NnAll (t :: Nn_tail).

Definition rules Nn := rules_ind Nn Nn.

Fixpoint FindInRules {NnAll Nn t} (Rr : rules_ind NnAll Nn) (X : ElementOfList t Nn) : rule NnAll t :=
  match X in ElementOfList _ Nn return rules_ind _ Nn -> _ with
  | FirstEl _ _ => fun Rr => match Rr with ConsRules _ _ _ rule1 _ => rule1 end
  | NextEl _ _ _ X_tail => fun Rr =>
      match Rr with ConsRules _ _ _ _ Rr_tail => fun X_tail => FindInRules Rr_tail X_tail end X_tail
  end Rr.

Inductive grammar :=
  | Grammar : forall Nn, ElementOfList Ground Nn -> rules Nn -> grammar.

Definition NontermsOfGrammar Gg := 
  match Gg with Grammar Nn _ _ => Nn end.

Definition StartingNontermOfGrammar Gg : ElementOfList Ground (NontermsOfGrammar Gg):= 
  match Gg with Grammar _ X0 _ => X0 end.

Definition RulesOfGrammar Gg : (rules (NontermsOfGrammar Gg)) := 
  match Gg with Grammar _ _ Rr => Rr end.

Inductive substitution Nn VvNew : list type -> Set :=
  | EmptySubst : substitution Nn VvNew []
  | ConsSubst : forall t Vv_tail, term Nn VvNew t -> substitution Nn VvNew Vv_tail 
      -> substitution Nn VvNew (t :: Vv_tail).

Fixpoint FindInSubstitution {Nn VvNew Vv t} (sub : substitution Nn VvNew Vv) (x : ElementOfList t Vv) : term Nn VvNew t :=
  match x in ElementOfList _ Vv return substitution _ _ Vv -> _ with
  | FirstEl _ _ => fun sub => match sub with ConsSubst _ _ _ _ M1 _ => M1 end
  | NextEl _ _ _ x_tail => fun sub =>
      match sub with ConsSubst _ _ _ _ _ sub_tail => fun x_tail => FindInSubstitution sub_tail x_tail end x_tail
  end sub.

Fixpoint Substitute {Nn VvNew Vv} (sub : substitution Nn VvNew Vv) {t} (M : term Nn Vv t) : term Nn VvNew t :=
  match M with 
  | Nontermi _ _ _ X => Nontermi _ _ _ X
  | Var _ _ _ x => FindInSubstitution sub x
  | And _ _ chldrn => And _ _ (map (Substitute sub) chldrn)
  | Or _ _ chldrn => Or _ _ (map (Substitute sub) chldrn)
  | App _ _ _ _ K L => App _ _ _ _ (Substitute sub K) (Substitute sub L)
  end.

Fixpoint ApplyArgs {Nn VvNew Vv} (sub : substitution Nn VvNew Vv) : term Nn VvNew (Arr Vv) -> term Nn VvNew Ground :=
  match sub with
  | EmptySubst _ _ => fun K => K
  | ConsSubst _ _ _ _ L1 sub_tail => fun K => ApplyArgs sub_tail (App _ _ _ _ K L1)
  end.

Section Reduces.
  Variable Gg : grammar.
  Let Nn := NontermsOfGrammar Gg.

  Inductive Reduces {Vv} : term Nn Vv Ground -> list (term Nn Vv Ground) -> Prop := 
    | ReducesNontermi : forall t X (sub : substitution _ _ (ArgsOfType t)),
        Reduces (ApplyArgs sub (Nontermi _ _ _ X))
          [Substitute sub (TermOfRule (FindInRules (RulesOfGrammar Gg) X))]
    | ReducesOr : forall K chldrn, In K chldrn -> Reduces (Or _ _ chldrn) [K]
    | ReducesAnd : forall chldrn, Reduces (And _ _ chldrn) chldrn.

  Inductive ProducesFiniteTree : term Nn [] Ground -> Prop := 
    | PFTReduces : forall M NNN, Reduces M NNN -> (forall N, In N NNN -> ProducesFiniteTree N)
        -> ProducesFiniteTree M.
End Reduces.

Definition GrammarProducesFiniteTree Gg := ProducesFiniteTree Gg (Nontermi _ _ _ (StartingNontermOfGrammar Gg)).

(***********************************************************************************************)
(* PART 2: Definitions of the transformation                                                   *)
(***********************************************************************************************)

Definition OnlyOrder0Vars := fold_right (fun t acc => match t with Arr [] => acc | _ => false end) true.

Fixpoint TailLen T := match T with
  | [] => 0
  | t1 :: T_tail => if OnlyOrder0Vars (t1 :: T_tail) then length (t1 :: T_tail) else TailLen T_tail
  end.

Fixpoint HOPart T := match T with
  | [] => []
  | t1 :: T_tail => if OnlyOrder0Vars (t1 :: T_tail) then [] else t1 :: HOPart T_tail
  end.

Fixpoint AppendVarAux (t_app : type) numG Vv := match numG with
  | 0 => t_app :: Vv
  | S numG0 => AppendVarAux t_app numG0 (AppendVarAux t_app numG0 Vv)
  end.

Fixpoint TransType t := match t with 
  | Arr T => Arr ((fix TransTypeList T := match T with 
    | [] => [] 
    | t1 :: T_tail => if OnlyOrder0Vars T then [] else
        AppendVarAux (TransType t1) (TailLen (ArgsOfType t1)) (TransTypeList T_tail) 
    end) T)
  end.

Definition TransVars := fold_right (fun t => AppendVarAux (TransType t) (TailLen (ArgsOfType t))) [].

Definition GrVars numG := repeat Ground numG.

Fixpoint Subset numG := match numG with
  | 0 => unit
  | S numG0 => prod bool (Subset numG0)
  end.

Definition Subset0 : Subset (TailLen (ArgsOfType Ground)) := tt.

Fixpoint ShiftVarAux (t_app : type) numG {Vv t} (x : ElementOfList t Vv) : 
    ElementOfList t (AppendVarAux t_app numG Vv) := 
  match numG with
  | 0 => NextEl _ _ _ x
  | S numG0 => ShiftVarAux t_app numG0 (ShiftVarAux t_app numG0 x)
  end.

Fixpoint FindNewVarAux (t_app : type) {numG} (A : Subset numG) Vv :=
  match numG as numG return Subset numG -> ElementOfList t_app (AppendVarAux t_app numG Vv) with
  | 0 => fun _ => FirstEl _ _
  | S numG0 => fun A => match A with
      | (val, A_tail) => if val then ShiftVarAux t_app numG0 (FindNewVarAux t_app A_tail Vv)
          else FindNewVarAux t_app A_tail (AppendVarAux t_app numG0 Vv) 
      end
  end A.

Fixpoint FindNewVar {Vv t} (A : Subset (TailLen (ArgsOfType t))) (x : ElementOfList t Vv) : 
    ElementOfList (TransType t) (TransVars Vv) :=
  match x with
  | FirstEl _ Vv_tail => FindNewVarAux (TransType t) A (TransVars Vv_tail)
  | NextEl _ t1 Vv_tail x_tail => ShiftVarAux (TransType t1) (TailLen (ArgsOfType t1)) (FindNewVar A x_tail)
  end.

(* Now we have some lemmata needed for type casts in definitions below *)

Lemma SkipInTail_HO {t1 Vv_tail} (eq : OnlyOrder0Vars (t1 :: Vv_tail) = false) : TailLen (t1 :: Vv_tail) = TailLen Vv_tail.
  unfold TailLen.
  rewrite eq.
  auto.
Qed.

Lemma SkipInTail_HO_castV {t t1 Vv_tail} (eq : OnlyOrder0Vars (t1 :: Vv_tail) = false) :
    ElementOfList t (GrVars (TailLen Vv_tail)) = ElementOfList t (GrVars (TailLen (t1 :: Vv_tail))).
  rewrite SkipInTail_HO; auto.
Qed.

Lemma FirstIsGround_oo0 {t1 Vv_tail} (eq : OnlyOrder0Vars (t1 :: Vv_tail) = true) : t1 = Ground.
  destruct t1.
  destruct l; easy.
Qed.

Lemma TailIsAll_oo0 {Vv} (eq : OnlyOrder0Vars Vv = true) : Vv = GrVars (TailLen Vv).
  induction Vv.
    auto.
  assert (OnlyOrder0Vars Vv = true).
    destruct a.
    destruct l; easy.
  replace (TailLen (a :: Vv)) with (S (TailLen Vv)).
    rewrite IHVv at 1; auto.
    rewrite (FirstIsGround_oo0 eq); auto.
    auto.
  unfold TailLen.
  rewrite eq.
  destruct Vv; auto.
  rewrite H.
  auto.
Qed.

Lemma TailIsAll_oo0_castV {t Vv} (eq : OnlyOrder0Vars Vv = true) :
    ElementOfList t Vv = ElementOfList t (GrVars (TailLen Vv)).
  rewrite TailIsAll_oo0 at 1; auto.
Qed.

Lemma ShiftInHO_HO {t1 Vv_tail} (eq : OnlyOrder0Vars (t1 :: Vv_tail) = false) : HOPart (t1 :: Vv_tail) = t1 :: HOPart Vv_tail.
  unfold HOPart.
  rewrite eq.
  auto.
Qed.

Lemma ShiftInHO_HO_castV {t t1 Vv_tail} (eq : OnlyOrder0Vars (t1 :: Vv_tail) = false) :
    ElementOfList t (t1 :: HOPart Vv_tail) = ElementOfList t (HOPart (t1 :: Vv_tail)).
  rewrite ShiftInHO_HO; auto.
Qed.

Lemma OnlyGround_GrVars {t numG} (x : ElementOfList t (GrVars numG)) : t = Ground.
  induction numG.
    easy.
  dependent destruction x.
    easy.
  apply IHnumG.
  auto.
Qed.

Lemma OnlyGround_GrVars_castT {Nn Vv t numG} (x : ElementOfList t (GrVars numG)) : term Nn Vv Ground = term Nn Vv (TransType t).
  rewrite (OnlyGround_GrVars x); auto.
Qed.

Lemma ShiftInTail_oo0 {t1 Vv_tail} (eq : OnlyOrder0Vars (t1 :: Vv_tail) = true) : TailLen (t1 :: Vv_tail) = S (TailLen Vv_tail).
  unfold TailLen.
  rewrite eq.
  destruct t1.
  destruct l; try easy.
  simpl in eq.
  destruct Vv_tail.
    auto.
  rewrite eq.
  auto.
Qed.

Lemma ShiftInTail_oo0_castSet {t1 T_tail} (eq : OnlyOrder0Vars (t1 :: T_tail) = true) :
    prod bool (Subset (TailLen T_tail)) = Subset (TailLen (ArgsOfType (Arr (t1 :: T_tail)))).
  unfold ArgsOfType.
  rewrite ShiftInTail_oo0; auto.
Qed.

Lemma TransTypeIsGround_oo0 {T} (eq : OnlyOrder0Vars T = true) : TransType (Arr T) = Ground.
  destruct T.
    auto.
  unfold TransType.
  rewrite eq.
  auto.
Qed.

Lemma TransTypeIsGround_oo0_castT {Nn Vv T} (eq : OnlyOrder0Vars T = true) :
    term Nn Vv (TransType (Arr T)) = term Nn Vv Ground.
  rewrite TransTypeIsGround_oo0; auto.
Qed.

Lemma TransTypeTailIsGround_oo0 {t1 T_tail} (eq : OnlyOrder0Vars (t1 :: T_tail) = true) : TransType (Arr T_tail) = Ground.
  rewrite TransTypeIsGround_oo0.
    auto.
  destruct t1.
  destruct l; easy.
Qed.

Lemma TransTypeTailIsGround_oo0_castT {Nn Vv t1 T_tail} (eq : OnlyOrder0Vars (t1 :: T_tail) = true) : 
    term Nn Vv Ground = term Nn Vv (TransType (Arr T_tail)).
  rewrite (TransTypeTailIsGround_oo0 eq); auto.
Qed.

Lemma FirstIsGround_oo0_castSet {t1 T_tail} (eq : OnlyOrder0Vars (t1 :: T_tail) = true) :
    (unit : Type) = Subset (TailLen (ArgsOfType t1)).
  rewrite (FirstIsGround_oo0 eq).
  auto.
Qed.

Lemma FirstIsGround_oo0_castT {Nn Vv t1 T_tail} (eq : OnlyOrder0Vars (t1 :: T_tail) = true) :
    term Nn Vv (TransType t1) = term Nn Vv Ground.
  rewrite (FirstIsGround_oo0 eq).
  auto.
Qed.

Lemma SkipInTail_HO_castSet {t1 T_tail} (eq : OnlyOrder0Vars (t1 :: T_tail) = false) :
    Subset (TailLen T_tail) = Subset (TailLen (ArgsOfType (Arr (t1 :: T_tail)))).
  unfold ArgsOfType.
  rewrite SkipInTail_HO; auto.
Qed.

Lemma TransType_HO {t1 T_tail} (eq : OnlyOrder0Vars (t1 :: T_tail) = false) :
    TransType (Arr (t1 :: T_tail)) = 
    Arr (AppendVarAux (TransType t1) (TailLen (ArgsOfType t1)) (ArgsOfType (TransType (Arr T_tail)))).
  unfold TransType.
  rewrite eq.
  auto.
Qed.

Lemma TransType_HO_castT {Nn Vv t1 T_tail} (eq : OnlyOrder0Vars (t1 :: T_tail) = false) :
    term Nn Vv (TransType (Arr (t1 :: T_tail))) = 
    term Nn Vv (Arr (AppendVarAux (TransType t1) (TailLen (ArgsOfType t1)) (ArgsOfType (TransType (Arr T_tail))))).
  rewrite TransType_HO; auto.
Qed.

Lemma DestructGrVars {t1 Vv_tail numG} (eq : t1 :: Vv_tail = GrVars (S numG)) : Vv_tail = GrVars numG.
  simplify_eq eq.
  auto.
Qed.

Lemma DestructGrVars_castV {t t1 Vv_tail numG} (eq : t1 :: Vv_tail = GrVars (S numG)) :
    ElementOfList t Vv_tail = ElementOfList t (GrVars numG).
  rewrite (DestructGrVars eq).
  auto.
Qed.

Lemma TransType_is_TransVars {t} : TransType t = Arr (TransVars (HOPart (ArgsOfType t))).
  destruct t.
  induction l.
    auto.
  unfold ArgsOfType.
  unfold TransType.
  unfold HOPart.
  destruct (OnlyOrder0Vars (a :: l)).
    auto.
  fold HOPart.
  simpl.
  simpl in IHl.
  simplify_eq IHl.
  intro.
  rewrite <- H.
  easy.
Qed.

Lemma TransType_is_TransVars_castT {Nn t t2} :
    term Nn (TransVars (HOPart (ArgsOfType t))) t2 = term Nn (ArgsOfType (TransType t)) t2.
  rewrite TransType_is_TransVars.
  auto.
Qed.

(* Now definitions again *)

Fixpoint RemainsOrTail {Vv t} (x : ElementOfList t Vv) :
    sum (ElementOfList t (HOPart Vv)) (ElementOfList t (GrVars (TailLen Vv))) :=
  match OnlyOrder0Vars Vv as oo return OnlyOrder0Vars Vv = oo -> _ with
  | true => fun eq => inr (type_cast (TailIsAll_oo0_castV eq) x)
  | false => match x in ElementOfList _ Vv return OnlyOrder0Vars Vv = false -> _ with
      | FirstEl _ _ => fun eq => inl (type_cast (ShiftInHO_HO_castV eq) (FirstEl _ _))
      | NextEl _ _ _ x_tail => fun eq => match RemainsOrTail x_tail with
          | inl x_ret => inl (type_cast (ShiftInHO_HO_castV eq) (NextEl _ _ _ x_ret))
          | inr x_ret => inr (type_cast (SkipInTail_HO_castV eq) x_ret)
          end
      end
  end eq_refl.

Fixpoint ApplyArgsForAllA {Nn Vv t_app numG T2} :
    term Nn Vv (Arr (AppendVarAux t_app numG T2)) -> (Subset numG -> term Nn Vv t_app) -> term Nn Vv (Arr T2) :=
  match numG as numG return term _ _ (Arr (AppendVarAux _ numG _)) -> (Subset numG -> _) -> _ with
  | 0 => fun K L => App _ _ _ _ K (L tt)
  | S numG0 => fun (K : term _ _ (Arr (AppendVarAux _ numG0 _))) L => 
      ApplyArgsForAllA (ApplyArgsForAllA K (fun A => L (false, A))) (fun A => L (true, A))
  end.

Fixpoint BelongsToSubset {t numG} (x : ElementOfList t (GrVars numG)) :=
  match numG as numG return ElementOfList _ (GrVars numG) -> Subset numG -> bool with
  | 0 => fun x _ => match x with end
  | S numG0 => fun x A => let (val, A_tail) := A in
      match x in ElementOfList _ Vv return Vv = GrVars (S numG0) -> _ with
      | FirstEl _ _ => fun _ => val
      | NextEl _ _ _ x_tail => fun eq => BelongsToSubset (type_cast (DestructGrVars_castV eq) x_tail) A_tail
      end eq_refl
  end x.

Fixpoint TransTerm {Nn Vv t} (A : Subset (TailLen (ArgsOfType t))) (V : Subset (TailLen Vv))
    (M : term Nn Vv t) : term (TransVars Nn) (TransVars (HOPart Vv)) (TransType t) :=
  match M in term _ _ t return Subset (TailLen (ArgsOfType t)) -> _ with
  | Nontermi _ _ _ X => fun A => Nontermi _ _ _ (FindNewVar A X)
  | Var _ _ _ x => fun A => match RemainsOrTail x with
      | inl xHO => Var _ _ _ (FindNewVar A xHO)
      | inr xFO => type_cast (OnlyGround_GrVars_castT xFO) (if BelongsToSubset xFO V then And _ _ [] else Or _ _ [])
      end
  | And _ _ chldrn => fun A => And _ _ (map (TransTerm A V) chldrn)
  | Or _ _ chldrn => fun A => Or _ _ (map (TransTerm A V) chldrn)
  | App _ _ t1 T_tail K L => fun A =>
      match OnlyOrder0Vars (t1 :: T_tail) as oo return OnlyOrder0Vars (t1 :: T_tail) = oo -> _ with
      | true => fun eq => type_cast (TransTypeTailIsGround_oo0_castT eq) (Or _ _ [
          type_cast (TransTypeIsGround_oo0_castT eq)
            (TransTerm (type_cast (ShiftInTail_oo0_castSet eq) (false, A)) V K);
          And _ _ [
            type_cast (TransTypeIsGround_oo0_castT eq)
              (TransTerm (type_cast (ShiftInTail_oo0_castSet eq) (true, A)) V K);
            type_cast (FirstIsGround_oo0_castT eq)
              (TransTerm (type_castT (FirstIsGround_oo0_castSet eq) tt) V L)]])
      | false => fun eq => ApplyArgsForAllA 
          (type_cast (TransType_HO_castT eq) (TransTerm (type_cast (SkipInTail_HO_castSet eq) A) V K))
          (fun A => TransTerm A V L)
      end eq_refl
  end A.

Definition TransRule {Nn t} (A : Subset (TailLen (ArgsOfType t))) (R : rule Nn t) : rule (TransVars Nn) (TransType t) :=
  match R with RuleCons _ _ K => 
    RuleCons _ _ (type_cast TransType_is_TransVars_castT (TransTerm Subset0 A K))
  end.

Fixpoint AppendRulesForAllA {NnAll Nn t_app numG} (R : Subset numG -> rule NnAll t_app) 
    (Rr : rules_ind NnAll Nn) : rules_ind NnAll (AppendVarAux t_app numG Nn) :=
  match numG as numG return (Subset numG -> _) -> rules_ind _ (AppendVarAux _ numG _) with
  | 0 => fun R => ConsRules _ _ _ (R tt) Rr
  | _ => fun R => AppendRulesForAllA (fun A => R (false, A)) (AppendRulesForAllA (fun A => R (true, A)) Rr)
  end R.

Fixpoint TransRules {NnAll Nn} (Rr : rules_ind NnAll Nn) : rules_ind (TransVars NnAll) (TransVars Nn) :=
  match Rr in rules_ind _ Nn return rules_ind _ (TransVars Nn) with
  | EmptyRules _ => EmptyRules _
  | ConsRules _ t1 t2 R Rr_tail => AppendRulesForAllA (fun A => TransRule A R) (TransRules Rr_tail)
  end.

Definition TransGrammar Gg := match Gg with Grammar _ X0 Rr => Grammar _ (FindNewVar Subset0 X0) (TransRules Rr) end.

(***********************************************************************************************)
(* PART 3: Definitions for an intermediate step: extended terms                                *)
(***********************************************************************************************)

(* Lemmata needed for type casts in definitions: *)

Lemma ShiftInTail_oo0_castS {Nn numGNew t1 Vv_tail} (eq : OnlyOrder0Vars (t1 :: Vv_tail) = true) : 
    substitution Nn (GrVars (S (TailLen Vv_tail) + numGNew)) (Ground :: Vv_tail) =
    substitution Nn (GrVars (TailLen (t1 :: Vv_tail) + numGNew)) (t1 :: Vv_tail).
  rewrite ShiftInTail_oo0; auto.
  rewrite (FirstIsGround_oo0 eq); auto.
Qed.

Lemma ShiftInTail_oo0_castS2 {Nn VvNew t1 Vv_tail} (eq : OnlyOrder0Vars (t1 :: Vv_tail) = true) : 
    substitution Nn VvNew (t1 :: GrVars (TailLen Vv_tail)) = substitution Nn VvNew (GrVars (TailLen (t1 :: Vv_tail))).
  rewrite ShiftInTail_oo0; auto.
  rewrite (FirstIsGround_oo0 eq); auto.
Qed.

Lemma SkipInTail_HO_castS {Nn Vv numGNew t1 Vv_tail} (eq : OnlyOrder0Vars (t1 :: Vv_tail) = false) : 
    substitution Nn (GrVars (TailLen Vv_tail + numGNew)) Vv = substitution Nn (GrVars (TailLen (t1 :: Vv_tail) + numGNew)) Vv.
  rewrite SkipInTail_HO; auto.
Qed.

Lemma SkipInTail_HO_castS2 {Nn VvNew t1 Vv_tail} (eq : OnlyOrder0Vars (t1 :: Vv_tail) = false) : 
    substitution Nn VvNew (GrVars (TailLen Vv_tail)) = substitution Nn VvNew (GrVars (TailLen (t1 :: Vv_tail))).
  rewrite SkipInTail_HO; auto.
Qed.

(* Definitions: *)

Inductive ext_term Nn numG :=
  | ExplicitSubst : ext_term Nn (S numG) -> term Nn (GrVars numG) Ground -> ext_term Nn numG
  | StdTerm : term Nn (GrVars numG) Ground -> ext_term Nn numG.

Fixpoint AddVariablesToVar {numG} numGAdd {t : type} (x : ElementOfList t (GrVars numG)) :=
  match numGAdd as numGAdd return ElementOfList t (GrVars (numGAdd + numG)) with 
  | 0 => x
  | _ => NextEl _ _ _ (AddVariablesToVar _ x)
  end.

Fixpoint AddVariablesToTerm {Nn numG} numGAdd {t} (M : term Nn (GrVars numG) t) : 
    term Nn (GrVars (numGAdd + numG)) t :=
  match M with 
  | Nontermi _ _ _ X => Nontermi _ _ _ X
  | Var _ _ _ x => Var _ _ _ (AddVariablesToVar _ x)
  | And _ _ chldrn => And _ _ (map (AddVariablesToTerm _) chldrn)
  | Or _ _ chldrn => Or _ _ (map (AddVariablesToTerm _) chldrn)
  | App _ _ _ _ K L => App _ _ _ _ (AddVariablesToTerm _ K) (AddVariablesToTerm _ L)
  end.

Fixpoint AddVariablesToSubst {Nn numG Vv} numGAdd (sub : substitution Nn (GrVars numG) Vv) 
    : substitution Nn (GrVars (numGAdd + numG)) Vv :=
  match sub with 
  | EmptySubst _ _ => EmptySubst _ _
  | ConsSubst _ _ _ _ M1 sub_tail => ConsSubst _ _ _ _ (AddVariablesToTerm _ M1) (AddVariablesToSubst _ sub_tail)
  end.

Fixpoint GetHOSub {Nn numGNew Vv} (sub : substitution Nn (GrVars numGNew) Vv) :
    substitution Nn (GrVars (TailLen Vv + numGNew)) Vv :=
  match sub with
  | EmptySubst _ _ => EmptySubst _ _
  | ConsSubst _ _ t1 Vv_tail M1 sub_tail =>
      match OnlyOrder0Vars (t1 :: Vv_tail) as oo0 return OnlyOrder0Vars (t1 :: Vv_tail) = oo0 -> _ with
      | true => fun eq => type_cast (ShiftInTail_oo0_castS eq) (ConsSubst _ _ _ _
          (Var _ _ _ (FirstEl Ground (GrVars (TailLen Vv_tail + numGNew))))
          (AddVariablesToSubst 1 (GetHOSub sub_tail)))
      | false => fun eq => type_cast (SkipInTail_HO_castS eq) (ConsSubst _ _ _ _ (AddVariablesToTerm _ M1) (GetHOSub sub_tail))
      end eq_refl
  end.

Fixpoint GetExpSub {Nn numGNew Vv} (sub : substitution Nn (GrVars numGNew) Vv) : 
    substitution Nn (GrVars numGNew) (GrVars (TailLen Vv)) :=
  match sub with
  | EmptySubst _ _ => EmptySubst _ _
  | ConsSubst _ _ t1 Vv_tail M1 sub_tail =>
      match OnlyOrder0Vars (t1 :: Vv_tail) as oo0 return OnlyOrder0Vars (t1 :: Vv_tail) = oo0 -> _ with
      | true => fun eq => type_cast (ShiftInTail_oo0_castS2 eq) (ConsSubst _ _ _ _ M1 (GetExpSub sub_tail))
      | false => fun eq => type_cast (SkipInTail_HO_castS2 eq) (GetExpSub sub_tail)
      end eq_refl
  end.

Fixpoint AppendExplicitSubst {Nn numG numGAdd} (exp_sub : substitution Nn (GrVars numG) (GrVars numGAdd)) :
    ext_term Nn (numGAdd + numG) -> ext_term Nn numG :=
  match numGAdd as numGAdd return substitution _ _ (GrVars numGAdd) -> ext_term _ (numGAdd + _) -> ext_term _ numG with
  | 0 => fun _ eM => eM
  | S numG_tail => fun exp_sub eM => 
      let (R1, exp_sub_tail) := 
        match exp_sub with ConsSubst _ _ (Arr []) _ R1 exp_sub_tail => (R1, exp_sub_tail) end in
      AppendExplicitSubst exp_sub_tail (ExplicitSubst _ _ eM (AddVariablesToTerm _ R1))
end exp_sub.

Definition ExtSubstitute {Nn numG Vv} (sub : substitution Nn (GrVars numG) Vv) (M : term Nn Vv Ground) : ext_term Nn numG :=
  AppendExplicitSubst (GetExpSub sub) (StdTerm _ _ (Substitute (GetHOSub sub) M)).

Section ExtReduces.
  Variable Gg : grammar.
  Let Nn := NontermsOfGrammar Gg.

  Inductive ExtReduces numG : ext_term Nn numG -> list (ext_term Nn numG) -> Prop := 
    | ExtReducesNontermi : forall t X (sub : substitution _ _ (ArgsOfType t)), ExtReduces numG 
        (StdTerm _ _ (ApplyArgs sub (Nontermi _ _ _ X)))
        [ExtSubstitute sub (TermOfRule (FindInRules (RulesOfGrammar Gg) X))]
    | ExtReducesOr : forall K chldrn, In K chldrn -> ExtReduces numG (StdTerm _ _ (Or _ _ chldrn)) [StdTerm _ _ K]
    | ExtReducesAnd : forall chldrn, ExtReduces numG (StdTerm _ _ (And _ _ chldrn)) (map (fun K => StdTerm _ _ K) chldrn)
    | ExtReducesSubst : forall R, ExtReduces numG
        (ExplicitSubst _ _ (StdTerm _ _ (Var _ _ _ (FirstEl _ _ : ElementOfList _ (GrVars (S _))))) R)
        [StdTerm _ _ R]
    | ExtReducesSimpl : forall R x, ExtReduces numG 
        (ExplicitSubst _ _ (StdTerm _ _ (Var _ _ _ (NextEl _ _ _ x : ElementOfList _ (GrVars (S _))))) R)
        [StdTerm _ _ (Var _ _ _ x)]
    | ExtReducesInd : forall eM eNNN R, ExtReduces _ eM eNNN 
        -> ExtReduces numG (ExplicitSubst _ _ eM R) (map (fun eN => ExplicitSubst _ _ eN R) eNNN).

  Inductive ExtProducesFiniteTree : ext_term Nn 0 -> Prop := 
    | ExtPFTReduces : forall eM eNNN, ExtReduces _ eM eNNN -> (forall eN, In eN eNNN -> ExtProducesFiniteTree eN)
        -> ExtProducesFiniteTree eM.
End ExtReduces.

Definition GrammarExtProducesFiniteTree Gg := 
  ExtProducesFiniteTree Gg (StdTerm _ _ (Nontermi _ _ _ (StartingNontermOfGrammar Gg))).

(***********************************************************************************************)
(* PART 4: Standard reductions and extended reductions are equivalent                          *)
(***********************************************************************************************)

Fixpoint SubstituteFirst {Nn Vv tR} (R : term Nn Vv tR) {t} (M : term Nn (tR :: Vv) t) : term Nn Vv t :=
  match M with 
  | Nontermi _ _ _ X => Nontermi _ _ _ X
  | Var _ _ t0 x => match x with
      | FirstEl _ _ => fun R => R
      | NextEl _ _ _ y => fun _ => Var _ _ _ y
      end R
  | And _ _ chldrn => And _ _ (map (SubstituteFirst R) chldrn)
  | Or _ _ chldrn => Or _ _ (map (SubstituteFirst R) chldrn)
  | App _ _ _ _ K L => App _ _ _ _ (SubstituteFirst R K) (SubstituteFirst R L)
  end.

Fixpoint SubstituteFirstInSubstitution {Nn VvNew Vv tR} (R : term Nn VvNew tR) 
    (sub : substitution Nn (tR :: VvNew) Vv) : substitution Nn VvNew Vv :=
  match sub with 
  | EmptySubst _ _ => EmptySubst _ _
  | ConsSubst _ _ _ _ K sub_tail => 
      ConsSubst _ _ _ _ (SubstituteFirst R K) (SubstituteFirstInSubstitution R sub_tail)
  end.

Fixpoint ExtExpand {Nn Vv} (eM : ext_term Nn Vv) :=
  match eM with
  | StdTerm _ _ M => M
  | ExplicitSubst _ _ eN R => SubstituteFirst R (ExtExpand eN)
  end.

Lemma SubstituteFirst_ApplyArgs_com : forall Nn VvNew tR (R : term Nn VvNew tR) Vv sub (M : term _ _ (Arr Vv)), 
     SubstituteFirst R (ApplyArgs sub M) = ApplyArgs (SubstituteFirstInSubstitution R sub) (SubstituteFirst R M).
  induction Vv; dependent destruction sub.
    auto.
  intros.
  apply IHVv.
Qed.

Definition term_my_ind Nn Vv (P : forall {t}, term Nn Vv t -> Prop)
    (stepNontermi : forall {t} (X : ElementOfList t Nn), P (Nontermi _ _ t X))
    (stepVar : forall {t} (x : ElementOfList t Vv), P (Var _ _ t x))
    (stepAnd : forall {chldrn}, (forall k, In k chldrn -> P k) -> P (And _ _ chldrn))
    (stepOr : forall {chldrn}, (forall k, In k chldrn -> P k) -> P (Or _ _ chldrn))
    (stepApp : forall {tL T} {K : term _ _ (Arr (tL :: T))} {L}, P K -> P L -> P (App _ _ _ _ K L)) :=
  fix F {t} (M : term _ _ t) := match M with
  | Nontermi _ _ _ X => stepNontermi X
  | Var _ _ _ x => stepVar x
  | And _ _ chldrn => stepAnd (proj1 (Forall_forall _ _) ((fix F2 ch := match ch as ch return Forall P ch with
      | [] => Forall_nil P
      | K :: tl => Forall_cons _ (F K) (F2 tl)
      end) chldrn))
  | Or _ _ chldrn => stepOr (proj1 (Forall_forall _ _) ((fix F2 ch := match ch as ch return Forall P ch with
      | [] => Forall_nil P
      | K :: tl => Forall_cons _ (F K) (F2 tl)
      end) chldrn))
  | App _ _ _ _ K L => stepApp (F K) (F L)
  end.

Lemma SubstituteFirst_Substitute_com : forall Nn VvNew Vv tR (R : term Nn VvNew tR) t sub (M : term _ Vv t), 
     SubstituteFirst R (Substitute sub M) = Substitute (SubstituteFirstInSubstitution R sub) M.
  induction M using term_my_ind; simpl; auto.
        dependent induction sub; dependent destruction x; simpl; auto.
      rewrite (map_map (Substitute sub) (SubstituteFirst R) chldrn).
      replace (map (Substitute (SubstituteFirstInSubstitution R sub)) chldrn) with
          (map (fun K => SubstituteFirst R (Substitute sub K)) chldrn).
        auto.
      apply map_ext_in.
      auto.
    f_equal.
    rewrite map_map.
    apply map_ext_in.
    auto.
  rewrite IHM1.
  rewrite IHM2.
  auto.
Qed.

Lemma Reduces_add_SubstituteFirst : forall Gg Vv tR (R : term _ Vv tR) M NNN, 
    Reduces Gg M NNN -> Reduces Gg (SubstituteFirst R M) (map (SubstituteFirst R) NNN).
  intros.
  induction H.
      simpl.
      destruct t.
      replace (SubstituteFirst R (ApplyArgs _ _ )) with
          (ApplyArgs (SubstituteFirstInSubstitution R sub) 
            (SubstituteFirst R (Nontermi (NontermsOfGrammar Gg) (tR :: Vv) (Arr l) X))).
        replace (SubstituteFirst R (Substitute sub (TermOfRule (FindInRules (RulesOfGrammar Gg) X)))) with
            (Substitute (SubstituteFirstInSubstitution R sub) (TermOfRule (FindInRules (RulesOfGrammar Gg) X))).
          apply ReducesNontermi.
        symmetry.
        apply SubstituteFirst_Substitute_com.
      symmetry.
      apply SubstituteFirst_ApplyArgs_com.
    apply ReducesOr.
    apply in_map.
    auto.
  apply ReducesAnd.
Qed.

Fixpoint PerformExplicitSubst {Nn numG numGNew} (exp_sub : substitution Nn (GrVars numGNew) (GrVars numG)) {t} :
    term Nn (GrVars (numG + numGNew)) t -> term Nn (GrVars numGNew) t :=
  match numG as numG return substitution _ _ (GrVars numG) -> term _ (GrVars (numG + _)) t -> term _ (GrVars numGNew) _ with
  | 0 => fun _ M => M
  | S numG_tail => fun exp_sub M => 
      let (R1, exp_sub_tail) := 
        match exp_sub with ConsSubst _ _ (Arr []) _ R1 exp_sub_tail => (R1, exp_sub_tail) end in
      PerformExplicitSubst exp_sub_tail (SubstituteFirst (AddVariablesToTerm _ R1) M)
end exp_sub.

Lemma Expand_of_Append_is_Perform Nn numGNew numG (exp_sub : substitution Nn (GrVars numGNew) (GrVars numG)) eM :
    ExtExpand (AppendExplicitSubst exp_sub eM) = PerformExplicitSubst exp_sub (ExtExpand eM).
  induction numG.
    auto.
  dependent destruction exp_sub.
  simpl.
  replace (ExtExpand (AppendExplicitSubst exp_sub (ExplicitSubst _ _ eM (AddVariablesToTerm _ t0)))) with
      (PerformExplicitSubst exp_sub (ExtExpand (ExplicitSubst _ _ eM (AddVariablesToTerm _ t0)))).
    auto.
  easy.
Qed.

Definition ExtSubstituteInd {Nn numGNew Vv} (sub : substitution Nn (GrVars numGNew) Vv) {t} (M : term _ _ t) :=
  PerformExplicitSubst (GetExpSub sub) (Substitute (GetHOSub sub) M).

Lemma PerformExplicitSubst_Nontermi_com Nn numGNew numG (exp_sub : substitution Nn (GrVars numGNew) (GrVars numG))
    t (X : ElementOfList t Nn) : PerformExplicitSubst exp_sub (Nontermi _ _ _ X) = Nontermi _ _ _ X.
  induction numG.
    auto.
  dependent destruction exp_sub.
  apply IHnumG.
Qed.

Lemma PerformExplicitSubst_And_com Nn numGNew numG (exp_sub : substitution Nn (GrVars numGNew) (GrVars numG)) chldrn
    : PerformExplicitSubst exp_sub (And _ _ chldrn) = And _ _ (map (PerformExplicitSubst exp_sub) chldrn).
  induction numG.
    rewrite map_id.
    auto.
  dependent destruction exp_sub.
  simpl.
  rewrite IHnumG.
  rewrite map_map.
  auto.
Qed.

Lemma PerformExplicitSubst_Or_com Nn numGNew numG (exp_sub : substitution Nn (GrVars numGNew) (GrVars numG)) chldrn
    : PerformExplicitSubst exp_sub (Or _ _ chldrn) = Or _ _ (map (PerformExplicitSubst exp_sub) chldrn).
  induction numG.
    rewrite map_id.
    auto.
  dependent destruction exp_sub.
  simpl.
  rewrite IHnumG.
  rewrite map_map.
  auto.
Qed.

Lemma PerformExplicitSubst_App_com Nn numGNew numG (exp_sub : substitution Nn (GrVars numGNew) (GrVars numG)) tL T
    (K : term _ _ (Arr (tL :: T))) L : PerformExplicitSubst exp_sub (App _ _ _ _ K L) = 
    App _ _ _ _ (PerformExplicitSubst exp_sub K) (PerformExplicitSubst exp_sub L).
  induction numG.
    auto.
  dependent destruction exp_sub.
  apply IHnumG.
Qed.

Lemma PerformExplicitSubst_AddVariablesToTerm_void Nn numGNew numG t exp_sub (M : term Nn (GrVars numGNew) t) : 
    PerformExplicitSubst exp_sub (AddVariablesToTerm numG M) = M.
  induction M using term_my_ind; simpl.
          rewrite PerformExplicitSubst_Nontermi_com.
          auto.
        induction numG.
          auto.
        dependent destruction exp_sub.
        simpl.
        auto.
      rewrite PerformExplicitSubst_And_com.
      f_equal.
      rewrite map_map.
      rewrite <- map_id.
      apply map_ext_in.
      auto.
    rewrite PerformExplicitSubst_Or_com.
    f_equal.
    rewrite map_map.
    rewrite <- map_id.
    apply map_ext_in.
    auto.
  rewrite PerformExplicitSubst_App_com.
  rewrite IHM1.
  rewrite IHM2.
  auto.
Qed.

Lemma FindInSubstitution_AddVariables_com {Nn Vv numG} numGAdd t (sub : substitution Nn (GrVars numG) Vv)
    (x : ElementOfList t Vv) :
    FindInSubstitution (AddVariablesToSubst numGAdd sub) x = AddVariablesToTerm numGAdd (FindInSubstitution sub x).
  dependent induction x; dependent destruction sub; simpl; auto.
Qed.

Lemma AddNoVariables_void Nn numG t (M : term Nn (GrVars numG) t) : AddVariablesToTerm 0 M = M.
  induction M using term_my_ind; simpl; f_equal; auto;
    rewrite <- map_id;
    apply map_ext_in;
    auto.
Qed.

Lemma EquivStdExtSubstituteVar Nn numGNew Vv (sub : substitution Nn (GrVars numGNew) Vv) t (x : ElementOfList t Vv) :
    ExtSubstituteInd sub (Var _ _ _ x) = FindInSubstitution sub x.
  unfold ExtSubstituteInd.
  induction sub.
    auto.
  unfold GetExpSub.
  fold @GetExpSub.
  unfold GetHOSub.
  fold @GetHOSub.
  generalize (@eq_refl bool (OnlyOrder0Vars (t0 :: Vv_tail))).
  generalize (OnlyOrder0Vars (t0 :: Vv_tail)) at 2 3 7.
  destruct b; intro.
    generalize (@ShiftInTail_oo0_castS2 Nn (GrVars numGNew) t0 Vv_tail e).
    generalize (@ShiftInTail_oo0_castS Nn numGNew t0 Vv_tail e).
    rewrite (ShiftInTail_oo0 e).
    revert t1 x.
    replace t0 with Ground; try rewrite (FirstIsGround_oo0 e); auto.
    intros R1 x.
    repeat dependent destruction e0; clear x.
    dependent destruction x0; simpl.
      rewrite PerformExplicitSubst_AddVariablesToTerm_void.
      auto.
    rewrite <- IHsub.
    f_equal.
    change (S (TailLen Vv_tail + numGNew)) with (1 + (TailLen Vv_tail + numGNew)).
    rewrite FindInSubstitution_AddVariables_com.
    simpl.
    generalize (FindInSubstitution (GetHOSub sub) x0).
    change (Arr []) with Ground.
    generalize (AddVariablesToTerm (TailLen Vv_tail) R1).
    intros R1s M.
    replace M with
        (PerformExplicitSubst (ConsSubst _ _ _ _ R1s (EmptySubst _ _) : substitution _ _ (GrVars 1)) 
            (AddVariablesToTerm _ M)) at 2.
      simpl.
      rewrite AddNoVariables_void.
      auto.
    apply PerformExplicitSubst_AddVariablesToTerm_void.
  generalize (@SkipInTail_HO_castS2 Nn (GrVars numGNew) t0 Vv_tail e).
  generalize (@SkipInTail_HO_castS Nn (t0 :: Vv_tail) numGNew t0 Vv_tail e).
  rewrite (SkipInTail_HO e).
  repeat dependent destruction e0.
  dependent destruction x.
    simpl.
    apply PerformExplicitSubst_AddVariablesToTerm_void.
  apply IHsub.
Qed.

Lemma EquivStdExtSubstituteInd {Nn numGNew Vv} (sub : substitution Nn (GrVars numGNew) Vv) t (M : term _ _ t) : 
    ExtSubstituteInd sub M = Substitute sub M.
  induction M using term_my_ind; unfold ExtSubstituteInd; simpl.
          apply PerformExplicitSubst_Nontermi_com.
        apply EquivStdExtSubstituteVar.
      rewrite PerformExplicitSubst_And_com.
      f_equal.
      rewrite map_map.
      apply map_ext_in.
      auto.
    rewrite PerformExplicitSubst_Or_com.
    f_equal.
    rewrite map_map.
    apply map_ext_in.
    auto.
  rewrite PerformExplicitSubst_App_com.
  rewrite <- IHM1.
  rewrite <- IHM2.
  auto.
Qed.

Lemma EquivStdExtSubstitute Nn numGNew Vv (sub : substitution Nn (GrVars numGNew) Vv) M : 
    ExtExpand (ExtSubstitute sub M) = Substitute sub M.
  rewrite <- EquivStdExtSubstituteInd.
  apply Expand_of_Append_is_Perform. 
Qed.

Lemma ExtReduces2Reduces : forall {Gg Vv} (eM : ext_term _ Vv) eNNN, ExtReduces _ _ eM eNNN -> 
    Reduces Gg (ExtExpand eM) (map ExtExpand eNNN) \/ map ExtExpand eNNN = [ExtExpand eM].
  intros.
  induction H.
            left.
            simpl.
            replace (ExtExpand (ExtSubstitute sub (TermOfRule (FindInRules (RulesOfGrammar Gg) X))))
                with (Substitute sub (TermOfRule (FindInRules (RulesOfGrammar Gg) X))).
              apply ReducesNontermi.
            rewrite EquivStdExtSubstitute.
            auto.
          left.
          apply ReducesOr.
          auto.
        left.
        rewrite map_map.
        simpl.
        rewrite map_id.
        apply ReducesAnd.
      auto.
    auto.
  rewrite map_map.
  simpl.
  replace (map _ _) with (map (SubstituteFirst R) (map ExtExpand eNNN)).
    destruct IHExtReduces.
      left.
      apply Reduces_add_SubstituteFirst.
      auto.
    rewrite H0.
    auto.
  apply map_map.
Qed.

(* reflexive-transitive closure of ExtReduces *)
Section ExtRTReduces.
  Variable Gg : grammar.
  Let Nn := NontermsOfGrammar Gg.
  Inductive ExtRTReduces {Vv} : ext_term Nn Vv -> ext_term Nn Vv -> Prop := 
    | ExtRTReducesSelf : forall eM, ExtRTReduces eM eM
    | ExtRTReducesStep : forall eM eP eN, 
        ExtRTReduces eM eP -> ExtReduces Gg _ eP [eN] -> ExtRTReduces eM eN.
End ExtRTReduces.

Fixpoint ExtIsSimplified {Nn} {Vv} (eM : ext_term Nn Vv) :=
  match eM with
  | StdTerm _ _ (Var _ _ _ _) => False
  | StdTerm _ _ _ => True
  | ExplicitSubst _ _ eN _ => ExtIsSimplified eN
  end.

Definition ExtIsVariable {Nn} {Vv} (eM : ext_term Nn Vv) :=
  match eM with
  | StdTerm _ _ (Var _ _ _ _) => True
  | _ => False
  end.

Lemma Raise_ExtRTReduces Gg Vv eM eN R : ExtRTReduces Gg eM eN ->
    ExtRTReduces Gg (ExplicitSubst _ Vv eM R) (ExplicitSubst _ Vv eN R).
  intro.
  induction H.
    apply ExtRTReducesSelf.
  apply (ExtRTReducesStep _ _ (ExplicitSubst _ _ eP R)).
    auto.
  replace [ExplicitSubst _ _ eN R] with (map (fun eN => ExplicitSubst _ _ eN R) [eN]).
    apply ExtReducesInd.
    auto.
  easy.
Qed.

Lemma Std_is_Simplified_or_Variable Nn Vv M : ExtIsSimplified (StdTerm Nn Vv M) \/ ExtIsVariable (StdTerm _ _ M).
  dependent destruction M; try (left; easy).
  right.
  easy.
Qed.

Lemma ExtReduces_to_Simplified Gg Vv x R : exists eN, 
    ExtReduces Gg Vv (ExplicitSubst _ _ (StdTerm _ _ (Var _ _ _ x)) R) [eN]
    /\ (ExtIsSimplified eN \/ ExtIsVariable eN) 
    /\ ExtExpand (ExplicitSubst _ _ (StdTerm _ _ (Var _ _ _ x)) R) = ExtExpand eN.
  dependent destruction x.
    exists (StdTerm _ _ R).
    split.
      apply ExtReducesSubst.
    split.
      apply Std_is_Simplified_or_Variable.
    auto.
  exists (StdTerm _ _ (Var _ _ _ x)).
  split.
    apply ExtReducesSimpl.
  split.
    right.
    easy.
  auto.
Qed.

Lemma ExtRTReduces_to_Simplified {Gg Vv} (eM : ext_term _ Vv) : exists eN,
    ExtRTReduces Gg eM eN /\ (ExtIsSimplified eN \/ ExtIsVariable eN) /\ ExtExpand eM = ExtExpand eN.
  induction eM.
    destruct IHeM.
    destruct H.
    destruct H0.
    assert (ExtRTReduces Gg (ExplicitSubst _ _ eM t) (ExplicitSubst _ _ x t)).
      apply Raise_ExtRTReduces.
      auto.
    assert (ExtExpand (ExplicitSubst _ _ eM t) = ExtExpand (ExplicitSubst _ _ x t)).
      simpl.
      rewrite H1.
      auto.
    destruct H0.
      eauto.
    assert (exists eN, ExtReduces Gg _ (ExplicitSubst _ _ x t) [eN] /\ (ExtIsSimplified eN \/ ExtIsVariable eN) 
        /\ ExtExpand (ExplicitSubst _ _ x t) = ExtExpand eN).
      destruct x.
        contradiction.
      dependent destruction t0; try contradiction.
      apply ExtReduces_to_Simplified.
    destruct H4.
    exists x0.
    split.
      eapply ExtRTReducesStep.
      apply H2.
      easy.
    split.
      easy.
    rewrite H3.
    easy.
  exists (StdTerm _ _ t).
  split.
    apply ExtRTReducesSelf.
  split.
    apply Std_is_Simplified_or_Variable.
  auto.
Qed.

Definition IsVariable {Nn} {Vv} {t} (M : term Nn Vv t) :=
  match M with
  | Var _ _ _ _ => True
  | _ => False
  end.

Lemma ApplyArgs_SubstituteFirst_com Nn numG (R : term Nn (GrVars numG) Ground) T subR M (KR : term _ _ (Arr T)) : 
    ~IsVariable M -> SubstituteFirst R M = ApplyArgs subR KR ->
    exists sub K, M = ApplyArgs sub K /\ SubstituteFirstInSubstitution R sub = subR /\ SubstituteFirst R K = KR.
  induction T; dependent destruction subR.
    exists (EmptySubst _ _).
    exists M.
    auto.
  intros.
  simpl in H0.
  specialize (IHT subR (App _ _ _ _ KR t0) H H0).
  destruct IHT as (sub_tl & IHT).
  destruct IHT as (K_tl & IHT).
  destruct IHT.
  destruct H2.
  dependent destruction K_tl; try easy.
    destruct T.
      rewrite H1 in H.
      dependent destruction sub_tl.
      simpl in H.
      contradiction.
    dependent destruction e.
    easy.
  inversion H3.
  destruct H5.
  exists (ConsSubst _ _ _ _ K_tl2 sub_tl).
  exists K_tl1.
  dependent destruction H7.
  auto.
Qed.

Lemma Reduces_remove_SubstituteFirst : forall Gg numG (R : term _ (GrVars numG) Ground) M NNN, 
    ~IsVariable M -> Reduces Gg (SubstituteFirst R M) NNN -> 
    exists NNN_tl, Reduces Gg M NNN_tl /\ map (SubstituteFirst R) NNN_tl = NNN.
  intros *.
  intros NotVar Red.
  dependent induction Red.
      assert (exists sub2 K, M = ApplyArgs sub2 K /\ SubstituteFirstInSubstitution R sub2 = sub /\ 
          SubstituteFirst R K = Nontermi _ _ _ X).
        apply ApplyArgs_SubstituteFirst_com; auto.
      destruct H as (sub2 & H).
      destruct H.
      destruct H.
      destruct H0.
      exists [Substitute sub2 (TermOfRule (FindInRules (RulesOfGrammar Gg) X))].
      split.
        rewrite H.
        destruct t.
        dependent destruction x0; try easy.
          inversion H1.
          dependent destruction H1.
          apply ReducesNontermi.
        rewrite H in NotVar.
        simpl in sub2.
        dependent destruction sub2.
          simpl in NotVar.
          contradiction.
        dependent destruction e.
        easy.
      rewrite <- H0.
      rewrite <- SubstituteFirst_Substitute_com.
      auto. 
    dependent destruction M; simpl in *; try easy.
    inversion x.
    rewrite H1 in H.
    rewrite in_map_iff in H.
    destruct H.
    exists [x0].
    destruct H.
    split.
      apply ReducesOr.
      auto.
    rewrite <- H.
    auto.
  dependent destruction M; simpl in *; try easy.
  exists l.
  split.
  apply ReducesAnd.
  inversion x.
  auto.
Qed.

Lemma ExtExpand_of_Simplified_not_Variable Nn Vv (eM : ext_term Nn Vv) : 
    ExtIsSimplified eM -> ~IsVariable (ExtExpand eM).
  dependent induction eM; intros; simpl in *.
    destruct (ExtExpand eM); auto.
    specialize (IHeM H).
    simpl in IHeM.
    contradiction.
  intros.
  destruct t; auto.
Qed.

Lemma Reduces2ExtReduces {Gg numG} eM NNN : ExtIsSimplified eM -> Reduces Gg (ExtExpand eM) NNN ->
    exists eNNN, ExtReduces Gg numG eM eNNN /\ map ExtExpand eNNN = NNN.
  induction eM.
    intros Simp Red.
    simpl in *.
    assert (exists NNN_tl, Reduces Gg (ExtExpand eM) NNN_tl /\ map (SubstituteFirst t) NNN_tl = NNN) as Red_tl.
      apply Reduces_remove_SubstituteFirst; auto.
      change (Ground :: GrVars numG) with (GrVars (S numG)).
      apply ExtExpand_of_Simplified_not_Variable.
      auto.
    destruct Red_tl as (NNN_tl & Red_tl).
    destruct Red_tl.
    specialize (IHeM NNN_tl Simp H).
    destruct IHeM as (eNNN & IHeM).
    destruct IHeM.
    exists (map (fun eN => ExplicitSubst _ _ eN t) eNNN).
    split.
      apply ExtReducesInd.
      auto.
    rewrite map_map.
    simpl.
    rewrite <- map_map.
    change (Ground :: GrVars numG) with (GrVars (S numG)).
    rewrite H2.
    auto.
  intros.
  simpl in H0.
  destruct H0.
      exists ([ExtSubstitute sub (TermOfRule (FindInRules (RulesOfGrammar Gg) X))]).
      split.
        apply ExtReducesNontermi.
      rewrite <- EquivStdExtSubstitute.
      auto.
    exists [StdTerm _ _ K].
    split.
      apply ExtReducesOr.
      auto.
    auto.
  exists (map (fun K => StdTerm _ _ K) chldrn).
  split.
    apply ExtReducesAnd.
  rewrite map_map.
  apply map_id.
Qed.

Lemma ExtRTReduces_preserves_ExtProducesFiniteTree Gg eM eN : 
    ExtProducesFiniteTree Gg eN -> ExtRTReduces Gg eM eN -> ExtProducesFiniteTree Gg eM.
  intros.
  induction H0.
    auto.
  apply IHExtRTReduces.
  eapply ExtPFTReduces.
  eauto.
  intros.
  inversion H2.
    rewrite <- H3.
    auto.
  easy.
Qed.

Lemma EquivStdExtTerm : forall Gg eM, ExtProducesFiniteTree Gg eM <-> ProducesFiniteTree Gg (ExtExpand eM).
  split; intros.
    induction H.
    specialize (ExtReduces2Reduces eM eNNN H) as ?.
    destruct H2.
      eapply PFTReduces.
        eauto.
      intros.
      specialize (in_map_iff ExtExpand eNNN N) as ?.
      destruct H4.
      specialize (H4 H3).
      destruct H4 as (eN & H4).
      destruct H4.
      rewrite <- H4.
      apply H1.
      auto.
    dependent destruction eNNN.
      easy.
    inversion H2.
    apply H1.
    left.
    auto.
  dependent induction H.
  specialize (ExtRTReduces_to_Simplified eM) as ?.
  destruct H2 as (eM_simpl & H2).
  destruct H2.
  destruct H3.
  destruct H3.
    rewrite H4 in H.
    specialize (Reduces2ExtReduces eM_simpl NNN H3 H) as ?.
    destruct H5 as (eNNN & H5).
    destruct H5.
    apply (ExtRTReduces_preserves_ExtProducesFiniteTree _ _ eM_simpl); auto.
    eapply ExtPFTReduces.
      eauto.
    intros.
    apply (H1 (ExtExpand eN)).
      rewrite <- H6.
      apply in_map.
      auto.
    auto.
  destruct eM_simpl.
    easy.
  dependent destruction t; easy.
Qed.

(* Final theorem of this part: standard and extended reductions give the same *)
Theorem EquivStdExt (Gg : grammar) : GrammarExtProducesFiniteTree Gg <-> GrammarProducesFiniteTree Gg.
  apply EquivStdExtTerm.
Qed.

(***********************************************************************************************)
(* PART 5: Extended reductions are equivalent with the transformed grammar                     *)
(***********************************************************************************************)

Lemma OnlyOrder0Vars_GrVars {numG} : OnlyOrder0Vars (GrVars numG) = true.
  induction numG; easy.
Qed.

Lemma TailIsAll_GrVars {numG} : TailLen (GrVars numG) = numG.
  destruct numG.
    auto.
  simpl.
  rewrite OnlyOrder0Vars_GrVars.
  rewrite repeat_length.
  auto.
Qed.

Lemma TailIsAll_GrVars_castSet {numG} : Subset numG = Subset (TailLen (GrVars numG)).
  rewrite TailIsAll_GrVars.
  auto.
Qed.

Lemma HOPartEmpty_GrVars {numG} : HOPart (GrVars numG) = [].
  destruct numG.
    auto.
  simpl.
  rewrite OnlyOrder0Vars_GrVars.
  auto.
Qed.

Lemma HOPartEmpty_GrVars_castT {Nn numG t} : term Nn (TransVars (HOPart (GrVars numG))) t = term Nn [] t.
  rewrite HOPartEmpty_GrVars; auto.
Qed.

Fixpoint TransExtTerm {Nn numG} (V : Subset numG) (eM : ext_term Nn numG) : term (TransVars Nn) [] Ground :=
  match eM with
  | ExplicitSubst _ _ eK L => Or _ _ [
      TransExtTerm ((false, V) : Subset (S _)) eK;
      And _ _ [
        TransExtTerm ((true, V) : Subset (S _)) eK; 
        type_cast HOPartEmpty_GrVars_castT
          (TransTerm Subset0 (type_cast TailIsAll_GrVars_castSet V) L)]]
  | StdTerm _ _ M => type_cast HOPartEmpty_GrVars_castT
      (TransTerm Subset0 (type_cast TailIsAll_GrVars_castSet V) M)
  end.

Lemma RemainsOrTail_oo0 {t Vv} (x : ElementOfList t Vv) (OO0 : OnlyOrder0Vars Vv = true) :
    RemainsOrTail x = inr (type_cast (TailIsAll_oo0_castV OO0) x).
  unfold RemainsOrTail.
  dependent destruction x.
    generalize (@eq_refl bool (OnlyOrder0Vars (t :: tail))).
    generalize (OnlyOrder0Vars (t :: tail)) at 2 3.
    intros.
    destruct b; try (exfalso; rewrite e in OO0; easy).
    f_equal.
    apply type_cast_invariance.
  generalize (@eq_refl bool (OnlyOrder0Vars (first :: tail))).
  generalize (OnlyOrder0Vars (first :: tail)) at 2 3.
  intros.
  destruct b; try (exfalso; rewrite e in OO0; easy).
  f_equal.
  apply type_cast_invariance.
Qed.

Lemma First_is_First numG (V : Subset numG) val :
    exists xFO : ElementOfList Ground (GrVars (TailLen (GrVars (S numG)))),
      RemainsOrTail (FirstEl Ground (GrVars numG)) = inr xFO /\ 
      BelongsToSubset xFO (type_cast TailIsAll_GrVars_castSet ((val, V) : Subset (S _))) = val.
  assert (OnlyOrder0Vars (GrVars (S numG)) = true) as OO0.
    apply OnlyOrder0Vars_GrVars.
  exists (type_cast (TailIsAll_oo0_castV OO0) (FirstEl _ _ )).
  split.
    apply RemainsOrTail_oo0.
  generalize (TailIsAll_oo0_castV (t := Ground) OO0).
  generalize (TailIsAll_GrVars_castSet (numG := S numG)).
  replace (TailLen (GrVars (S numG))) with (S numG).
    repeat dependent destruction e.
    auto.
  rewrite TailIsAll_GrVars.
  auto.
Qed.

Lemma Next_is_Next numG (V : Subset numG) val (x_tail : ElementOfList Ground (GrVars numG)) :
    exists (xFO_t : ElementOfList Ground (GrVars (TailLen (GrVars numG))))
    (xFO : ElementOfList Ground (GrVars (TailLen (GrVars (S numG))))),
      RemainsOrTail x_tail = inr xFO_t /\ RemainsOrTail (NextEl _ Ground _ x_tail) = inr xFO /\ 
      BelongsToSubset xFO (type_cast TailIsAll_GrVars_castSet ((val, V) : Subset (S _))) = 
        BelongsToSubset xFO_t (type_cast TailIsAll_GrVars_castSet V).
  unfold RemainsOrTail.
  change (Ground :: GrVars numG) with (GrVars (S numG)).
  generalize (eq_refl (A := bool) (x := OnlyOrder0Vars (GrVars (S numG)))).
  generalize (OnlyOrder0Vars (GrVars (S numG))) at 2 3.
  intros.
  destruct b; try (exfalso; rewrite OnlyOrder0Vars_GrVars in e; easy).
  fold @RemainsOrTail.
  assert (OnlyOrder0Vars (GrVars numG) = true) as OO0.
    apply OnlyOrder0Vars_GrVars.
  exists (type_cast (TailIsAll_oo0_castV OO0) x_tail).
  exists (type_cast (TailIsAll_oo0_castV e) (NextEl Ground Ground (GrVars numG) x_tail)).
  repeat split.
    apply RemainsOrTail_oo0.
  generalize (TailIsAll_oo0_castV (t := Ground) e).
  generalize (TailIsAll_oo0_castV (t := Ground) OO0).
  generalize (TailIsAll_GrVars_castSet (numG := numG)).
  generalize (TailIsAll_GrVars_castSet (numG := S numG)).
  replace (TailLen (GrVars (S numG))) with (S numG).
    replace (TailLen (GrVars numG)) with numG.
      repeat dependent destruction e0.
      simpl.
      generalize (@DestructGrVars_castV Ground Ground (GrVars numG) numG (@eq_refl (list type) (GrVars (S numG)))).
      dependent destruction e0.
      auto.
    rewrite TailIsAll_GrVars.
    auto.
  rewrite TailIsAll_GrVars.
  auto.
Qed.

Lemma TransNextVar Nn numG (V : Subset numG) val (x_tail : ElementOfList Ground (GrVars numG)) :
    type_cast HOPartEmpty_GrVars_castT (TransTerm Subset0
      (type_cast TailIsAll_GrVars_castSet ((val, V) : Subset (S _))) (Var Nn _ _ (NextEl _ Ground _ x_tail))) =
    type_cast HOPartEmpty_GrVars_castT (TransTerm Subset0
      (type_cast TailIsAll_GrVars_castSet V) (Var Nn _ _ x_tail)).
  unfold TransTerm.
  specialize (Next_is_Next numG V val x_tail) as ?.
  destruct H as (xFO_t & H).
  destruct H as (xFO & H).
  destruct H.
  destruct H0.
  rewrite H.
  change (RemainsOrTail (Vv := _) (t := _)) with (RemainsOrTail (Vv := GrVars (S numG)) (t := Ground)) in H0.
  rewrite H0.
  rewrite H1.
  generalize (@HOPartEmpty_GrVars_castT (TransVars Nn) numG (TransType Ground)).
  assert (TransVars (HOPart (GrVars numG)) = []).
    rewrite HOPartEmpty_GrVars; auto.
  generalize H2.
  generalize (TransVars (HOPart (GrVars numG))).
  generalize (@HOPartEmpty_GrVars_castT (TransVars Nn) (S numG) (TransType Ground)).
  assert (TransVars (HOPart (GrVars (S numG))) = []).
    rewrite HOPartEmpty_GrVars; auto.
  generalize H3.
  generalize (TransVars (HOPart (GrVars (S numG)))).
  destruct l.
    destruct l.
      dependent destruction e.
      dependent destruction e.
      generalize (OnlyGround_GrVars_castT (Nn := TransVars Nn) (Vv := []) xFO).
      generalize (OnlyGround_GrVars_castT (Nn := TransVars Nn) (Vv := []) xFO_t).
      dependent destruction e.
      dependent destruction e.
      auto.
    simplify_eq 1.
  simplify_eq 1.
Qed.

Inductive smaller_term {Nn Vv} : forall {t}, term Nn Vv t -> term Nn Vv t -> Prop :=
  | STNontermi : forall t X, smaller_term (Nontermi _ _ _ X) (Nontermi _ _ t X)
  | STVar : forall t x, smaller_term (Var _ _ _ x) (Var _ _ t x)
  | STAnd : forall chldrn1 chldrn2, Forall2 (fun K1 K2 => smaller_term K1 K2) chldrn1 chldrn2 ->
      smaller_term (And _ _ chldrn1) (And _ _ chldrn2)
  | STOr : forall chldrn1 chldrn2, Forall2 (fun K1 K2 => smaller_term K1 K2) chldrn1 chldrn2 ->
      smaller_term (Or _ _ chldrn1) (Or _ _ chldrn2)
  | STApp : forall tK T K1 K2 L1 L2, smaller_term K1 K2 -> smaller_term L1 L2 -> 
      smaller_term (App _ _ _ _ K1 L1) (App _ _ tK T K2 L2)
  | STChange : smaller_term (Or _ _ []) (And _ _ []).

Definition smaller_term_my_ind Nn Vv (P : forall {t}, term Nn Vv t -> term Nn Vv t -> Prop)
    (stepNontermi : forall {t} (X : ElementOfList t Nn), P (Nontermi _ _ t X) (Nontermi _ _ t X))
    (stepVar : forall {t} (x : ElementOfList t Vv), P (Var _ _ t x) (Var _ _ t x))
    (stepAnd : forall {chldrn1 chldrn2}, Forall2 P chldrn1 chldrn2 -> P (And _ _ chldrn1) (And _ _ chldrn2))
    (stepOr : forall {chldrn1 chldrn2}, Forall2 P chldrn1 chldrn2 -> P (Or _ _ chldrn1) (Or _ _ chldrn2))
    (stepApp : forall {tL T} {K1 K2 : term _ _ (Arr (tL :: T))} {L1 L2}, P K1 K2 -> P L1 L2 -> 
        P (App _ _ _ _ K1 L1) (App _ _ _ _ K2 L2))
    (stepChange : P (Or _ _ []) (And _ _ [])) :=
  fix F {t} {M1 M2 : term _ _ t} (s : smaller_term M1 M2) := match s with
  | STNontermi _ X => stepNontermi X
  | STVar _ x => stepVar x
  | STAnd chldrn1 chldrn2 sm_ch => stepAnd ((fix F2 {ch1 ch2} (sm_ch : Forall2 smaller_term ch1 ch2) := 
      match sm_ch in Forall2 _ ch1 ch2 return Forall2 P ch1 ch2 with
      | Forall2_nil _ => Forall2_nil P
      | Forall2_cons _ _ smK sm_tl => Forall2_cons _ _ (F smK) (F2 sm_tl)
      end) chldrn1 chldrn2 sm_ch)
  | STOr chldrn1 chldrn2 sm_ch => stepOr ((fix F2 {ch1 ch2} (sm_ch : Forall2 smaller_term ch1 ch2) := 
      match sm_ch in Forall2 _ ch1 ch2 return Forall2 P ch1 ch2 with
      | Forall2_nil _ => Forall2_nil P
      | Forall2_cons _ _ smK sm_tl => Forall2_cons _ _ (F smK) (F2 sm_tl)
      end) chldrn1 chldrn2 sm_ch)
  | STApp _ _ _ _ _ _ smK smL => stepApp (F smK) (F smL)
  | STChange => stepChange
  end.

Inductive smaller_substitution {Nn VvNew} : forall {Vv}, substitution Nn VvNew Vv -> substitution Nn VvNew Vv -> Prop :=
  | SSEmptySubst : smaller_substitution (EmptySubst _ _) (EmptySubst _ _)
  | SSConsSubst : forall t Vv_tail K1 K2 s1_tail s2_tail, smaller_term K1 K2 -> smaller_substitution s1_tail s2_tail ->
      smaller_substitution (ConsSubst _ _ t Vv_tail K1 s1_tail) (ConsSubst _ _ _ _ K2 s2_tail).

Lemma smaller_term_self Nn Vv t (K : term Nn Vv t) : smaller_term K K.
  induction K using term_my_ind.
          apply STNontermi.
        apply STVar.
      apply STAnd.
      apply Forall2_self.
      auto.
    apply STOr.
    apply Forall2_self.
    auto.
  apply STApp; auto.
Qed.

Lemma ConstructGreaterSubstitution Nn VvNew Vv (sub1 : substitution Nn VvNew Vv) (K1 : term Nn VvNew (Arr Vv))
    (M2 : term Nn VvNew Ground) : smaller_term (ApplyArgs sub1 K1) M2 ->
    exists K2 sub2, ApplyArgs sub2 K2 = M2 /\ smaller_term K1 K2 /\ smaller_substitution sub1 sub2.
  induction sub1; simpl.
    exists M2.
    exists (EmptySubst _ _).
    split.
      auto.
    split.
      auto.
    apply SSEmptySubst.
  specialize (IHsub1 (App _ _ _ _ K1 t0)).
  intro.
  destruct IHsub1 as (K2_tail & H0).
    auto.
  destruct H0 as (sub2_tail & H0).
  destruct H0.
  destruct H1.
  dependent destruction H1.
  exists K2.
  exists (ConsSubst _ _ _ _ L2 sub2_tail).
  split.
    auto.
  split.
    auto.
  apply SSConsSubst; auto.
Qed.

Lemma Substitute_smaller_com Nn VvNew Vv t (sub1 sub2 : substitution Nn VvNew Vv) (K1 K2 : term Nn Vv t) :
    smaller_substitution sub1 sub2 -> smaller_term K1 K2 -> smaller_term (Substitute sub1 K1) (Substitute sub2 K2).
  intros.
  induction H0 using smaller_term_my_ind.
            apply STNontermi.
          all: cycle 1.
          apply STAnd.
          apply Forall2_map_com.
          auto.
        apply STOr.
        apply Forall2_map_com.
        auto.
      apply STApp; auto.
    apply STChange.
  induction H.
    easy.
  dependent destruction x.
    auto.
  apply IHsmaller_substitution.
Qed.

Lemma GreaterReducesMore Gg (M1 : term _ [] _) NNN1 M2 : Reduces Gg M1 NNN1 -> smaller_term M1 M2 -> 
    exists NNN2, Reduces Gg M2 NNN2 /\ Forall2 (fun N1 N2 => smaller_term N1 N2) NNN1 NNN2.
  destruct 1; intro.
      specialize (ConstructGreaterSubstitution _ _ _ sub (Nontermi _ _ _ X) M2) as ?.
      destruct H0 as (K2 & H0).
        auto.
      destruct H0 as (sub2 & H0).
      destruct H0.
      destruct H1.
      dependent destruction H1.
            exists [Substitute sub2 (TermOfRule (FindInRules (RulesOfGrammar Gg) X))].
            split.
              apply ReducesNontermi.
            apply Forall2_cons; auto.
            apply Substitute_smaller_com; auto.
            apply smaller_term_self.
          destruct t.
          simpl in x0.
          dependent destruction x0.
          dependent destruction x1.
        destruct t.
        simpl in x0.
        dependent destruction x0.
        dependent destruction x1.
      destruct t.
      simpl in x0.
      dependent destruction x0.
      dependent destruction x1.
    dependent destruction H0; try easy.
    assert (exists K2, smaller_term K K2 /\ In K2 chldrn2).
      eapply exists_Forall2_fw; eauto.
    destruct H1.
    exists [x].
    destruct H1.
    split.
      apply ReducesOr.
      auto.
    auto.
  dependent destruction H.
  exists chldrn2.
  split.
    apply ReducesAnd.
  auto.
Qed.

Lemma GreaterProducesMore Gg M1 M2 : smaller_term M1 M2 -> ProducesFiniteTree Gg M1 -> ProducesFiniteTree Gg M2.
  intros.
  revert M2 H.
  induction H0.
  intros.
  specialize (GreaterReducesMore Gg M NNN M2) as ?.
  destruct H3; auto.
  destruct H3.
  eapply PFTReduces.
    eauto.
  intros.
  assert (exists N0, smaller_term N0 N /\ In N0 NNN).
    eapply exists_Forall2_bw; eauto.
  destruct H6.
  destruct H6.
  eapply H1; eauto.
Qed.

Lemma TransTerm_OK_for_TransGrammar {Gg} : 
    term (TransVars (NontermsOfGrammar Gg)) [] Ground = term (NontermsOfGrammar (TransGrammar Gg)) [] Ground.
  destruct Gg.
  easy.
Qed.

Inductive smaller_subset : forall numG, Subset numG -> Subset numG -> Prop :=
  | SSNil : smaller_subset 0 tt tt
  | SSSame : forall v numG S1 S2, smaller_subset numG S1 S2 -> smaller_subset (S numG) (v, S1) (v, S2)
  | SSChange : forall numG S1 S2, smaller_subset numG S1 S2 -> smaller_subset (S numG) (false, S1) (true, S2).

Lemma SmallerSubsetContainsLess t numG V1 V2 (x : ElementOfList t (GrVars numG)) :
    smaller_subset numG V1 V2 -> BelongsToSubset x V1 = true -> BelongsToSubset x V2 = true.
  intros.
  dependent induction H; dependent destruction x; simpl; auto.
Qed.

Lemma SmallerTerm_ApplyArgsForAllA_com Nn Vv t_app numG T2 (K1 K2 : term Nn Vv (Arr (AppendVarAux t_app numG T2)))
    (L1 L2 : Subset numG -> term Nn Vv t_app) : smaller_term K1 K2 -> (forall V, smaller_term (L1 V) (L2 V)) ->
    smaller_term (ApplyArgsForAllA K1 L1) (ApplyArgsForAllA K2 L2).
  revert T2 K1 K2.
  induction numG; intros.
    apply STApp; auto.
  apply IHnumG; auto.
Qed.

Lemma SmallerSubsetGivesSmallerTerm {Nn numG t} A V1 V2 (M : term Nn (GrVars numG) t) : smaller_subset _ V1 V2 -> 
    smaller_term (TransTerm A (type_cast TailIsAll_GrVars_castSet V1) M) (TransTerm A (type_cast TailIsAll_GrVars_castSet V2) M).
  induction M using term_my_ind; intro.
          apply STNontermi.
        simpl.
        generalize (RemainsOrTail x).
        destruct s.
          apply STVar.
        generalize (OnlyGround_GrVars_castT (Nn := TransVars Nn) (Vv := TransVars (HOPart (GrVars numG))) e).
        replace (TransType t) with Ground.
          dependent destruction e0.
          case_eq (BelongsToSubset e (type_cast TailIsAll_GrVars_castSet V2)); 
                  case_eq (BelongsToSubset e (type_cast TailIsAll_GrVars_castSet V1)); intros.
                apply STAnd.
                auto.
              apply STChange.
            revert e H0 H1.
            generalize (TailIsAll_GrVars_castSet (numG := numG)).
            replace (TailLen (GrVars numG)) with numG.
              dependent destruction e.
              intros.
              assert (BelongsToSubset e V2 = true).
                apply (SmallerSubsetContainsLess _ _ V1); auto.
              simpl in H1.
              rewrite H1 in H2.
              easy.
            rewrite TailIsAll_GrVars.
            auto.
          apply STOr.
          auto.
        rewrite (OnlyGround_GrVars e).
        auto.
      apply STAnd.
      apply Forall2_map.
      auto.
    apply STOr.
    apply Forall2_map.
    auto.
  unfold TransTerm.
  fold @TransTerm.
  generalize (eq_refl (A := bool) (x := OnlyOrder0Vars (tL :: T))).
  generalize (OnlyOrder0Vars (tL :: T)) at 2 3 7.
  intros.
  destruct b.
    generalize (TransTypeTailIsGround_oo0_castT (Nn := TransVars Nn) (Vv := TransVars (HOPart (GrVars numG))) e).
    rewrite (TransTypeTailIsGround_oo0 e); auto.
    dependent destruction e0.
    apply STOr.
    apply Forall2_cons.
      generalize (TransTypeIsGround_oo0_castT (Nn := TransVars Nn) (Vv := TransVars (HOPart (GrVars numG))) e).
      rewrite <- (TransTypeIsGround_oo0 e); auto.
      dependent destruction e0.
      apply IHM1.
      auto.
    apply Forall2_cons; auto.
    apply STAnd.
    apply Forall2_cons.
      generalize (TransTypeIsGround_oo0_castT (Nn := TransVars Nn) (Vv := TransVars (HOPart (GrVars numG))) e).
      rewrite <- (TransTypeIsGround_oo0 e); auto.
      dependent destruction e0.
      apply IHM1.
      auto.
    apply Forall2_cons; auto.
    generalize (FirstIsGround_oo0_castT (Nn := TransVars Nn) (Vv := TransVars (HOPart (GrVars numG))) e).
    replace Ground with (TransType tL).
      dependent destruction e0.
      apply IHM2.
      auto.
    rewrite (FirstIsGround_oo0 e); auto.
  assert (smaller_term (TransTerm (type_cast (SkipInTail_HO_castSet e) A) (type_cast TailIsAll_GrVars_castSet V1) M1)
      (TransTerm (type_cast (SkipInTail_HO_castSet e) A) (type_cast TailIsAll_GrVars_castSet V2) M1)).
    apply IHM1.
    auto.
  revert H0.
  generalize (TransTerm (type_cast (SkipInTail_HO_castSet e) A) (type_cast TailIsAll_GrVars_castSet V1) M1).
  generalize (TransTerm (type_cast (SkipInTail_HO_castSet e) A) (type_cast TailIsAll_GrVars_castSet V2) M1).
  generalize (TransType_HO_castT (Nn := TransVars Nn) (Vv := TransVars (HOPart (GrVars numG))) e).
  rewrite TransType_HO; auto.
  dependent destruction e0.
  intros.
  apply SmallerTerm_ApplyArgsForAllA_com; auto.
Qed.

Lemma SmallerSubsetGivesSmallerTermExt Nn numG V1 V2 (eM : ext_term Nn numG) :
    smaller_subset _ V1 V2 -> smaller_term (TransExtTerm V1 eM) (TransExtTerm V2 eM).
  induction eM.
    simpl.
    intro.
    apply STOr.
    apply Forall2_cons.
      apply IHeM.
      apply SSSame.
      auto.
    apply Forall2_cons; auto.
    apply STAnd.
    apply Forall2_cons.
      apply IHeM.
      apply SSSame.
      auto.
    apply Forall2_cons; auto.
    change (Arr []) with Ground.
    generalize (@HOPartEmpty_GrVars_castT (TransVars Nn) numG Ground).
    replace [] with (TransVars (HOPart (GrVars numG))).
      dependent destruction e.
      apply (SmallerSubsetGivesSmallerTerm Subset0).
      auto.
    rewrite HOPartEmpty_GrVars.
    auto.
  simpl.
  change (Arr []) with Ground.
  generalize (HOPartEmpty_GrVars_castT (Nn := TransVars Nn) (numG := numG) (t := Ground)).
  replace [] with (TransVars (HOPart (GrVars numG))).
    dependent destruction e.
    apply (SmallerSubsetGivesSmallerTerm Subset0).
  rewrite HOPartEmpty_GrVars.
  auto.
Qed.

Lemma PFT_false_implies_true Gg numG V (eM : ext_term (NontermsOfGrammar Gg) (S numG)) :
    ProducesFiniteTree _ (type_cast TransTerm_OK_for_TransGrammar (TransExtTerm ((false, V) : Subset (S _)) eM)) ->
    ProducesFiniteTree _ (type_cast TransTerm_OK_for_TransGrammar (TransExtTerm ((true, V) : Subset (S _)) eM)).
  apply GreaterProducesMore.
  generalize (TransTerm_OK_for_TransGrammar (Gg := Gg)).
  destruct Gg.
  dependent destruction e0.
  apply SmallerSubsetGivesSmallerTermExt.
  apply SSChange.
  clear.
  induction numG.
    destruct V.
    apply SSNil.
  destruct V.
  apply SSSame.
  auto.
Qed.

Lemma ApplyArgs_is_App_or_Nontermi Nn Vv : 
    let App_or_Nontermi {T} (M : term _ _ (Arr T)) := (exists tL K L, M = App Nn Vv tL T K L) \/ (exists X, M = Nontermi _ _ _ X) in
    forall T sub (M : term _ _ (Arr T)), App_or_Nontermi M -> App_or_Nontermi (ApplyArgs sub M).
  dependent induction sub.
    auto.
  intros.
  apply IHsub.
  left.
  eauto.
Qed.

Fixpoint AppendSubstForAllA {Nn VvNew VvTail t_app numG} (K : Subset numG -> term Nn VvNew t_app) 
    (sub : substitution Nn VvNew VvTail) : substitution Nn VvNew (AppendVarAux t_app numG VvTail) :=
  match numG as numG return (Subset numG -> _) -> substitution _ _ (AppendVarAux _ numG _) with
  | 0 => fun K => ConsSubst _ _ _ _ (K tt) sub
  | _ => fun K => AppendSubstForAllA (fun A => K (false, A)) (AppendSubstForAllA (fun A => K (true, A)) sub)
  end K.

Lemma HOPartEmpty_oo0 {Vv} (eq : OnlyOrder0Vars Vv = true) : HOPart Vv = [].
  destruct Vv.
    auto.
  unfold HOPart.
  rewrite eq.
  auto.
Qed.

Lemma HOPartEmpty_oo0_castS {Nn VvNew Vv} (eq : OnlyOrder0Vars Vv = true) :
    substitution Nn VvNew [] = substitution Nn VvNew (TransVars (HOPart Vv)).
  rewrite HOPartEmpty_oo0; auto.
Qed.

Lemma ShiftInHO_HO_castS {Nn VvNew t1 Vv_tail} (eq : OnlyOrder0Vars (t1 :: Vv_tail) = false) :
    substitution Nn VvNew (TransVars (t1 :: HOPart Vv_tail)) = substitution Nn VvNew (TransVars (HOPart (t1 :: Vv_tail))).
  rewrite ShiftInHO_HO; auto.
Qed.

Fixpoint TransSubst {Nn VvNew Vv} (V : Subset (TailLen VvNew)) (sub : substitution Nn VvNew Vv) :
    substitution (TransVars Nn) (TransVars (HOPart VvNew)) (TransVars (HOPart Vv)) :=
  match sub in substitution _ _ Vv return substitution _ _ (TransVars (HOPart Vv)) with
  | EmptySubst _ _ => EmptySubst _ _
  | ConsSubst _ _ t1 T_tail K1 sub_tail => 
      match OnlyOrder0Vars (t1 :: T_tail) as oo return OnlyOrder0Vars (t1 :: T_tail) = oo -> _ with
      | true => fun eq => type_cast (HOPartEmpty_oo0_castS eq) (EmptySubst _ _)
      | false => fun eq => type_cast (ShiftInHO_HO_castS eq)
          (AppendSubstForAllA (fun A => TransTerm A V K1) (TransSubst V sub_tail))
      end eq_refl
  end.

Fixpoint ExtractSubsetForFirst numG {numGNew} : Subset (numG + numGNew) -> Subset numG :=
  match numG as numG return Subset (numG + _) -> Subset numG with
  | 0 => fun V => ()
  | S numG => fun V => match V with (val, V_tail) => (val, ExtractSubsetForFirst numG V_tail) end
  end.

Lemma ApplyArgsForAllA_eq {Nn Vv t_app numG T2} (K : term Nn Vv (Arr (AppendVarAux t_app numG T2))) 
    (L1 L2 : Subset numG -> term Nn Vv t_app) :
    (forall A, L1 A = L2 A) -> ApplyArgsForAllA K L1 = ApplyArgsForAllA K L2.
  revert T2 K.
  induction numG; intros.
    simpl.
    rewrite H.
    auto.
  simpl.
  fold AppendVarAux.
  replace (@ApplyArgsForAllA Nn Vv t_app numG (AppendVarAux t_app numG T2) K (fun A => L1 (false, A)))
      with (@ApplyArgsForAllA Nn Vv t_app numG (AppendVarAux t_app numG T2) K (fun A => L2 (false, A)));
    apply IHnumG; easy.
Qed.

Lemma ApplyArgsForAllA_Substitute_com {Nn VvNew Vv t_app numG T2} (K : term Nn Vv (Arr (AppendVarAux t_app numG T2))) 
    (L : Subset numG -> term Nn Vv t_app) (sub : substitution Nn VvNew Vv) : 
    ApplyArgsForAllA (Substitute sub K) (fun A => Substitute sub (L A)) = Substitute sub (ApplyArgsForAllA K L).
  revert T2 K.
  induction numG.
    auto.
  simpl.
  intros.
  rewrite <- IHnumG.
  rewrite <- IHnumG.
  auto.
Qed.

Lemma ShiftVarAux_AppendSubstForAllA_com Nn VvNew Vv_tail numG t_app t (sub : substitution Nn VvNew Vv_tail)
    (K : Subset numG -> term Nn VvNew t_app) (x : ElementOfList t Vv_tail) :
    FindInSubstitution (AppendSubstForAllA K sub) (ShiftVarAux t_app numG x) = FindInSubstitution sub x.
  revert Vv_tail x sub.
  induction numG.
    auto.
  intros.
  simpl.
  rewrite IHnumG.
  apply IHnumG.
Qed.

Lemma FindNewVar_AppendSubstForAllA_com {Nn VvNew Vv_tail t} (A : Subset (TailLen (ArgsOfType t)))
    (sub : substitution Nn VvNew (TransVars Vv_tail)) (K : Subset (TailLen (ArgsOfType t)) -> term Nn VvNew (TransType t)) :
    FindInSubstitution (AppendSubstForAllA K sub) (FindNewVar A (FirstEl t Vv_tail)) = K A.
  unfold FindNewVar.
  revert sub A K.
  generalize (TransVars Vv_tail) as VvTail.
  generalize (TailLen (ArgsOfType t)) as numG.
  induction numG; intros.
    destruct A.
    auto.
  destruct A.
  destruct b; simpl.
    rewrite ShiftVarAux_AppendSubstForAllA_com.
    apply IHnumG.
  apply IHnumG.
Qed.

Lemma ShiftInTail_oo0_castT {Nn t numGNew t1 Vv_tail} (eq : OnlyOrder0Vars (t1 :: Vv_tail) = true) : 
    term Nn (GrVars (S (TailLen Vv_tail) + numGNew)) t =
    term Nn (GrVars (TailLen (t1 :: Vv_tail) + numGNew)) t.
  rewrite ShiftInTail_oo0; auto.
Qed.

Fixpoint AddVariablesToVarBackAux {Vv} VvNew {t : type} (x : ElementOfList t Vv) : ElementOfList t (Vv ++ VvNew) :=
  match x with 
  | FirstEl _ _ => FirstEl _ _
  | NextEl _ _ _ x2 => NextEl _ _ _ (AddVariablesToVarBackAux _ x2)
  end.

Lemma GrVars_app_com n1 n2 : GrVars n1 ++ GrVars n2 = GrVars (n1 + n2).
  apply repeat_app_com.
Qed.

Lemma GrVars_app_com_castV {t n1 n2} : ElementOfList t (GrVars n1 ++ GrVars n2) = ElementOfList t (GrVars (n1 + n2)).
  rewrite GrVars_app_com; auto.
Qed.

Definition AddVariablesToVarBack {numG} numGNew {t : type} (x : ElementOfList t (GrVars numG)) :
    ElementOfList t (GrVars (numG + numGNew)) := type_cast GrVars_app_com_castV (AddVariablesToVarBackAux (GrVars numGNew) x).

Lemma TailIsAll_oo0_castV2 {t Vv numGNew} (eq : OnlyOrder0Vars Vv = true) :
    ElementOfList t (Vv ++ GrVars numGNew) = ElementOfList t (GrVars (TailLen Vv + numGNew)).
  rewrite (TailIsAll_oo0 eq) at 1; auto.
  rewrite GrVars_app_com; auto.
Qed.

Lemma FindInSubstitution_oo0_Aux {Nn Vv numGNew t} (sub : substitution Nn (GrVars numGNew) Vv) (x : ElementOfList t Vv)
    (OO0 : OnlyOrder0Vars Vv = true) : FindInSubstitution (GetHOSub sub) x =
    Var _ _ _ (type_cast (TailIsAll_oo0_castV2 OO0) (AddVariablesToVarBackAux (GrVars numGNew) x)).
  induction Vv; try easy.
  dependent destruction sub.
  unfold GetHOSub.
  fold @GetHOSub.
  generalize (@eq_refl bool (OnlyOrder0Vars (a :: Vv))).
  generalize (OnlyOrder0Vars (a :: Vv)) at 2 3.
  intros.
  destruct b; try (exfalso; rewrite e in OO0; easy).
  destruct a.
  destruct l; try easy.
  assert (term Nn (GrVars (S (TailLen Vv) + numGNew)) t = term Nn (GrVars (TailLen (Arr [] :: Vv) + numGNew)) t).
    rewrite <- (ShiftInTail_oo0 e); auto.
  assert (forall ss, FindInSubstitution (type_cast (ShiftInTail_oo0_castS e) ss) x = type_cast H (FindInSubstitution ss x)).
    revert H.
    generalize (@ShiftInTail_oo0_castS Nn numGNew (Arr []) Vv e).
    replace (S (TailLen Vv)) with (TailLen (Arr [] :: Vv)).
      simpl.
      dependent destruction e0.
      dependent destruction H.
      auto.
    apply ShiftInTail_oo0; auto.
  rewrite H0.
  dependent destruction x; simpl.
    fold (Vv ++ GrVars numGNew).
    change (if OnlyOrder0Vars Vv then S (length Vv) else TailLen Vv) with (TailLen (Ground :: Vv)).
    generalize (@TailIsAll_oo0_castV2 (Arr []) (Arr [] :: Vv) numGNew OO0).
    clear H0.
    revert H.
    change ((Arr [] :: Vv) ++ GrVars numGNew) with (Arr [] :: Vv ++ GrVars numGNew).
    replace (Vv ++ GrVars numGNew) with (GrVars (TailLen Vv + numGNew)).
      change Ground with (Arr []).
      replace (TailLen (Arr [] :: Vv)) with (S (TailLen Vv)).
        dependent destruction H.
        dependent destruction e0.
        auto.
      rewrite ShiftInTail_oo0; auto.
    replace Vv with (GrVars (TailLen Vv)) at 2.
      rewrite GrVars_app_com; auto.
    rewrite <- TailIsAll_oo0; auto.
  rewrite (FindInSubstitution_AddVariables_com 1).
  rewrite (IHVv _ _ OO0).
  simpl.
  generalize (AddVariablesToVarBackAux (GrVars numGNew) x) as xx.
  change (_ Ground (TailLen Vv + numGNew)) with (GrVars (TailLen Vv + numGNew)).
  change (if OnlyOrder0Vars Vv then S (length Vv) else TailLen Vv) with (TailLen (Ground :: Vv)).
  generalize (@TailIsAll_oo0_castV2 t Vv numGNew OO0).
  generalize (@TailIsAll_oo0_castV2 t (Arr [] :: Vv) numGNew OO0).
  clear H0.
  revert H.
  change ((Arr [] :: Vv) ++ GrVars numGNew) with (Arr [] :: Vv ++ GrVars numGNew).
  replace (Vv ++ GrVars numGNew) with (GrVars (TailLen Vv + numGNew)).
    change Ground with (Arr []).
    replace (TailLen (Arr [] :: Vv)) with (S (TailLen Vv)).
      dependent destruction H.
      dependent destruction e0.
      dependent destruction e0.
      auto.
    rewrite ShiftInTail_oo0; auto.
  replace Vv with (GrVars (TailLen Vv)) at 2.
    rewrite GrVars_app_com; auto.
  rewrite <- TailIsAll_oo0; auto.
Qed.

Lemma FindInHOSubstitution_oo0 {Nn Vv numGNew t} (sub : substitution Nn (GrVars numGNew) Vv) (x : ElementOfList t Vv) xFO :
    RemainsOrTail x = inr xFO -> OnlyOrder0Vars Vv = true ->
    FindInSubstitution (GetHOSub sub) x = Var _ _ _ (AddVariablesToVarBack numGNew xFO).
  intros.
  rewrite (FindInSubstitution_oo0_Aux _ _ H0).
  f_equal.
  rewrite (RemainsOrTail_oo0 _ H0) in H.
  simplify_eq H.
  intro.
  rewrite <- H1.
  unfold AddVariablesToVarBack.
  generalize (@GrVars_app_com_castV t (TailLen Vv) numGNew).
  generalize (@TailIsAll_oo0_castV t Vv H0).
  replace (GrVars (TailLen Vv)) with Vv.
    dependent destruction e.
    intros.
    apply type_cast_invariance.
  rewrite <- TailIsAll_oo0; auto.
Qed.

Lemma SkipInTail_HO_castT {Nn numGNew t1 Vv_tail t} (eq : OnlyOrder0Vars (t1 :: Vv_tail) = false) : 
    term Nn (GrVars (TailLen Vv_tail + numGNew)) t = term Nn (GrVars (TailLen (t1 :: Vv_tail) + numGNew)) t.
  rewrite SkipInTail_HO; auto.
Qed.

Lemma FindInSubstitution_SkipInTail_HO_cast_com Nn a Vv t numGNew (x : ElementOfList t (a :: Vv)) 
    (sub : substitution Nn (GrVars (TailLen Vv + numGNew)) (a :: Vv)) (nOO0 : OnlyOrder0Vars (a :: Vv) = false) :
    FindInSubstitution (type_cast (SkipInTail_HO_castS nOO0) sub) x =
    type_cast (SkipInTail_HO_castT nOO0) (FindInSubstitution sub x).
  generalize (@SkipInTail_HO_castS Nn (a :: Vv) numGNew a Vv nOO0).
  generalize (@SkipInTail_HO_castT Nn numGNew a Vv t nOO0).
  replace (TailLen (a :: Vv)) with (TailLen Vv).
    dependent destruction e.
    dependent destruction e.
    auto.
  rewrite SkipInTail_HO; auto.
Qed.
 
Lemma FindInHOSubstitution_tail {Nn Vv numGNew t} (sub : substitution Nn (GrVars numGNew) Vv) (x : ElementOfList t Vv) xFO :
    RemainsOrTail x = inr xFO -> FindInSubstitution (GetHOSub sub) x = Var _ _ _ (AddVariablesToVarBack numGNew xFO).
  induction Vv; try easy.
  intro.
  case_eq (OnlyOrder0Vars (a :: Vv)).
    apply FindInHOSubstitution_oo0; auto.
  intro.
  dependent destruction x.
    enough (exists xHO, RemainsOrTail (FirstEl a Vv) = inl xHO).
      rewrite H in H1.
      destruct H1.
      easy.
    unfold RemainsOrTail.
    generalize (@eq_refl bool (OnlyOrder0Vars (a :: Vv))).
    generalize (OnlyOrder0Vars (a :: Vv)) at 2 3.
    destruct b; intro; try (rewrite e in H0; easy).
    eauto.
  assert (exists xFO_t, RemainsOrTail (NextEl t a Vv x) = inr (type_cast (SkipInTail_HO_castV H0) xFO_t)
      /\ RemainsOrTail x = inr xFO_t).
    revert H.
    unfold RemainsOrTail.
    generalize (@eq_refl bool (OnlyOrder0Vars (a :: Vv))).
    generalize (OnlyOrder0Vars (a :: Vv)) at 2 3 7.
    destruct b; intro; try (exfalso; rewrite e in H0; easy).
    fold @RemainsOrTail.
    case_eq (RemainsOrTail x).
      easy.
    intros.
    exists e0.
    split; auto.
    f_equal.
    apply type_cast_invariance.
  destruct H1 as (xFO_t & H1).
  destruct H1.
  rewrite H in H1.
  dependent destruction sub.
  unfold GetHOSub.
  generalize (@eq_refl bool (OnlyOrder0Vars (a :: Vv))).
  generalize (OnlyOrder0Vars (a :: Vv)) at 2 3.
  destruct b; intro; try (exfalso; rewrite H0 in e; easy).
  fold @GetHOSub.
  rewrite FindInSubstitution_SkipInTail_HO_cast_com.
  simpl (FindInSubstitution _ _).
  rewrite (IHVv _ _ xFO_t); auto.
  simplify_eq H1.
  intros.
  rewrite H3.
  clear H1 H2 H3.
  revert xFO_t.
  generalize (@SkipInTail_HO_castV t a Vv H0).
  generalize (@SkipInTail_HO_castT Nn numGNew a Vv t e).
  change (if match a with
      | Arr [] => OnlyOrder0Vars Vv
      | Arr (_ :: _) => false
      end then S (@length type Vv) else TailLen Vv) with (TailLen (a :: Vv)).
   replace (TailLen Vv) with (TailLen (a :: Vv)).
    dependent destruction e0.
    dependent destruction e0.
    auto.
  apply SkipInTail_HO; auto.
Qed.

Lemma TransTerm_4var_tail {Nn Vv numGNew t} (A : Subset (TailLen (ArgsOfType t))) (V : Subset (TailLen Vv + numGNew))
    (sub : substitution Nn (GrVars numGNew) Vv) (x : ElementOfList t Vv) xFO : RemainsOrTail x = inr xFO ->
    TransTerm A (type_cast TailIsAll_GrVars_castSet V) (FindInSubstitution (GetHOSub sub) x) = 
      type_cast (OnlyGround_GrVars_castT xFO)
        (if BelongsToSubset xFO (ExtractSubsetForFirst (TailLen Vv) V)
        then And _ _ [] else Or _ _ []).
  intro.
  rewrite (FindInHOSubstitution_tail _ _ xFO); auto.
  simpl.
  assert (OnlyOrder0Vars (GrVars (TailLen Vv + numGNew)) = true) as OO0.
    apply OnlyOrder0Vars_GrVars.
  rewrite (RemainsOrTail_oo0 _ OO0).
  assert (forall y : ElementOfList t _, 
      BelongsToSubset (type_cast (TailIsAll_oo0_castV OO0) y) (type_cast TailIsAll_GrVars_castSet V) =
      BelongsToSubset y V).
    generalize (@TailIsAll_GrVars_castSet (TailLen Vv + numGNew)).
    generalize (@TailIsAll_oo0_castV t (GrVars (TailLen Vv + numGNew)) OO0).
    replace (TailLen (GrVars (TailLen Vv + numGNew))) with (TailLen Vv + numGNew).
      dependent destruction e.
      dependent destruction e.
      auto.
    rewrite TailIsAll_GrVars.
    auto.
  rewrite H0.
  assert (BelongsToSubset (AddVariablesToVarBack numGNew xFO) V = 
      BelongsToSubset xFO (ExtractSubsetForFirst (TailLen Vv) V)).
    clear.
    revert xFO V.
    generalize (TailLen Vv).
    induction n.
      easy.
    destruct V.
    unfold AddVariablesToVarBack.
    generalize (@GrVars_app_com_castV t (S n) numGNew).
    dependent destruction xFO; simpl.
      change (_ (repeat _ _) (GrVars _)) with (GrVars n ++ GrVars numGNew).
      intro.
      assert (type_cast e (FirstEl (Arr []) (GrVars n ++ GrVars numGNew)) = FirstEl _ _).
        revert e.
        replace (GrVars n ++ GrVars numGNew) with (GrVars (n + numGNew)).
          dependent destruction e.
          auto.
        rewrite GrVars_app_com; auto.
      rewrite H; auto.
    generalize (@DestructGrVars_castV t (Arr []) (@repeat type (Arr []) n) n (@eq_refl (list type) (GrVars (S n)))).
    dependent destruction e.
    simpl.
    rewrite <- IHn.
    unfold AddVariablesToVarBack.
    change (AddVariablesToVarBackAux _ _) with (AddVariablesToVarBackAux (GrVars numGNew) xFO).
    generalize (AddVariablesToVarBackAux (GrVars numGNew) xFO) as xx.
    intros.
    replace (type_cast e (NextEl t (Arr []) (repeat (Arr []) n ++ GrVars numGNew) xx))
        with (NextEl t (Arr []) _ (type_cast GrVars_app_com_castV xx)).
      generalize (@DestructGrVars_castV t (Arr []) (GrVars (n + numGNew)) (n + numGNew) 
          (@eq_refl (list type) (GrVars (S (n + numGNew))))).
      dependent destruction e0.
      auto.
    revert e.
    generalize (@GrVars_app_com_castV t n numGNew).
    change (GrVars (S (n + numGNew))) with (Ground :: GrVars (n + numGNew)).
    replace (GrVars (n + numGNew)) with (GrVars n ++ GrVars numGNew).
      dependent destruction e.
      dependent destruction e.
      auto.
    apply GrVars_app_com.
  rewrite H1.
  generalize (BelongsToSubset xFO (ExtractSubsetForFirst (TailLen Vv) V)).
  intros.
  generalize (if b
      then And (TransVars Nn) (TransVars (HOPart (GrVars (TailLen Vv + numGNew)))) []
      else Or (TransVars Nn) (TransVars (HOPart (GrVars (TailLen Vv + numGNew)))) []).
  generalize (@OnlyGround_GrVars_castT (TransVars Nn) (TransVars (HOPart (GrVars (TailLen Vv + numGNew)))) t (TailLen Vv) xFO).
  generalize (@OnlyGround_GrVars_castT (TransVars Nn) (TransVars (HOPart (GrVars (TailLen Vv + numGNew)))) t
     (TailLen (GrVars (TailLen Vv + numGNew)))
     (@type_cast (@ElementOfList type t (GrVars (TailLen Vv + numGNew)))
        (@ElementOfList type t (GrVars (TailLen (GrVars (TailLen Vv + numGNew)))))
        (@TailIsAll_oo0_castV t (GrVars (TailLen Vv + numGNew)) OO0) (@AddVariablesToVarBack (TailLen Vv) numGNew t xFO))).
  replace (TransType t) with Ground.
    dependent destruction e.
    dependent destruction e.
    auto.
  clear H H1.
  rewrite (OnlyGround_GrVars xFO); auto.
Qed.

Lemma FindInSubstitution_Trans_com {Nn VvNew Vv t} (A : Subset (TailLen (ArgsOfType t))) (V : Subset (TailLen VvNew)) 
    (sub : substitution Nn VvNew Vv) (x : ElementOfList t Vv) xHO : RemainsOrTail x = inl xHO ->
    FindInSubstitution (TransSubst V sub) (FindNewVar A xHO) =
    TransTerm A V (FindInSubstitution sub x).
  intro.
  induction Vv.
    easy.
  dependent destruction sub.
  unfold TransSubst.
  fold @TransSubst.
  generalize (@eq_refl bool (OnlyOrder0Vars (a :: Vv))).
  generalize (OnlyOrder0Vars (a :: Vv)) at 2 3.
  destruct b; intro.
    specialize (RemainsOrTail_oo0 x e).
    rewrite H.
    easy.
  set (ss := (AppendSubstForAllA (fun A0 : Subset (TailLen (ArgsOfType a)) => TransTerm A0 V t1) (TransSubst V sub))).
  assert (forall xHO_, FindInSubstitution (type_cast (ShiftInHO_HO_castS e) ss) (FindNewVar A (type_cast (ShiftInHO_HO_castV e) xHO_)) =
      FindInSubstitution ss (FindNewVar A xHO_)).
    generalize ss.
    clear.
    generalize (@ShiftInHO_HO_castS (TransVars Nn) (TransVars (HOPart VvNew)) a Vv e).
    generalize (@ShiftInHO_HO_castV t a Vv e).
    replace (HOPart (a :: Vv)) with (a :: HOPart Vv).
      dependent destruction e0.
      dependent destruction e0.
      auto.
    rewrite ShiftInHO_HO; auto.
  unfold ss in *.
  dependent destruction x.
    assert (xHO = type_cast (ShiftInHO_HO_castV e) (FirstEl _ _)).
      enough (RemainsOrTail (FirstEl a Vv) = inl (type_cast (ShiftInHO_HO_castV e) (FirstEl _ _))).
        rewrite H in H1.
        simplify_eq H1.
        auto.
      unfold RemainsOrTail.
      generalize (@eq_refl bool (OnlyOrder0Vars (a :: Vv))).
      generalize (OnlyOrder0Vars (a :: Vv)) at 2 3.
      destruct b; intro; try (exfalso; rewrite e in e0; easy).
      f_equal.
      apply type_cast_invariance.
    rewrite H1.
    rewrite H0.
    rewrite FindNewVar_AppendSubstForAllA_com.
    auto.
  assert (exists xHO_t, RemainsOrTail (NextEl t a Vv x) = inl (type_cast (ShiftInHO_HO_castV e) (NextEl _ _ _ xHO_t))
      /\ RemainsOrTail x = inl xHO_t).
    unfold RemainsOrTail.
    generalize (@eq_refl bool (OnlyOrder0Vars (a :: Vv))).
    generalize (OnlyOrder0Vars (a :: Vv)) at 2 3.
    destruct b; intro; try (exfalso; rewrite e in e0; easy).
    fold @RemainsOrTail.
    case_eq (RemainsOrTail x); intros xHO_t H1.
      exists xHO_t.
      split.
        f_equal.
        apply type_cast_invariance.
      auto.
    enough (exists xFO, RemainsOrTail (NextEl t a Vv x) = inr xFO).
      rewrite H in H2.
      destruct H2.
      easy.
    unfold RemainsOrTail.
    generalize (@eq_refl bool (OnlyOrder0Vars (a :: Vv))).
    generalize (OnlyOrder0Vars (a :: Vv)) at 2 3.
    destruct b; intro; try (exfalso; rewrite e in e1; easy).
    fold @RemainsOrTail.
    rewrite H1.
    exists (type_cast (SkipInTail_HO_castV e1) xHO_t).
    auto.
  destruct H1 as (xHO_t & H1).
  destruct H1.
  rewrite H in H1.
  simplify_eq H1; intro.
  rewrite H3.
  rewrite H0.
  unfold FindNewVar.
  rewrite ShiftVarAux_AppendSubstForAllA_com.
  rewrite (IHVv _ x); auto.
Qed.

Lemma TransTerm_Substitute_var_com Nn Vv numGNew t (A : Subset (TailLen (ArgsOfType t))) (V : Subset (TailLen Vv + numGNew))
    (sub : substitution Nn (GrVars numGNew) Vv) (x : ElementOfList t Vv) :
    TransTerm A (type_cast TailIsAll_GrVars_castSet V) (FindInSubstitution (GetHOSub sub) x) =
      Substitute (TransSubst (type_cast TailIsAll_GrVars_castSet V) (GetHOSub sub)) 
        (TransTerm A (ExtractSubsetForFirst (TailLen Vv) V) (Var Nn Vv t x)).
  case_eq (RemainsOrTail x).
    intros xHO H.
    simpl.
    rewrite H.
    simpl.
    rewrite (FindInSubstitution_Trans_com _ _ _ x); auto.
  intros xFO H.
  rewrite (TransTerm_4var_tail _ _ _ _ xFO); auto.
  simpl (TransTerm _ _ _).
  rewrite H.
  generalize (BelongsToSubset xFO (ExtractSubsetForFirst (TailLen Vv) V)).
  generalize (@OnlyGround_GrVars_castT (TransVars Nn) (TransVars (HOPart (GrVars (TailLen Vv + numGNew)))) t (TailLen Vv) xFO).
  generalize (@OnlyGround_GrVars_castT (TransVars Nn) (TransVars (HOPart Vv)) t (TailLen Vv) xFO).
  replace (TransType t) with Ground; try (rewrite (OnlyGround_GrVars xFO); auto).
  dependent destruction e.
  dependent destruction e.
  destruct b; auto.
Qed.

Lemma TransTerm_Substitute_com Nn numGNew Vv t (A : Subset (TailLen (ArgsOfType t))) (M : term Nn Vv t) 
    (sub : substitution Nn (GrVars numGNew) Vv) (V : Subset (TailLen Vv + numGNew)) :
    TransTerm A (type_cast TailIsAll_GrVars_castSet V) (Substitute (GetHOSub sub) M) =
      Substitute (TransSubst (type_cast TailIsAll_GrVars_castSet V) (GetHOSub sub))
        (TransTerm A (ExtractSubsetForFirst (TailLen Vv) V) M).
  induction M using term_my_ind.
          auto.
        apply TransTerm_Substitute_var_com.
      simpl.
      f_equal.
      rewrite map_map.
      rewrite map_map.
      apply map_ext_in.
      auto.
    simpl.
    f_equal.
    rewrite map_map.
    rewrite map_map.
    apply map_ext_in.
    auto.
  simpl (Substitute (GetHOSub _) _).
  unfold TransTerm.
  generalize (@eq_refl bool (OnlyOrder0Vars (tL :: T))).
  generalize (OnlyOrder0Vars (tL :: T)) at 2 3 7.
  set (ss := TransSubst (type_cast TailIsAll_GrVars_castSet V) (GetHOSub sub)).
  destruct b; intro.
    rewrite IHM1.
    rewrite IHM1.
    rewrite IHM2.
    generalize (@TransTypeTailIsGround_oo0_castT (TransVars Nn) (TransVars (HOPart (GrVars (TailLen Vv + numGNew)))) tL T e).
    generalize (@TransTypeTailIsGround_oo0_castT (TransVars Nn) (TransVars (HOPart Vv)) tL T e).
    replace (TransType (Arr T)) with Ground.
    all: swap 1 2.
      rewrite (TransTypeTailIsGround_oo0 e).
      auto.
    repeat dependent destruction e0.
    simpl.
    assert (forall M, Substitute ss (type_cast (TransTypeIsGround_oo0_castT e) M) =
        type_cast (TransTypeIsGround_oo0_castT e) (Substitute ss M)).
      generalize (@TransTypeIsGround_oo0_castT (TransVars Nn) (TransVars (HOPart Vv)) (tL :: T) e).
      generalize (@TransTypeIsGround_oo0_castT (TransVars Nn) (TransVars (HOPart (GrVars (TailLen Vv + numGNew)))) (tL :: T) e).
      replace (TransType (Arr (tL :: T))) with Ground.
        repeat dependent destruction e0.
        auto.
      rewrite TransTypeIsGround_oo0; auto.
    assert(forall M, Substitute ss (type_cast (FirstIsGround_oo0_castT e) M) =
        type_cast (FirstIsGround_oo0_castT e) (Substitute ss M)).
      generalize (@FirstIsGround_oo0_castT (TransVars Nn) (TransVars (HOPart (GrVars (TailLen Vv + numGNew)))) tL T e).
      generalize (@FirstIsGround_oo0_castT (TransVars Nn) (TransVars (HOPart Vv)) tL T e).
      replace (TransType tL) with Ground.
        repeat dependent destruction e0.
        auto.
      rewrite (FirstIsGround_oo0 e); auto.
    repeat rewrite H.
    rewrite H0.
    auto.
  rewrite IHM1.
  fold @TransTerm.
  rewrite <- (ApplyArgsForAllA_Substitute_com (type_cast (TransType_HO_castT e) _)).
  assert (forall M, Substitute ss (type_cast (TransType_HO_castT e) M) = type_cast (TransType_HO_castT e) (Substitute ss M)).
    generalize (@TransType_HO_castT (TransVars Nn) (TransVars (HOPart Vv)) tL T e).
    generalize (@TransType_HO_castT (TransVars Nn) (TransVars (HOPart (GrVars (TailLen Vv + numGNew)))) tL T e).
    replace (Arr (AppendVarAux (TransType tL) (TailLen (ArgsOfType tL)) (ArgsOfType (TransType (Arr T))))) with
        (TransType (Arr (tL :: T))).
      repeat dependent destruction e0.
      auto.
    apply TransType_HO.
    auto.
  rewrite H.
  apply ApplyArgsForAllA_eq.
  apply IHM2.
Qed.

Fixpoint AppendTransExplicitSubst {Nn numG numGAdd} (V : Subset numG) : substitution Nn (GrVars numG) (GrVars numGAdd) ->
    (Subset (numGAdd + numG) -> term (TransVars Nn) [] Ground) -> term (TransVars Nn) [] Ground :=
  match numGAdd as numGAdd return substitution _ _ (GrVars numGAdd) -> (Subset (numGAdd + _) -> _) -> _ with
  | 0 => fun _ tM => tM V
  | S numG_tail => fun exp_sub tM =>
      let (R1, exp_sub_tail) :=
        match exp_sub with ConsSubst _ _ (Arr []) _ R1 exp_sub_tail => (R1, exp_sub_tail) end in
      AppendTransExplicitSubst V exp_sub_tail (fun Ve => Or _ _ [tM ((false, Ve) : Subset (S _));
        And _ _ [tM ((true, Ve) : Subset (S _)); type_cast HOPartEmpty_GrVars_castT 
          (TransTerm Subset0 (type_cast TailIsAll_GrVars_castSet Ve) (AddVariablesToTerm _ R1))]])
  end.

Lemma Trans_Append_com {Nn numG numGAdd} (V : Subset numG) (exp_sub : substitution Nn (GrVars numG) (GrVars numGAdd))
    (eM : ext_term Nn (numGAdd + numG)) :
    TransExtTerm V (AppendExplicitSubst exp_sub eM) = AppendTransExplicitSubst V exp_sub (fun Ve => TransExtTerm Ve eM).
  induction numGAdd.
    easy.
  dependent destruction exp_sub.
  simpl.
  rewrite IHnumGAdd.
  auto.
Qed.

Lemma AppendTransExplicitSubst_eq {Nn numG numGAdd} (V : Subset numG) (exp_sub : substitution Nn (GrVars numG) (GrVars numGAdd))
    (tM1 tM2 : Subset (numGAdd + numG) -> term (TransVars Nn) [] Ground) :
    (forall V, tM1 V = tM2 V) -> AppendTransExplicitSubst V exp_sub tM1 = AppendTransExplicitSubst V exp_sub tM2.
  induction numGAdd; intros.
    apply H.
  dependent destruction exp_sub.
  apply IHnumGAdd.
  intro.
  repeat rewrite H.
  auto.
Qed.

Lemma Trans_ExtSubstitute_com {Nn numG Vv} (V : Subset numG) (sub : substitution Nn (GrVars numG) Vv) (M : term Nn Vv Ground) :
    TransExtTerm V (ExtSubstitute sub M) = AppendTransExplicitSubst V (GetExpSub sub) (fun Ve =>
      type_cast HOPartEmpty_GrVars_castT (Substitute (TransSubst (type_cast TailIsAll_GrVars_castSet Ve) (GetHOSub sub))
        (TransTerm Subset0 (ExtractSubsetForFirst (TailLen Vv) Ve) M))).
  unfold ExtSubstitute.
  rewrite Trans_Append_com.
  apply AppendTransExplicitSubst_eq.
  intro.
  simpl.
  rewrite TransTerm_Substitute_com.
  auto.
Qed.

Lemma TransType_is_TransVars_castT2 {Nn Vv t} : term Nn Vv (TransType t) = term Nn Vv (Arr (TransVars (HOPart (ArgsOfType t)))).
  rewrite TransType_is_TransVars.
  auto.
Qed.

Lemma VarsCast_Or_com Nn Vv1 Vv2 (eq : Vv1 = Vv2) (cast : term Nn Vv1 Ground = term Nn Vv2 Ground)
    (chldrn : list (term Nn Vv1 Ground)) :
    type_cast cast (Or _ _ chldrn) = Or _ _ (map (type_cast cast) chldrn).
  revert cast chldrn.
  rewrite eq.
  dependent destruction cast.
  intro.
  rewrite map_id.
  auto.
Qed.

Lemma VarsCast_And_com Nn Vv1 Vv2 (eq : Vv1 = Vv2) (cast : term Nn Vv1 Ground = term Nn Vv2 Ground)
    (chldrn : list (term Nn Vv1 Ground)) :
    type_cast cast (And _ _ chldrn) = And _ _ (map (type_cast cast) chldrn).
  revert cast chldrn.
  rewrite eq.
  dependent destruction cast.
  intro.
  rewrite map_id.
  auto.
Qed.

Lemma VarsCast_Or_And_com Nn Vv1 Vv2 (eq : Vv1 = Vv2) (cast : term Nn Vv1 Ground = term Nn Vv2 Ground)
    (K L M : term Nn Vv1 Ground) :
    type_cast cast (Or _ _ [K; And _ _ [L; M]]) = Or _ _ [type_cast cast K; And _ _ [type_cast cast L; type_cast cast M]].
  rewrite VarsCast_Or_com; auto.
  simpl.
  rewrite VarsCast_And_com; auto.
Qed.

Lemma VarsCast_ApplyArgsForAllA_com {Nn Vv1 Vv2 t_app numG T2} (cast : forall t, term Nn Vv1 t = term Nn Vv2 t) (eq : Vv1 = Vv2)
    (K : term Nn Vv1 (Arr (AppendVarAux t_app numG T2))) (L : Subset numG -> term Nn Vv1 t_app) :
    type_cast (cast _) (ApplyArgsForAllA K L) = ApplyArgsForAllA (type_cast (cast _) K) (fun A => type_cast (cast _) (L A)).
  revert cast K L.
  rewrite eq.
  intros.
  generalize (cast (Arr T2)).
  generalize (cast (Arr (AppendVarAux t_app numG T2))).
  generalize (cast t_app).
  repeat dependent destruction e.
  auto.
Qed.

Lemma TransTerm_AddVariables_com Nn numG numG2 t (A : Subset (TailLen (ArgsOfType t))) (val : bool)
    (V : Subset (numG + numG2)) (M : term Nn _ t) :
    type_cast HOPartEmpty_GrVars_castT (TransTerm A (type_cast TailIsAll_GrVars_castSet V) (AddVariablesToTerm numG M)) =
    type_cast HOPartEmpty_GrVars_castT (TransTerm A (type_cast TailIsAll_GrVars_castSet ((val, V) : Subset (S _)))
      (AddVariablesToTerm (S numG) M)).
  induction M using term_my_ind.
          simpl.
          generalize (@HOPartEmpty_GrVars_castT (TransVars Nn) (numG + numG2) (TransType t)).
          replace (HOPart (GrVars (numG + numG2))) with (HOPart (GrVars (S (numG + numG2)))).
            intro.
            apply type_cast_invariance.
          repeat rewrite HOPartEmpty_GrVars.
          auto.
        simpl AddVariablesToTerm.
        generalize (AddVariablesToVar numG x).
        fold (numG + numG2).
        fold (repeat Ground (numG + numG2)).
        fold (GrVars (numG + numG2)).
        clear x; intro x.
        unfold TransTerm.
        unfold RemainsOrTail.
        fold @RemainsOrTail.
        generalize (@eq_refl bool (OnlyOrder0Vars (GrVars (S (numG + numG2))))).
        generalize (OnlyOrder0Vars (GrVars (S (numG + numG2)))) at 2 3.
        destruct b; intro; try (exfalso; rewrite OnlyOrder0Vars_GrVars in e; easy).
        assert (OnlyOrder0Vars (GrVars (numG + numG2)) = true).
          rewrite OnlyOrder0Vars_GrVars; auto.
        rewrite (RemainsOrTail_oo0 _ H).
        replace (BelongsToSubset (_ _ (NextEl _ _ _ _)) _) with
            (BelongsToSubset (type_cast (TailIsAll_oo0_castV H) x) (type_cast TailIsAll_GrVars_castSet V)).
          generalize (@HOPartEmpty_GrVars_castT (TransVars Nn) (numG + numG2) (TransType t)).
          generalize (@HOPartEmpty_GrVars_castT (TransVars Nn) (S (numG + numG2)) (TransType t)).
          repeat rewrite HOPartEmpty_GrVars.
          repeat dependent destruction e0.
          simpl.
          apply type_cast_invariance.
        fold (repeat Ground (numG + numG2)).
        fold (GrVars (numG + numG2)).
        generalize (@TailIsAll_oo0_castV t (GrVars (numG + numG2)) H).
        generalize (@TailIsAll_oo0_castV t (GrVars (S (numG + numG2))) e).
        generalize (@TailIsAll_GrVars_castSet (numG + numG2)).
        generalize (@TailIsAll_GrVars_castSet (S (numG + numG2))).
        repeat rewrite TailIsAll_GrVars.
        repeat dependent destruction e0.
        simpl.
        generalize (@DestructGrVars_castV t Ground (GrVars (numG + numG2)) (numG + numG2)
            (@eq_refl (list type) (GrVars (S (numG + numG2))))).
        dependent destruction e0.
        auto.
      simpl AddVariablesToTerm.
      unfold TransTerm.
      fold @TransTerm.
      repeat rewrite VarsCast_And_com; try rewrite HOPartEmpty_GrVars; auto.
      repeat rewrite map_map.
      f_equal.
      apply map_ext_in.
      auto.
    simpl AddVariablesToTerm.
    unfold TransTerm.
    fold @TransTerm.
    repeat rewrite VarsCast_Or_com; try rewrite HOPartEmpty_GrVars; auto.
    repeat rewrite map_map.
    f_equal.
    apply map_ext_in.
    auto.
  simpl AddVariablesToTerm.
  unfold TransTerm.
  fold @TransTerm.
  generalize (@eq_refl bool (OnlyOrder0Vars (tL :: T))).
  generalize (OnlyOrder0Vars (tL :: T)) at 2 3 7.
  destruct b; intro OO0.
    generalize (@TransTypeTailIsGround_oo0_castT (TransVars Nn) (TransVars (HOPart (GrVars (numG + numG2)))) tL T OO0).
    generalize (@TransTypeTailIsGround_oo0_castT (TransVars Nn) (TransVars (HOPart (GrVars (S (numG + numG2))))) tL T OO0).
    rewrite (TransTypeTailIsGround_oo0 OO0).
    repeat dependent destruction e.
    repeat rewrite VarsCast_Or_And_com; try rewrite HOPartEmpty_GrVars; auto.
    repeat f_equal.
        generalize (@TransTypeIsGround_oo0_castT (TransVars Nn) (TransVars (HOPart (GrVars (numG + numG2)))) (tL :: T) OO0).
        generalize (@TransTypeIsGround_oo0_castT (TransVars Nn) (TransVars (HOPart (GrVars (S (numG + numG2))))) (tL :: T) OO0).
        rewrite <- (TransTypeIsGround_oo0 OO0).
        repeat dependent destruction e.
        apply IHM1.
      generalize (@TransTypeIsGround_oo0_castT (TransVars Nn) (TransVars (HOPart (GrVars (numG + numG2)))) (tL :: T) OO0).
      generalize (@TransTypeIsGround_oo0_castT (TransVars Nn) (TransVars (HOPart (GrVars (S (numG + numG2))))) (tL :: T) OO0).
      rewrite <- (TransTypeIsGround_oo0 OO0).
      repeat dependent destruction e.
      apply IHM1.
    generalize (@FirstIsGround_oo0_castT (TransVars Nn) (TransVars (HOPart (GrVars (numG + numG2)))) tL T OO0).
    generalize (@FirstIsGround_oo0_castT (TransVars Nn) (TransVars (HOPart (GrVars (S (numG + numG2))))) tL T OO0).
    replace Ground with (TransType tL).
      repeat dependent destruction e.
      apply IHM2.
    rewrite (FirstIsGround_oo0 OO0).
    auto.
  unfold TransType.
  repeat rewrite (VarsCast_ApplyArgsForAllA_com (@HOPartEmpty_GrVars_castT _ _)); try rewrite HOPartEmpty_GrVars; auto.
  assert (forall Nn numG (K : term Nn (TransVars (HOPart (GrVars numG))) _), 
      type_cast HOPartEmpty_GrVars_castT (type_cast (TransType_HO_castT OO0) K) =
      type_cast (TransType_HO_castT OO0) (type_cast HOPartEmpty_GrVars_castT K)).
    clear; intros Nn numG.
    generalize (@HOPartEmpty_GrVars_castT Nn numG
        (Arr (AppendVarAux (TransType tL) (TailLen (ArgsOfType tL)) (ArgsOfType (TransType (Arr T)))))).
    generalize (@TransType_HO_castT Nn (TransVars (HOPart (GrVars numG))) tL T OO0).
    generalize (@TransType_HO_castT Nn [] tL T OO0).
    generalize (@HOPartEmpty_GrVars_castT Nn numG (TransType (Arr (tL :: T)))).
    rewrite HOPartEmpty_GrVars.
    rewrite TransType_HO; auto.
    repeat dependent destruction e.
    auto.
  repeat rewrite H.
  rewrite IHM1.
  apply ApplyArgsForAllA_eq.
  apply IHM2.
Qed.

Lemma Trans_ApplyArgs_com_oo0_Aux {Nn numG Vv} (V : Subset numG) (sub : substitution Nn (GrVars numG) Vv)
    (M : term Nn (GrVars numG) (Arr Vv)) (oo0 : OnlyOrder0Vars Vv = true) :
    type_cast HOPartEmpty_GrVars_castT (TransTerm Subset0 (type_cast TailIsAll_GrVars_castSet V) (ApplyArgs sub M)) =
    AppendTransExplicitSubst V (GetExpSub sub) (fun Ve => 
      type_cast HOPartEmpty_GrVars_castT (type_cast (TransTypeIsGround_oo0_castT oo0) (TransTerm
        (ExtractSubsetForFirst (TailLen Vv) Ve : Subset (TailLen (ArgsOfType (Arr _)))) 
        (type_cast TailIsAll_GrVars_castSet Ve)
        (AddVariablesToTerm _ M)))).
  dependent induction sub.
    simpl.
    rewrite AddNoVariables_void.
    generalize (@TransTypeIsGround_oo0_castT (TransVars Nn) (TransVars (HOPart (GrVars numG))) [] oo0).
    dependent destruction e.
    auto.
  simpl (ApplyArgs _ _).
  destruct t.
  destruct l; try easy.
  rewrite (IHsub _ oo0).
  unfold GetExpSub at 2.
  fold @GetExpSub.
  generalize (@eq_refl bool (OnlyOrder0Vars (Arr [] :: Vv_tail))).
  generalize (OnlyOrder0Vars (Arr [] :: Vv_tail)) at 2 3.
  destruct b; intro; try (exfalso; rewrite e in oo0; easy).
  assert (Subset (TailLen (Arr [] :: Vv_tail)) = Subset (S (TailLen Vv_tail))) as cast.
    rewrite ShiftInTail_oo0; auto.
  rewrite (AppendTransExplicitSubst_eq _ _ _ (fun Ve => type_cast HOPartEmpty_GrVars_castT
      (type_cast (TransTypeIsGround_oo0_castT oo0) (TransTerm 
        (type_cast (ShiftInTail_oo0_castSet e) (type_cast cast (ExtractSubsetForFirst (TailLen (Arr [] :: Vv_tail)) Ve)))
        (type_cast TailIsAll_GrVars_castSet Ve)
        (AddVariablesToTerm (TailLen (Arr [] :: Vv_tail)) M))))).
  all: cycle 1.
    intro; repeat f_equal.
    generalize cast.
    generalize (@ShiftInTail_oo0_castSet (Arr []) Vv_tail e).
    change (prod bool (Subset (TailLen Vv_tail))) with (Subset (S (TailLen Vv_tail))).
    rewrite <- (ShiftInTail_oo0 e).
    dependent destruction e0.
    dependent destruction cast0.
    auto.
  revert cast.
  generalize (@ShiftInTail_oo0_castS2 Nn (GrVars numG) (Arr []) Vv_tail e).
  rewrite (ShiftInTail_oo0 e).
  dependent destruction e0.
  dependent destruction cast.
  unfold AppendTransExplicitSubst.
  apply AppendTransExplicitSubst_eq.
  simpl AddVariablesToTerm.
  unfold TransTerm.
  fold @TransTerm.
  generalize (@eq_refl bool (OnlyOrder0Vars (Arr [] :: Vv_tail))).
  generalize (OnlyOrder0Vars (Arr [] :: Vv_tail)) at 2 3.
  destruct b; intro; try (exfalso; rewrite e in e0; easy).
  intro.
  rewrite type_cast_type_cast_is_id.
  rewrite VarsCast_Or_And_com; try rewrite HOPartEmpty_GrVars; auto.
  assert (forall Nn numG (K : term Nn (TransVars (HOPart (GrVars (TailLen Vv_tail + numG)))) _),
      type_cast HOPartEmpty_GrVars_castT (type_cast (TransTypeIsGround_oo0_castT e0) K) =
      type_cast (TransTypeIsGround_oo0_castT e0) (type_cast HOPartEmpty_GrVars_castT K)) as ch1.
    intro; intro.
    generalize (@HOPartEmpty_GrVars_castT Nn0 (TailLen Vv_tail + numG0) Ground).
    generalize (@TransTypeIsGround_oo0_castT Nn0 (TransVars (HOPart (GrVars (TailLen Vv_tail + numG0)))) (Arr [] :: Vv_tail) e0).
    generalize (@HOPartEmpty_GrVars_castT Nn0 (TailLen Vv_tail + numG0) (TransType (Arr (Arr [] :: Vv_tail)))).
    generalize (@TransTypeIsGround_oo0_castT Nn0 [] (Arr [] :: Vv_tail) e0).
    rewrite HOPartEmpty_GrVars.
    rewrite TransTypeIsGround_oo0; auto.
    repeat dependent destruction e1.
    auto.
  rewrite ch1.
  rewrite ch1.
  assert (forall Nn numG (K : term Nn (TransVars (HOPart (GrVars (S (TailLen Vv_tail) + numG)))) _),
      type_cast HOPartEmpty_GrVars_castT (type_cast (TransTypeIsGround_oo0_castT oo0) K) =
      type_cast (TransTypeIsGround_oo0_castT e0) (type_cast HOPartEmpty_GrVars_castT K)) as ch2.
    intro; intro.
    generalize (@HOPartEmpty_GrVars_castT Nn0 (S (TailLen Vv_tail) + numG0) Ground).
    generalize (@TransTypeIsGround_oo0_castT Nn0 (TransVars (HOPart (GrVars (S (TailLen Vv_tail) + numG0)))) 
        (Arr [] :: Vv_tail) oo0).
    generalize (@TransTypeIsGround_oo0_castT Nn0 [] (Arr [] :: Vv_tail) e0).
    generalize (@HOPartEmpty_GrVars_castT Nn0 (S (TailLen Vv_tail) + numG0) (TransType (Arr (Arr [] :: Vv_tail)))).
    rewrite HOPartEmpty_GrVars.
    rewrite TransTypeIsGround_oo0; auto.
    repeat dependent destruction e1.
    auto.
  rewrite ch2.
  rewrite ch2.
  clear.
  repeat f_equal.
      replace (type_cast (ShiftInTail_oo0_castSet e0) _)
          with (type_cast (ShiftInTail_oo0_castSet e) (false, ExtractSubsetForFirst (TailLen Vv_tail) V0));
      try apply type_cast_invariance.
      apply TransTerm_AddVariables_com.
    replace (type_cast (ShiftInTail_oo0_castSet e0) _)
        with (type_cast (ShiftInTail_oo0_castSet e) (true, ExtractSubsetForFirst (TailLen Vv_tail) V0));
    try apply type_cast_invariance.
    apply TransTerm_AddVariables_com.
  generalize (AddVariablesToTerm (TailLen Vv_tail) t0).
  generalize (type_cast TailIsAll_GrVars_castSet V0).
  intros.
  generalize (@FirstIsGround_oo0_castT (TransVars Nn) (TransVars (HOPart (GrVars (TailLen Vv_tail + numG)))) 
      (Arr []) Vv_tail e0).
  generalize (@FirstIsGround_oo0_castSet (Arr []) Vv_tail e0).
  repeat dependent destruction e1.
  auto.
Qed.

Lemma Trans_ApplyArgs_com_oo0 {Nn numG Vv} (V : Subset numG) (sub : substitution Nn (GrVars numG) Vv)
    (M : term Nn (GrVars numG) (Arr Vv)) : OnlyOrder0Vars Vv = true ->
    type_cast HOPartEmpty_GrVars_castT (TransTerm Subset0 (type_cast TailIsAll_GrVars_castSet V) (ApplyArgs sub M)) =
    AppendTransExplicitSubst V (GetExpSub sub) (fun Ve =>
      type_cast HOPartEmpty_GrVars_castT (ApplyArgs (TransSubst (type_cast TailIsAll_GrVars_castSet Ve) (GetHOSub sub))
        (type_cast TransType_is_TransVars_castT2 (TransTerm
          (ExtractSubsetForFirst (TailLen Vv) Ve : Subset (TailLen (ArgsOfType (Arr _))))
          (type_cast TailIsAll_GrVars_castSet Ve)
          (AddVariablesToTerm _ M))))).
  intro OO0.
  rewrite (Trans_ApplyArgs_com_oo0_Aux _ _ _ OO0).
  apply AppendTransExplicitSubst_eq.
  intro.
  f_equal.
  set (tM := TransTerm _ _ _).
  generalize (GetHOSub sub) as HO_sub.
  dependent destruction HO_sub.
    apply type_cast_invariance.
  unfold TransSubst.
  generalize (@eq_refl bool (OnlyOrder0Vars (t :: Vv_tail))).
  generalize (OnlyOrder0Vars (t :: Vv_tail)) at 2 3.
  destruct b; intro; try (exfalso; rewrite e in OO0; easy).
  generalize tM.
  generalize (TransVars Nn).
  generalize (TransVars (HOPart (GrVars (TailLen (t :: Vv_tail) + numG)))).
  intros Vv Nn2.
  generalize (@TransTypeIsGround_oo0_castT Nn2 Vv (t :: Vv_tail) OO0).
  generalize (@HOPartEmpty_oo0_castS Nn2 Vv (t :: Vv_tail) e).
  generalize (@TransType_is_TransVars_castT2 Nn2 Vv (Arr (t :: Vv_tail))).
  rewrite (TransTypeIsGround_oo0 OO0).
  change (ArgsOfType _ ) with (t:: Vv_tail).
  rewrite (HOPartEmpty_oo0 OO0).
  repeat dependent destruction e0.
  auto.
Qed.

Lemma ApplyArgsForAllA_AppendSubstForAllA_com Nn VvNew Vv_tail numG t_app (sub : substitution Nn VvNew Vv_tail)
    (R : Subset numG -> term Nn VvNew t_app) (M : term Nn VvNew (Arr (AppendVarAux t_app numG Vv_tail))) :
    ApplyArgs sub (ApplyArgsForAllA M R) = ApplyArgs (AppendSubstForAllA R sub) M.
  revert Vv_tail sub M.
  induction numG.
    auto.
  simpl.
  intros.
  rewrite IHnumG.
  rewrite IHnumG.
  auto.
Qed.

Lemma Trans_ApplyArgs_com {Nn numG Vv} (V : Subset numG) (sub : substitution Nn (GrVars numG) Vv)
    (M : term Nn (GrVars numG) (Arr Vv)) :
    type_cast HOPartEmpty_GrVars_castT (TransTerm Subset0 (type_cast TailIsAll_GrVars_castSet V) (ApplyArgs sub M)) =
    AppendTransExplicitSubst V (GetExpSub sub) (fun Ve =>
      type_cast HOPartEmpty_GrVars_castT (ApplyArgs (TransSubst (type_cast TailIsAll_GrVars_castSet Ve) (GetHOSub sub))
        (type_cast TransType_is_TransVars_castT2 (TransTerm
          (ExtractSubsetForFirst (TailLen Vv) Ve : Subset (TailLen (ArgsOfType (Arr _))))
          (type_cast TailIsAll_GrVars_castSet Ve)
          (AddVariablesToTerm _ M))))).
  dependent induction sub.
    apply Trans_ApplyArgs_com_oo0.
    auto.
  case_eq (OnlyOrder0Vars (t :: Vv_tail)).
    apply Trans_ApplyArgs_com_oo0.
  intro OO0.
  simpl (TransTerm Subset0 _ _).
  rewrite IHsub.
  unfold GetExpSub.
  fold @GetExpSub.
  generalize (GetExpSub sub); intro exp_sub.
  unfold GetHOSub.
  fold @GetHOSub.
  generalize (GetHOSub sub); intro HO_sub.
  generalize (@eq_refl bool (OnlyOrder0Vars (t :: Vv_tail))).
  generalize (OnlyOrder0Vars (t :: Vv_tail)) at 2 3 7.
  destruct b; intro; try (exfalso; rewrite e in OO0; easy).
  assert (Subset (TailLen Vv_tail + numG) = Subset (TailLen (t :: Vv_tail) + numG)) as cast.
    rewrite SkipInTail_HO; auto.
  assert (forall F, AppendTransExplicitSubst V (type_cast (SkipInTail_HO_castS2 e) exp_sub) (fun Ve => F Ve) =
      AppendTransExplicitSubst V exp_sub (fun Ve => F (type_cast cast Ve))) as ch.
    revert cast.
    generalize (@SkipInTail_HO_castS2 Nn (GrVars numG) t Vv_tail e).
    rewrite SkipInTail_HO; auto.
    dependent destruction e0.
    dependent destruction cast.
    auto.
  rewrite ch.
  apply AppendTransExplicitSubst_eq.
  intros.
  clear.
  assert (forall LLL (eq : LLL = TailLen Vv_tail) e0 e1 cast ss2, 
      type_cast HOPartEmpty_GrVars_castT
        (ApplyArgs (TransSubst (type_cast TailIsAll_GrVars_castSet (type_cast cast V0)) (type_cast e1 ss2))
          (type_cast TransType_is_TransVars_castT2
            (TransTerm (type_cast (SkipInTail_HO_castSet e) (type_cast e0 (ExtractSubsetForFirst LLL (type_cast cast V0))))
              (type_cast TailIsAll_GrVars_castSet (type_cast cast V0)) (AddVariablesToTerm LLL M)))) =
      type_cast HOPartEmpty_GrVars_castT
        (ApplyArgs (TransSubst (type_cast TailIsAll_GrVars_castSet V0) ss2)
          (type_cast TransType_is_TransVars_castT2
            (TransTerm (type_cast (SkipInTail_HO_castSet e) (ExtractSubsetForFirst (TailLen Vv_tail) V0)) 
              (type_cast TailIsAll_GrVars_castSet V0) (AddVariablesToTerm (TailLen Vv_tail) M))))) as ch.
     intros LLL eq.
     rewrite eq.
     dependent destruction e0.
     dependent destruction e1.
     dependent destruction cast0.
     auto.
  assert (Subset (TailLen (t :: Vv_tail)) = Subset (TailLen Vv_tail)) as cast2.
    rewrite SkipInTail_HO; auto.
  assert (ExtractSubsetForFirst (TailLen (t :: Vv_tail)) (type_cast cast V0) =
      type_cast (SkipInTail_HO_castSet e) (type_cast cast2 
        (ExtractSubsetForFirst (TailLen (t :: Vv_tail)) (type_cast cast V0)))) as ch2.
    generalize (ExtractSubsetForFirst (TailLen (t :: Vv_tail)) (type_cast cast V0)).
    revert cast2.
    generalize (@SkipInTail_HO_castSet t Vv_tail e).
    rewrite <- (SkipInTail_HO e).
    dependent destruction e0.
    dependent destruction cast2.
    auto.
  rewrite ch2.
  rewrite ch; try apply SkipInTail_HO; auto.
  f_equal.
  clear.
  unfold TransSubst.
  fold @TransSubst.
  generalize (@eq_refl bool (OnlyOrder0Vars (t :: Vv_tail))).
  generalize (OnlyOrder0Vars (t :: Vv_tail)) at 2 3.
  destruct b; intro; try (exfalso; rewrite e in e0; easy).
  simpl (AddVariablesToTerm _ _).
  unfold TransTerm at 1.
  generalize (@eq_refl bool (OnlyOrder0Vars (t :: Vv_tail))).
  generalize (OnlyOrder0Vars (t :: Vv_tail)) at 2 3.
  destruct b; intro; try (exfalso; rewrite e in e1; easy).
  fold @TransTerm.
  generalize (TransSubst (type_cast TailIsAll_GrVars_castSet V0) HO_sub); intro sub.
  generalize (fun A => TransTerm A (type_cast TailIsAll_GrVars_castSet V0) (AddVariablesToTerm (TailLen Vv_tail) t0)).
  intro R.
  replace (TransTerm (type_cast (SkipInTail_HO_castSet e1) (ExtractSubsetForFirst (TailLen Vv_tail) V0))
         (type_cast TailIsAll_GrVars_castSet V0) (AddVariablesToTerm (TailLen Vv_tail) M)) with
      (TransTerm (type_cast (SkipInTail_HO_castSet e) (ExtractSubsetForFirst (TailLen Vv_tail) V0))
         (type_cast TailIsAll_GrVars_castSet V0) (AddVariablesToTerm (TailLen Vv_tail) M)).
  all: cycle 1.
    f_equal.
    apply type_cast_invariance.
  generalize (TransTerm (type_cast (SkipInTail_HO_castSet e) (ExtractSubsetForFirst (TailLen Vv_tail) V0))
      (type_cast TailIsAll_GrVars_castSet V0) (AddVariablesToTerm (TailLen Vv_tail) M)); intro K.
  generalize (@TransType_is_TransVars_castT2 (TransVars Nn) (TransVars (HOPart (GrVars (TailLen Vv_tail + numG))))
      (Arr (t :: Vv_tail))).
  generalize (@ShiftInHO_HO_castS (TransVars Nn) (TransVars (HOPart (GrVars (TailLen Vv_tail + numG)))) t Vv_tail e0).
  generalize (@TransType_HO_castT (TransVars Nn) (TransVars (HOPart (GrVars (TailLen Vv_tail + numG)))) t Vv_tail e1).
  generalize (@TransType_is_TransVars_castT2 (TransVars Nn) (TransVars (HOPart (GrVars (TailLen Vv_tail + numG)))) (Arr Vv_tail)).
  revert K sub R.
  generalize (TransVars Nn); intro Nn2.
  generalize (TransVars (HOPart (GrVars (TailLen Vv_tail + numG)))); intro Vv.
  change (ArgsOfType (Arr Vv_tail)) with Vv_tail.
  rewrite TransType_is_TransVars.
  change (ArgsOfType (Arr (t :: Vv_tail))) with (t :: Vv_tail).
  rewrite (ShiftInHO_HO e).
  change (TransType (Arr Vv_tail)) with (Arr (ArgsOfType (TransType (Arr Vv_tail)))).
  rewrite (TransType_is_TransVars (t := Arr Vv_tail)).
  repeat dependent destruction e2.
  apply ApplyArgsForAllA_AppendSubstForAllA_com.
Qed.

Lemma OrReducesAsOr {Gg Vv chldrn NNN} : Reduces Gg (Or _ Vv chldrn) NNN -> exists N, NNN = [N] /\ In N chldrn.
  intro.
  dependent destruction H; eauto.
  specialize (ApplyArgs_is_App_or_Nontermi _ _ _ sub (Nontermi _ _ _ X)) as AA.
  destruct AA.
      right.
      eauto.
    rewrite x in H.
    destruct H.
    destruct H.
    destruct H.
    simplify_eq H.
  rewrite x in H.
  destruct H.
  simplify_eq H.
Qed.

Lemma AndReducesAsAnd {Gg Vv chldrn NNN} : Reduces Gg (And _ Vv chldrn) NNN -> NNN = chldrn.
  intro.
  dependent destruction H; auto.
  specialize (ApplyArgs_is_App_or_Nontermi _ _ _ sub (Nontermi _ _ _ X)) as AA.
  destruct AA.
      right.
      eauto.
    rewrite x in H.
    destruct H.
    destruct H.
    destruct H.
    simplify_eq H.
  rewrite x in H.
  destruct H.
  simplify_eq H.
Qed.

Lemma ProducesFiniteTree_AppendTransExplicitSubst_com {Gg numGNew numG} (V : Subset numGNew) 
    (exp_sub : substitution (NontermsOfGrammar Gg) (GrVars numGNew) (GrVars numG))
    (M1 M2 : Subset (numG + numGNew) -> term (TransVars (NontermsOfGrammar Gg)) [] Ground) :
    ProducesFiniteTree _ (type_cast TransTerm_OK_for_TransGrammar (AppendTransExplicitSubst V exp_sub M2)) ->
    (forall V, ProducesFiniteTree _ (type_cast TransTerm_OK_for_TransGrammar (M2 V)) ->
      ProducesFiniteTree _ (type_cast TransTerm_OK_for_TransGrammar (M1 V))) ->
    ProducesFiniteTree _ (type_cast TransTerm_OK_for_TransGrammar (AppendTransExplicitSubst V exp_sub M1)).
  intros.
  induction numG.
    apply H0.
    auto.
  dependent destruction exp_sub.
  simpl.
  eapply IHnumG.
    eauto.
  clear - H0.
  intros.
  revert H H0.
  generalize (@TransTerm_OK_for_TransGrammar Gg).
  destruct Gg.
  dependent destruction e0.
  clear x.
  intros.
  dependent destruction H.
  specialize (OrReducesAsOr H).
  clear H.
  intro.
  destruct H.
  destruct H.
  dependent destruction H.
  destruct H2.
    dependent destruction H.
    eapply PFTReduces.
      apply ReducesOr.
      left.
      eauto.
    intros.
    destruct H; try easy.
    dependent destruction H.
    apply H1.
    apply H0.
    left.
    auto.
  eapply PFTReduces.
    apply ReducesOr.
    right; left.
    eauto.
  intros.
  destruct H2; try easy.
  dependent destruction H2.
  destruct H; try easy.
  assert (In x [x]).
    left.
    auto.
  specialize (H0 x H2); clear H2.
  dependent destruction H.
  eapply PFTReduces.
    apply ReducesAnd.
  intros.
  dependent destruction H0.
  specialize (AndReducesAsAnd H); clear H.
  intro.
  dependent destruction H.
  destruct H2.
    dependent destruction H.
    apply H1.
    apply H0.
    left.
    auto.
  destruct H; try easy.
  dependent destruction H.
  apply H0.
  right.
  left.
  auto.
Qed.

Lemma ShiftVarAux_AppendRulesForAllA_com NnAll Nn numG t_app t (Rr : rules_ind NnAll Nn)
    (R : Subset numG -> rule NnAll t_app) (X : ElementOfList t Nn) :
    FindInRules (AppendRulesForAllA R Rr) (ShiftVarAux t_app numG X) = FindInRules Rr X.
  revert Nn X Rr.
  induction numG.
    auto.
  intros.
  simpl.
  rewrite IHnumG.
  apply IHnumG.
Qed.

Lemma FindNewVar_AppendRulesForAllA_com {NnAll Nn t} (A : Subset (TailLen (ArgsOfType t))) (Rr : rules_ind NnAll (TransVars Nn))
    (R : Subset (TailLen (ArgsOfType t)) -> rule NnAll (TransType t)) :
    FindInRules (AppendRulesForAllA R Rr) (FindNewVar A (FirstEl t Nn)) = R A.
  unfold FindNewVar.
  revert Rr A R.
  generalize (TransVars Nn).
  generalize (TailLen (ArgsOfType t)) as numG.
  induction numG; intros.
    destruct A.
    auto.
  destruct A.
  destruct b; simpl.
    rewrite ShiftVarAux_AppendRulesForAllA_com.
    apply IHnumG.
  apply IHnumG.
Qed.

Lemma Trans_FindInRules_com NnAll Nn t (Rr : rules_ind NnAll Nn) (A : Subset (TailLen (ArgsOfType t))) (X : ElementOfList t Nn) :
    type_cast TransType_is_TransVars_castT (TransTerm Subset0 A (TermOfRule (FindInRules Rr X))) =
    TermOfRule (FindInRules (TransRules Rr) (FindNewVar A X)).
  induction Rr.
    easy.
  simpl.
  dependent destruction X.
    rewrite FindNewVar_AppendRulesForAllA_com.
    destruct r.
    auto.
  rewrite IHRr.
  simpl.
  rewrite ShiftVarAux_AppendRulesForAllA_com.
  auto.
Qed.

Lemma ExtReduces2TransReduces {Gg numG} (V : Subset numG) (eM : ext_term _ numG) eNNN :
    ExtReduces Gg _ eM eNNN ->
    (forall eN, In eN eNNN -> ProducesFiniteTree _ (type_cast TransTerm_OK_for_TransGrammar (TransExtTerm V eN))) ->
    ProducesFiniteTree _ (type_cast TransTerm_OK_for_TransGrammar (TransExtTerm V eM)).
  intros.
  induction H.
            (* Nonterminal *)
            simpl.
            rewrite Trans_ApplyArgs_com.
            specialize (H0 (ExtSubstitute sub (TermOfRule (FindInRules (RulesOfGrammar Gg) X)))).
            rewrite Trans_ExtSubstitute_com in H0.
            eapply ProducesFiniteTree_AppendTransExplicitSubst_com.
              apply H0.
              left.
              auto.
            clear.
            intros.
            apply (PFTReduces _ _ [type_cast TransTerm_OK_for_TransGrammar
                ((fun Ve => type_cast HOPartEmpty_GrVars_castT
                  (Substitute (TransSubst (type_cast TailIsAll_GrVars_castSet Ve) (GetHOSub sub))
                    (TransTerm Subset0 (ExtractSubsetForFirst (TailLen (ArgsOfType t)) Ve)
                      (TermOfRule (FindInRules (RulesOfGrammar Gg) X))))) V)]).
              all: swap 1 2.
              intros.
              destruct H0.
                rewrite <- H0.
                auto.
              easy.
            clear.
            generalize (TransSubst (type_cast TailIsAll_GrVars_castSet V) (GetHOSub sub)); clear sub; intro sub.
            simpl AddVariablesToTerm.
            unfold TransTerm at 1.
            change (TransType Ground) with Ground.
            generalize (@HOPartEmpty_GrVars_castT (TransVars (NontermsOfGrammar Gg)) (TailLen (ArgsOfType t) + numG) Ground).
            revert sub.
            rewrite HOPartEmpty_GrVars.
            dependent destruction e.
            assert(forall Nn t t2, term Nn (ArgsOfType (TransType t)) t2 = term Nn (TransVars (HOPart (ArgsOfType t))) t2) as cast.
              intros.
              rewrite TransType_is_TransVars.
              auto.
            replace (TransTerm _ _ _) with (type_cast (cast _ _ _) (type_cast TransType_is_TransVars_castT (TransTerm
                Subset0 (ExtractSubsetForFirst (TailLen (ArgsOfType t)) V) (TermOfRule (FindInRules (RulesOfGrammar Gg) X)))));
              try apply type_cast_type_cast_is_id.
            destruct t.
            rewrite Trans_FindInRules_com.
            generalize (@TransType_is_TransVars_castT2 (TransVars (NontermsOfGrammar Gg)) (TransVars [])
                (Arr (ArgsOfType (Arr l)))).
            generalize (cast (TransVars (NontermsOfGrammar Gg)) (Arr l) (TransType Ground)).
            revert sub.
            repeat change (ArgsOfType (Arr l)) with l.
            change (TransVars (HOPart l)) with (ArgsOfType (Arr (TransVars (HOPart (ArgsOfType (Arr l)))))).
            rewrite <- (TransType_is_TransVars (t := Arr l)).
            generalize (@TransTerm_OK_for_TransGrammar Gg).
            destruct Gg.
            repeat dependent destruction e0.
            apply ReducesNontermi.
          (* Or *)
          apply (PFTReduces _ _ [type_cast TransTerm_OK_for_TransGrammar
              (type_cast HOPartEmpty_GrVars_castT(TransTerm Subset0
                (type_cast TailIsAll_GrVars_castSet V) K))]).
            simpl.
            change (term _ (TransVars _) _) with
                (term (TransVars (NontermsOfGrammar Gg)) (TransVars (HOPart (GrVars numG))) (TransType Ground)).
            assert (In (TransTerm Subset0 (type_cast TailIsAll_GrVars_castSet V) K)
                (map (TransTerm Subset0 (type_cast TailIsAll_GrVars_castSet V)) chldrn)).
              apply in_map.
              auto.
            revert H1.
            generalize (TransTerm Subset0 (type_cast TailIsAll_GrVars_castSet V) K) as trK.
            generalize (map (TransTerm Subset0 (type_cast TailIsAll_GrVars_castSet V)) chldrn).
            generalize (HOPartEmpty_GrVars_castT (Nn := TransVars (NontermsOfGrammar Gg)) (numG := numG) (t := Arr [])).
            assert (TransVars (HOPart (GrVars numG)) = []).
              rewrite HOPartEmpty_GrVars; auto.
            generalize H1.
            generalize (TransTerm_OK_for_TransGrammar (Gg := Gg)).
            destruct Gg.
            dependent destruction e0.
            generalize (TransVars (HOPart (GrVars numG))).
            destruct l.
              dependent destruction e0.
              intros.
              apply ReducesOr.
              auto.
            simplify_eq 1.
          specialize (H0 (StdTerm _ _ K)).
          intros.
          destruct H1.
            rewrite <- H1.
            apply H0.
            left.
            auto.
          easy.
        (* And *)
        apply (PFTReduces _ _ (map (fun trK => type_cast TransTerm_OK_for_TransGrammar
            (type_cast HOPartEmpty_GrVars_castT trK)) (map (TransTerm Subset0
              (type_cast TailIsAll_GrVars_castSet V)) chldrn))).
          simpl.
          change (term _ (TransVars _) _) with
              (term (TransVars (NontermsOfGrammar Gg)) (TransVars (HOPart (GrVars numG))) (TransType Ground)).
          generalize (map (TransTerm Subset0 (type_cast TailIsAll_GrVars_castSet V)) chldrn).
          change (Arr []) with Ground.
          generalize (HOPartEmpty_GrVars_castT (Nn := TransVars (NontermsOfGrammar Gg)) (numG := numG) (t := Ground)).
          assert (TransVars (HOPart (GrVars numG)) = []).
            rewrite HOPartEmpty_GrVars; auto.
          generalize H.
          generalize (TransTerm_OK_for_TransGrammar (Gg := Gg)).
          destruct Gg.
          dependent destruction e0.
          generalize (TransVars (HOPart (GrVars numG))).
          destruct l.
            dependent destruction e0.
            simpl.
            intro.
            rewrite map_id.
            change (TransVars Nn) with (NontermsOfGrammar (Grammar _
                (FindNewVar Subset0 e) (TransRules r))).
            apply ReducesAnd.
          simplify_eq 1.
        intros.
        rewrite map_map in H.
        apply in_map_iff in H.
        destruct H.
        destruct H.
        rewrite <- H.
        specialize (H0 (StdTerm _ _ x)).
        apply H0.
        apply in_map.
        auto.
      (* Subst *)
      revert H0.
      generalize (TransTerm_OK_for_TransGrammar (Gg := Gg)).
      destruct Gg.
      dependent destruction e0.
      intros.
      eapply PFTReduces.
        eapply ReducesOr.
        right.
        left. 
        auto.
      intros.
      destruct H; try easy.
      rewrite <- H.
      eapply PFTReduces.
        apply ReducesAnd.
      intros.
      destruct H1.
        rewrite <- H1.
        unfold TransTerm.
        change (RemainsOrTail _) with (RemainsOrTail (FirstEl Ground (GrVars numG))).
        specialize (First_is_First numG V true) as ?.
        destruct H2.
        destruct H2.
        rewrite H2.
        change (BelongsToSubset _ _) with 
            (BelongsToSubset x0 (type_cast TailIsAll_GrVars_castSet ((true, V):  Subset (S _)))).
        rewrite H3.
        change (OnlyGround_GrVars_castT x0) with 
            (OnlyGround_GrVars_castT (Nn := TransVars Nn) (Vv := TransVars (HOPart (GrVars (S numG)))) x0).
        generalize (OnlyGround_GrVars_castT (Nn := TransVars Nn) (Vv := TransVars (HOPart (GrVars (S numG)))) x0).
        dependent destruction e0.
        generalize (@HOPartEmpty_GrVars_castT (TransVars (NontermsOfGrammar (Grammar Nn e r))) (S numG) (TransType Ground)).
        assert (TransVars (HOPart (GrVars (S numG))) = []).
          rewrite HOPartEmpty_GrVars; auto.
        generalize H4.
        generalize (TransVars (HOPart (GrVars (S numG)))).
        destruct l.
          dependent destruction e0.
          eapply (PFTReduces _ _ []).
            apply ReducesAnd.
          destruct 1.
        simplify_eq 1.
      destruct H1; try easy.
      rewrite <- H1.
      specialize (H0 (StdTerm _ _ R)).
      apply H0.
      left.
      auto.
    (* Simpl *)
    revert H0.
    generalize (TransTerm_OK_for_TransGrammar (Gg := Gg)).
    destruct Gg.
    dependent destruction e0.
    intros.
    eapply PFTReduces.
      eapply ReducesOr.
      left.
      auto.
    intros.
    destruct H; try easy.
    rewrite <- H.
    rewrite TransNextVar.
    specialize (H0 (StdTerm _ _ (Var _ _ _ x0))).
    apply H0.
    left.
    auto.
  (* Ind *)
  revert H0 IHExtReduces.
  simpl.
  generalize (TransTerm_OK_for_TransGrammar (Gg := Gg)).
  destruct Gg.
  dependent destruction e0.
  intros.
  assert (
      (forall eN, In eN eNNN -> ProducesFiniteTree _ (TransExtTerm ((true, V) : Subset (S _)) eN :
        term (NontermsOfGrammar (TransGrammar (Grammar Nn e r))) _ _)) /\
      ((forall eN, In eN eNNN -> ProducesFiniteTree _ (TransExtTerm ((false, V) : Subset (S _)) eN :
        term (NontermsOfGrammar (TransGrammar (Grammar Nn e r))) _ _)) \/
      ProducesFiniteTree _ (type_cast HOPartEmpty_GrVars_castT 
        (TransTerm Subset0 (type_cast TailIsAll_GrVars_castSet V) R) : 
          term (NontermsOfGrammar (TransGrammar (Grammar Nn e r))) _ _))).
    revert H0.
    clear.
    induction eNNN.
      split.
        easy.
      left.
      easy.
    intros.
    destruct IHeNNN.
      intros.
      apply H0.
      right.
      auto.
    assert (In (ExplicitSubst _ _ a R) (map (fun eN => ExplicitSubst _ _ eN R) (a :: eNNN))).
      left. 
      auto.
    specialize (H0 (ExplicitSubst _ _ a R) H2) as H3.
    inversion H3.
    specialize (OrReducesAsOr H4).
    fold @TransExtTerm.
    clear H2 H3 H4 H6 M.
    intro.
    destruct H2 as (N & H2).
    destruct H2.
    dependent destruction H2.
    assert (In N [N]).
      left.
      auto.
    specialize (H5 N H2).
    clear - H H1 H5 H3.
    destruct H3.
      dependent destruction H0.
      assert (ProducesFiniteTree (TransGrammar (Grammar Nn e r)) (TransExtTerm ((true, V) : Subset (S _)) a)).
        specialize (PFT_false_implies_true (Grammar Nn e r)).
        generalize (TransTerm_OK_for_TransGrammar (Gg := (Grammar Nn e r))).
        dependent destruction e0.
        intro.
        apply H0.
        apply H5.
      split.
        intros.
        destruct H2; auto.
        dependent destruction H2.
        auto.
      destruct H1.
        left.
        intros.
        destruct H2; auto.
        dependent destruction H2.
        auto.
      right.
      auto.
    destruct H0; try easy.
    dependent destruction H0.
    dependent destruction H5.
    specialize (AndReducesAsAnd H0); clear H0.
    intro.
    dependent destruction H0.
    split.
      intros.
      destruct H0; auto.
      dependent destruction H0.
      apply H2.
      left.
      auto.
    right.
    apply H2.
    right.
    left.
    auto.
  destruct H1.
  destruct H2.
    eapply PFTReduces.
      eapply ReducesOr.
      left.
      eauto.
    intros.
    destruct H3; try easy.
    dependent destruction H3.
    apply IHExtReduces.
    auto.
  eapply PFTReduces.
    eapply ReducesOr.
    right.
    left.
    eauto.
  intros.
  destruct H3; try easy.
  dependent destruction H3.
  eapply PFTReduces.
    eapply ReducesAnd.
  intros.
  destruct H3.
    dependent destruction H3.
    apply IHExtReduces.
    auto.
  destruct H3; try easy.
  dependent destruction H3.
  auto.
Qed.

Lemma PFT_Ext2Trans Gg eM : ExtProducesFiniteTree Gg eM ->
    ProducesFiniteTree (TransGrammar Gg) (type_cast TransTerm_OK_for_TransGrammar (TransExtTerm Subset0 eM)).
  induction 1.
  apply (ExtReduces2TransReduces _ _ eNNN); auto.
Qed.

Section ProducesFiniteTreeSteps.
  Variable Gg : grammar.
  Let Nn := NontermsOfGrammar Gg.
  Inductive ProducesFiniteTreeSteps : nat -> term Nn [] Ground -> Prop := 
    | PFTSReduces : forall M nnn NNN, Reduces Gg M NNN -> Forall2 (fun n N => ProducesFiniteTreeSteps n N) nnn NNN
        -> ProducesFiniteTreeSteps (S (fold_right add 0 nnn)) M.
End ProducesFiniteTreeSteps.

Lemma PFT2PFTSteps {Gg M} : ProducesFiniteTree Gg M -> exists n, ProducesFiniteTreeSteps Gg n M.
  induction 1.
  enough (exists nnn, Forall2 (fun n N => ProducesFiniteTreeSteps Gg n N) nnn NNN).
    destruct H2 as (nnn & H2).
    exists (S (fold_right add 0 nnn)).
    eapply PFTSReduces; eauto.
  clear - H1.
  induction NNN.
    exists [].
    easy.
  destruct IHNNN.
    intros.
    apply H1.
    right.
    auto.
  specialize (H1 a).
  destruct H1.
    left.
    auto.
  exists (x0 :: x).
  apply Forall2_cons; auto.
Qed.

Lemma Var_PFTS_iff_in_set {Nn X0 Rr n numG} {V : Subset numG} {x} :
    ProducesFiniteTreeSteps (TransGrammar (Grammar Nn X0 Rr)) n (TransExtTerm V (StdTerm _ numG (Var _ _ Ground x))) <->
      BelongsToSubset x V = true /\ n = 1.
  unfold TransExtTerm.
  unfold TransTerm.
  assert (OnlyOrder0Vars (GrVars numG) = true) as oo0.
    apply OnlyOrder0Vars_GrVars.
  rewrite (RemainsOrTail_oo0 _ oo0).
  set (cast1 := OnlyGround_GrVars_castT _).
  set (cast2 := HOPartEmpty_GrVars_castT).
  generalize cast1 cast2; clear cast1 cast2.
  dependent destruction cast1.
  rewrite HOPartEmpty_GrVars.
  dependent destruction cast2.
  set (cast1 := TailIsAll_oo0_castV oo0).
  set (cast2 := TailIsAll_GrVars_castSet).
  generalize cast1 cast2; clear cast1 cast2.
  rewrite TailIsAll_GrVars.
  dependent destruction cast1.
  dependent destruction cast2.
  simpl (type_cast _ _).
  clear.
  split; intro.
    dependent destruction H.
    revert H.
    case_eq (BelongsToSubset x0 V).
      intros.
      specialize (AndReducesAsAnd H1) as ?.
      dependent destruction H2.
      dependent destruction H0.
      auto.
    intros.
    specialize (OrReducesAsOr H1) as ?.
    destruct H2.
    easy.
  destruct H.
  dependent destruction H0.
  rewrite H.
  change 1 with (S (fold_right add 0 [])).
  eapply PFTSReduces.
    apply ReducesAnd.
  auto.
Qed.

Lemma AppSeqEndsWithNonterminal {Nn numG t1 T} (sub : substitution Nn (GrVars numG) (t1 :: T))
    (M : term Nn (GrVars numG) (Arr (t1 :: T))) :
    exists t sub2 X, ApplyArgs sub M = ApplyArgs sub2 (Nontermi _ _ (Arr (ArgsOfType t)) X).
  dependent induction M.
      exists (Arr (t1 :: T)).
      eauto.
    enough (Arr (t1 :: T) = Ground).
      easy.
    eapply OnlyGround_GrVars.
    eauto.
  replace (ApplyArgs sub (App _ _ _ _ M1 M2)) with (ApplyArgs (ConsSubst _ _ _ _ M2 sub) M1); auto.
Qed.

Lemma FormsOfTerm {Nn numG} (M : term Nn (GrVars numG) Ground) : IsVariable M \/ (exists chldrn, M = Or _ _ chldrn) \/
    (exists chldrn, M = And _ _ chldrn) \/ (exists t sub X, M = ApplyArgs sub (Nontermi _ _ (Arr (ArgsOfType t)) X)).
  dependent destruction M.
          right.
          right.
          right.
          exists Ground.
          exists (EmptySubst _ _).
          exists e.
          auto.
        left.
        easy.
      right.
      right.
      left.
      eauto.
    right.
    left.
    eauto.
  right.
  right.
  right.
  replace (App _ _ _ _ M1 M2) with (ApplyArgs (ConsSubst _ _ _ _ M2 (EmptySubst _ _)) M1); auto.
  apply AppSeqEndsWithNonterminal.
Qed.

Lemma ProducesFiniteTreeSteps_AppendTransExplicitSubst_com {Nn X0 Rr numGNew numG} (V : Subset numGNew)
    (exp_sub : substitution Nn (GrVars numGNew) (GrVars numG))
    (M1 M2 : Subset (numG + numGNew) -> term (TransVars Nn) [] Ground) n :
    ProducesFiniteTreeSteps (TransGrammar (Grammar Nn X0 Rr)) n (AppendTransExplicitSubst V exp_sub M1) ->
    (forall V j, ProducesFiniteTreeSteps (TransGrammar (Grammar Nn X0 Rr)) j (M1 V) ->
      exists i, i < j /\ ProducesFiniteTreeSteps (TransGrammar (Grammar Nn X0 Rr)) i (M2 V)) ->
    exists m, m < n /\ ProducesFiniteTreeSteps (TransGrammar (Grammar Nn X0 Rr)) m (AppendTransExplicitSubst V exp_sub M2).
  intros.
  induction numG.
    apply H0.
    auto.
  dependent destruction exp_sub.
  simpl.
  eapply IHnumG.
    eauto.
  clear - H0.
  intros.
  dependent destruction H.
  specialize (OrReducesAsOr H).
  clear H.
  intro.
  destruct H.
  destruct H.
  dependent destruction H.
  destruct H2.
    dependent destruction H.
    repeat dependent destruction H1.
    clear x.
    specialize (H0 _ _ H).
    clear H.
    destruct H0 as (i & ?).
    destruct H.
    exists (S (fold_right add 0 [i])).
    split.
      simpl.
      omega.
    eapply PFTSReduces; eauto.
    apply ReducesOr.
    left.
    eauto.
  destruct H; try easy.
  dependent destruction H.
  repeat dependent destruction H1.
  clear x.
  dependent destruction H.
  specialize (AndReducesAsAnd H).
  clear H.
  intro.
  dependent destruction H.
  dependent destruction H1.
  dependent destruction H1.
  dependent destruction H2.
  clear x.
  specialize (H0 _ _ H).
  clear H.
  destruct H0 as (i & ?).
  destruct H.
  exists (S (fold_right add 0 [S (fold_right add 0 [i; x0])])).
  split.
    simpl.
    omega.
  eapply PFTSReduces.
    apply ReducesOr.
    right; left.
    eauto.
  apply Forall2_cons; auto.
  eapply PFTSReduces; eauto.
  apply ReducesAnd.
Qed.

Fixpoint HeadType {Nn Vv t} (M : term Nn Vv t) : type :=
  match M with
  | App _ _ _ _ K L => HeadType K
  | _ => t
  end.

Lemma AppPreservesHead {Nn Vv T} sub (M : term Nn Vv (Arr T)) : HeadType (ApplyArgs sub M) = HeadType M.
  dependent induction sub.
    auto.
  simpl.
  rewrite IHsub.
  auto.
Qed.

Lemma AppUnique {Nn Vv T sub1 sub2} {M1 M2 : term Nn Vv (Arr T)} : ApplyArgs sub1 M1 = ApplyArgs sub2 M2 ->
    sub1 = sub2 /\ M1 = M2.
  induction T.
    dependent destruction sub1.
    dependent destruction sub2.
    auto.
  dependent destruction sub1.
  dependent destruction sub2.
  simpl.
  intro.
  specialize (IHT _ _ _ _ H).
  destruct IHT.
  dependent destruction H1.
  auto.
Qed.

Lemma AppReducesAsApp {Gg Vv T sub X NNN} : Reduces Gg (ApplyArgs sub (Nontermi _ Vv (Arr T) X)) NNN ->
    NNN = [Substitute sub (TermOfRule (FindInRules (RulesOfGrammar Gg) X))].
  intro.
  specialize (ApplyArgs_is_App_or_Nontermi _ _ _ sub (Nontermi _ _ _ X)) as AA.
  dependent destruction H;
    try (try clear H;
      destruct AA as [H | H];
      try (right; eauto);
      destruct H;
      try (destruct H;
      destruct H);
      rewrite H in x;
      easy).
  clear AA.
  specialize (AppPreservesHead sub (Nontermi _ _ _ X)) as Head1.
  specialize (AppPreservesHead sub0 (Nontermi _ _ _ X0)) as Head2.
  simpl in *.
  rewrite x in Head2.
  rewrite Head1 in Head2.
  dependent destruction Head2.
  specialize (AppUnique x) as ?.
  destruct H.
  dependent destruction H.
  dependent destruction H0.
  auto.
Qed.

Lemma TransReduces2ExtReduces4std Nn X0 Rr numG (V : Subset numG) (M : term _ (GrVars numG) Ground) n :
    ProducesFiniteTreeSteps (TransGrammar (Grammar Nn X0 Rr)) n
      (type_cast HOPartEmpty_GrVars_castT (TransTerm Subset0 (type_cast TailIsAll_GrVars_castSet V) M)) ->
    IsVariable M \/ exists eNNN, ExtReduces (Grammar Nn X0 Rr) _ (StdTerm _ _ M) eNNN /\
      (forall eN, In eN eNNN -> exists m, m < n /\
        ProducesFiniteTreeSteps (TransGrammar (Grammar Nn X0 Rr)) m (TransExtTerm V eN)).
  intro.
  remember H as PFTOrig; clear HeqPFTOrig.
  dependent destruction H.
  assert (term (TransVars (NontermsOfGrammar (Grammar Nn X0 Rr))) [] (TransType Ground) =
      term (TransVars (NontermsOfGrammar (Grammar Nn X0 Rr))) (TransVars (HOPart (GrVars numG))) (TransType Ground)) as cast.
    rewrite HOPartEmpty_GrVars.
    auto.
  assert (map (type_cast HOPartEmpty_GrVars_castT) (map (type_cast cast) NNN) = NNN).
    rewrite map_map.
    rewrite <- map_id.
    apply map_ext.
    intro.
    rewrite type_cast_type_cast_is_id.
    auto.
  revert H0 H.
  rewrite <- H1.
  generalize (map (type_cast cast) NNN); clear NNN H1 cast; intro NNN.
  intros.
  assert (Reduces (TransGrammar (Grammar Nn X0 Rr)) (TransTerm Subset0 (type_cast TailIsAll_GrVars_castSet V) M) NNN).
    revert H.
    simpl TransVars.
    generalize (@HOPartEmpty_GrVars_castT (TransVars Nn) numG (TransType Ground)).
    replace [] with (TransVars (HOPart (GrVars numG))).
      dependent destruction e.
      rewrite map_id.
      auto.
    rewrite HOPartEmpty_GrVars.
    auto.
  clear H.
  specialize (FormsOfTerm M) as ?.
  destruct H.
    auto.
  right.
  destruct H.
    destruct H.
    dependent destruction H.
    specialize (OrReducesAsOr H1) as ?; clear H1.
    fold @TransTerm in H.
    destruct H as (N & H).
    destruct H.
    dependent destruction H.
    rewrite in_map_iff in H1.
    destruct H1 as (eN & H1).
    destruct H1.
    dependent destruction H.
    esplit.
    split.
      apply ExtReducesOr.
      eauto.
    intros.
    destruct H; try easy.
    dependent destruction H.
    repeat dependent destruction H0.
    exists x0.
    split.
      simpl.
      omega.
    auto.
  destruct H.
    destruct H.
    dependent destruction H.
    specialize (AndReducesAsAnd H1) as ?; clear H1.
    fold @TransTerm in H.
    dependent destruction H.
    esplit.
    split.
      apply ExtReducesAnd.
    intros.
    clear PFTOrig.
    revert nnn H0.
    induction x.
      easy.
    destruct nnn.
      easy.
    intro.
    dependent destruction H0.
    destruct H.
      dependent destruction H.
      exists n.
      split.
        simpl.
        omega.
      auto.
    specialize (IHx H nnn H1).
    destruct IHx as (m & ?).
    destruct H2.
    exists m.
    split.
      simpl.
      omega.
    auto.
  destruct H as (t & H).
  destruct H as (sub & H).
  destruct H as (X & H).
  dependent destruction H.
  clear H0 H1.
  exists [ExtSubstitute sub (TermOfRule (FindInRules Rr X))].
  split.
    apply ExtReducesNontermi.
  intros.
  destruct H; try easy.
  dependent destruction H.
  rewrite Trans_ApplyArgs_com in PFTOrig.
  rewrite Trans_ExtSubstitute_com.
  eapply ProducesFiniteTreeSteps_AppendTransExplicitSubst_com.
    eauto.
  clear.
  intros.
  dependent destruction H.
  revert H.
  simpl NontermsOfGrammar.
  generalize (TransSubst (type_cast TailIsAll_GrVars_castSet V) (GetHOSub sub)); clear sub; intro sub.
  simpl AddVariablesToTerm.
  unfold TransTerm at 1.
  change (TransType Ground) with Ground.
  generalize (@HOPartEmpty_GrVars_castT (TransVars Nn) (TailLen (ArgsOfType t) + numG) Ground).
  revert sub.
  rewrite HOPartEmpty_GrVars.
  dependent destruction e.
  assert(forall Nn t t2, term Nn (ArgsOfType (TransType t)) t2 = term Nn (TransVars (HOPart (ArgsOfType t))) t2) as cast.
    intros.
    rewrite TransType_is_TransVars.
    auto.
  replace (TransTerm _ _ _) with (type_cast (cast _ _ _) (type_cast TransType_is_TransVars_castT (TransTerm
      Subset0 (ExtractSubsetForFirst (TailLen (ArgsOfType t)) V) (TermOfRule (FindInRules Rr X)))));
    try apply type_cast_type_cast_is_id.
  destruct t.
  rewrite Trans_FindInRules_com.
  generalize (@TransType_is_TransVars_castT2 (TransVars Nn) (TransVars [])
      (Arr (ArgsOfType (Arr l)))).
  generalize (cast (TransVars Nn) (Arr l) (TransType Ground)).
  revert sub.
  repeat change (ArgsOfType (Arr l)) with l.
  change (TransVars (HOPart l)) with (ArgsOfType (Arr (TransVars (HOPart (ArgsOfType (Arr l)))))).
  rewrite <- (TransType_is_TransVars (t := Arr l)).
  repeat dependent destruction e.
  clear - H0.
  intro.
  specialize (AppReducesAsApp H).
  clear H.
  intro.
  dependent destruction H.
  dependent destruction H0.
  dependent destruction H0.
  clear x.
  exists x0.
  split.
    simpl.
    omega.
  auto.
Qed.

Lemma TransReduces2ExtReduces4ext {Gg numG} {V : Subset numG} {eM : ext_term _ numG} {n} :
    ProducesFiniteTreeSteps _ n (type_cast TransTerm_OK_for_TransGrammar (TransExtTerm V eM)) ->
    ExtIsVariable eM \/ exists eNNN, ExtReduces Gg _ eM eNNN /\
      forall eN, In eN eNNN -> exists m, m < n /\
        ProducesFiniteTreeSteps _ m (type_cast TransTerm_OK_for_TransGrammar (TransExtTerm V eN)).
  generalize (@TransTerm_OK_for_TransGrammar Gg).
  destruct Gg.
  dependent destruction e0; clear x.
  revert n.
  induction eM; unfold TransExtTerm; fold @TransExtTerm; intros.
    right.
    dependent destruction H.
    specialize (OrReducesAsOr H); clear H; intro.
    destruct H.
    destruct H.
    dependent destruction H.
    dependent destruction H0.
    dependent destruction H0; clear x.
    destruct H1.
      dependent destruction H0.
      specialize (IHeM (false, V) x0).
      destruct IHeM.
          auto.
        (* variable with false *)
        dependent destruction eM; try easy.
        dependent destruction t; try easy.
        specialize ((proj1 Var_PFTS_iff_in_set) H) as ?.
        destruct H1.
        dependent destruction H2.
        dependent destruction e0.
          easy.
        exists [StdTerm _ _ (Var _ _ _ e0)].
        split.
          apply ExtReducesSimpl.
        intros.
        destruct H2; try easy.
        dependent destruction H2.
        exists 1.
        split.
          auto.
        apply Var_PFTS_iff_in_set.
        destruct H1.
        simpl.
        generalize (@DestructGrVars_castV (Arr []) (Arr []) (@repeat type (Arr []) numG) numG
            (@eq_refl (list type) (GrVars (S numG)))).
        dependent destruction e1.
        auto.
      (* term with false *)
      destruct H0 as (eNNN & H0).
      exists (map (fun eN => ExplicitSubst _ _ eN t) eNNN).
      destruct H0.
      split.
        apply ExtReducesInd.
        auto.
      intros.
      rewrite in_map_iff in H2.
      destruct H2.
      destruct H2.
      dependent destruction H2.
      unfold TransExtTerm.
      fold @TransExtTerm.
      specialize (H1 _ H3).
      destruct H1.
      destruct H1.
      exists (S (fold_right add 0 [x1])).
      split.
        simpl.
        omega.
      eapply PFTSReduces.
        eapply ReducesOr.
        left.
        eauto.
      apply Forall2_cons; try easy.
    destruct H0; try easy.
    dependent destruction H0.
    dependent destruction H.
    specialize (AndReducesAsAnd H); clear H; intro.
    dependent destruction H.
    dependent destruction H0.
    dependent destruction H0.
    dependent destruction H1.
    clear x.
    specialize (IHeM (true, V) x1).
    destruct IHeM.
        auto.
      (* variable with true *)
      dependent destruction eM; try easy.
      dependent destruction t; try easy.
      specialize ((proj1 Var_PFTS_iff_in_set) H) as ?.
      destruct H2.
      dependent destruction H3.
      dependent destruction e0.
        exists [StdTerm _ _ t0].
        split.
          apply ExtReducesSubst.
        intros.
        destruct H3; try easy.
        dependent destruction H3.
        exists x0.
        split.
          simpl.
          omega.
        auto.
      exists [StdTerm _ _ (Var _ _ _ e0)].
      split.
        apply ExtReducesSimpl.
      intros.
      destruct H3; try easy.
      dependent destruction H3.
      exists 1.
      split.
        simpl.
        omega.
      apply Var_PFTS_iff_in_set.
      destruct H2.
      simpl.
      generalize (@DestructGrVars_castV (Arr []) (Arr []) (@repeat type (Arr []) numG) numG
          (@eq_refl (list type) (GrVars (S numG)))).
      dependent destruction e1.
      auto.
    (* term with true *)
    destruct H1 as (eNNN & H1).
    exists (map (fun eN => ExplicitSubst _ _ eN t) eNNN).
    destruct H1.
    split.
      apply ExtReducesInd.
      auto.
    intros.
    rewrite in_map_iff in H3.
    destruct H3.
    destruct H3.
    dependent destruction H3.
    unfold TransExtTerm.
    fold @TransExtTerm.
    specialize (H2 _ H4).
    destruct H2.
    destruct H2.
    exists (S (fold_right add 0 [S (fold_right add 0 [x2; x0])])).
    split.
      simpl.
      omega.
    eapply PFTSReduces.
      eapply ReducesOr.
      right.
      left.
      eauto.
    apply Forall2_cons; try easy.
    eapply PFTSReduces.
      eapply ReducesAnd.
    apply Forall2_cons.
      auto.
    apply Forall2_cons; easy.
  apply TransReduces2ExtReduces4std.
  auto.
Qed.

Lemma PFTS_Trans2Ext {Gg} N {eM : ext_term _ 0} {n} :
    ProducesFiniteTreeSteps _ n (type_cast TransTerm_OK_for_TransGrammar (TransExtTerm Subset0 eM)) -> n <= N ->
    ExtProducesFiniteTree Gg eM.
  revert n eM.
  induction N; intros.
    dependent destruction H0.
    easy.
  specialize (TransReduces2ExtReduces4ext H) as ?.
  destruct H1.
    dependent destruction eM; try easy.
    dependent destruction t; easy.
  destruct H1.
  destruct H1.
  eapply ExtPFTReduces.
    eauto.
  intros.
  specialize (H2 _ H3).
  destruct H2.
  destruct H2.
  eapply IHN.
    eauto.
  omega.
Qed.

Lemma PFT_Trans2Ext Gg eM :
    ProducesFiniteTree (TransGrammar Gg) (type_cast TransTerm_OK_for_TransGrammar (TransExtTerm Subset0 eM)) ->
    ExtProducesFiniteTree Gg eM.
  intro.
  specialize (PFT2PFTSteps H) as ?.
  destruct H0.
  eapply PFTS_Trans2Ext.
    eauto.
  eauto.
Qed.

(* Final theorem of this part: extended reductions give the same as the transformed grammar *)
Theorem EquivExtTrans Gg : GrammarProducesFiniteTree (TransGrammar Gg) <-> GrammarExtProducesFiniteTree Gg.
  unfold GrammarProducesFiniteTree.
  replace (Nontermi _ _ _ (StartingNontermOfGrammar (TransGrammar Gg))) with 
      (type_cast TransTerm_OK_for_TransGrammar 
        (TransExtTerm Subset0 (StdTerm _ _ (Nontermi _ _ _ (StartingNontermOfGrammar Gg))))).
    split.
      apply PFT_Trans2Ext.
    apply PFT_Ext2Trans.
  generalize (TransTerm_OK_for_TransGrammar (Gg := Gg)).
  destruct Gg.
  simpl.
  generalize (@HOPartEmpty_GrVars_castT (TransVars Nn) 0 (Arr [])).
  repeat dependent destruction e0.
  auto.
Qed.

(***********************************************************************************************)
(* The final theorem                                                                           *)
(***********************************************************************************************)

Theorem TransOK (Gg : grammar) : GrammarProducesFiniteTree (TransGrammar Gg) <-> GrammarProducesFiniteTree Gg.
  rewrite EquivExtTrans.
  apply EquivStdExt.
Qed.

(***********************************************************************************************)

Fixpoint Order t := match t with Arr T => fold_right (fun t_arg => max (S (Order t_arg))) 0 T end.

(* Definition OrderOfGrammar Gg :=
 *)  



Definition Order01 t := match Order t with
  | 0 => true
  | 1 => true
  | _ => false
  end.

