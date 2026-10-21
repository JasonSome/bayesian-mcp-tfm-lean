import FCAppendix.Affine.Tail04.FocalInsertionSampling
import FCAppendix.Affine.Tail04.JoinedHighPolicy

noncomputable section
namespace FCAppendix.Affine.Tail04.FocalInsertion
open MeasureTheory Set Classical
open EqualPrivateSignal JoinedHighPolicy

def Guard (N H0 H1 c : ℕ) (ξ B R Rp : ℝ) (reg : Bool)
    (I O0 O1 : Finset (Fin N)) (b : Fin N → ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) : Prop :=
  TypicalHighPolicy.Structural N H0 H1 c I O0 O1 ∧
    LocalGuard N H0 c ξ B reg O0 I b ∧ LocalGuard N H1 c ξ B reg O1 I b ∧
    PartialGuard N H0 c ξ R Rp reg O0 I b ν0 ∧ PartialGuard N H1 c ξ R Rp reg O1 I b ν1

lemma measurable_baseline_realization (N H c : ℕ) (ξ : ℝ) (reg : Bool)
    (O I : Finset (Fin N)) (z : Marks H) :
    Measurable (fun b : Fin N → ℝ => TypicalHighPolicy.multiplier N H c ξ reg O I b z) := by
  simp_rw [TypicalHighPolicy.multiplier_formula]
  exact measurable_const.div (measurable_reciprocal N I)

lemma measurableSet_localGuard (N H c : ℕ) (ξ B : ℝ) (reg : Bool)
    (O I : Finset (Fin N)) :
    MeasurableSet {b : Fin N → ℝ | LocalGuard N H c ξ B reg O I b} := by
  simp only [LocalGuard,setOf_forall]
  apply MeasurableSet.iInter
  intro z
  exact (measurableSet_le measurable_const (measurable_baseline_realization N H c ξ reg O I z)).inter
    (measurableSet_le ((measurable_baseline_realization N H c ξ reg O I z).add
      (measurable_const.div (measurable_reciprocal N I))) measurable_const)

lemma measurableSet_partialGuard (N H c : ℕ) (ξ R Rp : ℝ) (reg : Bool)
    (O I : Finset (Fin N)) (ν : FiniteLaw (Marks H)) :
    MeasurableSet {b : Fin N → ℝ | PartialGuard N H c ξ R Rp reg O I b ν} := by
  cases reg
  · exact measurableSet_le ((measurable_baseline N H c ξ false O I ν).add
      (measurable_const.div (measurable_reciprocal N I))) measurable_const
  · exact measurableSet_le measurable_const (measurable_baseline N H c ξ true O I ν)

lemma measurableSet_guard (N H0 H1 c : ℕ) (ξ B R Rp : ℝ) (reg : Bool)
    (I O0 O1 : Finset (Fin N)) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) :
    MeasurableSet {b : Fin N → ℝ | Guard N H0 H1 c ξ B R Rp reg I O0 O1 b ν0 ν1} := by
  by_cases hs : TypicalHighPolicy.Structural N H0 H1 c I O0 O1
  · simp only [Guard,hs,true_and]
    exact (measurableSet_localGuard N H0 c ξ B reg O0 I).inter
      ((measurableSet_localGuard N H1 c ξ B reg O1 I).inter
        ((measurableSet_partialGuard N H0 c ξ R Rp reg O0 I ν0).inter
          (measurableSet_partialGuard N H1 c ξ R Rp reg O1 I ν1)))
  · simp only [Guard,hs,false_and,setOf_false]
    exact MeasurableSet.empty

def PublicGuard (N H0 H1 c : ℕ) (ξ B R Rp : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (p : JoinedHighPolicy.Parameters N H0 R Rp B) : Prop :=
  Guard N H0 H1 c ξ B R Rp (regime p.1.1) (JoinedHighPolicy.mixed p.1.1) (owner0 p.1.1) (owner1 p.1.1)
    (publicBids p) ν0 ν1

lemma measurableSet_publicGuard (N H0 H1 c : ℕ) (ξ B R Rp : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) :
    MeasurableSet {p | PublicGuard N H0 H1 c ξ B R Rp ν0 ν1 p} := by
  have he : {p | PublicGuard N H0 H1 c ξ B R Rp ν0 ν1 p}=
      ⋃ s : Scenario N,{p : JoinedHighPolicy.Parameters N H0 R Rp B | p.1.1=s} ∩
        {p | Guard N H0 H1 c ξ B R Rp (regime s) (JoinedHighPolicy.mixed s) (owner0 s) (owner1 s)
          (publicBids p) ν0 ν1} := by
    ext p
    simp [PublicGuard]
  rw [he]
  apply MeasurableSet.iUnion
  intro s
  exact (measurableSet_eq_fun (measurable_fst.comp measurable_fst) measurable_const).inter
    ((measurableSet_guard N H0 H1 c ξ B R Rp (regime s) (JoinedHighPolicy.mixed s) (owner0 s) (owner1 s) ν0 ν1).preimage
      measurable_publicBids)

def Use (N H0 H1 c : ℕ) (ξ B R Rp width : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (p : JoinedHighPolicy.Parameters N H0 R Rp B) : Prop :=
  UseTypical N H0 H1 c ξ B R Rp width ν0 ν1 p ∧
    PublicGuard N H0 H1 c ξ B R Rp ν0 ν1 p

lemma measurableSet_use (N H0 H1 c : ℕ) (ξ B R Rp width : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) :
    MeasurableSet {p | Use N H0 H1 c ξ B R Rp width ν0 ν1 p} :=
  (measurableSet_useTypical N H0 H1 c ξ B R Rp width ν0 ν1).inter
    (measurableSet_publicGuard N H0 H1 c ξ B R Rp ν0 ν1)

end FCAppendix.Affine.Tail04.FocalInsertion
