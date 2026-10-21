import FCAppendix.Affine.Tail04.TypicalTargetCount
import FCAppendix.Affine.Tail04.TwoCoinContinuity
import FCAppendix.Affine.Hybrid.FavoredValue

noncomputable section
namespace FCAppendix.Affine.Tail04
open MeasureTheory Set Filter Topology
open scoped BigOperators
variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [TopologicalSpace X]

def sourceFlagProb (e0 B : ℝ) (b : ι → ℝ) (i : ι) : ℝ :=
  probabilityClip (mixedFlagProbability e0 B (b i))

omit [Fintype ι] [DecidableEq ι] in
theorem sourceFlagProb_nonneg (e0 B : ℝ) (b : ι → ℝ) (i : ι) :
    0 ≤ sourceFlagProb e0 B b i := (probabilityClip_bounds _).1

omit [Fintype ι] [DecidableEq ι] in
theorem sourceFlagProb_le_one (e0 B : ℝ) (b : ι → ℝ) (i : ι) :
    sourceFlagProb e0 B b i ≤ 1 := (probabilityClip_bounds _).2

omit [Fintype ι] [DecidableEq ι] in
theorem sourceFlagProb_eq {e0 B : ℝ} (he0 : 0 ≤ e0) (he1 : e0 ≤ 1)
    (hB : 1 < B) (b : ι → ℝ) (i : ι) (hb : b i ∈ Icc 1 B) :
    sourceFlagProb e0 B b i=mixedFlagProbability e0 B (b i) :=
  probabilityClip_eq ⟨mixedFlagProbability_nonneg he0,
    mixedFlagProbability_le_one he0 he1 hB hb⟩

omit [Fintype ι] [DecidableEq ι] in
theorem continuous_sourceFlagProb (e0 B : ℝ) (i : ι) :
    Continuous (fun b : ι → ℝ => sourceFlagProb e0 B b i) :=
  continuous_probabilityClip.comp ((continuous_mixedFlagProbability e0 B).comp
    (continuous_apply i))

theorem continuousAt_meanMarginal (xi : ℝ) (c ell : ℕ) (privateMean : ℝ) (M : ℕ)
    (W bi : X → ℝ) {x : X} (hW : ContinuousAt W x) (hb : ContinuousAt bi x)
    (hW0 : W x ≠ 0) (hb0 : bi x ≠ 0) :
    ContinuousAt (fun y => meanMarginal xi c ell privateMean M (W y) (bi y)) x := by
  have hLambda : ContinuousAt
      (fun y => ((M:ℝ)-xi*((c:ℝ)-privateMean-ell))/W y) x :=
    continuousAt_const.div hW hW0
  exact continuous_probabilityClip.continuousAt.comp
    ((continuousAt_const.sub (hLambda.div hb hb0)).div_const xi)

theorem continuousAt_meanCountLaw_mass (xi : ℝ) (c ell0 ell1 : ℕ)
    (mean0 mean1 : ℝ) (M : ℕ) (W bi : X → ℝ) {x : X}
    (hW : ContinuousAt W x) (hb : ContinuousAt bi x)
    (hW0 : W x ≠ 0) (hb0 : bi x ≠ 0) (r : Fin 3) :
    ContinuousAt (fun y => (meanCountLaw xi c ell0 ell1 mean0 mean1 M (W y) (bi y)).mass r) x := by
  have hp := continuousAt_meanMarginal xi c ell0 mean0 M W bi hW hb hW0 hb0
  have hq := continuousAt_meanMarginal xi c ell1 mean1 M W bi hW hb hW0 hb0
  unfold meanCountLaw
  exact continuousAt_twoCoinCountLaw_mass _ _ _ _ _ _ hp hq r

omit [Fintype ι] [DecidableEq ι] in
theorem continuousAt_mixedReciprocalSum (I : Finset ι) (b : ι → ℝ)
    (hb : ∀ i ∈ I, b i ≠ 0) :
    ContinuousAt (fun a : ι → ℝ => mixedReciprocalSum I a) b := by
  unfold mixedReciprocalSum
  exact tendsto_finsetSum _ fun i hi => continuousAt_const.div (continuous_apply i).continuousAt (hb i hi)

theorem continuousAt_targetStateCount_mass (P : TypicalCountParameters)
    (b : ι → ℝ) (hb : ∀ i, 0 < b i) (target : ι) (flags : ι → Bool)
    (focal : ι) (r : Fin 3) :
    ContinuousAt (fun a : ι → ℝ => (targetStateCount P.mixedCount a target flags focal).mass r) b := by
  by_cases hi : focal ∈ targetMixedSet target flags
  · simp only [targetStateCount,if_pos hi,TypicalCountParameters.mixedCount]
    apply continuousAt_meanCountLaw_mass
      P.xi P.c (P.owner0 (targetMixedSet target flags).card)
      (P.owner1 (targetMixedSet target flags).card) P.privateMean0 P.privateMean1
      (targetMixedSet target flags).card
    · exact continuousAt_mixedReciprocalSum _ b (fun i _ => (hb i).ne')
    · exact (continuous_apply focal).continuousAt
    · have hpos : 0 < mixedReciprocalSum (targetMixedSet target flags) b := by
        simpa only [mixedReciprocalSum, one_div] using
          Hybrid.reciprocal_sum_pos b _ ⟨focal,hi⟩ (fun i _ => hb i)
      exact hpos.ne'
    · exact (hb focal).ne'
  · simp only [targetStateCount,if_neg hi]
    exact continuousAt_const

theorem continuousAt_targetTypicalWeight (phi : ℕ → ℝ → unitInterval)
    (hphi : ∀ M W, 0 < W → ContinuousAt (fun W' => (phi M W':ℝ)) W)
    (b : ι → ℝ) (hb : ∀ i, 0 < b i) (target : ι) (flags : ι → Bool) :
    ContinuousAt (fun a : ι → ℝ => targetTypicalWeight phi a target flags) b := by
  by_cases hI : (targetMixedSet target flags).Nonempty
  · have hW : 0 < mixedReciprocalSum (targetMixedSet target flags) b :=
      by simpa only [mixedReciprocalSum, one_div] using
        Hybrid.reciprocal_sum_pos b _ hI (fun i _ => hb i)
    exact (hphi _ _ hW).comp
      (continuousAt_mixedReciprocalSum _ b (fun i _ => (hb i).ne'))
  · have hI0 : targetMixedSet target flags=∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    simp only [targetTypicalWeight,hI0,mixedReciprocalSum,Finset.sum_empty]
    exact continuousAt_const

theorem continuousAt_sourceFlagLaw_mass (e0 B : ℝ) (b : ι → ℝ) (flags : ι → Bool) :
    ContinuousAt (fun a : ι → ℝ =>
      (independentFlagLaw (sourceFlagProb e0 B a)
        (sourceFlagProb_nonneg e0 B a) (sourceFlagProb_le_one e0 B a)).mass flags) b := by
  change ContinuousAt (fun a : ι → ℝ =>
    ∏ i, if flags i then sourceFlagProb e0 B a i else 1-sourceFlagProb e0 B a i) b
  apply tendsto_finsetProd
  intro i _
  cases h : flags i
  · simp only [Bool.false_eq_true,ite_false]
    exact continuousAt_const.sub (continuous_sourceFlagProb e0 B i).continuousAt
  · simp only [ite_true]
    exact (continuous_sourceFlagProb e0 B i).continuousAt

theorem continuousAt_conditionalTargetCount_mass (P : TypicalCountParameters)
    (phi : ℕ → ℝ → unitInterval) (hphi : ∀ M W, 0 < W → ContinuousAt (fun W' => (phi M W':ℝ)) W)
    (e0 B : ℝ) (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    (target focal : ι) (fallback : CountLaw 2) (r : Fin 3) :
    ContinuousAt (fun a : ι → ℝ =>
      (conditionalTargetCount P.mixedCount phi a (sourceFlagProb e0 B a)
        (sourceFlagProb_nonneg e0 B a) (sourceFlagProb_le_one e0 B a)
        target focal fallback).mass r) b := by
  unfold conditionalTargetCount FiniteLaw.finiteMix FiniteLaw.expect FiniteLaw.mixture
  apply tendsto_finsetSum
  intro flags _
  have hw := continuousAt_targetTypicalWeight phi hphi b hb target flags
  exact (continuousAt_sourceFlagLaw_mass e0 B b flags).mul
    ((hw.mul (continuousAt_targetStateCount_mass P b hb target flags focal r)).add
      ((continuousAt_const.sub hw).mul continuousAt_const))

def sourceTypicalJointPayoff [Nonempty ι] (P : TypicalCountParameters)
    (phi : ℕ → ℝ → unitInterval) (e0 B eta : ℝ)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) (focal : ι) (fallback : CountLaw 2)
    (x : ℝ × (ι → ℝ)) : ℝ :=
  affineCountUtility
    (typicalRankCount P.mixedCount phi x.2 (sourceFlagProb e0 B x.2)
      (sourceFlagProb_nonneg e0 B x.2) (sourceFlagProb_le_one e0 B x.2) focal fallback)
    x.1 (x.2 focal) eta heta0 heta1

theorem continuousAt_joint_conditionalTargetUtility (P : TypicalCountParameters)
    (phi : ℕ → ℝ → unitInterval) (hphi : ∀ M W, 0 < W → ContinuousAt (fun W' => (phi M W':ℝ)) W)
    (e0 B eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (target focal : ι) (fallback : CountLaw 2) (x : ℝ × (ι → ℝ))
    (hb : ∀ i, 0 < x.2 i) :
    ContinuousAt (fun y : ℝ × (ι → ℝ) =>
      affineCountUtility
        (conditionalTargetCount P.mixedCount phi y.2 (sourceFlagProb e0 B y.2)
          (sourceFlagProb_nonneg e0 B y.2) (sourceFlagProb_le_one e0 B y.2)
          target focal fallback) y.1 (y.2 focal) eta heta0 heta1) x := by
  unfold affineCountUtility CountLaw.utility FiniteLaw.expect
  apply tendsto_finsetSum
  intro r _
  have hm := (continuousAt_conditionalTargetCount_mass P phi hphi e0 B x.2 hb
    target focal fallback r).comp continuousAt_snd
  apply hm.mul
  unfold userPayoff
  exact ((continuousAt_fst.mul continuousAt_const).sub
    (((continuous_apply focal : Continuous (fun b : ι → ℝ => b focal)).continuousAt.comp continuousAt_snd).mul
      continuousAt_const)).sub continuousAt_const

theorem continuousAt_sourceTypicalJointPayoff [Nonempty ι] (P : TypicalCountParameters)
    (phi : ℕ → ℝ → unitInterval) (hphi : ∀ M W, 0 < W → ContinuousAt (fun W' => (phi M W':ℝ)) W)
    (e0 B eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (focal : ι) (fallback : CountLaw 2) (x : ℝ × (ι → ℝ))
    (hb : ∀ i, 0 < x.2 i)
    (hnotie : ∀ j, j ≠ focal → x.2 j ≠ x.2 focal) :
    ContinuousAt (sourceTypicalJointPayoff P phi e0 B eta heta0 heta1 focal fallback) x := by
  unfold sourceTypicalJointPayoff
  simp_rw [typicalRankCount_utility]
  apply Hybrid.continuousAt_rankLaw_expect
    (fun j => (continuous_apply j).continuousAt.comp continuousAt_snd)
    (fun target => continuousAt_joint_conditionalTargetUtility P phi hphi e0 B eta
      heta0 heta1 target focal fallback x hb)
  intro t u htu
  change x.2 t = x.2 u at htu
  by_cases htu' : t=u
  · rw [htu']
  · have hit : focal ≠ t := by
      intro h
      subst t
      exact hnotie u (Ne.symm htu') htu.symm
    have hiu : focal ≠ u := by
      intro h
      subst u
      exact hnotie t htu' htu
    have hp : sourceFlagProb e0 B x.2 t=sourceFlagProb e0 B x.2 u := by
      unfold sourceFlagProb
      rw [htu]
    rw [conditionalTargetCount_rival_tie P.mixedCount phi x.2
      (sourceFlagProb e0 B x.2) (sourceFlagProb_nonneg e0 B x.2)
      (sourceFlagProb_le_one e0 B x.2) focal t u hit hiu htu hp fallback]

end FCAppendix.Affine.Tail04
