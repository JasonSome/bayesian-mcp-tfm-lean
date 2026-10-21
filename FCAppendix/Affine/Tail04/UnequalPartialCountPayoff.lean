import FCAppendix.Affine.Tail04.UnequalNoisyCountPayoff
import FCAppendix.Affine.Tail04.AtypicalPartialNoisy
import FCAppendix.Affine.Tail04.JoinedPartialNoisy

noncomputable section
namespace FCAppendix.Affine.Tail04.UnequalPartialCountPayoff
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open EqualPrivateSignal AllNoiseFiniteSelector
open scoped BigOperators

def rawWeight (N H0 H1 c : ℕ) (ξ B R Rp width e0 F : ℝ) (reg lowPresent : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (b : Fin N → ℝ) : ℝ :=
  if hN : N=0 then 0 else
    letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hN)
    if lowPresent then
      (Hybrid.rankLaw b).expect fun t =>
        (independentFlagLaw (sourceFlagProb e0 F b)
          (sourceFlagProb_nonneg e0 F b) (sourceFlagProb_le_one e0 F b)).expect fun z =>
            targetTypicalWeight (TypicalGuardStatistics.phi N H0 H1 c ξ B R Rp width reg ν0 ν1) b t z
    else 0

lemma rawWeight_bounds (N H0 H1 c : ℕ) (ξ B R Rp width e0 F : ℝ) (reg lowPresent : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (b : Fin N → ℝ) :
    rawWeight N H0 H1 c ξ B R Rp width e0 F reg lowPresent ν0 ν1 b∈Icc (0:ℝ) 1 := by
  unfold rawWeight
  split_ifs
  · norm_num
  · exact ⟨FiniteLaw.expect_nonneg _ (fun t => FiniteLaw.expect_nonneg _
      (fun z => (targetTypicalWeight_bounds _ b t z).1)),
      FiniteLaw.expect_le_const _ (fun t => FiniteLaw.expect_le_const _
      (fun z => (targetTypicalWeight_bounds _ b t z).2))⟩
  · norm_num

lemma measurable_rawWeight (N H0 H1 c : ℕ) (ξ B R Rp width e0 F : ℝ) (reg lowPresent : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) :
    Measurable (rawWeight N H0 H1 c ξ B R Rp width e0 F reg lowPresent ν0 ν1) := by
  change Measurable (fun b : Fin N → ℝ => rawWeight N H0 H1 c ξ B R Rp width e0 F reg lowPresent ν0 ν1 b)
  by_cases hN : N=0
  · simp only [rawWeight,dif_pos hN]
    exact measurable_const
  · letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hN)
    cases lowPresent
    · simp only [rawWeight,dif_neg hN,Bool.false_eq_true,ite_false]
      exact measurable_const
    · simp only [rawWeight,dif_neg hN,ite_true,FiniteLaw.expect]
      apply Finset.measurable_sum
      intro t _
      apply (Hybrid.measurable_rankLaw_mass t).mul
      apply Finset.measurable_sum
      intro z _
      apply ((continuous_iff_continuousAt.mpr
        (fun b => continuousAt_sourceFlagLaw_mass e0 F b z)).measurable).mul
      exact (UnequalNoisyCountPayoff.measurable_phi H0 H1 c ξ B R Rp width reg ν0 ν1 _).comp
        (UnequalNoisyCountPayoff.measurable_mixedReciprocalSum _)

lemma continuousAt_rawWeight (N H0 H1 c : ℕ) (ξ B R Rp width e0 F : ℝ) (reg lowPresent : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (b : Fin N → ℝ) (hb : ∀ i,0< b i) (hn : ∀ i j,i≠j → b i≠b j) :
    ContinuousAt (rawWeight N H0 H1 c ξ B R Rp width e0 F reg lowPresent ν0 ν1) b := by
  change ContinuousAt (fun a : Fin N → ℝ => rawWeight N H0 H1 c ξ B R Rp width e0 F reg lowPresent ν0 ν1 a) b
  by_cases hN : N=0
  · simp only [rawWeight,dif_pos hN]
    exact continuousAt_const
  · letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hN)
    cases lowPresent
    · simp only [rawWeight,dif_neg hN,Bool.false_eq_true,ite_false]
      exact continuousAt_const
    · simp only [rawWeight,dif_neg hN,ite_true]
      apply Hybrid.continuousAt_rankLaw_expect (fun i => (continuous_apply i).continuousAt)
      · intro t
        unfold FiniteLaw.expect
        apply tendsto_finsetSum
        intro z _
        exact (continuousAt_sourceFlagLaw_mass e0 F b z).mul
          (continuousAt_targetTypicalWeight _
            (TypicalGuardStatistics.continuousAt_phi N H0 H1 c ξ B R Rp width reg ν0 ν1) b hb t z)
      · intro i j hij
        have he : i=j := by_contra (fun h => hn i j h hij)
        rw [he]

def weight (N H0 H1 c : ℕ) (ξ B R Rp width e0 F eps : ℝ) (reg lowPresent : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (b : Fin N → ℝ) : unitInterval :=
  ⟨∫ z : Fin N → unitInterval,
      rawWeight N H0 H1 c ξ B R Rp width e0 F reg lowPresent ν0 ν1 (noisyBids eps b z)
        ∂Measure.pi (fun _ : Fin N => (volume : Measure unitInterval)), by
    constructor
    · exact integral_nonneg (fun z => (rawWeight_bounds N H0 H1 c ξ B R Rp width e0 F
        reg lowPresent ν0 ν1 _).1)
    · have hm : AEStronglyMeasurable (fun z : Fin N → unitInterval =>
          rawWeight N H0 H1 c ξ B R Rp width e0 F reg lowPresent ν0 ν1 (noisyBids eps b z))
          (Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))) :=
        ((measurable_rawWeight N H0 H1 c ξ B R Rp width e0 F reg lowPresent ν0 ν1).comp
          ((continuous_noisyBids eps).comp (show Continuous (fun z : Fin N → unitInterval => (b,z)) from continuous_const.prodMk continuous_id)).measurable).aestronglyMeasurable
      have hi := Integrable.of_bound hm 1 (ae_of_all _ (fun z => by
        rw [Real.norm_eq_abs,abs_of_nonneg (rawWeight_bounds N H0 H1 c ξ B R Rp width e0 F
          reg lowPresent ν0 ν1 _).1]
        exact (rawWeight_bounds N H0 H1 c ξ B R Rp width e0 F reg lowPresent ν0 ν1 _).2))
      simpa using integral_mono_ae hi (integrable_const (1:ℝ))
        (ae_of_all _ (fun z => (rawWeight_bounds N H0 H1 c ξ B R Rp width e0 F
          reg lowPresent ν0 ν1 _).2))⟩

theorem continuousAt_weight (N H0 H1 c : ℕ) (ξ B R Rp width e0 F : ℝ) (reg lowPresent : Bool)
    {eps : ℝ} (heps : 0< eps) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (b : Fin N → ℝ) (hb : ∀ i,0< b i) :
    ContinuousAt (weight N H0 H1 c ξ B R Rp width e0 F eps reg lowPresent ν0 ν1) b := by
  apply tendsto_subtype_rng.mpr
  apply MeasureTheory.continuousAt_of_dominated
    (F:=fun a z => rawWeight N H0 H1 c ξ B R Rp width e0 F reg lowPresent ν0 ν1 (noisyBids eps a z))
    (bound:=fun _ => (1:ℝ))
  · exact Eventually.of_forall (fun a =>
      ((measurable_rawWeight N H0 H1 c ξ B R Rp width e0 F reg lowPresent ν0 ν1).comp
        ((continuous_noisyBids eps).comp (continuous_const.prodMk continuous_id)).measurable).aestronglyMeasurable)
  · exact Eventually.of_forall (fun a => ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (rawWeight_bounds N H0 H1 c ξ B R Rp width e0 F
        reg lowPresent ν0 ν1 _).1]
      exact (rawWeight_bounds N H0 H1 c ξ B R Rp width e0 F reg lowPresent ν0 ν1 _).2))
  · exact integrable_const 1
  · filter_upwards [AtypicalActiveNoisy.ae_noisyBids_distinct heps.ne' b (fun i => (hb i).ne')]
      with z hz
    have hbz (i : Fin N) : 0< noisyBids eps b z i :=
      mul_pos (hb i) (by nlinarith [mul_nonneg heps.le (z i).2.1])
    have hnoisy : Continuous (fun a : Fin N → ℝ => noisyBids eps a z) :=
      (continuous_noisyBids eps).comp
        (show Continuous (fun a : Fin N → ℝ => (a,z)) from continuous_id.prodMk continuous_const)
    exact (continuousAt_rawWeight N H0 H1 c ξ B R Rp width e0 F reg lowPresent ν0 ν1
      (noisyBids eps b z) hbz hz).comp (f:=fun a : Fin N → ℝ => noisyBids eps a z) hnoisy.continuousAt

abbrev Input (N H : ℕ) (R U eps : ℝ) :=
  (Fin N → ℝ)×AtypicalPartialNoisy.AveragingInput H R U eps

def utility (N H0 H1 c : ℕ) (ξ B R U width e0 F eps : ℝ) (side reg lowPresent : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (j : Fin (AllCountAtypical.ownCount H0 H1 side))
    (p : ℝ×Input N (AllCountAtypical.ownCount H0 H1 side) R U eps) : ℝ :=
  let x := (weight N H0 H1 c ξ B R (U*(1+eps)) width e0 F eps reg lowPresent ν0 ν1 p.2.1,p.2.2)
  p.1*AtypicalPartialNoisy.branchInclusion N H0 H1 c side reg j x-
    AtypicalPartialNoisy.branchPayment N H0 H1 c side reg j x

theorem continuousAt_utility (N H0 H1 c : ℕ) (ξ B R U width e0 F : ℝ) (side reg lowPresent : Bool)
    {eps : ℝ} (heps : 0< eps) (hR : 0< R)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (j : Fin (AllCountAtypical.ownCount H0 H1 side))
    (p : ℝ×Input N (AllCountAtypical.ownCount H0 H1 side) R U eps)
    (hb : ∀ i,0< p.2.1 i) :
    ContinuousAt (utility N H0 H1 c ξ B R U width e0 F eps side reg lowPresent ν0 ν1 j) p := by
  have hproj : ContinuousAt (fun x : ℝ×Input N (AllCountAtypical.ownCount H0 H1 side) R U eps => x.2.1) p :=
    (continuous_fst.comp continuous_snd).continuousAt
  have hw := (continuousAt_weight N H0 H1 c ξ B R (U*(1+eps)) width e0 F reg lowPresent
    heps ν0 ν1 p.2.1 hb).comp (f:=fun x : ℝ×Input N (AllCountAtypical.ownCount H0 H1 side) R U eps => x.2.1) hproj
  have hs : ContinuousAt (fun x : ℝ×Input N (AllCountAtypical.ownCount H0 H1 side) R U eps => x.2.2) p :=
    (continuous_snd.comp continuous_snd).continuousAt
  have hx := hw.prodMk hs
  exact (continuousAt_fst.mul
    ((AtypicalPartialNoisy.continuous_branchInclusion N H0 H1 c hR heps.ne' side reg j).continuousAt.comp hx)).sub
      ((AtypicalPartialNoisy.continuous_branchPayment N H0 H1 c hR heps side reg j).continuousAt.comp hx)

end FCAppendix.Affine.Tail04.UnequalPartialCountPayoff
