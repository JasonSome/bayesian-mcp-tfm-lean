import FCAppendix.Affine.Uniform06.SupportIntervalDomination
import FCAppendix.Affine.Uniform06.DensityIC
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.VectorMeasure.WithDensity

noncomputable section
namespace FCAppendix.Affine.Uniform06.CompactStieltjes

open MeasureTheory Set Filter Topology
open SupportIntervalDomination Rank

def clip (lo hi b : ℝ) : ℝ := max lo (min hi b)

theorem clip_mem {lo hi : ℝ} (h : lo ≤ hi) (b : ℝ) :
    clip lo hi b ∈ Icc lo hi :=
  ⟨le_max_left _ _,max_le h (min_le_left _ _)⟩

theorem clip_eq {lo hi b : ℝ} (hb : b ∈ Icc lo hi) : clip lo hi b=b := by
  unfold clip
  rw [min_eq_right hb.2,max_eq_right hb.1]

theorem clip_monotone (lo hi : ℝ) : Monotone (clip lo hi) :=
  monotone_const.max (monotone_const.min monotone_id)

theorem clip_continuous (lo hi : ℝ) : Continuous (clip lo hi) := by
  unfold clip
  fun_prop

def ofMonotoneOn (F : ℝ → ℝ) {lo hi : ℝ} (h : lo ≤ hi)
    (hm : MonotoneOn F (Icc lo hi)) (hc : ContinuousOn F (Icc lo hi)) :
    StieltjesFunction ℝ where
  toFun b := F (clip lo hi b)
  mono' a b hab := hm (clip_mem h a) (clip_mem h b) (clip_monotone lo hi hab)
  right_continuous' _b :=
    (hc.comp_continuous (clip_continuous lo hi) (clip_mem h)).continuousAt.continuousWithinAt

theorem ofMonotoneOn_continuous (F : ℝ → ℝ) {lo hi : ℝ} (h : lo ≤ hi)
    (hm : MonotoneOn F (Icc lo hi)) (hc : ContinuousOn F (Icc lo hi)) :
    Continuous (ofMonotoneOn F h hm hc) :=
  hc.comp_continuous (clip_continuous lo hi) (clip_mem h)

theorem ofMonotoneOn_eq (F : ℝ → ℝ) {lo hi : ℝ} (h : lo ≤ hi)
    (hm : MonotoneOn F (Icc lo hi)) (hc : ContinuousOn F (Icc lo hi))
    {b : ℝ} (hb : b ∈ Icc lo hi) : ofMonotoneOn F h hm hc b=F b := by
  change F (clip lo hi b)=F b
  rw [clip_eq hb]

theorem measure_real_Ioc (F : StieltjesFunction ℝ) {a b : ℝ} (hab : a ≤ b) :
    F.measure.real (Ioc a b)=F b-F a := by
  unfold Measure.real
  rw [F.measure_Ioc,ENNReal.toReal_ofReal (sub_nonneg.mpr (F.mono hab))]

theorem continuous_measure_atomless (F : StieltjesFunction ℝ) (hF : Continuous F)
    (b : ℝ) : F.measure {b}=0 := by
  rw [F.measure_singleton]
  have he : Function.leftLim F b=F b :=
    hF.continuousAt.continuousWithinAt.leftLim_eq
  rw [he,sub_self,ENNReal.ofReal_zero]

theorem finite_of_bounds (F : StieltjesFunction ℝ)
    (hF : ∀ b : ℝ, F b ∈ Icc (0:ℝ) 1) : IsFiniteMeasure F.measure :=
  F.isFiniteMeasure_of_forall_abs_le (fun b => by
    rw [abs_of_nonneg (hF b).1]
    exact (hF b).2)

theorem restriction_ac_of_anchored_increments
    (F : StieltjesFunction ℝ) [IsFiniteMeasure F.measure] (hF : Continuous F)
    {C : Set ℝ} (hC : IsClosed C) {lo hi δ K : ℝ}
    (hCI : C ⊆ Ioc lo hi) (hδ : 0 < δ) (hK : 0 ≤ K)
    (hinc : ∀ a ∈ C, ∀ b : ℝ,
      a ∈ Icc lo hi → b ∈ Icc lo hi → a ≤ b → b-a ≤ δ →
      F b-F a ≤ K*(b-a)) : F.measure.restrict C ≪ volume := by
  let μ := F.measure.restrict C
  let ν := ENNReal.ofReal K • volume.restrict (Ioc lo hi)
  letI : IsFiniteMeasure (volume.restrict (Ioc lo hi)) :=
    ⟨by simp only [Measure.restrict_apply_univ,Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  letI : IsFiniteMeasure ν := (volume.restrict (Ioc lo hi)).smul_finite ENNReal.ofReal_ne_top
  have hμatom := restricted_singleton_null F.measure (continuous_measure_atomless F hF) C
  have hνatom : ∀ x : ℝ, ν {x}=0 := by
    intro x
    simp only [ν,Measure.smul_apply,smul_eq_mul]
    rw [restricted_singleton_null volume (fun y => by simp) _ x,mul_zero]
  have hanc : ∀ a ∈ C, ∀ b : ℝ,
      a ∈ Icc lo hi → b ∈ Icc lo hi → a ≤ b → b-a ≤ δ →
      μ.real (Ioc a b) ≤ ν.real (Ioc a b) := by
    intro a ha b haI hbI hab hs
    have hsub : Ioc a b ⊆ Ioc lo hi := fun x hx =>
      ⟨haI.1.trans_lt hx.1,hx.2.trans hbI.2⟩
    have hμ : μ.real (Ioc a b) ≤ F b-F a := by
      dsimp only [μ]
      rw [measureReal_restrict_apply measurableSet_Ioc,← measure_real_Ioc F hab]
      exact measureReal_mono inter_subset_left
    have hν : ν.real (Ioc a b)=K*(b-a) := by
      simp only [ν,Measure.real,Measure.smul_apply,smul_eq_mul,
        Measure.restrict_apply measurableSet_Ioc,inter_eq_left.mpr hsub,
        Real.volume_Ioc,ENNReal.toReal_mul,ENNReal.toReal_ofReal hK,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
    rw [hν]
    exact hμ.trans (hinc a ha b haI hbI hab hs)
  have hdom := measure_restrict_le_of_local_support_bounds μ ν hC
    (ae_restrict_mem hC.measurableSet) hμatom hνatom hδ hanc
  have hμJ : μ.restrict (Ioc lo hi)=μ := by
    dsimp only [μ]
    rw [Measure.restrict_restrict measurableSet_Ioc,inter_eq_right.mpr hCI]
  rw [hμJ] at hdom
  intro A hA
  have hres : (volume.restrict (Ioc lo hi)) A=0 :=
    le_antisymm ((Measure.restrict_le_self A).trans hA.le) zero_le
  have hνA : ν A=0 := by simp only [ν,Measure.smul_apply,smul_eq_mul,hres,mul_zero]
  exact le_antisymm ((hdom A).trans ((Measure.restrict_le_self A).trans hνA.le)) zero_le

theorem restricted_rn_reconstruction (μ : Measure ℝ) [IsFiniteMeasure μ]
    {C : Set ℝ} (hC : MeasurableSet C) (hAC : μ.restrict C ≪ volume) :
    (volume.restrict C).withDensity ((μ.restrict C).rnDeriv volume)=μ.restrict C := by
  rw [← restrict_withDensity hC,
    Measure.withDensity_rnDeriv_eq _ _ hAC,
    Measure.restrict_restrict hC,inter_self]

theorem vector_identity_of_actual_rn
    (μS μD : Measure ℝ) [IsFiniteMeasure μS] [IsFiniteMeasure μD]
    {C : Set ℝ} (hC : MeasurableSet C) [IsFiniteMeasure (volume.restrict C)]
    (hSAC : μS.restrict C ≪ volume) (hDAC : μD.restrict C ≪ volume)
    (w A z : ℝ → ℝ) (hw : Measurable w) (_hA : Measurable A) (hz : Measurable z)
    (W Z : ℝ)
    (hwb : ∀ x ∈ C, ‖w x‖ ≤ W) (hzb : ∀ x ∈ C, ‖z x‖ ≤ Z)
    (hAi : Integrable A (volume.restrict C))
    (hidentity : ∀ᵐ x ∂volume.restrict C,
      w x*((μS.restrict C).rnDeriv volume x).toReal=
        A x+z x*((μD.restrict C).rnDeriv volume x).toReal) :
    (μS.restrict C).withDensityᵥ w=
      (volume.restrict C).withDensityᵥ A+(μD.restrict C).withDensityᵥ z := by
  let lamMeasure := volume.restrict C
  have hρS : Integrable (fun x => ((μS.restrict C).rnDeriv volume x).toReal) lamMeasure :=
    Measure.integrableOn_toReal_rnDeriv (measure_ne_top (μS.restrict C) C)
  have hρD : Integrable (fun x => ((μD.restrict C).rnDeriv volume x).toReal) lamMeasure :=
    Measure.integrableOn_toReal_rnDeriv (measure_ne_top (μD.restrict C) C)
  have hwp : Integrable (fun x => w x*((μS.restrict C).rnDeriv volume x).toReal) lamMeasure := by
    apply hρS.bdd_mul hw.aestronglyMeasurable
    filter_upwards [ae_restrict_mem hC] with x hx
    exact hwb x hx
  have hzp : Integrable (fun x => z x*((μD.restrict C).rnDeriv volume x).toReal) lamMeasure := by
    apply hρD.bdd_mul hz.aestronglyMeasurable
    filter_upwards [ae_restrict_mem hC] with x hx
    exact hzb x hx
  have hS : lamMeasure.withDensityᵥ (fun x => w x*((μS.restrict C).rnDeriv volume x).toReal)=
      (μS.restrict C).withDensityᵥ w := by
    have hp := withDensityᵥ_smul_eq_withDensityᵥ_withDensity'
      (Measure.measurable_rnDeriv (μS.restrict C) volume).aemeasurable
      (ae_restrict_of_ae (Measure.rnDeriv_lt_top (μS.restrict C) volume))
      (show Integrable (fun x => ((μS.restrict C).rnDeriv volume x).toReal • w x) lamMeasure by
        simpa only [smul_eq_mul,mul_comm] using hwp)
    rw [restricted_rn_reconstruction μS hC hSAC] at hp
    simpa only [smul_eq_mul,mul_comm] using hp
  have hD : lamMeasure.withDensityᵥ (fun x => z x*((μD.restrict C).rnDeriv volume x).toReal)=
      (μD.restrict C).withDensityᵥ z := by
    have hp := withDensityᵥ_smul_eq_withDensityᵥ_withDensity'
      (Measure.measurable_rnDeriv (μD.restrict C) volume).aemeasurable
      (ae_restrict_of_ae (Measure.rnDeriv_lt_top (μD.restrict C) volume))
      (show Integrable (fun x => ((μD.restrict C).rnDeriv volume x).toReal • z x) lamMeasure by
        simpa only [smul_eq_mul,mul_comm] using hzp)
    rw [restricted_rn_reconstruction μD hC hDAC] at hp
    simpa only [smul_eq_mul,mul_comm] using hp
  rw [← hS,← hD,← withDensityᵥ_add' hAi hzp]
  exact WithDensityᵥEq.congr_ae hidentity

end FCAppendix.Affine.Uniform06.CompactStieltjes
