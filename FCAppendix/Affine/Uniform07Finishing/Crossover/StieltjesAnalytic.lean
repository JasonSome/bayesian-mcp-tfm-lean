import Mathlib.Analysis.Calculus.Monotone
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover.StieltjesAnalytic
open MeasureTheory Set Filter Topology

private theorem ac_congr_on {f g : ℝ→ℝ} {L R : ℝ}
    (hf : AbsolutelyContinuousOnInterval f L R)
    (heq : EqOn f g (uIcc L R)) : AbsolutelyContinuousOnInterval g L R := by
  apply (absolutelyContinuousOnInterval_iff g L R).2
  intro eps heps
  obtain ⟨delta,hdelta,hbound⟩ :=
    (absolutelyContinuousOnInterval_iff f L R).1 hf eps heps
  refine ⟨delta,hdelta,?_⟩
  intro E hE hlen
  have he : (∑ i∈Finset.range E.1,dist (g (E.2 i).1) (g (E.2 i).2)) =
      ∑ i∈Finset.range E.1,dist (f (E.2 i).1) (f (E.2 i).2) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [←heq ((hE.1 i hi).1),←heq ((hE.1 i hi).2)]
  rw [he]
  exact hbound E hE hlen

def restrictedDensity (μ : Measure ℝ) (L R x : ℝ) : ℝ :=
  ((μ.restrict (Ioc L R)).rnDeriv volume x).toReal

theorem restrictedDensity_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] (L R : ℝ) :
    Integrable (restrictedDensity μ L R) volume :=
  Measure.integrable_toReal_rnDeriv

theorem integral_restrictedDensity (μ : Measure ℝ) [IsFiniteMeasure μ]
    {L R : ℝ} (hAC : μ.restrict (Ioc L R) ≪ volume)
    {x : ℝ} (hx : x∈Icc L R) :
    (∫ y in L..x,restrictedDensity μ L R y)=μ.real (Ioc L x) := by
  rw [intervalIntegral.integral_of_le hx.1]
  rw [show (∫ y in Ioc L x,restrictedDensity μ L R y)=
      (μ.restrict (Ioc L R)).real (Ioc L x) from
    Measure.setIntegral_toReal_rnDeriv hAC (Ioc L x)]
  have hsub : Ioc L x ⊆ Ioc L R := fun _ hy => ⟨hy.1,hy.2.trans hx.2⟩
  simp only [Measure.real,Measure.restrict_apply measurableSet_Ioc,
    inter_eq_left.mpr hsub]

theorem absolutelyContinuous_of_measure_increments
    (μ : Measure ℝ) [IsFiniteMeasure μ] (f : ℝ→ℝ)
    {L R : ℝ} (hLR : L≤ R) (hAC : μ.restrict (Ioc L R) ≪ volume)
    (hinc : ∀ x∈Icc L R,f x-f L=μ.real (Ioc L x)) :
    AbsolutelyContinuousOnInterval f L R := by
  have hi : IntervalIntegrable (restrictedDensity μ L R) volume L R :=
    (restrictedDensity_integrable μ L R).intervalIntegrable
  have hp : AbsolutelyContinuousOnInterval
      (fun x => ∫ y in L..x,restrictedDensity μ L R y) L R :=
    hi.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hc : LipschitzOnWith 0 (fun _ : ℝ=>f L) (uIcc L R) := by
    intro x hx y hy
    simp only [edist_self]
    exact bot_le
  apply ac_congr_on (hc.absolutelyContinuousOnInterval.add hp)
  intro x hx
  have hx' : x∈Icc L R := by simpa only [uIcc_of_le hLR] using hx
  change f L+(∫ y in L..x,restrictedDensity μ L R y)=f x
  rw [integral_restrictedDensity μ hAC hx']
  linarith [hinc x hx']

theorem absolutelyContinuous_stieltjes
    (F : StieltjesFunction ℝ) [IsFiniteMeasure F.measure]
    {L R : ℝ} (hLR : L≤ R) (hAC : F.measure.restrict (Ioc L R) ≪ volume) :
    AbsolutelyContinuousOnInterval (fun x=>F x) L R := by
  apply absolutelyContinuous_of_measure_increments F.measure (fun x=>F x) hLR hAC
  intro x hx
  simp only [Measure.real,F.measure_Ioc,ENNReal.toReal_ofReal
    (sub_nonneg.mpr (F.mono hx.1))]

theorem absolutelyContinuous_literal_kernel
    (F : StieltjesFunction ℝ) [IsFiniteMeasure F.measure] (f : ℝ→ℝ)
    {L R : ℝ} (hLR : L≤ R) (hAC : F.measure.restrict (Ioc L R) ≪ volume)
    (hagrees : ∀ x∈Icc L R,F x=f x) :
    AbsolutelyContinuousOnInterval f L R := by
  apply ac_congr_on (absolutelyContinuous_stieltjes F hLR hAC)
  intro x hx
  exact hagrees x (by simpa only [uIcc_of_le hLR] using hx)

theorem ae_hasDerivAt_restricted_density
    (F : StieltjesFunction ℝ) [IsFiniteMeasure F.measure]
    {C : Set ℝ} (hC : MeasurableSet C) :
    ∀ᵐ x∂(volume : Measure ℝ), x∈C →
      HasDerivAt (fun y=>F y) (((F.measure.restrict C).rnDeriv volume x).toReal) x := by
  have hr := Measure.rnDeriv_restrict F.measure volume hC
  filter_upwards [F.ae_hasDerivAt,hr] with x hx hrx hxC
  rw [hrx,Set.indicator_of_mem hxC]
  exact hx

theorem ae_hasDerivAt_literal_kernel
    (F : StieltjesFunction ℝ) (f : ℝ→ℝ) {L R : ℝ}
    (hagrees : ∀ x∈Icc L R,F x=f x) :
    ∀ᵐ x∂(volume : Measure ℝ), x∈Ioo L R →
      HasDerivAt f ((F.measure.rnDeriv volume x).toReal) x := by
  filter_upwards [F.ae_hasDerivAt] with x hx hxI
  apply hx.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hxI.1 hxI.2] with y hy
  exact (hagrees y ⟨hy.1.le,hy.2.le⟩).symm

theorem common_derivatives_of_three_AC {M S D : ℝ→ℝ} {L R : ℝ}
    (hM : AbsolutelyContinuousOnInterval M L R)
    (hS : AbsolutelyContinuousOnInterval S L R)
    (hD : AbsolutelyContinuousOnInterval D L R) :
    ∀ᵐ b∂(volume : Measure ℝ), b∈uIcc L R →
      HasDerivAt M (deriv M b) b ∧ HasDerivAt S (deriv S b) b ∧
        HasDerivAt D (deriv D b) b := by
  filter_upwards [hM.ae_differentiableAt,hS.ae_differentiableAt,
    hD.ae_differentiableAt] with b hbM hbS hbD hb
  exact ⟨(hbM hb).hasDerivAt,(hbS hb).hasDerivAt,(hbD hb).hasDerivAt⟩

end FCAppendix.Affine.Uniform07Finishing.Crossover.StieltjesAnalytic
