import FCAppendix.Existence.R01Distributional
import FCAppendix.Probability.Resample

noncomputable section
namespace FCAppendix.Affine.Tail04.NoisyCarrierIC
open MeasureTheory ProbabilityTheory Set Classical Filter
open Existence.Distributional

variable {T A Ω : Type*} [MeasurableSpace T] [MeasurableSpace A] [MeasurableSpace Ω]
  (μ : Measure T) (π : Law (A:=A) μ)
  (ν : Measure Ω) [IsProbabilityMeasure ν]

def expected (pay : (T×A)×Ω → ℝ) (x : T×A) : ℝ := ∫ ω,pay (x,ω) ∂ν

def gain (eligible : Set (T×A)) (dev : T×A → A) (pay : (T×A)×Ω → ℝ)
    (z : (T×A)×Ω) : ℝ :=
  if z.1∈eligible then pay ((z.1.1,dev z.1),z.2)-pay z else 0

lemma integrable_fixed_pay (pay : (T×A)×Ω → ℝ) (hp : Measurable pay)
    (B : ℝ) (hB : ∀ z,‖pay z‖≤ B) (x : T×A) :
    Integrable (fun ω => pay (x,ω)) ν :=
  Integrable.of_bound (hp.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable B
    (Eventually.of_forall (fun ω => hB (x,ω)))

lemma measurable_gain (eligible : Set (T×A)) (he : MeasurableSet eligible)
    (dev : T×A → A) (hd : Measurable dev)
    (pay : (T×A)×Ω → ℝ) (hp : Measurable pay) :
    Measurable (gain eligible dev pay) :=
  Measurable.ite (he.preimage measurable_fst)
    ((hp.comp (((measurable_fst.comp measurable_fst).prodMk
      (hd.comp measurable_fst)).prodMk measurable_snd)).sub hp) measurable_const

lemma integrable_gain (eligible : Set (T×A)) (he : MeasurableSet eligible)
    (dev : T×A → A) (hd : Measurable dev)
    (pay : (T×A)×Ω → ℝ) (hp : Measurable pay)
    (B : ℝ) (hB0 : 0≤ B) (hB : ∀ z,‖pay z‖≤ B) :
    Integrable (gain eligible dev pay) ((π.1 : Measure (T×A)).prod ν) := by
  apply Integrable.of_bound (measurable_gain eligible he dev hd pay hp).aestronglyMeasurable (2*B)
  apply Eventually.of_forall
  intro z
  by_cases hz : z.1∈eligible
  · rw [gain,if_pos hz]
    exact (norm_sub_le _ _).trans (by linarith [hB ((z.1.1,dev z.1),z.2),hB z])
  · simp only [gain,if_neg hz,norm_zero]
    positivity

theorem original_integrated_noisy_IC (eligible : Set (T×A)) (he : MeasurableSet eligible)
    (dev : T×A → A) (hd : Measurable dev)
    (pay : (T×A)×Ω → ℝ) (hp : Measurable pay)
    (B : ℝ) (hB0 : 0≤ B) (hB : ∀ z,‖pay z‖≤ B)
    (hC1 : AllActionOptimal π (expected ν pay)) :
    (∫ z,gain eligible dev pay z ∂((π.1 : Measure (T×A)).prod ν))≤0 := by
  rw [integral_prod _ (integrable_gain μ π ν eligible he dev hd pay hp B hB0 hB)]
  apply integral_nonpos_of_ae
  filter_upwards [hC1] with x hx
  by_cases he' : x∈eligible
  · simp only [gain,if_pos he']
    rw [integral_sub (integrable_fixed_pay ν pay hp B hB (x.1,dev x))
      (integrable_fixed_pay ν pay hp B hB x)]
    exact sub_nonpos.mpr (hx (dev x))
  · simp [gain,he']

theorem weighted_original_integrated_noisy_IC (h : ℝ) (hh : 0≤ h)
    (eligible : Set (T×A)) (he : MeasurableSet eligible)
    (dev : T×A → A) (hd : Measurable dev)
    (pay : (T×A)×Ω → ℝ) (hp : Measurable pay)
    (B : ℝ) (hB0 : 0≤ B) (hB : ∀ z,‖pay z‖≤ B)
    (hC1 : AllActionOptimal π (expected ν pay)) :
    (∫ z,gain eligible dev pay z ∂
      ((ENNReal.ofReal h • (π.1 : Measure (T×A))).prod ν))≤0 := by
  rw [Measure.prod_smul_left,integral_smul_measure,ENNReal.toReal_ofReal hh]
  exact mul_nonpos_of_nonneg_of_nonpos hh
    (original_integrated_noisy_IC μ π ν eligible he dev hd pay hp B hB0 hB hC1)

end FCAppendix.Affine.Tail04.NoisyCarrierIC
