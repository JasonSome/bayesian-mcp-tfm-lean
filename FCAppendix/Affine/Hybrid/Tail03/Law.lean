import FCAppendix.PayOnce.Tails
import Mathlib.Probability.Distributions.Pareto
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib

noncomputable section
namespace FCAppendix.Affine.Hybrid.Tail03
open MeasureTheory ProbabilityTheory Set Filter Topology

structure LawInput where
  s : ℝ
  h : ℝ
  a : ℝ
  d0 : ℝ
  w : ℝ
  vA : ℝ
  zeta : ℝ
  M : ℝ
  s_large : (1 : ℝ) / 100 < s
  h_pos : 0 < h
  a_pos : 0 < a
  masses : s + h + a = 1
  d0_pos : 0 < d0
  w_pos : 0 < w
  zeta_pos : 0 < zeta
  zeta_lt_one : zeta < 1
  low_partial : d0 < 2 - w
  partial_bulk : 2 + w < vA - w
  bulk_tail : vA + w < M

namespace LawInput

theorem s_pos (p : LawInput) : 0 < p.s := by linarith [p.s_large]
theorem M_pos (p : LawInput) : 0 < p.M := by
  linarith [p.d0_pos, p.w_pos, p.low_partial, p.partial_bulk, p.bulk_tail]

theorem ordered_bands (p : LawInput) :
    0 < p.d0 ∧ p.d0 < 2-p.w ∧ 2-p.w < 2+p.w ∧
    2+p.w < p.vA-p.w ∧ p.vA-p.w < p.vA+p.w ∧ p.vA+p.w < p.M := by
  exact ⟨p.d0_pos, p.low_partial, by linarith [p.w_pos], p.partial_bulk,
    by linarith [p.w_pos], p.bulk_tail⟩

end LawInput

def bandPDF (l u v : ℝ) : ℝ :=
  if v ∈ Icc l u then 1 / (u-l) else 0

def bandMeasure (l u : ℝ) : Measure ℝ :=
  volume.withDensity (fun v => ENNReal.ofReal (bandPDF l u v))

theorem bandPDF_measurable (l u : ℝ) : Measurable (bandPDF l u) := by
  exact measurable_const.ite measurableSet_Icc measurable_const

theorem bandPDF_nonneg {l u : ℝ} (hlu : l < u) (v : ℝ) :
    0 ≤ bandPDF l u v := by
  unfold bandPDF
  split_ifs <;> positivity

theorem bandMeasure_eq_smul_restrict (l u : ℝ) :
    bandMeasure l u = ENNReal.ofReal (1/(u-l)) • volume.restrict (Icc l u) := by
  have he : (fun v => ENNReal.ofReal (bandPDF l u v)) =
      (Icc l u).indicator (fun _ => ENNReal.ofReal (1/(u-l))) := by
    funext v
    by_cases hv : v ∈ Icc l u <;> simp [bandPDF, hv]
  rw [bandMeasure, he, withDensity_indicator measurableSet_Icc, withDensity_const]

theorem bandMeasure_probability {l u : ℝ} (hlu : l < u) :
    IsProbabilityMeasure (bandMeasure l u) := by
  constructor
  rw [bandMeasure_eq_smul_restrict]
  simp only [Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Icc,
    smul_eq_mul]
  rw [← ENNReal.ofReal_mul (by positivity), one_div_mul_cancel (sub_pos.mpr hlu).ne']
  norm_num

instance bandMeasure_atomless (l u : ℝ) : NullSingletonClass (bandMeasure l u) := by
  unfold bandMeasure
  infer_instance

theorem bandMeasure_supported (l u : ℝ) :
    ∀ᵐ v ∂bandMeasure l u, v ∈ Icc l u := by
  rw [bandMeasure_eq_smul_restrict]
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _

theorem bandMeasure_Ioi_zero (l u t : ℝ) (hut : u ≤ t) :
    bandMeasure l u (Ioi t) = 0 := by
  have hi : Ioi t ∩ Icc l u = (∅ : Set ℝ) := by
    ext v
    simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_empty_iff_false, iff_false]
    rintro ⟨hvt, hvl, hvu⟩
    linarith
  rw [bandMeasure_eq_smul_restrict]
  simp [Measure.restrict_apply, hi]

theorem bandMeasure_Iic_zero (l u t : ℝ) (htl : t < l) :
    bandMeasure l u (Iic t) = 0 := by
  have hi : Iic t ∩ Icc l u = (∅ : Set ℝ) := by
    ext v
    simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_empty_iff_false, iff_false]
    rintro ⟨hvt, hvl, hvu⟩
    linarith
  rw [bandMeasure_eq_smul_restrict]
  simp [Measure.restrict_apply, hi]

theorem bandMeasure_Iic {l u t : ℝ} (hlu : l < u) (ht : t ∈ Icc l u) :
    (bandMeasure l u).real (Iic t) = (t-l)/(u-l) := by
  have hi : Iic t ∩ Icc l u = Icc l t := by
    ext v
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · rintro ⟨hvt, hvl, hvu⟩; exact ⟨hvl, hvt⟩
    · rintro ⟨hvl, hvt⟩; exact ⟨hvt, hvl, hvt.trans ht.2⟩
  rw [Measure.real, bandMeasure_eq_smul_restrict, Measure.smul_apply,
    Measure.restrict_apply measurableSet_Iic, hi, Real.volume_Icc]
  simp only [smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sub_nonneg.mpr ht.1),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 1/(u-l))]
  ring

theorem bandMeasure_integrable_id (l u : ℝ) :
    Integrable (fun v : ℝ => v) (bandMeasure l u) := by
  rw [bandMeasure_eq_smul_restrict]
  have hi : IntegrableOn (fun v : ℝ => v) (Icc l u) volume := continuous_id.integrableOn_Icc
  exact hi.smul_measure ENNReal.ofReal_ne_top

theorem pareto_supported (M : ℝ) :
    ∀ᵐ v ∂paretoMeasure M 10, M ≤ v := by
  rw [ae_iff]
  have he : {v : ℝ | ¬M≤v}=Iio M := by ext v; exact not_le
  rw [he]
  rw [paretoMeasure, withDensity_apply _ measurableSet_Iio]
  exact lintegral_paretoPDF_of_le le_rfl

instance pareto_atomless (M : ℝ) : NullSingletonClass (paretoMeasure M 10) := by
  unfold paretoMeasure
  infer_instance

theorem pareto_tail {M t : ℝ} (hM : 0 < M) (hMt : M ≤ t) :
    (paretoMeasure M 10).real (Ioi t) = (M/t)^10 := by
  have hh := PayOnce.Limit.paretoMeasure_tail hM (by norm_num : (0:ℝ)<10) t hMt
  rw [←Real.rpow_natCast (M/t) 10]
  exact hh

theorem pareto_density_times_value {M v : ℝ} (hM : 0 < M) (hv : M ≤ v) :
    paretoPDFReal M 10 v * v = 10 * M^10 * v^(-10 : ℝ) := by
  have hv0 : 0 < v := hM.trans_le hv
  simp only [paretoPDFReal, if_pos hv]
  rw [show M^(10:ℝ)=M^10 from Real.rpow_natCast M 10]
  have he : v^(-(10+1) : ℝ) * v = v^(-10 : ℝ) := by
    calc
      v^(-(10+1) : ℝ) * v = v^(-(10+1) : ℝ) * v^(1 : ℝ) := by
        rw [Real.rpow_one]
      _ = v^((-(10+1) : ℝ)+1) := (Real.rpow_add hv0 _ _).symm
      _ = v^(-10 : ℝ) := by norm_num
  rw [mul_assoc, he]

theorem pareto_integrable_id {M : ℝ} (hM : 0 < M) :
    Integrable (fun v : ℝ => v) (paretoMeasure M 10) := by
  unfold paretoMeasure
  apply (integrable_withDensity_iff_integrable_smul'
    (measurable_paretoPDFReal M 10).ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).2
  have hi : IntegrableOn (fun v : ℝ => 10*M^10*v^(-10 : ℝ)) (Ici M) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact (integrableOn_Ioi_rpow_of_lt (by norm_num : (-10:ℝ)< -1) hM).const_mul _
  have hg : (fun v : ℝ => (paretoPDF M 10 v).toReal • v) =
      (Ici M).indicator (fun v : ℝ => 10*M^10*v^(-10 : ℝ)) := by
    funext v
    rw [paretoPDF, ENNReal.toReal_ofReal
      (paretoPDFReal_nonneg hM.le (by norm_num) v), smul_eq_mul]
    by_cases hv : M ≤ v
    · change paretoPDFReal M 10 v * v = if M ≤ v then _ else 0
      rw [if_pos hv]
      exact pareto_density_times_value hM hv
    · change paretoPDFReal M 10 v * v = if M ≤ v then _ else 0
      simp [paretoPDFReal, hv]
  change Integrable (fun v : ℝ => (paretoPDF M 10 v).toReal • v) volume
  rw [hg]
  exact hi.integrable_indicator measurableSet_Ici

theorem integral_pareto_id {M : ℝ} (hM : 0 < M) :
    (∫ v : ℝ, v ∂paretoMeasure M 10) = 10*M/9 := by
  change (∫v : ℝ,v ∂volume.withDensity (fun v => ENNReal.ofReal (paretoPDFReal M 10 v))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_paretoPDFReal M 10).ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have hg : (fun v : ℝ => (paretoPDF M 10 v).toReal • v) =
      (Ici M).indicator (fun v : ℝ => 10*M^10*v^(-10 : ℝ)) := by
    funext v
    rw [paretoPDF, ENNReal.toReal_ofReal
      (paretoPDFReal_nonneg hM.le (by norm_num) v), smul_eq_mul]
    by_cases hv : M ≤ v
    · change paretoPDFReal M 10 v * v = if M ≤ v then _ else 0
      rw [if_pos hv]
      exact pareto_density_times_value hM hv
    · change paretoPDFReal M 10 v * v = if M ≤ v then _ else 0
      simp [paretoPDFReal, hv]
  change (∫ v : ℝ,(paretoPDF M 10 v).toReal • v) = _
  rw [hg, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-10:ℝ)< -1) hM]
  norm_num
  field_simp [hM.ne']

def mixtureMeasure (p : LawInput) : Measure ℝ :=
  ENNReal.ofReal p.s • bandMeasure 0 p.d0 +
  ENNReal.ofReal p.h • bandMeasure (2-p.w) (2+p.w) +
  ENNReal.ofReal (p.a*(1-p.zeta)) • bandMeasure (p.vA-p.w) (p.vA+p.w) +
  ENNReal.ofReal (p.a*p.zeta) • paretoMeasure p.M 10

instance mixture_probability (p : LawInput) : IsProbabilityMeasure (mixtureMeasure p) := by
  letI := bandMeasure_probability p.d0_pos
  letI := bandMeasure_probability (show 2-p.w < 2+p.w by linarith [p.w_pos])
  letI := bandMeasure_probability (show p.vA-p.w < p.vA+p.w by linarith [p.w_pos])
  letI := isProbabilityMeasure_paretoMeasure p.M_pos (by norm_num : (0:ℝ)<10)
  constructor
  simp only [mixtureMeasure, Measure.add_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  have hs0 := p.s_pos
  have hh0 := p.h_pos
  have ha0 := p.a_pos
  have hz0 := p.zeta_pos
  have hz1 : 0 < 1-p.zeta := sub_pos.mpr p.zeta_lt_one
  have hab : 0 ≤ p.a*(1-p.zeta) := by positivity
  rw [← ENNReal.ofReal_add p.s_pos.le p.h_pos.le,
    ← ENNReal.ofReal_add (by positivity) hab,
    ← ENNReal.ofReal_add (by positivity)
      (mul_nonneg p.a_pos.le p.zeta_pos.le)]
  have he : p.s+p.h+p.a*(1-p.zeta)+p.a*p.zeta=1 := by nlinarith [p.masses]
  rw [he, ENNReal.ofReal_one]

instance mixture_atomless (p : LawInput) : NullSingletonClass (mixtureMeasure p) := by
  constructor
  intro v
  simp [mixtureMeasure, Measure.add_apply, Measure.smul_apply]

def mixFourComponents (p : LawInput) : ProbabilityMeasure ℝ :=
  ⟨mixtureMeasure p, inferInstance⟩

def fixedUpperValueMeasure (p : LawInput) : Measure ℝ :=
  ENNReal.ofReal (1-p.zeta) • bandMeasure (p.vA-p.w) (p.vA+p.w) +
  ENNReal.ofReal p.zeta • paretoMeasure p.M 10

instance fixedUpperValue_probability (p : LawInput) :
    IsProbabilityMeasure (fixedUpperValueMeasure p) := by
  letI := bandMeasure_probability (show p.vA-p.w < p.vA+p.w by linarith [p.w_pos])
  letI := isProbabilityMeasure_paretoMeasure p.M_pos (by norm_num : (0:ℝ)<10)
  constructor
  simp only [fixedUpperValueMeasure, Measure.add_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr p.zeta_lt_one.le) p.zeta_pos.le]
  norm_num

instance fixedUpperValue_atomless (p : LawInput) :
    NullSingletonClass (fixedUpperValueMeasure p) := by
  constructor
  intro v
  simp [fixedUpperValueMeasure, Measure.add_apply, Measure.smul_apply]

def fixedUpperValueLaw (p : LawInput) : ProbabilityMeasure ℝ :=
  ⟨fixedUpperValueMeasure p, inferInstance⟩

def fixedUpperMeasure (p : LawInput) : Measure ℝ :=
  ENNReal.ofReal p.a • fixedUpperValueMeasure p

instance fixedUpper_finite (p : LawInput) : IsFiniteMeasure (fixedUpperMeasure p) := by
  constructor
  simp only [fixedUpperMeasure, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.ofReal_lt_top

instance fixedUpper_atomless (p : LawInput) : NullSingletonClass (fixedUpperMeasure p) := by
  constructor
  intro v
  simp [fixedUpperMeasure, Measure.smul_apply]

theorem fixedUpper_supported (p : LawInput) :
    ∀ᵐ v ∂fixedUpperValueMeasure p, p.vA-p.w ≤ v := by
  apply ae_add_measure_iff.mpr
  constructor
  · exact Measure.ae_smul_measure
      ((bandMeasure_supported (p.vA-p.w) (p.vA+p.w)).mono fun _ hv => hv.1) _
  · apply Measure.ae_smul_measure _ _
    filter_upwards [pareto_supported p.M] with v hv
    linarith [p.bulk_tail, p.w_pos]

theorem fixedUpper_mass (p : LawInput) : (fixedUpperMeasure p).real univ = p.a := by
  simp [fixedUpperMeasure, Measure.real, Measure.smul_apply,
    ENNReal.toReal_ofReal p.a_pos.le]

theorem fixedUpper_tail (p : LawInput) {v : ℝ} (hv : p.M ≤ v) :
    (fixedUpperMeasure p).real (Ioi v) = p.a*p.zeta*(p.M/v)^10 := by
  have hAv : p.vA+p.w ≤ v := p.bulk_tail.le.trans hv
  simp only [fixedUpperMeasure, fixedUpperValueMeasure, Measure.real,
    Measure.smul_apply, Measure.add_apply,
    bandMeasure_Ioi_zero (p.vA-p.w) (p.vA+p.w) v hAv,
    smul_eq_mul, mul_zero, zero_add, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal p.a_pos.le, ENNReal.toReal_ofReal p.zeta_pos.le]
  rw [show ((paretoMeasure p.M 10) (Ioi v)).toReal=(p.M/v)^10 from pareto_tail p.M_pos hv]
  ring

theorem commonLaw_fixedUpper_decomposition (p : LawInput) :
    mixtureMeasure p =
      ENNReal.ofReal p.s • bandMeasure 0 p.d0 +
      ENNReal.ofReal p.h • bandMeasure (2-p.w) (2+p.w) + fixedUpperMeasure p := by
  rw [fixedUpperMeasure, fixedUpperValueMeasure, smul_add, smul_smul, smul_smul,
    ← ENNReal.ofReal_mul p.a_pos.le, ← ENNReal.ofReal_mul p.a_pos.le]
  simp only [mixtureMeasure, add_assoc]

theorem commonLaw_restrict_fixedUpper (p : LawInput) :
    (mixtureMeasure p).restrict (Ioi (p.vA-p.w))=fixedUpperMeasure p := by
  have h0 : p.d0≤ p.vA-p.w := by
    linarith [p.low_partial,p.partial_bulk,p.w_pos]
  have h2 : 2+p.w≤ p.vA-p.w := p.partial_bulk.le
  have hz0 := Measure.restrict_eq_zero.mpr
    (bandMeasure_Ioi_zero 0 p.d0 (p.vA-p.w) h0)
  have hz2 := Measure.restrict_eq_zero.mpr
    (bandMeasure_Ioi_zero (2-p.w) (2+p.w) (p.vA-p.w) h2)
  have hstrict : ∀ᵐv ∂fixedUpperValueMeasure p,p.vA-p.w< v := by
    filter_upwards [fixedUpper_supported p,(fixedUpperValueMeasure p).ae_ne (p.vA-p.w)]
      with v hv hne
    exact lt_of_le_of_ne hv (Ne.symm hne)
  have hweighted : ∀ᵐv ∂fixedUpperMeasure p,v∈Ioi (p.vA-p.w) :=
    Measure.ae_smul_measure hstrict _
  rw [commonLaw_fixedUpper_decomposition p]
  simp only [Measure.restrict_add,Measure.restrict_smul,hz0,hz2,smul_zero,zero_add,
    Measure.restrict_eq_self_of_ae_mem hweighted]

theorem commonLaw_fixedUpper_conditional (p : LawInput) :
    ENNReal.ofReal (1/p.a) • (mixtureMeasure p).restrict (Ioi (p.vA-p.w)) =
      fixedUpperValueMeasure p := by
  have ha := p.a_pos
  rw [commonLaw_restrict_fixedUpper p,fixedUpperMeasure,smul_smul,
    ← ENNReal.ofReal_mul (by positivity : 0≤1/p.a),
    one_div_mul_cancel p.a_pos.ne',ENNReal.ofReal_one,one_smul]

def mixturePDF (p : LawInput) (v : ℝ) : ℝ :=
  p.s*bandPDF 0 p.d0 v + p.h*bandPDF (2-p.w) (2+p.w) v +
  (p.a*(1-p.zeta))*bandPDF (p.vA-p.w) (p.vA+p.w) v +
  (p.a*p.zeta)*paretoPDFReal p.M 10 v

theorem mixturePDF_measurable (p : LawInput) : Measurable (mixturePDF p) := by
  unfold mixturePDF
  exact (((measurable_const.mul (bandPDF_measurable _ _)).add
    (measurable_const.mul (bandPDF_measurable _ _))).add
    (measurable_const.mul (bandPDF_measurable _ _))).add
    (measurable_const.mul (measurable_paretoPDFReal _ _))

theorem mixturePDF_nonneg (p : LawInput) (v : ℝ) : 0 ≤ mixturePDF p v := by
  unfold mixturePDF
  have hl := bandPDF_nonneg p.d0_pos v
  have hh := bandPDF_nonneg (show 2-p.w < 2+p.w by linarith [p.w_pos]) v
  have ha := bandPDF_nonneg (show p.vA-p.w < p.vA+p.w by linarith [p.w_pos]) v
  have hp := paretoPDFReal_nonneg p.M_pos.le (by norm_num : (0:ℝ)≤10) v
  have hs0 := p.s_pos
  have hh0 := p.h_pos
  have ha0 := p.a_pos
  have hz0 := p.zeta_pos
  have hz1 : 0 < 1-p.zeta := sub_pos.mpr p.zeta_lt_one
  positivity

theorem mixture_eq_withDensity (p : LawInput) :
    mixtureMeasure p = volume.withDensity (fun v => ENNReal.ofReal (mixturePDF p v)) := by
  have he : (fun v => ENNReal.ofReal (mixturePDF p v)) =
      (fun v => ENNReal.ofReal p.s * ENNReal.ofReal (bandPDF 0 p.d0 v)) +
      (fun v => ENNReal.ofReal p.h * ENNReal.ofReal (bandPDF (2-p.w) (2+p.w) v)) +
      (fun v => ENNReal.ofReal (p.a*(1-p.zeta)) *
        ENNReal.ofReal (bandPDF (p.vA-p.w) (p.vA+p.w) v)) +
      (fun v => ENNReal.ofReal (p.a*p.zeta) * paretoPDF p.M 10 v) := by
    funext v
    have hlow := bandPDF_nonneg p.d0_pos v
    have hpartial := bandPDF_nonneg (show 2-p.w < 2+p.w by linarith [p.w_pos]) v
    have hbulk := bandPDF_nonneg (show p.vA-p.w < p.vA+p.w by linarith [p.w_pos]) v
    have htail := paretoPDFReal_nonneg p.M_pos.le (by norm_num : (0:ℝ)≤10) v
    have hs0 := p.s_pos
    have hh0 := p.h_pos
    have ha0 := p.a_pos
    have hz0 := p.zeta_pos
    have hz1 : 0 < 1-p.zeta := sub_pos.mpr p.zeta_lt_one
    simp only [mixturePDF, Pi.add_apply, paretoPDF]
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity)]
    simp only [ENNReal.ofReal_mul p.s_pos.le, ENNReal.ofReal_mul p.h_pos.le,
      ENNReal.ofReal_mul (show 0 ≤ p.a*(1-p.zeta) by positivity),
      ENNReal.ofReal_mul (mul_nonneg p.a_pos.le p.zeta_pos.le)]
  have h0 : Measurable (fun v => ENNReal.ofReal p.s *
      ENNReal.ofReal (bandPDF 0 p.d0 v)) :=
    measurable_const.mul (bandPDF_measurable _ _).ennreal_ofReal
  have h1 : Measurable (fun v => ENNReal.ofReal p.h *
      ENNReal.ofReal (bandPDF (2-p.w) (2+p.w) v)) :=
    measurable_const.mul (bandPDF_measurable _ _).ennreal_ofReal
  have h2 : Measurable (fun v => ENNReal.ofReal (p.a*(1-p.zeta)) *
      ENNReal.ofReal (bandPDF (p.vA-p.w) (p.vA+p.w) v)) :=
    measurable_const.mul (bandPDF_measurable _ _).ennreal_ofReal
  rw [he, withDensity_add_left ((h0.add h1).add h2),
    withDensity_add_left (h0.add h1), withDensity_add_left h0]
  change mixtureMeasure p =
    volume.withDensity (ENNReal.ofReal p.s • (fun v => ENNReal.ofReal (bandPDF 0 p.d0 v))) +
    volume.withDensity (ENNReal.ofReal p.h • (fun v => ENNReal.ofReal (bandPDF (2-p.w) (2+p.w) v))) +
    volume.withDensity (ENNReal.ofReal (p.a*(1-p.zeta)) •
      (fun v => ENNReal.ofReal (bandPDF (p.vA-p.w) (p.vA+p.w) v))) +
    volume.withDensity (ENNReal.ofReal (p.a*p.zeta) • paretoPDF p.M 10)
  rw [withDensity_smul' _ _ ENNReal.ofReal_ne_top,
    withDensity_smul' _ _ ENNReal.ofReal_ne_top,
    withDensity_smul' _ _ ENNReal.ofReal_ne_top,
    withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  rfl

theorem commonLaw_integrable_id (p : LawInput) :
    Integrable (fun v : ℝ => v) (mixtureMeasure p) := by
  apply Integrable.add_measure
  · apply Integrable.add_measure
    · apply Integrable.add_measure
      · exact (bandMeasure_integrable_id 0 p.d0).smul_measure ENNReal.ofReal_ne_top
      · exact (bandMeasure_integrable_id (2-p.w) (2+p.w)).smul_measure ENNReal.ofReal_ne_top
    · exact (bandMeasure_integrable_id (p.vA-p.w) (p.vA+p.w)).smul_measure ENNReal.ofReal_ne_top
  · exact (pareto_integrable_id p.M_pos).smul_measure ENNReal.ofReal_ne_top

theorem commonLaw_nonnegative (p : LawInput) :
    ∀ᵐ v ∂mixtureMeasure p, 0 ≤ v := by
  apply ae_add_measure_iff.mpr
  refine ⟨ae_add_measure_iff.mpr ⟨ae_add_measure_iff.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact Measure.ae_smul_measure ((bandMeasure_supported 0 p.d0).mono fun _ h => h.1) _
  · apply Measure.ae_smul_measure _ _
    filter_upwards [bandMeasure_supported (2-p.w) (2+p.w)] with v hv
    exact p.d0_pos.le.trans (p.low_partial.le.trans hv.1)
  · apply Measure.ae_smul_measure _ _
    filter_upwards [bandMeasure_supported (p.vA-p.w) (p.vA+p.w)] with v hv
    linarith [p.low_partial, p.partial_bulk, p.d0_pos, p.w_pos, hv.1]
  · exact Measure.ae_smul_measure ((pareto_supported p.M).mono
      (fun _ hv => p.M_pos.le.trans hv)) _

theorem commonLaw_tail (p : LawInput) {t : ℝ} (ht : p.M ≤ t) :
    (mixtureMeasure p).real (Ioi t) = p.a*p.zeta*(p.M/t)^10 := by
  have h0 : p.d0 ≤ t := by linarith [p.low_partial, p.partial_bulk, p.bulk_tail, p.w_pos]
  have h2 : 2+p.w ≤ t := by linarith [p.partial_bulk, p.bulk_tail, p.w_pos]
  have hA : p.vA+p.w ≤ t := p.bulk_tail.le.trans ht
  have htail := pareto_tail p.M_pos ht
  simp only [Measure.real, mixtureMeasure, Measure.add_apply, Measure.smul_apply,
    bandMeasure_Ioi_zero 0 p.d0 t h0,
    bandMeasure_Ioi_zero (2-p.w) (2+p.w) t h2,
    bandMeasure_Ioi_zero (p.vA-p.w) (p.vA+p.w) t hA,
    smul_eq_mul, mul_zero, zero_add, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (mul_nonneg p.a_pos.le p.zeta_pos.le)]
  exact congrArg (fun x => p.a*p.zeta*x) htail

theorem pareto_restrict_above {M t : ℝ} (hM : 0 < M) (hMt : M ≤ t) :
    (paretoMeasure M 10).restrict (Ioi t) =
      ENNReal.ofReal ((M/t)^10) • paretoMeasure t 10 := by
  have ht : 0 < t := hM.trans_le hMt
  change (volume.withDensity (paretoPDF M 10)).restrict (Ioi t) =
    ENNReal.ofReal ((M/t)^10) • volume.withDensity (paretoPDF t 10)

  rw [restrict_withDensity measurableSet_Ioi,
    ← withDensity_indicator measurableSet_Ioi,
    ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  apply withDensity_congr_ae
  filter_upwards [volume.ae_ne t] with v hvt
  change (if t < v then paretoPDF M 10 v else 0) =
    ENNReal.ofReal ((M/t)^10) * paretoPDF t 10 v
  by_cases hv : t < v
  · rw [if_pos hv]
    have hMv : M ≤ v := hMt.trans hv.le
    simp only [paretoPDF, paretoPDFReal, if_pos hMv, if_pos hv.le]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (M/t)^10)]
    congr 1
    rw [show (M : ℝ)^(10 : ℝ)=M^10 by norm_num,
      show (t : ℝ)^(10 : ℝ)=t^10 by norm_num]
    field_simp [ht.ne']
  · have hlt : v < t := lt_of_le_of_ne (le_of_not_gt hv) hvt
    rw [if_neg hv]
    simp [paretoPDF, paretoPDFReal, not_le.mpr hlt]

theorem commonLaw_restrict_tail (p : LawInput) {t : ℝ} (ht : p.M ≤ t) :
    (mixtureMeasure p).restrict (Ioi t) =
      ENNReal.ofReal (p.a*p.zeta*(p.M/t)^10) • paretoMeasure t 10 := by
  have h0 : p.d0 ≤ t := by linarith [p.low_partial, p.partial_bulk, p.bulk_tail, p.w_pos]
  have h2 : 2+p.w ≤ t := by linarith [p.partial_bulk, p.bulk_tail, p.w_pos]
  have hA : p.vA+p.w ≤ t := p.bulk_tail.le.trans ht
  have hz0 := Measure.restrict_eq_zero.mpr (bandMeasure_Ioi_zero 0 p.d0 t h0)
  have hz2 := Measure.restrict_eq_zero.mpr (bandMeasure_Ioi_zero (2-p.w) (2+p.w) t h2)
  have hzA := Measure.restrict_eq_zero.mpr (bandMeasure_Ioi_zero (p.vA-p.w) (p.vA+p.w) t hA)
  rw [mixtureMeasure]
  simp only [Measure.restrict_add, Measure.restrict_smul, hz0, hz2, hzA,
    smul_zero, zero_add]
  rw [pareto_restrict_above p.M_pos ht, smul_smul,
    ← ENNReal.ofReal_mul (mul_nonneg p.a_pos.le p.zeta_pos.le)]

theorem commonLaw_tail_conditional (p : LawInput) {t : ℝ} (ht : p.M≤ t) :
    ENNReal.ofReal (1/(p.a*p.zeta*(p.M/t)^10)) •
      (mixtureMeasure p).restrict (Ioi t) = paretoMeasure t 10 := by
  have ht0 : 0< t := p.M_pos.trans_le ht
  have ha := p.a_pos
  have hz := p.zeta_pos
  have hM := p.M_pos
  have hmass : 0< p.a*p.zeta*(p.M/t)^10 := by positivity
  rw [commonLaw_restrict_tail p ht,smul_smul,
    ← ENNReal.ofReal_mul (by positivity : 0≤1/(p.a*p.zeta*(p.M/t)^10)),
    one_div_mul_cancel hmass.ne',ENNReal.ofReal_one,one_smul]

theorem commonLaw_unbounded (p : LawInput) (K : ℝ) :
    0 < mixtureMeasure p (Ioi K) := by
  have hlarge : 0 < (mixtureMeasure p).real (Ioi (max p.M K)) := by
    rw [commonLaw_tail p (le_max_left _ _)]
    have hden : 0 < max p.M K := p.M_pos.trans_le (le_max_left _ _)
    have ha0 := p.a_pos
    have hz0 := p.zeta_pos
    have hM0 := p.M_pos
    positivity
  have hreal : 0 < (mixtureMeasure p).real (Ioi K) :=
    hlarge.trans_le (measureReal_mono (Ioi_subset_Ioi (le_max_right _ _)))
  exact (ENNReal.toReal_pos_iff.mp hreal).1

def efficientCutoff (p : LawInput) : ℝ := p.d0/(100*p.s)

theorem efficientCutoff_mem (p : LawInput) : efficientCutoff p ∈ Ioo 0 p.d0 := by
  have hs : 1 < 100*p.s := by linarith [p.s_large]
  have hd0 := p.d0_pos
  have hs0 := p.s_pos
  refine ⟨by unfold efficientCutoff; positivity, ?_⟩
  unfold efficientCutoff
  apply (div_lt_iff₀ (by positivity : 0 < 100*p.s)).2
  nlinarith [p.d0_pos]

theorem efficientCutoff_mass (p : LawInput) :
    (mixtureMeasure p).real (Iic (efficientCutoff p)) = 1/100 := by
  have hc := efficientCutoff_mem p
  have h2 : efficientCutoff p < 2-p.w := hc.2.trans p.low_partial
  have hA : efficientCutoff p < p.vA-p.w := by
    linarith [p.partial_bulk, p.w_pos]
  have hM : efficientCutoff p < p.M := by
    linarith [p.bulk_tail, p.w_pos]
  have htail0 : paretoMeasure p.M 10 (Iic (efficientCutoff p)) = 0 := by
    have hz : paretoMeasure p.M 10 (Iio p.M) = 0 := by
      rw [paretoMeasure, withDensity_apply _ measurableSet_Iio]
      exact lintegral_paretoPDF_of_le le_rfl
    exact measure_mono_null (show Iic (efficientCutoff p) ⊆ Iio p.M from
      fun v hv => lt_of_le_of_lt hv hM) hz
  simp only [Measure.real, mixtureMeasure, Measure.add_apply, Measure.smul_apply,
    bandMeasure_Iic_zero (2-p.w) (2+p.w) (efficientCutoff p) h2,
    bandMeasure_Iic_zero (p.vA-p.w) (p.vA+p.w) (efficientCutoff p) hA,
    htail0, smul_eq_mul, mul_zero, add_zero, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal p.s_pos.le]
  change p.s * (bandMeasure 0 p.d0).real (Iic (efficientCutoff p)) = 1/100
  rw [bandMeasure_Iic p.d0_pos ⟨hc.1.le, hc.2.le⟩]
  unfold efficientCutoff
  field_simp [p.s_pos.ne', p.d0_pos.ne']
  ring

theorem mixturePDF_on_low (p : LawInput) {v : ℝ} (hv : v ∈ Icc 0 p.d0) :
    mixturePDF p v = p.s/p.d0 := by
  have hp : v ∉ Icc (2-p.w) (2+p.w) := by intro h; linarith [p.low_partial, hv.2, h.1]
  have ha : v ∉ Icc (p.vA-p.w) (p.vA+p.w) := by
    intro h; linarith [p.low_partial, p.partial_bulk, p.w_pos, hv.2, h.1]
  have ht : ¬p.M ≤ v := by
    linarith [p.low_partial, p.partial_bulk, p.bulk_tail, p.w_pos, hv.2]
  simp [mixturePDF, bandPDF, hv, hp, ha, paretoPDFReal, ht, div_eq_mul_inv]

theorem mixturePDF_on_tail (p : LawInput) {v : ℝ} (hv : p.M ≤ v) :
    mixturePDF p v = p.a*p.zeta*paretoPDFReal p.M 10 v := by
  have h0 : v ∉ Icc 0 p.d0 := by
    intro h; linarith [p.low_partial, p.partial_bulk, p.bulk_tail, p.w_pos, h.2]
  have h2 : v ∉ Icc (2-p.w) (2+p.w) := by
    intro h; linarith [p.partial_bulk, p.bulk_tail, p.w_pos, h.2]
  have hA : v ∉ Icc (p.vA-p.w) (p.vA+p.w) := by
    intro h; linarith [p.bulk_tail, h.2]
  simp [mixturePDF, bandPDF, h0, h2, hA]

def PositiveDensityNearEfficientCutoffAndTail
    (F : ProbabilityMeasure ℝ) (cutoff M : ℝ) : Prop :=
  ∃ density : ℝ → ℝ, Measurable density ∧ (∀ v, 0 ≤ density v) ∧
    (F : Measure ℝ) = volume.withDensity (fun v => ENNReal.ofReal (density v)) ∧
    ∃ radius : ℝ, 0 < radius ∧
      (∀ v ∈ Ioo (cutoff-radius) (cutoff+radius), 0 < density v) ∧
      (∀ v, M ≤ v → 0 < density v)

theorem commonLaw_positive_density (p : LawInput) :
    PositiveDensityNearEfficientCutoffAndTail (mixFourComponents p) (efficientCutoff p) p.M := by
  let eps := min (efficientCutoff p) (p.d0-efficientCutoff p)/2
  have hc := efficientCutoff_mem p
  have heps : 0 < eps := by
    exact half_pos (lt_min hc.1 (sub_pos.mpr hc.2))
  refine ⟨mixturePDF p, mixturePDF_measurable p, mixturePDF_nonneg p,
    mixture_eq_withDensity p, eps, heps, ?_, ?_⟩
  · intro v hv
    have hlo := min_le_left (efficientCutoff p) (p.d0-efficientCutoff p)
    have hhi := min_le_right (efficientCutoff p) (p.d0-efficientCutoff p)
    have hvin : v ∈ Icc 0 p.d0 := by
      dsimp [eps] at hv
      constructor <;> linarith [hv.1, hv.2, hc.1, hc.2]
    rw [mixturePDF_on_low p hvin]
    exact div_pos p.s_pos p.d0_pos
  · intro v hv
    rw [mixturePDF_on_tail p hv]
    exact mul_pos (mul_pos p.a_pos p.zeta_pos)
      (paretoPDFReal_pos p.M_pos (by norm_num) hv)

def AtomlessUnboundedPositiveDensity (F : ProbabilityMeasure ℝ) (M : ℝ) : Prop :=
  NullSingletonClass (F : Measure ℝ) ∧
    (∀ K : ℝ, 0 < (F : Measure ℝ) (Ioi K)) ∧
    Integrable (fun v : ℝ => v) (F : Measure ℝ) ∧
    (∀ᵐ v ∂(F : Measure ℝ), 0 ≤ v) ∧
    ∃ cutoff : ℝ, 0 < cutoff ∧
      (F : Measure ℝ).real (Iic cutoff) = 1/100 ∧
      PositiveDensityNearEfficientCutoffAndTail F cutoff M

theorem uniform_pareto_mixture_properties (p : LawInput) :
    AtomlessUnboundedPositiveDensity (mixFourComponents p) p.M := by
  exact ⟨show NullSingletonClass (mixtureMeasure p) from inferInstance,
    commonLaw_unbounded p, commonLaw_integrable_id p,
    commonLaw_nonnegative p, efficientCutoff p, (efficientCutoff_mem p).1,
    efficientCutoff_mass p, commonLaw_positive_density p⟩

end FCAppendix.Affine.Hybrid.Tail03
