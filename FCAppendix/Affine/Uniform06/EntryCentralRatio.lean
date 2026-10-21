import FCAppendix.Affine.Uniform06.EntryConvolution
import FCAppendix.PayOnce.EndpointMoments

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryCentralRatio
open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.Affine.Uniform06
local notation "γ" => gaussianReal 0 1

theorem integrable_weighted_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Y : Ω → ℝ)
    (hY : Measurable Y) (hY0 : ∀ᵐ ω ∂μ, 0 ≤ Y ω) (j : ℕ)
    (hI : Integrable (fun ω => (Y ω)^(j+1)) μ) :
    IntegrableOn (fun t : ℝ => μ.real {ω | t < Y ω}*t^j) (Ioi (0 : ℝ)) := by
  let T : ℝ → ℝ := fun t => μ.real {ω | t < Y ω}*t^j
  have hm0 : Measurable (fun t : ℝ => μ {ω | t < Y ω}) :=
    Antitone.measurable (fun _ _ h => measure_mono (fun _ hω => h.trans_lt hω))
  have hm : Measurable T := hm0.ennreal_toReal.mul (measurable_id.pow_const j)
  have hT0 : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ T t := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact mul_nonneg measureReal_nonneg (pow_nonneg ht.le j)
  have hj : (0 : ℝ)<(j : ℝ)+1 := by positivity
  have hkey := lintegral_rpow_eq_lintegral_meas_lt_mul μ hY0 hY.aemeasurable hj
  have hp : (fun ω => ENNReal.ofReal ((Y ω)^((j : ℝ)+1)))=
      (fun ω => ENNReal.ofReal ((Y ω)^(j+1))) := by
    funext ω
    rw [← Nat.cast_add_one,Real.rpow_natCast]
  rw [hp] at hkey
  simp only [add_sub_cancel_right,Real.rpow_natCast] at hkey
  have hleft : (∫⁻ ω, ENNReal.ofReal ((Y ω)^(j+1)) ∂μ) ≠ ⊤ :=
    (lintegral_ofReal_ne_top_iff_integrable
      (hY.pow_const _).aestronglyMeasurable (hY0.mono fun _ h => pow_nonneg h _)).2 hI
  have htail : (∫⁻ t in Ioi (0 : ℝ),
      μ {ω | t < Y ω}*ENNReal.ofReal (t^j)) ≠ ⊤ := by
    intro htop
    rw [hkey,htop,ENNReal.mul_top (by exact ne_of_gt (ENNReal.ofReal_pos.mpr hj))] at hleft
    exact hleft rfl
  apply (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable.restrict hT0).1
  convert! htail using 1
  apply lintegral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  dsimp only [T]
  rw [ENNReal.ofReal_mul measureReal_nonneg,Measure.real,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

def positiveShortfall (z x : ℝ) : ℝ := max (z-x) 0

lemma measurable_positiveShortfall (z : ℝ) : Measurable (positiveShortfall z) := by
  unfold positiveShortfall
  fun_prop

lemma law_memLp_id (a b : ℝ) (p : NNReal) :
    MemLp (fun x : ℝ => x) p (EntryGaussianLaw.law a b) := by
  unfold EntryGaussianLaw.law
  exact (memLp_map_measure_iff aestronglyMeasurable_id
    (EntryGaussianLaw.continuous_sumFold a b).measurable.aemeasurable).2
      (EntryGaussianLaw.memLp_sumFold a b p)

lemma positiveShortfall_memLp (a b z : ℝ) (p : NNReal) :
    MemLp (positiveShortfall z) p (EntryGaussianLaw.law a b) := by
  exact ((memLp_const z).sub (law_memLp_id a b p)).pos_part

lemma strict_cdf_eq {a : ℝ} (ha : 0 < a) (b s : ℝ) :
    (EntryGaussianLaw.law a b).real (Iio s)=cdf (EntryGaussianLaw.law a b) s := by
  rw [cdf_eq_real,Measure.real,Measure.real]
  congr 1
  apply measure_congr
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (EntryGaussianLaw.singleton_null ha.ne' b s)]
    with x hx
  have hne : x ≠ s := by simpa only [mem_singleton_iff] using hx
  apply propext
  change (x < s ↔ x ≤ s)
  exact ⟨le_of_lt,fun h => lt_of_le_of_ne h hne⟩

lemma positiveShortfall_tail {a : ℝ} (ha : 0 < a) (b z : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    (EntryGaussianLaw.law a b).real {x | t < positiveShortfall z x}=
      cdf (EntryGaussianLaw.law a b) (z-t) := by
  have he : {x | t < positiveShortfall z x}=Iio (z-t) := by
    ext x
    simp only [positiveShortfall,mem_setOf_eq,lt_max_iff,mem_Iio]
    constructor
    · rintro (h | h)
      · linarith
      · exact (not_lt_of_ge ht h).elim
    · intro h
      exact Or.inl (by linarith)
  rw [he,strict_cdf_eq ha]

def success (a b z : ℝ) : ℝ := cdf (EntryGaussianLaw.law a b) z
def firstMoment (a b z : ℝ) : ℝ := ∫ x, positiveShortfall z x ∂EntryGaussianLaw.law a b
def secondMoment (a b z : ℝ) : ℝ := ∫ x, (positiveShortfall z x)^2 ∂EntryGaussianLaw.law a b
def survival (a b z t : ℝ) : ℝ := cdf (EntryGaussianLaw.law a b) (z-t)/success a b z

lemma survival_measurable (a b z : ℝ) : Measurable (survival a b z) :=
  (((monotone_cdf _).measurable.comp (measurable_const.sub measurable_id)).div_const _)

lemma success_pos {a : ℝ} (ha : 0 < a) (b z : ℝ) : 0 < success a b z :=
  EntryGaussianLaw.cdf_pos ha b z

lemma survival_nonneg {a : ℝ} (ha : 0 < a) (b z t : ℝ) : 0 ≤ survival a b z t :=
  div_nonneg (cdf_nonneg _ _) (success_pos ha b z).le

lemma survival_integrable {a : ℝ} (ha : 0 < a) (b z : ℝ) :
    IntegrableOn (survival a b z) (Ici (0 : ℝ)) := by
  have hT := integrable_weighted_tail (EntryGaussianLaw.law a b) (positiveShortfall z)
    (measurable_positiveShortfall z) (Eventually.of_forall fun _ => le_max_right _ _) 0
    (by simpa only [zero_add,pow_one] using
      (positiveShortfall_memLp a b z 1).integrable (by norm_num))
  have hI : IntegrableOn (fun t => cdf (EntryGaussianLaw.law a b) (z-t)) (Ioi (0 : ℝ)) := by
    apply hT.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    simp only [pow_zero,mul_one,positiveShortfall_tail ha b z ht.le]
  exact (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).2
    (hI.div_const (success a b z))

lemma weighted_survival_integrable {a : ℝ} (ha : 0 < a) (b z : ℝ) :
    Integrable (fun t => max t 0*survival a b z t) := by
  have hT := integrable_weighted_tail (EntryGaussianLaw.law a b) (positiveShortfall z)
    (measurable_positiveShortfall z) (Eventually.of_forall fun _ => le_max_right _ _) 1
    (positiveShortfall_memLp a b z 2).integrable_sq
  have hI : IntegrableOn (fun t => max t 0*survival a b z t) (Ioi (0 : ℝ)) := by
    apply (hT.div_const (success a b z)).congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    rw [positiveShortfall_tail ha b z ht.le,pow_one,max_eq_left ht.le]
    dsimp only [survival]
    ring
  apply hI.integrable_of_forall_notMem_eq_zero
  intro t ht
  have ht0 : t ≤ 0 := le_of_not_gt ht
  simp [max_eq_right ht0]

lemma firstMoment_tail {a : ℝ} (ha : 0 < a) (b z : ℝ) :
    firstMoment a b z = success a b z*∫ t in Ici (0 : ℝ), survival a b z t := by
  have he := FCAppendix.PayOnce.EndpointMoments.integral_pow_eq_tail
    (EntryGaussianLaw.law a b) (measurable_positiveShortfall z).aemeasurable
    (Eventually.of_forall fun _ => le_max_right _ _) 0
  norm_num only [Nat.cast_zero,zero_add,pow_one,pow_zero,mul_one,one_mul] at he
  unfold firstMoment
  rw [he,integral_Ici_eq_integral_Ioi,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  rw [positiveShortfall_tail ha b z ht.le]
  unfold survival
  field_simp [(success_pos ha b z).ne']

lemma secondMoment_tail {a : ℝ} (ha : 0 < a) (b z : ℝ) :
    secondMoment a b z = 2*success a b z*∫ t in Ici (0 : ℝ), t*survival a b z t := by
  have he := FCAppendix.PayOnce.EndpointMoments.integral_pow_eq_tail
    (EntryGaussianLaw.law a b) (measurable_positiveShortfall z).aemeasurable
    (Eventually.of_forall fun _ => le_max_right _ _) 1
  norm_num only [Nat.cast_one,one_add_one_eq_two,pow_one] at he
  have hI :
      (∫ t in Ioi (0 : ℝ), (EntryGaussianLaw.law a b).real {x | t < positiveShortfall z x}*t) =
        success a b z*(∫ t in Ici (0 : ℝ), t*survival a b z t) := by
    rw [integral_Ici_eq_integral_Ioi,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    rw [positiveShortfall_tail ha b z ht.le]
    unfold survival
    field_simp [(success_pos ha b z).ne']
  unfold secondMoment
  rw [he,hI]
  ring

lemma first_second_moment_pos {a : ℝ} (ha : 0 < a) (b z : ℝ) :
    0 < firstMoment a b z ∧ 0 < secondMoment a b z := by
  let μ := EntryGaussianLaw.law a b
  let f : ℝ → ℝ := (Iio (z-1)).indicator (fun _ => (1 : ℝ))
  have hf : Integrable f μ := (integrable_const (1 : ℝ)).indicator measurableSet_Iio
  have hp : 0 < ∫ x, f x ∂μ := by
    change 0 < ∫ x, (Iio (z-1)).indicator (fun _ => (1:ℝ)) x ∂EntryGaussianLaw.law a b
    rw [integral_indicator_const 1 measurableSet_Iio,smul_eq_mul,mul_one,
      strict_cdf_eq ha b (z-1)]
    exact EntryGaussianLaw.cdf_pos ha b (z-1)
  have hbound (x : ℝ) : f x ≤ positiveShortfall z x ∧ f x ≤ (positiveShortfall z x)^2 := by
    by_cases hx : x < z-1
    · have hY : 1 ≤ positiveShortfall z x := by
        exact (by linarith : 1 ≤ z-x).trans (le_max_left _ _)
      simp only [f,indicator_of_mem (show x ∈ Iio (z-1) from hx)]
      exact ⟨hY,by nlinarith [sq_nonneg (positiveShortfall z x-1)]⟩
    · simp only [f,indicator_of_notMem (show x ∉ Iio (z-1) from hx)]
      exact ⟨le_max_right _ _,sq_nonneg _⟩
  exact ⟨hp.trans_le (integral_mono hf
    ((positiveShortfall_memLp a b z 1).integrable (by norm_num)) (fun x => (hbound x).1)),
    hp.trans_le (integral_mono hf (positiveShortfall_memLp a b z 2).integrable_sq
      (fun x => (hbound x).2))⟩

theorem actual_central_moment_inequality {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (z : ℝ) :
    success a b z*secondMoment a b z ≤ 2*(firstMoment a b z)^2 := by
  have h := EntryHazard.survival_weighted_integral_le_square (survival a b z)
    (survival_measurable a b z) (fun t _ => survival_nonneg ha b z t)
    (survival_integrable ha b z) (weighted_survival_integrable ha b z)
    (fun x y hx hy => EntryConvolution.actual_positive_shortfall_survival_submul ha hb z hx hy)
  rw [firstMoment_tail ha,secondMoment_tail ha]
  have hp := mul_le_mul_of_nonneg_left h (show 0 ≤ 2*(success a b z)^2 by positivity)
  nlinarith [hp]

theorem actual_central_ratio_ge_half {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (z : ℝ) :
    (1/2 : ℝ) ≤ (firstMoment a b z)^2/(success a b z*secondMoment a b z) := by
  have hp := success_pos ha b z
  have hB := (first_second_moment_pos ha b z).2
  apply (le_div_iff₀ (mul_pos hp hB)).2
  nlinarith [actual_central_moment_inequality ha hb z]

end FCAppendix.Affine.Uniform06.EntryCentralRatio
