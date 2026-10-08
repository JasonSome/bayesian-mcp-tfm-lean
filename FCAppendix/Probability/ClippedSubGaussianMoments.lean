import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace FCAppendix.Probability
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators
variable {Ω : Type*} [MeasurableSpace Ω]

theorem integrable_rpow_of_bounded_nonneg (μ : Measure Ω) [IsFiniteMeasure μ]
    {Y : Ω → ℝ} (hY : Measurable Y) {D r : ℝ} (hr : 0 ≤ r)
    (hb : ∀ ω, Y ω ∈ Icc (0:ℝ) D) : Integrable (fun ω => (Y ω)^r) μ := by
  apply Integrable.of_bound (hY.pow_const r).aestronglyMeasurable (D^r)
  filter_upwards [] with ω
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (hb ω).1 _)]
  exact Real.rpow_le_rpow (hb ω).1 (hb ω).2 hr

theorem integrable_bounded_tail_weight (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) {D r : ℝ} (hr : 1 ≤ r) :
    IntegrableOn (fun t : ℝ => μ.real {ω | t ≤ Y ω}*t^(r-1)) (Ioc 0 D) := by
  have hm0 : Antitone (fun t : ℝ => μ {ω | t ≤ Y ω}) := by
    intro s t hst
    exact measure_mono (fun _ h => hst.trans h)
  have hm : Measurable (fun t : ℝ => μ.real {ω | t ≤ Y ω}) := hm0.measurable.ennreal_toReal
  apply Integrable.of_bound (hm.mul (measurable_id.pow_const (r-1))).aestronglyMeasurable.restrict
    (D^(r-1))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hp : 0 ≤ t^(r-1) := Real.rpow_nonneg ht.1.le _
  change ‖μ.real {ω | t ≤ Y ω}*t^(r-1)‖ ≤ D^(r-1)
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg measureReal_nonneg hp)]
  calc
    μ.real {ω | t ≤ Y ω}*t^(r-1) ≤ 1*t^(r-1) := mul_le_mul_of_nonneg_right measureReal_le_one hp
    _ ≤ D^(r-1) := by simpa only [one_mul] using Real.rpow_le_rpow ht.1.le ht.2 (by linarith)

theorem integral_rpow_eq_bounded_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} (hY : Measurable Y) {D r : ℝ} (hD : 0 ≤ D) (hr : 1 ≤ r)
    (hb : ∀ ω, Y ω ∈ Icc (0:ℝ) D) :
    (∫ ω, (Y ω)^r ∂μ) = r*∫ t in Ioc 0 D, μ.real {ω | t ≤ Y ω}*t^(r-1) := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hI := integrable_rpow_of_bounded_nonneg μ hY hrpos.le hb
  have hJ := integrable_bounded_tail_weight μ Y (D := D) hr
  have hkey := lintegral_rpow_eq_lintegral_meas_le_mul μ
    (Eventually.of_forall fun ω => (hb ω).1) hY.aemeasurable hrpos
  have hz : ∫⁻ t in Ioi D, μ {ω | t ≤ Y ω}*ENNReal.ofReal (t^(r-1)) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have he : {ω | t ≤ Y ω} = ∅ := by
      ext ω
      simp only [mem_setOf_eq,mem_empty_iff_false,iff_false]
      exact not_le.mpr ((hb ω).2.trans_lt ht)
    simp only [he,measure_empty,zero_mul,Pi.zero_apply]
  have htrunc : (∫⁻ t in Ioi 0, μ {ω | t ≤ Y ω}*ENNReal.ofReal (t^(r-1))) =
      ∫⁻ t in Ioc 0 D, μ {ω | t ≤ Y ω}*ENNReal.ofReal (t^(r-1)) := by
    rw [← Ioc_union_Ioi_eq_Ioi hD,lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl),hz,add_zero]
  rw [htrunc] at hkey
  have hJn : ∀ᵐ t ∂volume.restrict (Ioc 0 D), 0 ≤ μ.real {ω | t ≤ Y ω}*t^(r-1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_nonneg measureReal_nonneg (Real.rpow_nonneg ht.1.le _)
  have hJe : (∫⁻ t in Ioc 0 D, μ {ω | t ≤ Y ω}*ENNReal.ofReal (t^(r-1))) =
      ENNReal.ofReal (∫ t in Ioc 0 D, μ.real {ω | t ≤ Y ω}*t^(r-1)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hJ hJn]
    apply lintegral_congr
    intro t
    rw [ENNReal.ofReal_mul measureReal_nonneg,Measure.real,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hJe,← ofReal_integral_eq_lintegral_ofReal hI
    (Eventually.of_forall fun ω => Real.rpow_nonneg (hb ω).1 _)] at hkey
  have hh := congrArg ENNReal.toReal hkey
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hrpos.le,
    ENNReal.toReal_ofReal (integral_nonneg fun ω => Real.rpow_nonneg (hb ω).1 _),
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hJn)] using hh

noncomputable def gaussianMomentConstant (r C : ℝ) : ℝ :=
  r*∫ t : ℝ in Ioi 0, t^(r-1)*Real.exp (-t^2/C)

theorem integrable_gaussian_moment_weight {r C : ℝ} (hr : 1 ≤ r) (hC : 0 < C) :
    IntegrableOn (fun t : ℝ => t^(r-1)*Real.exp (-t^2/C)) (Ioi 0) := by
  have hh := integrableOn_rpow_mul_exp_neg_mul_sq (b := 1/C) (by positivity)
    (s := r-1) (by linarith)
  convert hh using 1
  funext t
  congr 1
  congr 1
  ring

theorem gaussianMomentConstant_nonneg {r C : ℝ} (hr : 1 ≤ r) :
    0 ≤ gaussianMomentConstant r C := by
  apply mul_nonneg (by linarith : 0 ≤ r)
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le

theorem bounded_rpow_moment_le_gaussian_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} (hY : Measurable Y) {D r α B C : ℝ}
    (hD : 0 ≤ D) (hr : 1 ≤ r) (hB : 0 ≤ B) (hC : 0 < C)
    (hb : ∀ ω, Y ω ∈ Icc (0:ℝ) D)
    (htail : ∀ ε : ℝ, 0 ≤ ε → μ.real {ω | ε ≤ Y ω} ≤ α+B*Real.exp (-ε^2/C)) :
    (∫ ω, (Y ω)^r ∂μ) ≤ D^r*α+B*gaussianMomentConstant r C := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hp : IntegrableOn (fun t : ℝ => t^(r-1)) (Ioc 0 D) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < r-1)).1
  have hg := integrable_gaussian_moment_weight hr hC
  have hg' := hg.mono_set (show Ioc (0:ℝ) D ⊆ Ioi 0 from Ioc_subset_Ioi_self)
  have hbound : (∫ t in Ioc 0 D, μ.real {ω | t ≤ Y ω}*t^(r-1)) ≤
      ∫ t in Ioc 0 D, α*t^(r-1)+B*(t^(r-1)*Real.exp (-t^2/C)) := by
    apply integral_mono_ae (integrable_bounded_tail_weight μ Y hr) ((hp.const_mul α).add (hg'.const_mul B))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hh := mul_le_mul_of_nonneg_right (htail t ht.1.le) (Real.rpow_nonneg ht.1.le (r-1))
    simp only [Pi.add_apply]
    nlinarith
  have hpi : (∫ t : ℝ in Ioc 0 D, t^(r-1)) = D^r/r := by
    rw [← intervalIntegral.integral_of_le hD,integral_rpow (Or.inl (by linarith : -1 < r-1))]
    simp only [sub_add_cancel,Real.zero_rpow hrpos.ne',sub_zero]
  have hgi : (∫ t : ℝ in Ioc 0 D, t^(r-1)*Real.exp (-t^2/C)) ≤
      ∫ t : ℝ in Ioi 0, t^(r-1)*Real.exp (-t^2/C) := by
    apply setIntegral_mono_set hg _ (Eventually.of_forall fun _ ht => ht.1)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le
  rw [integral_add (hp.const_mul α) (hg'.const_mul B),integral_const_mul,integral_const_mul,hpi] at hbound
  have hh := (mul_le_mul_of_nonneg_left hbound hrpos.le).trans
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hgi hB)) hrpos.le)
  calc
    (∫ ω, (Y ω)^r ∂μ) = r*∫ t in Ioc 0 D, μ.real {ω | t ≤ Y ω}*t^(r-1) :=
      integral_rpow_eq_bounded_tail μ hY hD hr hb
    _ ≤ r*(α*(D^r/r)+B*∫ t : ℝ in Ioi 0, t^(r-1)*Real.exp (-t^2/C)) := hh
    _ = D^r*α+B*gaussianMomentConstant r C := by
      dsimp only [gaussianMomentConstant]
      field_simp

theorem bounded_rpow_moment_le_scaled_gaussian_tail
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hY : Measurable Y)
    {D r α B C : ℝ} (hD : 0 ≤ D) (hr : 1 ≤ r) (hB : 0 ≤ B) (hC : 0 < C)
    (N : ℕ) (hN : 0 < N) (hb : ∀ ω, Y ω ∈ Icc (0:ℝ) D)
    (htail : ∀ ε : ℝ, 0 ≤ ε → μ.real {ω | ε ≤ Y ω} ≤ α+B*Real.exp (-(N:ℝ)*ε^2/C)) :
    (∫ ω, (Y ω)^r ∂μ) ≤
      D^r*α+B*gaussianMomentConstant r C*(N:ℝ)^(-r/2) := by
  let S := Real.sqrt (N:ℝ)
  let Z := fun ω => S*Y ω
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hS : 0 < S := Real.sqrt_pos.mpr hNR
  have hSsq : S^2 = (N:ℝ) := Real.sq_sqrt hNR.le
  have hZ : Measurable Z := hY.const_mul S
  have hZb (ω) : Z ω ∈ Icc (0:ℝ) (S*D) :=
    ⟨mul_nonneg hS.le (hb ω).1,mul_le_mul_of_nonneg_left (hb ω).2 hS.le⟩
  have hZtail (ε : ℝ) (hε : 0 ≤ ε) :
      μ.real {ω | ε ≤ Z ω} ≤ α+B*Real.exp (-ε^2/C) := by
    have he : {ω | ε ≤ Z ω} = {ω | ε/S ≤ Y ω} := by
      ext ω
      simp only [mem_setOf_eq,div_le_iff₀ hS,Z,mul_comm]
    have hexp : -(N:ℝ)*(ε/S)^2/C = -ε^2/C := by
      field_simp
      nlinarith [hSsq]
    rw [he]
    simpa only [hexp] using htail (ε/S) (by positivity)
  have hh := bounded_rpow_moment_le_gaussian_tail μ hZ (mul_nonneg hS.le hD) hr hB hC hZb hZtail
  have hZi : (∫ ω, (Z ω)^r ∂μ) = S^r*(∫ ω, (Y ω)^r ∂μ) := by
    simp_rw [Z,Real.mul_rpow hS.le (hb _).1]
    rw [integral_const_mul]
  have hSr : S^r = (N:ℝ)^(r/2) := by
    dsimp only [S]
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul hNR.le]
    congr 1
    ring
  have hscale : S^r*(N:ℝ)^(-r/2) = 1 := by
    rw [hSr,← Real.rpow_add hNR]
    convert Real.rpow_zero (N:ℝ) using 1
    congr 1
    ring
  have he : S^r*(D^r*α+B*gaussianMomentConstant r C*(N:ℝ)^(-r/2)) =
      (S*D)^r*α+B*gaussianMomentConstant r C := by
    rw [Real.mul_rpow hS.le hD]
    calc
      _ = S^r*D^r*α+(B*gaussianMomentConstant r C)*(S^r*(N:ℝ)^(-r/2)) := by ring
      _ = _ := by rw [hscale,mul_one]
  rw [hZi,← he] at hh
  exact (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hS r)).mp
    (by simpa only [mul_comm] using hh)

def clipToInterval (ℓ u x : ℝ) : ℝ := max ℓ (min u x)

theorem measurable_clipToInterval (ℓ u : ℝ) : Measurable (clipToInterval ℓ u) :=
  measurable_const.max (measurable_const.min measurable_id)

theorem clipToInterval_mem {ℓ u : ℝ} (hℓu : ℓ ≤ u) (x : ℝ) :
    clipToInterval ℓ u x ∈ Icc ℓ u :=
  ⟨le_max_left _ _,max_le hℓu (min_le_left _ _)⟩

theorem clipToInterval_le_iff {ℓ u T x : ℝ} (hT : T ∈ Ioo ℓ u) :
    clipToInterval ℓ u x ≤ T ↔ x ≤ T := by
  simp only [clipToInterval,max_le_iff,min_le_iff,hT.1.le,not_le.mpr hT.2,true_and,false_or]

theorem abs_clipToInterval_sub_le {ℓ u a : ℝ} (ha : a ∈ Icc ℓ u) (x : ℝ) :
    |clipToInterval ℓ u x-a| ≤ |x-a| := by
  by_cases hxℓ : x ≤ ℓ
  · rw [clipToInterval,min_eq_right (hxℓ.trans (ha.1.trans ha.2)),max_eq_left hxℓ]
    rw [abs_of_nonpos (sub_nonpos.mpr ha.1),abs_of_nonpos (sub_nonpos.mpr (hxℓ.trans ha.1))]
    linarith
  · by_cases hux : u ≤ x
    · rw [clipToInterval,min_eq_left hux,max_eq_right (ha.1.trans ha.2)]
      rw [abs_of_nonneg (sub_nonneg.mpr ha.2),abs_of_nonneg (sub_nonneg.mpr (ha.2.trans hux))]
      linarith
    · simp only [clipToInterval,min_eq_right (le_of_not_ge hux),max_eq_right (le_of_not_ge hxℓ),le_refl]

theorem abs_clipToInterval_sub_le_width {ℓ u a : ℝ} (ha : a ∈ Icc ℓ u) (x : ℝ) :
    |clipToInterval ℓ u x-a| ≤ u-ℓ := by
  have hc := clipToInterval_mem (ha.1.trans ha.2) x
  exact abs_le.mpr ⟨by linarith [hc.1,ha.2],by linarith [hc.2,ha.1]⟩

theorem integrable_abs_clipToInterval_sub_rpow (μ : Measure Ω) [IsFiniteMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) {ℓ u a r : ℝ}
    (ha : a ∈ Icc ℓ u) (hr : 0 ≤ r) :
    Integrable (fun ω => |clipToInterval ℓ u (X ω)-a|^r) μ := by
  apply integrable_rpow_of_bounded_nonneg μ
    (continuous_abs.measurable.comp (((measurable_clipToInterval ℓ u).comp hX).sub_const a)) hr
  exact fun ω => ⟨abs_nonneg _,abs_clipToInterval_sub_le_width ha (X ω)⟩

theorem memLp_clipToInterval_sub (μ : Measure Ω) [IsFiniteMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) {ℓ u a : ℝ}
    (ha : a ∈ Icc ℓ u) (p : ENNReal) :
    MemLp (fun ω => clipToInterval ℓ u (X ω)-a) p μ := by
  apply MemLp.of_bound (((measurable_clipToInterval ℓ u).comp hX).sub_const a).aestronglyMeasurable (u-ℓ)
  filter_upwards [] with ω
  simpa only [Real.norm_eq_abs,Function.comp_def] using abs_clipToInterval_sub_le_width ha (X ω)

theorem clipped_rpow_moment_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) {ℓ u a r α B C : ℝ}
    (ha : a ∈ Icc ℓ u) (hr : 1 ≤ r) (hB : 0 ≤ B) (hC : 0 < C)
    (N : ℕ) (hN : 0 < N)
    (htail : ∀ ε : ℝ, 0 ≤ ε → μ.real {ω | ε ≤ |X ω-a|} ≤ α+B*Real.exp (-(N:ℝ)*ε^2/C)) :
    (∫ ω, |clipToInterval ℓ u (X ω)-a|^r ∂μ) ≤
      (u-ℓ)^r*α+B*gaussianMomentConstant r C*(N:ℝ)^(-r/2) := by
  apply bounded_rpow_moment_le_scaled_gaussian_tail μ
    (continuous_abs.measurable.comp (((measurable_clipToInterval ℓ u).comp hX).sub_const a))
    (sub_nonneg.mpr (ha.1.trans ha.2)) hr hB hC N hN
    (fun ω => ⟨abs_nonneg _,abs_clipToInterval_sub_le_width ha (X ω)⟩)
  intro ε hε
  exact (measureReal_mono (show {ω | ε ≤ |clipToInterval ℓ u (X ω)-a|} ⊆
    {ω | ε ≤ |X ω-a|} from fun ω hω => hω.trans (abs_clipToInterval_sub_le ha (X ω)))).trans (htail ε hε)

theorem clipped_rpow_moment_le_exponential (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) {ℓ u a r A B C d : ℝ}
    (ha : a ∈ Icc ℓ u) (hr : 1 ≤ r) (hB : 0 ≤ B) (hC : 0 < C)
    (N : ℕ) (hN : 0 < N)
    (htail : ∀ ε : ℝ, 0 ≤ ε → μ.real {ω | ε ≤ |X ω-a|} ≤
      A*Real.exp (-d*(N:ℝ))+B*Real.exp (-(N:ℝ)*ε^2/C)) :
    Integrable (fun ω => |clipToInterval ℓ u (X ω)-a|^r) μ ∧
    (∫ ω, |clipToInterval ℓ u (X ω)-a|^r ∂μ) ≤
      (u-ℓ)^r*A*Real.exp (-d*(N:ℝ))+B*gaussianMomentConstant r C*(N:ℝ)^(-r/2) := by
  refine ⟨integrable_abs_clipToInterval_sub_rpow μ hX ha (by linarith),?_⟩
  simpa only [mul_assoc] using clipped_rpow_moment_le μ hX ha hr hB hC N hN htail

theorem eventually_exp_neg_mul_le_rpow {ι : Type*} {l : Filter ι} {s : ι → ℝ}
    (hs : Tendsto s l atTop) (p : ℝ) {d : ℝ} (hd : 0 < d) :
    ∀ᶠ t in l, Real.exp (-d*s t) ≤ (s t)^(-p) := by
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p d hd).comp hs
  filter_upwards [hh.eventually_lt_const zero_lt_one,hs.eventually_gt_atTop 0] with t ht hst
  rw [Real.rpow_neg hst.le,← one_div]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hst p)).mpr
  dsimp only [Function.comp_def] at ht
  nlinarith only [ht]

theorem eventually_nat_exp_neg_mul_le_rpow {ι : Type*} {l : Filter ι}
    (N : ι → ℕ) (hN : Tendsto N l atTop) (p : ℝ) {d : ℝ} (hd : 0 < d) :
    ∀ᶠ t in l, Real.exp (-d*(N t:ℝ)) ≤ (N t:ℝ)^(-p) :=
  eventually_exp_neg_mul_le_rpow (tendsto_natCast_atTop_atTop.comp hN) p hd

theorem eventually_uniform_power_bound_of_exponential
    {ι β : Type*} {l : Filter ι} (N : ι → ℕ) (hN : Tendsto N l atTop)
    {p d E G : ℝ} (hd : 0 < d) (hE : 0 ≤ E) (hG : 0 ≤ G)
    {S : Set β} {f : ι → β → ℝ}
    (hbound : ∀ᶠ t in l, ∀ b ∈ S,
      f t b ≤ E*Real.exp (-d*(N t:ℝ))+G*(N t:ℝ)^(-p)) :
    0 < E+G+1 ∧ ∀ᶠ t in l, ∀ b ∈ S, f t b ≤ (E+G+1)*(N t:ℝ)^(-p) := by
  refine ⟨by linarith,?_⟩
  filter_upwards [hbound,eventually_nat_exp_neg_mul_le_rpow N hN p hd] with t ht he
  intro b hb
  have hh := mul_le_mul_of_nonneg_left he hE
  have hp := Real.rpow_nonneg (Nat.cast_nonneg (N t) : (0:ℝ) ≤ N t) (-p)
  nlinarith [ht b hb]

end FCAppendix.Probability
