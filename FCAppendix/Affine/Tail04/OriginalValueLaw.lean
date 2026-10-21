import FCAppendix.Affine.Tail04.ParetoTail
import FCAppendix.Affine.Tail04.OriginalRankTail
import Mathlib

noncomputable section
namespace FCAppendix.Affine.Tail04
open MeasureTheory Set Real Filter Topology
open scoped ENNReal

def delta (theta : ℝ) : ℝ := theta ^ 2

def lowMass (theta : ℝ) : ℝ := 1 / 100 + delta theta

def partialMass : ℝ := 8 / 25

def activeMass (theta : ℝ) : ℝ := 67 / 100 - delta theta

theorem mass_sum (theta : ℝ) :
    lowMass theta + partialMass + activeMass theta = 1 := by
  unfold lowMass partialMass activeMass
  ring

theorem activeMass_pos (theta : ℝ) (h : theta ^ 2 < 67 / 100) :
    0 < activeMass theta := by
  unfold activeMass delta
  linarith

structure ValueParameters where
  theta : ℝ
  d0 : ℝ
  w : ℝ
  zeta : ℝ
  M : ℝ
  vA : ℝ
  theta_pos : 0 < theta
  theta_small : theta < 1 / 10
  d0_pos : 0 < d0
  w_pos : 0 < w
  zeta_pos : 0 < zeta
  zeta_lt_one : zeta < 1
  low_partial_gap : d0 < 2 - w
  partial_active_gap : 2 + w < vA - w
  active_tail_gap : vA + w < M

namespace ValueParameters

variable (P : ValueParameters)

theorem M_pos : 0 < P.M := by
  have h1 := P.d0_pos
  have h2 := P.low_partial_gap
  have h3 := P.partial_active_gap
  have h4 := P.active_tail_gap
  have hw := P.w_pos
  linarith

theorem active_mass_pos : 0 < activeMass P.theta := by
  apply activeMass_pos P.theta
  have h0 := P.theta_pos
  have h1 := P.theta_small
  nlinarith

theorem low_mass_pos : 0 < lowMass P.theta := by
  dsimp [lowMass, delta]
  positivity

def cutoff : ℝ := P.d0 / (100 * lowMass P.theta)

theorem cutoff_in_low_band : P.cutoff ∈ Ioo (0 : ℝ) P.d0 := by
  have hs := P.low_mass_pos
  have htheta2 : 0 < P.theta ^ 2 := sq_pos_of_ne_zero P.theta_pos.ne'
  have hden : 1 < 100 * lowMass P.theta := by
    dsimp [lowMass, delta]
    nlinarith
  constructor
  · exact div_pos P.d0_pos (by positivity)
  · dsimp [cutoff]
    exact (div_lt_iff₀ (by positivity)).2 (by nlinarith [P.d0_pos])

end ValueParameters

def bandDensity (l u v : ℝ) : ℝ :=
  (Icc l u).indicator (fun _ => 1 / (u - l)) v

def paretoDensity (M v : ℝ) : ℝ :=
  (Ici M).indicator (fun x => 10 / M * powerTail M 11 x) v

def valueDensity (P : ValueParameters) (v : ℝ) : ℝ :=
  lowMass P.theta * bandDensity 0 P.d0 v +
  partialMass * bandDensity (2 - P.w) (2 + P.w) v +
  activeMass P.theta * ((1 - P.zeta) * bandDensity (P.vA - P.w) (P.vA + P.w) v +
    P.zeta * paretoDensity P.M v)

def valueLaw (P : ValueParameters) : Measure ℝ :=
  volume.withDensity (fun v => ENNReal.ofReal (valueDensity P v))

theorem bandDensity_nonneg (l u v : ℝ) (hlu : l < u) : 0 ≤ bandDensity l u v := by
  dsimp [bandDensity, indicator]
  split_ifs <;> positivity

theorem bandDensity_measurable (l u : ℝ) : Measurable (bandDensity l u) :=
  measurable_const.indicator measurableSet_Icc

theorem bandDensity_integrable (l u : ℝ) : Integrable (bandDensity l u) := by
  change Integrable ((Icc l u).indicator (fun _ : ℝ=>1/(u-l)))
  rw [integrable_indicator_iff measurableSet_Icc]
  exact continuous_const.integrableOn_Icc

theorem integral_bandDensity (l u : ℝ) (hlu : l < u) :
    (∫ v, bandDensity l u v) = 1 := by
  change (∫v : ℝ,(Icc l u).indicator (fun _ : ℝ=>1/(u-l)) v)=1
  rw [integral_indicator measurableSet_Icc]
  simp [integral_const, Measure.real, Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hlu.le), sub_ne_zero.mpr hlu.ne']

private theorem paretoDensity_ae_Ioi (M : ℝ) :
    paretoDensity M =ᵐ[volume]
      (Ioi M).indicator (fun v => 10 / M * powerTail M 11 v) := by
  have hne : ∀ᵐ v : ℝ ∂volume, v ≠ M := by
    rw [ae_iff]
    simp only [not_not,Set.setOf_eq_eq_singleton,measure_singleton]
  filter_upwards [hne] with v hv
  dsimp [paretoDensity, indicator]
  by_cases h : M < v
  · simp [h, h.le]
  · have h' : ¬ M ≤ v := by intro hle; exact hv (le_antisymm (le_of_not_gt h) hle)
    simp [h, h']

theorem paretoDensity_nonneg (M v : ℝ) (hM : 0 < M) : 0 ≤ paretoDensity M v := by
  dsimp [paretoDensity, indicator]
  split_ifs with hv
  · have hv0 : 0 ≤ v := hM.le.trans hv
    exact mul_nonneg (by positivity) (powerTail_nonneg M 11 v hM hv0)
  · exact le_rfl

theorem paretoDensity_measurable (M : ℝ) : Measurable (paretoDensity M) := by
  have hm : Measurable (fun v : ℝ=>10/M*powerTail M 11 v) := by
    unfold powerTail
    fun_prop
  exact hm.indicator measurableSet_Ici

theorem paretoDensity_integrable (M : ℝ) (hM : 0 < M) : Integrable (paretoDensity M) := by
  have hi : Integrable ((Ioi M).indicator (fun v => 10 / M * powerTail M 11 v)) := by
    rw [integrable_indicator_iff measurableSet_Ioi]
    exact (powerTail_integrable M 11 hM (by norm_num)).const_mul (10 / M)
  exact hi.congr (paretoDensity_ae_Ioi M).symm

theorem integral_paretoDensity (M : ℝ) (hM : 0 < M) :
    (∫ v, paretoDensity M v) = 1 := by
  rw [integral_congr_ae (paretoDensity_ae_Ioi M), integral_indicator measurableSet_Ioi,
    integral_const_mul, integral_powerTail M 11 hM (by norm_num)]
  field_simp
  all_goals ring

theorem valueDensity_nonneg (P : ValueParameters) (v : ℝ) : 0 ≤ valueDensity P v := by
  have hlow := bandDensity_nonneg 0 P.d0 v P.d0_pos
  have hpartial := bandDensity_nonneg (2 - P.w) (2 + P.w) v (by linarith [P.w_pos])
  have hactive := bandDensity_nonneg (P.vA - P.w) (P.vA + P.w) v (by linarith [P.w_pos])
  have htail := paretoDensity_nonneg P.M v P.M_pos
  have hs := P.low_mass_pos
  have ha := P.active_mass_pos
  have hz0 := P.zeta_pos
  have hz1 : 0 < 1 - P.zeta := sub_pos.mpr P.zeta_lt_one
  dsimp [valueDensity, partialMass]
  positivity

theorem valueDensity_measurable (P : ValueParameters) : Measurable (valueDensity P) := by
  unfold valueDensity
  exact (((bandDensity_measurable 0 P.d0).const_mul _).add
    ((bandDensity_measurable (2 - P.w) (2 + P.w)).const_mul _)).add
      ((((bandDensity_measurable (P.vA - P.w) (P.vA + P.w)).const_mul _).add
        ((paretoDensity_measurable P.M).const_mul _)).const_mul _)

theorem valueDensity_integrable (P : ValueParameters) : Integrable (valueDensity P) := by
  unfold valueDensity
  exact (((bandDensity_integrable 0 P.d0).const_mul _).add
    ((bandDensity_integrable (2 - P.w) (2 + P.w)).const_mul _)).add
      ((((bandDensity_integrable (P.vA - P.w) (P.vA + P.w)).const_mul _).add
        ((paretoDensity_integrable P.M P.M_pos).const_mul _)).const_mul _)

theorem integral_valueDensity (P : ValueParameters) : (∫ v, valueDensity P v) = 1 := by
  have h0 := bandDensity_integrable 0 P.d0
  have h1 := bandDensity_integrable (2 - P.w) (2 + P.w)
  have h2 := bandDensity_integrable (P.vA - P.w) (P.vA + P.w)
  have h3 := paretoDensity_integrable P.M P.M_pos
  unfold valueDensity
  rw [integral_add (f:=fun v=>lowMass P.theta*bandDensity 0 P.d0 v+
      partialMass*bandDensity (2-P.w) (2+P.w) v)
      (g:=fun v=>activeMass P.theta*((1-P.zeta)*bandDensity (P.vA-P.w) (P.vA+P.w) v+
        P.zeta*paretoDensity P.M v))
      ((h0.const_mul (lowMass P.theta)).add (h1.const_mul partialMass))
      (((h2.const_mul (1-P.zeta)).add (h3.const_mul P.zeta)).const_mul (activeMass P.theta)),
    integral_add (h0.const_mul (lowMass P.theta)) (h1.const_mul partialMass)]
  simp only [integral_const_mul]
  rw [integral_add (h2.const_mul (1-P.zeta)) (h3.const_mul P.zeta)]
  simp only [integral_const_mul]
  rw [integral_bandDensity 0 P.d0 P.d0_pos,
    integral_bandDensity (2 - P.w) (2 + P.w) (by linarith [P.w_pos]),
    integral_bandDensity (P.vA - P.w) (P.vA + P.w) (by linarith [P.w_pos]),
    integral_paretoDensity P.M P.M_pos]
  simpa using mass_sum P.theta

instance valueLaw_probability (P : ValueParameters) : IsProbabilityMeasure (valueLaw P) := by
  constructor
  rw [valueLaw, withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (valueDensity_integrable P)
    (Eventually.of_forall (valueDensity_nonneg P)), integral_valueDensity]
  norm_num

theorem valueLaw_absolutelyContinuous (P : ValueParameters) : valueLaw P ≪ volume :=
  withDensity_absolutelyContinuous _ _

instance valueLaw_noAtoms (P : ValueParameters) : NullSingletonClass (valueLaw P) := by
  constructor
  intro v
  exact valueLaw_absolutelyContinuous P (by simp)

theorem valueDensity_on_low (P : ValueParameters) (v : ℝ) (hv : v ∈ Icc (0 : ℝ) P.d0) :
    valueDensity P v = lowMass P.theta / P.d0 := by
  have hvp : v < 2 - P.w := hv.2.trans_lt P.low_partial_gap
  have hva : v < P.vA - P.w := by linarith [P.partial_active_gap, P.w_pos]
  have hvt : v < P.M := by linarith [P.active_tail_gap, P.w_pos]
  simp [valueDensity, bandDensity, paretoDensity, hv,
    show v ∉ Icc (2 - P.w) (2 + P.w) from fun h => (not_le.mpr hvp) h.1,
    show v ∉ Icc (P.vA - P.w) (P.vA + P.w) from fun h => (not_le.mpr hva) h.1,
    show v ∉ Ici P.M from not_le.mpr hvt, div_eq_mul_inv]

theorem valueDensity_on_tail (P : ValueParameters) (v : ℝ) (hv : P.M ≤ v) :
    valueDensity P v = activeMass P.theta * P.zeta *
      (10 / P.M * powerTail P.M 11 v) := by
  have hvA : P.vA + P.w < v := P.active_tail_gap.trans_le hv
  have hvP : 2 + P.w < v := by linarith [P.partial_active_gap, P.w_pos]
  have hvL : P.d0 < v := by linarith [P.low_partial_gap, P.w_pos]
  simp [valueDensity, bandDensity, paretoDensity, hv,
    show v ∉ Icc 0 P.d0 from fun h => (not_le.mpr hvL) h.2,
    show v ∉ Icc (2 - P.w) (2 + P.w) from fun h => (not_le.mpr hvP) h.2,
    show v ∉ Icc (P.vA - P.w) (P.vA + P.w) from fun h => (not_le.mpr hvA) h.2,
    mul_assoc]

theorem valueDensity_tail_pos (P : ValueParameters) (v : ℝ) (hv : P.M ≤ v) :
    0 < valueDensity P v := by
  rw [valueDensity_on_tail P v hv]
  have hpow : 0 < powerTail P.M 11 v :=
    Real.rpow_pos_of_pos (div_pos (P.M_pos.trans_le hv) P.M_pos) _
  have ha := P.active_mass_pos
  have hz := P.zeta_pos
  have hM := P.M_pos
  positivity

theorem valueDensity_cutoff_pos (P : ValueParameters) : 0 < valueDensity P P.cutoff := by
  rw [valueDensity_on_low P P.cutoff
    ⟨P.cutoff_in_low_band.1.le, P.cutoff_in_low_band.2.le⟩]
  exact div_pos P.low_mass_pos P.d0_pos

theorem integral_valueDensity_tail (P : ValueParameters) (t : ℝ) (ht : P.M ≤ t) :
    (∫ v in Ioi t, valueDensity P v) =
      activeMass P.theta * P.zeta * powerTail P.M 10 t := by
  calc
    _ = ∫ v in Ioi t, (activeMass P.theta * P.zeta * (10 / P.M)) *
        powerTail P.M 11 v := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      rw [valueDensity_on_tail P v (ht.trans hv.le)]
      ring
    _ = (activeMass P.theta * P.zeta * (10 / P.M)) *
        (∫ v in Ioi t, powerTail P.M 11 v) := integral_const_mul _ _
    _ = activeMass P.theta * P.zeta * powerTail P.M 10 t := by
      rw [integral_powerTail_above P.M 11 t P.M_pos (by norm_num) ht]
      dsimp [powerTail]
      norm_num
      field_simp

theorem valueLaw_tail (P : ValueParameters) (t : ℝ) (ht : P.M ≤ t) :
    valueLaw P (Ioi t) =
      ENNReal.ofReal (activeMass P.theta * P.zeta * powerTail P.M 10 t) := by
  rw [valueLaw, withDensity_apply _ measurableSet_Ioi]
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((valueDensity_integrable P).integrableOn)
    (Eventually.of_forall (valueDensity_nonneg P)), integral_valueDensity_tail P t ht]

theorem valueLaw_unbounded (P : ValueParameters) (r : ℝ) :
    0 < valueLaw P (Ioi r) := by
  let t := max P.M r
  have ht : P.M ≤ t := le_max_left _ _
  have hpow : 0 < powerTail P.M 10 t :=
    Real.rpow_pos_of_pos (div_pos (P.M_pos.trans_le ht) P.M_pos) _
  have hpos : 0 < valueLaw P (Ioi t) := by
    rw [valueLaw_tail P t ht]
    exact ENNReal.ofReal_pos.mpr (mul_pos (mul_pos P.active_mass_pos P.zeta_pos) hpow)
  exact hpos.trans_le (measure_mono (Ioi_subset_Ioi (le_max_right _ _)))

theorem valueDensity_zero_below_zero (P : ValueParameters) (v : ℝ) (hv : v < 0) :
    valueDensity P v = 0 := by
  have hP : 0 < 2 - P.w := P.d0_pos.trans P.low_partial_gap
  have hA : 0 < P.vA - P.w := by linarith [P.partial_active_gap, P.w_pos]
  have hT := P.M_pos
  simp [valueDensity, bandDensity, paretoDensity,
    show v ∉ Icc 0 P.d0 from fun h => (not_le.mpr hv) h.1,
    show v ∉ Icc (2 - P.w) (2 + P.w) from fun h => by linarith [h.1],
    show v ∉ Icc (P.vA - P.w) (P.vA + P.w) from fun h => by linarith [h.1],
    show v ∉ Ici P.M from fun h => by have hvM : P.M≤v:=h;linarith]

theorem integral_valueDensity_low (P : ValueParameters) (x : ℝ)
    (hx0 : 0 < x) (hxd : x ≤ P.d0) :
    (∫ v in Iic x, valueDensity P v) = lowMass P.theta * x / P.d0 := by
  have heq : (Iic x).indicator (valueDensity P) =
      fun v => (lowMass P.theta * x / P.d0) * bandDensity 0 x v := by
    funext v
    by_cases hvx : v ≤ x
    · by_cases hv0 : 0 ≤ v
      · have hvd : v ∈ Icc (0 : ℝ) P.d0 := ⟨hv0, hvx.trans hxd⟩
        rw [Set.indicator_of_mem (show v∈Iic x from hvx), valueDensity_on_low P v hvd]
        simp only [bandDensity, indicator_of_mem (show v ∈ Icc (0 : ℝ) x from ⟨hv0, hvx⟩)]
        field_simp [hx0.ne',P.d0_pos.ne']
        ring
      · have hvneg : v < 0 := lt_of_not_ge hv0
        rw [Set.indicator_of_mem (show v∈Iic x from hvx), valueDensity_zero_below_zero P v hvneg]
        simp [bandDensity, hv0]
    · have hnot : v ∉ Icc (0 : ℝ) x := fun h => hvx h.2
      simp [Set.indicator_of_notMem (show v∉Iic x from hvx), bandDensity, hnot]
  rw [← integral_indicator measurableSet_Iic, heq, integral_const_mul,
    integral_bandDensity 0 x hx0, mul_one]

theorem valueLaw_low_cdf (P : ValueParameters) (x : ℝ)
    (hx0 : 0 < x) (hxd : x ≤ P.d0) :
    valueLaw P (Iic x) = ENNReal.ofReal (lowMass P.theta * x / P.d0) := by
  rw [valueLaw, withDensity_apply _ measurableSet_Iic]
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((valueDensity_integrable P).integrableOn)
    (Eventually.of_forall (valueDensity_nonneg P)),
    integral_valueDensity_low P x hx0 hxd]

theorem valueLaw_at_cutoff (P : ValueParameters) :
    valueLaw P (Iic P.cutoff) = ENNReal.ofReal (1 / 100 : ℝ) := by
  rw [valueLaw_low_cdf P P.cutoff P.cutoff_in_low_band.1 P.cutoff_in_low_band.2.le]
  congr 1
  dsimp [ValueParameters.cutoff]
  have hs := P.low_mass_pos.ne'
  have hd := P.d0_pos.ne'
  field_simp [hs,hd]

theorem valueDensity_cutoff_neighborhood (P : ValueParameters) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ v ∈ Ioo (P.cutoff - eps) (P.cutoff + eps), 0 < valueDensity P v := by
  let eps := min P.cutoff (P.d0 - P.cutoff) / 2
  have hc := P.cutoff_in_low_band
  have heps : 0 < eps := by
    dsimp [eps]
    exact div_pos (lt_min hc.1 (sub_pos.mpr hc.2)) (by norm_num)
  refine ⟨eps, heps, ?_⟩
  intro v hv
  have he1 : eps ≤ P.cutoff / 2 := by
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have he2 : eps ≤ (P.d0 - P.cutoff) / 2 := by
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hvlow : v ∈ Icc (0 : ℝ) P.d0 := by constructor <;> linarith [hv.1, hv.2]
  rw [valueDensity_on_low P v hvlow]
  exact div_pos P.low_mass_pos P.d0_pos

theorem valueDensity_first_gap (P : ValueParameters) (v : ℝ)
    (hv : v ∈ Ioo P.d0 (2 - P.w)) : valueDensity P v = 0 := by
  have hA : v < P.vA - P.w := by linarith [P.partial_active_gap, P.w_pos, hv.2]
  have hT : v < P.M := by linarith [P.active_tail_gap, P.w_pos]
  simp [valueDensity, bandDensity, paretoDensity,
    show v ∉ Icc 0 P.d0 from fun h => by linarith [h.2, hv.1],
    show v ∉ Icc (2 - P.w) (2 + P.w) from fun h => by linarith [h.1, hv.2],
    show v ∉ Icc (P.vA - P.w) (P.vA + P.w) from fun h => by linarith [h.1],
    show v ∉ Ici P.M from not_le.mpr hT]

end FCAppendix.Affine.Tail04
