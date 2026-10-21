import FCAppendix.Affine.Tail04.OriginalValueLaw
import FCAppendix.Affine.Tail04.PrivateComposition

noncomputable section
namespace FCAppendix.Affine.Tail04
open MeasureTheory ProbabilityTheory Set Filter Topology Game

namespace ValueParameters

variable (P : ValueParameters)

def lowValues : Set ℝ := Iic P.d0
def partialValues : Set ℝ := Icc (2-P.w) (2+P.w)
def fixedUpperValues : Set ℝ := Ici (P.vA-P.w)
def movingUpperValues (_P : ValueParameters) (t : ℝ) : Set ℝ := Ioi t
def movingActiveValues (t : ℝ) : Set ℝ := Icc (P.vA-P.w) t
def privateValues (t : ℝ) : Set ℝ := P.partialValues ∪ P.movingUpperValues t

def fixedUpperMeasure : Measure ℝ := (valueLaw P).restrict P.fixedUpperValues
def movingUpperMeasure (t : ℝ) : Measure ℝ :=
  (valueLaw P).restrict (P.movingUpperValues t)

instance fixedUpperMeasure_finite : IsFiniteMeasure P.fixedUpperMeasure := by
  unfold fixedUpperMeasure
  infer_instance

instance fixedUpperMeasure_atomless : NullSingletonClass P.fixedUpperMeasure := by
  unfold fixedUpperMeasure
  infer_instance

instance movingUpperMeasure_finite (t : ℝ) : IsFiniteMeasure (P.movingUpperMeasure t) := by
  unfold movingUpperMeasure
  infer_instance

instance movingUpperMeasure_atomless (t : ℝ) : NullSingletonClass (P.movingUpperMeasure t) := by
  unfold movingUpperMeasure
  infer_instance

theorem fixedUpperMeasure_support :
    ∀ᵐ v ∂P.fixedUpperMeasure, P.vA-P.w ≤ v :=
  ae_restrict_mem measurableSet_Ici

include P in
theorem movingUpperMeasure_support (t : ℝ) :
    ∀ᵐ v ∂P.movingUpperMeasure t, t ≤ v := by
  filter_upwards [ae_restrict_mem (μ := valueLaw P) measurableSet_Ioi] with v hv
  exact hv.le

theorem tailMass_nonneg (t : ℝ) (ht : P.M ≤ t) :
    0 ≤ activeMass P.theta*P.zeta*powerTail P.M 10 t := by
  have hpow := powerTail_nonneg P.M 10 t P.M_pos (P.M_pos.le.trans ht)
  exact mul_nonneg (mul_nonneg P.active_mass_pos.le P.zeta_pos.le) hpow

theorem real_tail (t : ℝ) (ht : P.M ≤ t) :
    (valueLaw P).real (Ioi t) = activeMass P.theta*P.zeta*powerTail P.M 10 t := by
  rw [measureReal_def, valueLaw_tail P t ht,
    ENNReal.toReal_ofReal (P.tailMass_nonneg t ht)]

theorem low_mass : (valueLaw P).real P.lowValues = lowMass P.theta := by
  rw [lowValues, measureReal_def, valueLaw_low_cdf P P.d0 P.d0_pos le_rfl]
  have he : lowMass P.theta*P.d0/P.d0 = lowMass P.theta :=
    mul_div_cancel_right₀ _ P.d0_pos.ne'
  rw [he, ENNReal.toReal_ofReal P.low_mass_pos.le]

theorem density_on_partial (v : ℝ) (hv : v ∈ P.partialValues) :
    valueDensity P v = partialMass/(2*P.w) := by
  have hvL : P.d0 < v := P.low_partial_gap.trans_le hv.1
  have hvA : v < P.vA-P.w := hv.2.trans_lt P.partial_active_gap
  have hvT : v < P.M := by linarith [P.active_tail_gap, P.w_pos]
  have hL : v ∉ Icc 0 P.d0 := fun h => (not_le.mpr hvL) h.2
  have hA : v ∉ Icc (P.vA-P.w) (P.vA+P.w) := fun h => (not_le.mpr hvA) h.1
  have hT : v ∉ Ici P.M := not_le.mpr hvT
  have hP : v ∈ Icc (2-P.w) (2+P.w) := hv
  simp only [valueDensity, bandDensity, paretoDensity, indicator_of_notMem hL,
    indicator_of_mem hP, indicator_of_notMem hA, indicator_of_notMem hT,
    mul_zero, zero_add, add_zero]
  rw [show (2+P.w)-(2-P.w) = 2*P.w by ring]
  ring

theorem partial_indicator :
    P.partialValues.indicator (valueDensity P) =
      fun v => partialMass*bandDensity (2-P.w) (2+P.w) v := by
  funext v
  change (Icc (2-P.w) (2+P.w)).indicator (valueDensity P) v = _
  by_cases hv : v ∈ Icc (2-P.w) (2+P.w)
  · rw [indicator_of_mem hv, P.density_on_partial v hv]
    simp only [bandDensity, indicator_of_mem hv]
    rw [show (2+P.w)-(2-P.w) = 2*P.w by ring]
    ring
  · simp only [indicator_of_notMem hv, bandDensity, mul_zero]

theorem partial_mass : (valueLaw P).real P.partialValues = partialMass := by
  have hi : (∫ v in P.partialValues, valueDensity P v) = partialMass := by
    change (∫ v in Icc (2-P.w) (2+P.w),valueDensity P v) = _
    rw [← integral_indicator measurableSet_Icc]
    change (∫ v,P.partialValues.indicator (valueDensity P) v) = _
    rw [P.partial_indicator,
      integral_const_mul, integral_bandDensity _ _ (by linarith [P.w_pos]), mul_one]
  change (valueLaw P).real (Icc (2-P.w) (2+P.w)) = _
  change (∫ v in Icc (2-P.w) (2+P.w), valueDensity P v) = partialMass at hi
  rw [measureReal_def, valueLaw, withDensity_apply _ measurableSet_Icc,
    ← ofReal_integral_eq_lintegral_ofReal (valueDensity_integrable P).integrableOn
      (Eventually.of_forall (valueDensity_nonneg P)), hi,
    ENNReal.toReal_ofReal (by norm_num [partialMass])]

theorem fixed_upper_indicator :
    P.fixedUpperValues.indicator (valueDensity P) = fun v =>
      activeMass P.theta*((1-P.zeta)*bandDensity (P.vA-P.w) (P.vA+P.w) v +
        P.zeta*paretoDensity P.M v) := by
  funext v
  change (Ici (P.vA-P.w)).indicator (valueDensity P) v = _
  by_cases hv : v ∈ Ici (P.vA-P.w)
  · have hvP : 2+P.w < v := P.partial_active_gap.trans_le hv
    have hvL : P.d0 < v := by linarith [P.low_partial_gap, P.w_pos]
    have hL : v ∉ Icc 0 P.d0 := fun h => (not_le.mpr hvL) h.2
    have hP : v ∉ Icc (2-P.w) (2+P.w) := fun h => (not_le.mpr hvP) h.2
    simp only [indicator_of_mem hv, valueDensity,
      bandDensity, indicator_of_notMem hL, indicator_of_notMem hP,
      mul_zero, zero_add]
  · have hA : v ∉ Icc (P.vA-P.w) (P.vA+P.w) := fun h => hv h.1
    have hT : v ∉ Ici P.M := by
      intro h
      have hMv : P.M ≤ v := h
      apply hv
      change P.vA-P.w ≤ v
      linarith [P.active_tail_gap, P.w_pos]
    simp only [indicator_of_notMem hv, bandDensity,
      paretoDensity, indicator_of_notMem hA, indicator_of_notMem hT,
      mul_zero, add_zero]

theorem fixed_upper_mass :
    (valueLaw P).real P.fixedUpperValues = activeMass P.theta := by
  have hi : (∫ v in P.fixedUpperValues, valueDensity P v) = activeMass P.theta := by
    change (∫ v in Ici (P.vA-P.w),valueDensity P v) = _
    rw [← integral_indicator measurableSet_Ici]
    change (∫ v,P.fixedUpperValues.indicator (valueDensity P) v) = _
    rw [P.fixed_upper_indicator,
      integral_const_mul,
      integral_add ((bandDensity_integrable _ _).const_mul _)
        ((paretoDensity_integrable P.M P.M_pos).const_mul _)]
    simp only [integral_const_mul]
    rw [integral_bandDensity _ _ (by linarith [P.w_pos]),
      integral_paretoDensity P.M P.M_pos]
    ring
  change (valueLaw P).real (Ici (P.vA-P.w)) = _
  change (∫ v in Ici (P.vA-P.w), valueDensity P v) = activeMass P.theta at hi
  rw [measureReal_def, valueLaw, withDensity_apply _ measurableSet_Ici,
    ← ofReal_integral_eq_lintegral_ofReal (valueDensity_integrable P).integrableOn
      (Eventually.of_forall (valueDensity_nonneg P)), hi,
    ENNReal.toReal_ofReal P.active_mass_pos.le]

theorem fixedUpperMeasure_mass :
    P.fixedUpperMeasure.real univ = activeMass P.theta := by
  simpa only [fixedUpperMeasure, measureReal_def, Measure.restrict_apply_univ] using
    P.fixed_upper_mass

theorem fixedUpperMeasure_mass_small : P.fixedUpperMeasure.real univ ≤ 7/10 := by
  rw [P.fixedUpperMeasure_mass]
  unfold activeMass delta
  nlinarith [sq_nonneg P.theta]

theorem fixedUpperMeasure_tail (v : ℝ) (hv : P.M ≤ v) :
    P.fixedUpperMeasure.real (Ioi v) =
      activeMass P.theta*P.zeta*powerTail P.M 10 v := by
  have hset : Ioi v ∩ P.fixedUpperValues = Ioi v := by
    apply inter_eq_left.mpr
    intro x hx
    change P.vA-P.w ≤ x
    have hM : P.vA-P.w < P.M := by linarith [P.active_tail_gap, P.w_pos]
    exact (hM.trans_le hv).le.trans hx.le
  rw [fixedUpperMeasure, measureReal_def, Measure.restrict_apply measurableSet_Ioi, hset]
  exact P.real_tail v hv

theorem movingUpperMeasure_mass (t : ℝ) (ht : P.M ≤ t) :
    (P.movingUpperMeasure t).real univ =
      activeMass P.theta*P.zeta*powerTail P.M 10 t := by
  simpa only [movingUpperMeasure, movingUpperValues, measureReal_def,
    Measure.restrict_apply_univ] using P.real_tail t ht

theorem movingUpperMeasure_relative (t : ℝ) (ht : P.M ≤ t)
    (v : ℝ) (hv : t ≤ v) :
    (P.movingUpperMeasure t).real (Ioi v) =
      (activeMass P.theta*P.zeta*powerTail P.M 10 t)*powerTail t 10 v := by
  have ht0 : 0 < t := P.M_pos.trans_le ht
  have hv0 : 0 < v := ht0.trans_le hv
  have hset : Ioi v ∩ P.movingUpperValues t = Ioi v :=
    inter_eq_left.mpr (Ioi_subset_Ioi hv)
  rw [movingUpperMeasure, measureReal_def, Measure.restrict_apply measurableSet_Ioi, hset]
  change (valueLaw P).real (Ioi v) = _
  rw [P.real_tail v (ht.trans hv), powerTail_ten P.M v P.M_pos hv0,
    powerTail_ten P.M t P.M_pos ht0, powerTail_ten t v ht0 hv0]
  field_simp

theorem moving_mass_exact (m : ℕ) (hm : P.M ≤ movingThreshold m) :
    (P.movingUpperMeasure (movingThreshold m)).real univ =
      movingPrivateMass (activeMass P.theta) P.zeta P.M m := by
  rw [P.movingUpperMeasure_mass _ hm, powerTail_ten P.M _ P.M_pos
    (P.M_pos.trans_le hm)]
  rfl

theorem moving_active_mass (t : ℝ) (ht : P.M ≤ t) :
    (valueLaw P).real (P.movingActiveValues t) = activeMass P.theta -
      activeMass P.theta*P.zeta*powerTail P.M 10 t := by
  have hLt : P.vA-P.w ≤ t := by linarith [P.active_tail_gap, P.w_pos]
  have hdis : Disjoint (P.movingActiveValues t) (P.movingUpperValues t) := by
    apply disjoint_left.mpr
    intro v hv hw
    exact (not_lt.mpr hv.2) hw
  have hunion : P.movingActiveValues t ∪ P.movingUpperValues t = P.fixedUpperValues := by
    ext v
    constructor
    · rintro (hv | hv)
      · exact hv.1
      · exact hLt.trans hv.le
    · intro hv
      by_cases hvt : v ≤ t
      · exact Or.inl ⟨hv, hvt⟩
      · exact Or.inr (lt_of_not_ge hvt)
  have he := measureReal_union (μ := valueLaw P) hdis measurableSet_Ioi
  rw [hunion, P.fixed_upper_mass] at he
  have ht' := P.real_tail t ht
  change (valueLaw P).real (P.movingUpperValues t) = _ at ht'
  linarith

theorem private_mass (t : ℝ) (ht : P.M ≤ t) :
    (valueLaw P).real (P.privateValues t) = partialMass +
      activeMass P.theta*P.zeta*powerTail P.M 10 t := by
  have hPt : 2+P.w < t := by
    linarith [P.partial_active_gap, P.active_tail_gap, P.w_pos]
  have hdis : Disjoint P.partialValues (P.movingUpperValues t) := by
    apply disjoint_left.mpr
    intro v hv hw
    have hvu : v ≤ 2+P.w := hv.2
    have htv : t < v := hw
    linarith
  rw [privateValues, measureReal_union hdis measurableSet_Ioi, P.partial_mass]
  rw [movingUpperValues, P.real_tail t ht]

theorem original_private_share (t : ℝ) (ht : P.M ≤ t) (j : Fin 2) :
    (cond ((valueLaw P).prod (FCAppendix.Game.permLaw 2))
      (P.privateValues t ×ˢ oneRouteEvent j)).real
      (P.movingUpperValues t ×ˢ (univ : Set (Equiv.Perm (Fin 2)))) =
      (activeMass P.theta*P.zeta*powerTail P.M 10 t) /
        (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t) := by
  rw [private_mark_given_route (valueLaw P) (FCAppendix.Game.permLaw 2)
    (P.privateValues t) (P.movingUpperValues t) (oneRouteEvent j)
    (measurableSet_Icc.union measurableSet_Ioi) (measurableSet_oneRouteEvent j)
    (by intro v hv; exact Or.inr hv)
    (by rw [P.private_mass t ht]; have h := P.tailMass_nonneg t ht
        norm_num [partialMass]; linarith)
    (by rw [original_fair_route_mass]; norm_num)]
  rw [P.private_mass t ht, movingUpperValues, P.real_tail t ht]

end ValueParameters
namespace OriginalValues
export ValueParameters (lowValues partialValues fixedUpperValues movingUpperValues movingActiveValues privateValues fixedUpperMeasure movingUpperMeasure fixedUpperMeasure_support movingUpperMeasure_support tailMass_nonneg real_tail low_mass density_on_partial partial_indicator partial_mass fixed_upper_indicator fixed_upper_mass fixedUpperMeasure_mass fixedUpperMeasure_mass_small fixedUpperMeasure_tail movingUpperMeasure_mass movingUpperMeasure_relative moving_mass_exact moving_active_mass private_mass original_private_share)
end OriginalValues
end FCAppendix.Affine.Tail04
