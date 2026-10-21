import FCAppendix.Affine.Tail04.OriginalValueSplits
import FCAppendix.Affine.Tail04.UpperCountLimits
import FCAppendix.Affine.Tail04.MovingOriginalUpper
import FCAppendix.Affine.Hybrid.NativeRows

noncomputable section
namespace FCAppendix.Affine.Tail04
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes
open Existence.RankEnvelope

namespace ValueParameters
open OriginalValues
variable (P : ValueParameters)

theorem fixedUpperBase_pos : 0 < P.vA-P.w := by
  linarith [P.partial_active_gap,P.w_pos]

theorem fixedUpperBase_le_tail : P.vA-P.w ≤ P.M := by
  linarith [P.active_tail_gap,P.w_pos]

theorem activeMass_le_one : activeMass P.theta ≤ 1 := by
  have h := P.fixedUpperMeasure_mass_small
  rw [P.fixedUpperMeasure_mass] at h
  linarith

theorem fixedUpperValues_mass :
    (valueLaw P) P.fixedUpperValues = ENNReal.ofReal (activeMass P.theta) := by
  rw [←P.fixed_upper_mass,ofReal_measureReal]

theorem fixedUpperValues_pos : (valueLaw P) P.fixedUpperValues ≠ 0 := by
  rw [P.fixedUpperValues_mass]
  exact (ENNReal.ofReal_pos.mpr P.active_mass_pos).ne'

def originalFixedUpperLaw : ProbabilityMeasure ℝ :=
  ⟨cond (valueLaw P) P.fixedUpperValues,cond_isProbabilityMeasure P.fixedUpperValues_pos⟩

instance originalFixedUpperLaw_atomless :
    NullSingletonClass (P.originalFixedUpperLaw : Measure ℝ) := by
  constructor
  intro v
  change cond (valueLaw P) P.fixedUpperValues {v}=0
  rw [cond_apply (show MeasurableSet P.fixedUpperValues from measurableSet_Ici)]
  have hz : valueLaw P (P.fixedUpperValues ∩ {v})=0 :=
    measure_mono_null inter_subset_right (measure_singleton v)
  rw [hz,mul_zero]

theorem originalFixedUpperLaw_support :
    ∀ᵐ v ∂(P.originalFixedUpperLaw : Measure ℝ), P.vA-P.w ≤ v := by
  change ∀ᵐ v ∂cond (valueLaw P) P.fixedUpperValues, P.vA-P.w ≤ v
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Ici) _

theorem weighted_originalFixedUpperLaw :
    ENNReal.ofReal (activeMass P.theta) •
      (P.originalFixedUpperLaw : Measure ℝ) = P.fixedUpperMeasure := by
  change ENNReal.ofReal (activeMass P.theta) •
    cond (valueLaw P) P.fixedUpperValues=(valueLaw P).restrict P.fixedUpperValues
  rw [←P.fixedUpperValues_mass,Hybrid.measure_smul_cond]

theorem originalFixedUpperLaw_tail (v : ℝ) (hv : P.M ≤ v) :
    (P.originalFixedUpperLaw : Measure ℝ).real (Ioi v)=
      P.zeta*powerTail P.M 10 v := by
  have he := congrArg (fun μ : Measure ℝ => μ.real (Ioi v)) P.weighted_originalFixedUpperLaw
  rw [measureReal_def,Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal P.active_mass_pos.le] at he
  change activeMass P.theta*(P.originalFixedUpperLaw : Measure ℝ).real (Ioi v)=
    P.fixedUpperMeasure.real (Ioi v) at he
  rw [P.fixedUpperMeasure_tail v hv] at he
  exact (mul_left_cancel₀ P.active_mass_pos.ne') (he.trans (by ring))

theorem originalFixedUpperLaw_unbounded (T : ℝ) :
    0 < (P.originalFixedUpperLaw : Measure ℝ).real (Ioi T) := by
  let v := max P.M T
  have hv0 : 0< v := P.M_pos.trans_le (le_max_left _ _)
  have htail : 0<(P.originalFixedUpperLaw : Measure ℝ).real (Ioi v) := by
    rw [P.originalFixedUpperLaw_tail v (le_max_left _ _)]
    unfold powerTail
    exact mul_pos P.zeta_pos (Real.rpow_pos_of_pos (div_pos hv0 P.M_pos) _)
  exact htail.trans_le (measureReal_mono (Ioi_subset_Ioi (le_max_right _ _)))

theorem original_tail_weight_bounds :
    activeMass P.theta*P.zeta ∈ Icc (0:ℝ) 1 := by
  refine ⟨mul_nonneg P.active_mass_pos.le P.zeta_pos.le,?_⟩
  exact (mul_le_mul_of_nonneg_left P.zeta_lt_one.le P.active_mass_pos.le).trans
    (by simpa only [mul_one] using P.activeMass_le_one)

def originalFixedUpperBid (m : ℕ) (R : ℝ) : ℝ → ℝ :=
  bid (rank P.fixedUpperMeasure (m-1) (marketCapacity m) 2) (P.vA-P.w) R

theorem exists_originalFixedUpperJoint (m : ℕ) (hm : 200≤ m)
    (R : ℝ) (hR : 0< R) (hRt : R< P.vA-P.w) :
    Continuous (P.originalFixedUpperBid m R) ∧
    (∀ v, P.vA-P.w≤ v → R≤ P.originalFixedUpperBid m R v ∧
      P.originalFixedUpperBid m R v≤ v) ∧
    ∃ hb : Measurable (P.originalFixedUpperBid m R),
      ∃ PH : ProbabilityMeasure (ℝ×JointAction 2),
      PH=Hybrid.upperJoint P.originalFixedUpperLaw (P.originalFixedUpperBid m R) hb ∧
      (PH : Measure (ℝ×JointAction 2)).map Prod.fst=
        (P.originalFixedUpperLaw : Measure ℝ) ∧
      (PH : Measure (ℝ×JointAction 2)).map (fun x => x.2.bid)=
        (P.originalFixedUpperLaw : Measure ℝ).map (P.originalFixedUpperBid m R) ∧
      (∀ᵐ x ∂(PH : Measure (ℝ×JointAction 2)), R≤ x.2.bid ∧ x.2.routeCount=1) ∧
      (∀ y : ℝ, (PH : Measure (ℝ×JointAction 2)) {x | x.2.bid=y}=0) := by
  have hc := capacity_bounds m hm
  have h := exists_original_upper_joint P.originalFixedUpperLaw
    (activeMass P.theta) P.active_mass_pos P.activeMass_le_one m (marketCapacity m)
    (by omega) hc.2.2.1 hc.2.2.2 (P.vA-P.w) R hR hRt P.originalFixedUpperLaw_support
  simpa only [P.weighted_originalFixedUpperLaw,originalFixedUpperBid] using h

theorem originalFixedUpperEnvelope (m : ℕ) (hm : 200≤ m)
    (R : ℝ) (hR : 0< R) (hRt : R< P.vA-P.w) :
    UpperEnvelopeProperties P.fixedUpperMeasure (m-2) (marketCapacity m)
      (rank P.fixedUpperMeasure (m-1) (marketCapacity m) 2)
      (P.originalFixedUpperBid m R)
      (utility (rank P.fixedUpperMeasure (m-1) (marketCapacity m) 2) (P.vA-P.w) R)
      (P.vA-P.w) R
      (error (rank P.fixedUpperMeasure (m-1) (marketCapacity m) 2) (P.vA-P.w) R) := by
  exact original_fixed_upper_envelope P.fixedUpperMeasure P.fixedUpperMeasure_mass_small
    (P.vA-P.w) R P.M (activeMass P.theta*P.zeta) hR hRt P.fixedUpperBase_le_tail
    P.original_tail_weight_bounds P.fixedUpperMeasure_support P.fixedUpperMeasure_tail m hm

theorem originalFixedUpperBid_tendsto (R : ℝ) (hR : 0< R) (hRt : R< P.vA-P.w)
    (v : ℝ) (hv : P.vA-P.w≤ v) :
    Tendsto (fun m => P.originalFixedUpperBid m R v) atTop (𝓝 R) :=
  original_fixed_upper_bid_tendsto P.fixedUpperMeasure P.fixedUpperMeasure_mass_small
    (P.vA-P.w) R P.M (activeMass P.theta*P.zeta) hR hRt P.fixedUpperBase_le_tail
    P.original_tail_weight_bounds P.fixedUpperMeasure_support P.fixedUpperMeasure_tail v hv

theorem originalFixedUpperConditional_tendsto
    {Seed : Type*} [MeasurableSpace Seed]
    (R : ℝ) (hR : 0< R) (hRt : R< P.vA-P.w)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hN200 : ∀ k, 200≤ N k)
    (Γ : ∀ k, FiniteGame (N k) 2 (marketCapacity (N k)) Seed)
    (hmean : ∀ k (i : Fin (N k)) (y : ℝ), R≤ y →
      meanAcceptProb (Γ k) i y=bidRank P.fixedUpperMeasure (N k-1)
        (marketCapacity (N k)) 2 (P.originalFixedUpperBid (N k) R) y)
    (hσ : ∀ k v, P.vA-P.w≤ v → (Γ k).σ v=
      Measure.dirac (Hybrid.upperAction (P.originalFixedUpperBid (N k) R) v)) :
    ∀ v, P.vA-P.w≤ v → ∀ f : Fin 3 → ℝ,
      Tendsto (fun k => (conditionalTypeCountLaw (Γ k)
        (by have := hN200 k;omega) v).expect f) atTop (𝓝 (f 1)) :=
  native_original_fixed_upper_conditional_tendsto P.fixedUpperMeasure
    P.fixedUpperMeasure_mass_small (P.vA-P.w) R hR hRt P.fixedUpperMeasure_support
    N hN hN200 Γ hmean hσ

def originalMovingRankConstant : ℝ := activeMass P.theta*P.zeta*P.M^10/2

theorem originalMovingRankConstant_nonneg : 0≤ P.originalMovingRankConstant := by
  unfold originalMovingRankConstant
  exact div_nonneg (mul_nonneg (mul_nonneg P.active_mass_pos.le P.zeta_pos.le)
    (pow_nonneg P.M_pos.le _)) (by norm_num)

theorem originalMovingTail_exact (m : ℕ) (hm : P.M≤ movingThreshold m)
    (v : ℝ) (hv : movingThreshold m≤ v) :
    (P.movingUpperMeasure (movingThreshold m)).real (Ioi v)=
      (2*P.originalMovingRankConstant/(m:ℝ)^2)*powerTail (movingThreshold m) 10 v := by
  rw [P.movingUpperMeasure_relative _ hm v hv]
  have hcoef : activeMass P.theta*P.zeta*powerTail P.M 10 (movingThreshold m)=
      2*P.originalMovingRankConstant/(m:ℝ)^2 := by
    rw [powerTail_ten P.M _ P.M_pos (P.M_pos.trans_le hm),div_pow,
      movingThreshold_pow_ten m]
    unfold originalMovingRankConstant
    ring
  rw [hcoef]

theorem originalMovingUpper_scaled_limits (R : ℕ → ℝ)
    (hR : ∀ᶠ m : ℕ in atTop, 0≤ R m ∧ R m≤ movingThreshold m) :
    Tendsto (fun m => movingThreshold m^2*
      originalMovingDeficit (fun n => P.movingUpperMeasure (movingThreshold n)) m)
      atTop (𝓝 0) ∧
    Tendsto (fun m => movingThreshold m*
      originalMovingError (fun n => P.movingUpperMeasure (movingThreshold n)) R m)
      atTop (𝓝 0) := by
  apply original_moving_upper_scaled_limits _ R P.originalMovingRankConstant
    P.originalMovingRankConstant_nonneg
  filter_upwards [hR,tendsto_atTop.1 movingThreshold_tendsto P.M] with m hRm hM
  exact ⟨hRm.1,hRm.2,P.originalMovingTail_exact m hM⟩

end ValueParameters
namespace OriginalValues
export ValueParameters (fixedUpperBase_pos fixedUpperBase_le_tail activeMass_le_one fixedUpperValues_mass fixedUpperValues_pos originalFixedUpperLaw originalFixedUpperLaw_support weighted_originalFixedUpperLaw originalFixedUpperLaw_tail originalFixedUpperLaw_unbounded original_tail_weight_bounds originalFixedUpperBid exists_originalFixedUpperJoint originalFixedUpperEnvelope originalFixedUpperBid_tendsto originalFixedUpperConditional_tendsto originalMovingRankConstant originalMovingRankConstant_nonneg originalMovingTail_exact originalMovingUpper_scaled_limits)
end OriginalValues
end FCAppendix.Affine.Tail04
