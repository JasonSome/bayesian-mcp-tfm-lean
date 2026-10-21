import FCAppendix.Affine.Tail04.SourceFloorRates
import FCAppendix.Affine.Tail04.CanonicalFailure

noncomputable section
namespace FCAppendix.Affine.Tail04.SourceUpperBudgets
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open OriginalValues SourceMovingScalarGuards SourceMovingMenuRates
open Existence.RankEnvelope SourceFloorRates

def zeroError (P : ValueParameters) (N : ℕ) : ℝ :=
  OriginalMovingUpperEnvelope.E P (cutoff N) (N+1) (capacity N) 0

lemma zeroError_eq (P : ValueParameters) (N : ℕ) :
    zeroError P N=originalMovingError
      (fun n=> P.movingUpperMeasure (movingThreshold n)) (fun _=>0) (N+1) := by
  simp only [zeroError,OriginalMovingUpperEnvelope.E,OriginalMovingUpperEnvelope.q,
    originalMovingError,cutoff,capacity_eq]

lemma zeroError_nonneg (P : ValueParameters) (N : ℕ) : 0≤ zeroError P N := by
  apply Existence.RankEnvelope.error_nonneg
  · exact (movingThreshold_pos (N+1) (by omega)).le
  · intro v
    exact (Existence.RankEnvelope.rank_bounds (P.movingUpperMeasure (cutoff N))
      ((N+1)-1) (capacity N) (by norm_num)
      (OriginalMovingUpperEnvelope.measure_mass_le_one P (cutoff N)) v).2

lemma error_le_zero (P : ValueParameters) (N : ℕ) {H : ℝ} (hH : 0≤ H) :
    OriginalMovingUpperEnvelope.E P (cutoff N) (N+1) (capacity N) H≤ zeroError P N := by
  have hd:=sub_nonneg.mpr (SourceFloorRates.q_bounds P N).2
  have hh:=mul_nonneg hH hd
  change (cutoff N-H)*(1-q P N)+_≤(cutoff N-0)*(1-q P N)+_
  linarith

theorem scaled_zeroError (P : ValueParameters) :
    Tendsto (fun N=> cutoff N*zeroError P N) atTop (𝓝 0) := by
  have hz : ∀ᶠm : ℕ in atTop,0≤(0:ℝ) ∧ (0:ℝ)≤ movingThreshold m :=
    Eventually.of_forall (fun m=>⟨le_rfl,Real.rpow_nonneg (Nat.cast_nonneg m) _⟩)
  have hh:=(P.originalMovingUpper_scaled_limits (fun _=>0) hz).2.comp
    (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def,cutoff,←zeroError_eq] using hh

theorem zeroError_tendsto (P : ValueParameters) : Tendsto (zeroError P) atTop (𝓝 0) := by
  apply squeeze_zero (zeroError_nonneg P) _ (scaled_zeroError P)
  intro N
  simpa only [one_mul,cutoff] using mul_le_mul_of_nonneg_right
    (movingThreshold_ge_one (N+1) (by omega)) (zeroError_nonneg P N)

theorem eventually_hidden (P : ValueParameters) {ξ : ℝ} (hξh : ξ<1/2) :
    ∀ᶠN in atTop,∀H : ℝ,1≤ H→
      OriginalMovingUpperEnvelope.E P (cutoff N) (N+1) (capacity N) H<
        (1-2*ξ)*H*(1-2*(1-q P N)) := by
  have hη : 0<1-2*ξ := by linarith
  have he:=(zeroError_tendsto P).eventually (gt_mem_nhds (by positivity : 0<(1-2*ξ)/2))
  have hq:=(q_tendsto P).eventually (lt_mem_nhds (by norm_num : (3/4:ℝ)<1))
  filter_upwards [he,hq] with N heN hqN
  intro H hH
  have hp : 0<1-2*(1-q P N) := by linarith
  have hm:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hH hη.le) hp.le
  have hl : (1-2*ξ)/2<(1-2*ξ)*(1-2*(1-q P N)) := by
    nlinarith [mul_pos hη (show 0< q P N-3/4 by linarith)]
  exact (error_le_zero P N (by linarith)).trans_lt
    (heN.trans (hl.trans_le (by simpa only [mul_one] using hm)))

theorem eventually_slope (P : ValueParameters) {d : ℝ} (hd : 0< d) :
    ∀ᶠN in atTop,1-d/cutoff N^2< q P N := by
  filter_upwards [(scaled_deficit P).eventually (gt_mem_nhds hd)] with N hN
  have ht:=movingThreshold_pos (N+1) (by omega)
  change 0< cutoff N at ht
  have hh : 1-q P N< d/cutoff N^2 := (lt_div_iff₀ (sq_pos_of_pos ht)).mpr (by nlinarith only [hN])
  linarith

theorem eventually_active_rank (P : ValueParameters) {ξ k : ℝ} (hξ : 0< ξ) (hk : 0< k) :
    ∀ᶠN in atTop,
      rate (SourceCommonMenuError.commonCoefficient P ξ) (lowMass P.theta) P.bulkWeight N+
        (1-q P N)< CanonicalFailure.movingCoefficient P ξ k/cutoff N^2 := by
  have hc:=CanonicalFailure.movingCoefficient_pos P hξ hk
  have hlim:=(scaled_rate_tendsto (K:=SourceCommonMenuError.commonCoefficient P ξ)
    P.low_mass_pos P.bulkWeight_pos).add (scaled_deficit P)
  have hlim' : Tendsto (fun N=> cutoff N^2*
      (rate (SourceCommonMenuError.commonCoefficient P ξ) (lowMass P.theta) P.bulkWeight N+
        (1-q P N))) atTop (𝓝 0) := by
    convert! hlim using 1
    · funext N
      ring
    · ring
  filter_upwards [hlim'.eventually (gt_mem_nhds hc)] with N hN
  have ht:=movingThreshold_pos (N+1) (by omega)
  change 0< cutoff N at ht
  apply (lt_div_iff₀ (sq_pos_of_pos ht)).mpr
  nlinarith only [hN]

structure Budget (P : ValueParameters) (ξ k : ℝ) (N : ℕ) : Prop where
  hidden : ∀H : ℝ,1≤ H→
    OriginalMovingUpperEnvelope.E P (cutoff N) (N+1) (capacity N) H<
      (1-2*ξ)*H*(1-2*(1-q P N))
  active : rate (SourceCommonMenuError.commonCoefficient P ξ) (lowMass P.theta) P.bulkWeight N+
    (1-q P N)< CanonicalFailure.movingCoefficient P ξ k/cutoff N^2
  lowerSlope : 1-(CanonicalFailure.movingCoefficient P ξ k/4)/cutoff N^2< q P N

theorem eventually_budget (P : ValueParameters) {ξ k : ℝ}
    (hξ : 0< ξ) (hξh : ξ<1/2) (hk : 0< k) :
    ∀ᶠN in atTop,Budget P ξ k N := by
  have hc:=CanonicalFailure.movingCoefficient_pos P hξ hk
  filter_upwards [eventually_hidden P hξh,eventually_active_rank P hξ hk,
    eventually_slope P (show 0< CanonicalFailure.movingCoefficient P ξ k/4 by positivity)]
      with N hh ha hs
  exact ⟨hh,ha,hs⟩

end FCAppendix.Affine.Tail04.SourceUpperBudgets
