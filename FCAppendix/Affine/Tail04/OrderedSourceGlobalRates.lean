import FCAppendix.Affine.Tail04.OrderedSourceMarketEstimates
import FCAppendix.Affine.Tail04.SourceFloorRates

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourceGlobalRates
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open OriginalValues SourceMenuPopulation SourceMomentRectangle
open SourceMovingScalarGuards SourceMovingMenuRates OrderedSourceMarketEstimates CanonicalFailure

theorem partial_scaled (P : ValueParameters) {ξ : ℝ} (hξ : 0< ξ) :
    Tendsto (fun N=> cutoff N^2*OrderedZeroSourcePartialCount.error P ξ N) atTop (𝓝 0) := by
  have hs := cutoff_square_over_sqrt
  have h0 := cutoff_square_exponential
    (show 0<(lowMass P.theta)^2/2 by have h:=P.low_mass_pos;positivity)
  have h1 := cutoff_square_exponential
    (show 0< P.bulkWeight^2/2 by have h:=P.bulkWeight_pos;positivity)
  have hA := cutoff_square_exponential
    (show 0<(radius ξ (centerMoment P false))^2/50 by
      have h:=SourcePartialPublicGuard.guard_radius_positive P hξ false;positivity)
  have hR := cutoff_square_exponential
    (show 0<(radius ξ (centerMoment P true))^2/50 by
      have h:=SourcePartialPublicGuard.guard_radius_positive P hξ true;positivity)
  have hh := ((((hs.const_mul (75/2)).add
    (((hA.const_mul (10*(1-P.theta))).add (hR.const_mul (10*P.theta))).const_mul 2)).add
      (h0.const_mul 2)).add h1).const_mul 2
  convert! hh using 1
  · funext N
    unfold OrderedZeroSourcePartialCount.error SourcePartialPublicGuard.badBound SourcePartialPublicGuard.error
    rw [show -(N:ℝ)*(lowMass P.theta)^2/2=-((lowMass P.theta)^2/2)*(N:ℝ) by ring,
      show -(N:ℝ)*P.bulkWeight^2/2=-(P.bulkWeight^2/2)*(N:ℝ) by ring,
      show -(N:ℝ)*(radius ξ (centerMoment P false))^2/50=
        -((radius ξ (centerMoment P false))^2/50)*(N:ℝ) by ring,
      show -(N:ℝ)*(radius ξ (centerMoment P true))^2/50=
        -((radius ξ (centerMoment P true))^2/50)*(N:ℝ) by ring]
    ring
  · simp

theorem low_scaled (P : ValueParameters) :
    Tendsto (fun N=> cutoff N^2*OrderedSourceLowCountLaws.error P N) atTop (𝓝 0) := by
  have hh := (cutoff_square_exponential
    (show 0<2*(OrderedSourceLowCountLaws.gap P)^2 by
      have h:=OrderedSourceLowCountLaws.gap_positive P;positivity)).const_mul 2
  convert! hh using 1
  · funext N
    unfold OrderedSourceLowCountLaws.error
    rw [show -2*(N:ℝ)*(OrderedSourceLowCountLaws.gap P)^2=
      -(2*(OrderedSourceLowCountLaws.gap P)^2)*(N:ℝ) by ring]
    ring
  · simp

def total (P : ValueParameters) (ξ u : ℝ) (N : ℕ) : ℝ :=
  commonRate P ξ N+SourceUnusedConstants.rate P ξ u N+
    OrderedZeroSourcePartialCount.error P ξ N+OrderedSourceLowCountLaws.error P N

lemma total_nonneg (P : ValueParameters) {ξ u : ℝ} (hξ : 0< ξ)
    (huB : 1+u< Central.B ξ) (N : ℕ) : 0≤ total P ξ u N := by
  have h0:=commonRate_nonneg P hξ N
  have h1:=SourceUnusedConstants.rate_nonneg P hξ huB N
  have h2:=OrderedZeroSourcePartialCount.error_nonnegative P ξ N
  unfold total OrderedSourceLowCountLaws.error
  positivity

lemma components_le (P : ValueParameters) {ξ u : ℝ} (hξ : 0< ξ)
    (huB : 1+u< Central.B ξ) (N : ℕ) :
    commonRate P ξ N≤ total P ξ u N ∧
      SourceUnusedConstants.rate P ξ u N≤ total P ξ u N ∧
      OrderedZeroSourcePartialCount.error P ξ N≤ total P ξ u N ∧
      OrderedSourceLowCountLaws.error P N≤ total P ξ u N := by
  have h0:=commonRate_nonneg P hξ N
  have h1:=SourceUnusedConstants.rate_nonneg P hξ huB N
  have h2:=OrderedZeroSourcePartialCount.error_nonnegative P ξ N
  have h3 : 0≤ OrderedSourceLowCountLaws.error P N := by unfold OrderedSourceLowCountLaws.error;positivity
  unfold total
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem total_scaled (P : ValueParameters) {ξ : ℝ} (hξ : 0< ξ) (u : ℝ) :
    Tendsto (fun N=> cutoff N^2*total P ξ u N) atTop (𝓝 0) := by
  have h0 := SourceMovingMenuRates.scaled_rate_tendsto
    (K:=OrderedSourceCommonMenuError.commonCoefficient P ξ) P.low_mass_pos P.bulkWeight_pos
  have hh := ((h0.add (SourceUnusedConstants.scaled_rate_tendsto P ξ u)).add
    (partial_scaled P hξ)).add (low_scaled P)
  convert! hh using 1
  · funext N
    unfold total commonRate
    ring
  · simp

theorem total_tendsto (P : ValueParameters) {ξ u : ℝ} (hξ : 0< ξ)
    (huB : 1+u< Central.B ξ) : Tendsto (total P ξ u) atTop (𝓝 0) := by
  apply squeeze_zero (fun N=> total_nonneg P hξ huB N) _ (total_scaled P hξ u)
  intro N
  have ht : 1≤ cutoff N := movingThreshold_ge_one (N+1) (by omega)
  have hs : 1≤ cutoff N^2 := by nlinarith
  have hh:=mul_le_mul_of_nonneg_right hs (total_nonneg P hξ huB N)
  simpa using hh

def utilityError (P : ValueParameters) (ξ u : ℝ) (N : ℕ) : ℝ :=
  (cutoff N+2*Central.B ξ)*total P ξ u N

lemma utilityError_nonneg (P : ValueParameters) {ξ u : ℝ} (hξ : 0< ξ)
    (huB : 1+u< Central.B ξ) (N : ℕ) : 0≤ utilityError P ξ u N := by
  have ht : 0< cutoff N := movingThreshold_pos (N+1) (by omega)
  have hB : 0< Central.B ξ := by unfold Central.B;linarith
  exact mul_nonneg (by linarith) (total_nonneg P hξ huB N)

lemma total_le_utilityError (P : ValueParameters) {ξ u : ℝ} (hξ : 0< ξ)
    (huB : 1+u< Central.B ξ) (N : ℕ) : total P ξ u N≤ utilityError P ξ u N := by
  have ht : 1≤ cutoff N := movingThreshold_ge_one (N+1) (by omega)
  have hB : 0≤ Central.B ξ := by unfold Central.B;linarith
  have hh:=mul_le_mul_of_nonneg_right (show 1≤ cutoff N+2*Central.B ξ by linarith)
    (total_nonneg P hξ huB N)
  simpa only [one_mul,utilityError] using hh

theorem utility_tendsto (P : ValueParameters) {ξ u : ℝ} (hξ : 0< ξ)
    (huB : 1+u< Central.B ξ) : Tendsto (utilityError P ξ u) atTop (𝓝 0) := by
  have hB : 0≤ Central.B ξ := by unfold Central.B;linarith
  have hc : Tendsto (fun N=>(1+2*Central.B ξ)*(cutoff N^2*total P ξ u N)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (total_scaled P hξ u).const_mul (1+2*Central.B ξ)
  apply squeeze_zero (fun N=> utilityError_nonneg P hξ huB N) _ hc
  intro N
  have ht : 1≤ cutoff N := movingThreshold_ge_one (N+1) (by omega)
  have hfac : cutoff N+2*Central.B ξ≤(1+2*Central.B ξ)*cutoff N^2 := by
    nlinarith [mul_nonneg hB (show 0≤ cutoff N^2-1 by nlinarith)]
  have hh:=mul_le_mul_of_nonneg_right hfac (total_nonneg P hξ huB N)
  simpa only [utilityError,mul_assoc] using hh

structure Budgets (P : ValueParameters) (ξ u k κ : ℝ) (N : ℕ) : Prop where
  cutoff_large : 100≤ cutoff N
  utility_small : utilityError P ξ u N< ξ/1000
  bulk_extension : 2*utilityError P ξ u N< κ*u
  partial_duplicate : 10*total P ξ u N<(1-2*ξ)*Central.R ξ*(1-P.theta)
  active_failure : cutoff N^2*total P ξ u N≤ movingCoefficient P ξ k/2
  other_failure : movingCoefficient P ξ k/(4*cutoff N^2)+total P ξ u N<
    min P.theta (min ((probabilityGap ξ)^2) 1)
  low_room : (MenuError.iidCapacity (99/200) N:ℝ)≤(N:ℝ)*(activeMass P.theta-
    activeMass P.theta*P.zeta*powerTail P.M 10 (cutoff N)-OrderedSourceLowCountLaws.gap P)
  unused_room : (∀reg,4*ξ/((N:ℝ)*centerMoment P reg)≤ γ ξ) ∧ 1≤ P.bulkWeight*(N:ℝ)/2

theorem eventually_budgets (P : ValueParameters) {ξ u k κ : ℝ}
    (hξ : 0< ξ) (hξh : ξ<1/2) (hu : 0< u) (huB : 1+u< Central.B ξ)
    (hk : 0< k) (hκ : 0< κ) : ∀ᶠN in atTop,Budgets P ξ u k κ N := by
  have hC := movingCoefficient_pos P hξ hk
  have hd : 0< min P.theta (min ((probabilityGap ξ)^2) 1) :=
    lt_min P.theta_pos (lt_min (sq_pos_of_pos (probabilityGap_pos hξ)) (by norm_num))
  have hdup : 0<(1-2*ξ)*Central.R ξ*(1-P.theta) := by
    have hR : 0< Central.R ξ := by unfold Central.R;linarith
    have hθ : 0<1-P.theta := by linarith only [P.theta_small]
    have hξ2 : 0<1-2*ξ := by linarith only [hξh]
    exact mul_pos (mul_pos hξ2 hR) hθ
  have he := utility_tendsto P hξ huB
  have hr := total_tendsto P hξ huB
  have hc : Tendsto (fun N=> movingCoefficient P ξ k/(4*cutoff N^2)) atTop (𝓝 0) := by
    have hh : Tendsto (fun N=>(movingCoefficient P ξ k/4)/cutoff N) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop cutoff_tendsto
    have hh' := hh.div_atTop cutoff_tendsto
    convert! hh' using 1
    funext N
    ring
  have hother : Tendsto (fun N=> movingCoefficient P ξ k/(4*cutoff N^2)+total P ξ u N) atTop (𝓝 0) := by
    simpa only [add_zero] using hc.add hr
  have hbulk : Tendsto (fun N => 2*utilityError P ξ u N) atTop (𝓝 0) := by
    simpa only [mul_zero] using he.const_mul 2
  have hroute : Tendsto (fun N => 10*total P ξ u N) atTop (𝓝 0) := by
    simpa only [mul_zero] using hr.const_mul 10
  filter_upwards [cutoff_tendsto.eventually_ge_atTop (100:ℝ),
    he.eventually (gt_mem_nhds (by positivity : 0< ξ/1000)),
    hbulk.eventually (gt_mem_nhds (mul_pos hκ hu)),
    hroute.eventually (gt_mem_nhds hdup),
    (total_scaled P hξ u).eventually (gt_mem_nhds (half_pos hC)),
    hother.eventually (gt_mem_nhds hd),OrderedSourceLowCountLaws.eventually_room P,
    SourceUnusedConstants.eventually_budgets P hξ]
      with N hsize hsmall hbulk hroute hactive hother hlow hroom
  refine ⟨hsize,hsmall,hbulk,hroute,hactive.le,hother,?_,hroom⟩
  simpa only [MenuError.iidCapacity,Markets.capacity,cutoff,Nat.cast_add,Nat.cast_one] using hlow.2.2

end FCAppendix.Affine.Tail04.OrderedSourceGlobalRates
