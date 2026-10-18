import FCAppendix.Exclusive.NarrowExistenceGameReference

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Existence
open MeasureTheory ProbabilityTheory Set Filter Topology

theorem hasDerivAt_polynomialFirst (n : ℕ) (f : ℕ → ℝ) (p : ℝ) :
    HasDerivAt (polynomialFirst n f) (polynomialSecond n f p) p :=
  ((contDiff_binomialPolynomialDerivative n f).differentiable (by simp) p).hasDerivAt

def finiteRowState {m : ℕ} {V : Type*} (d c : ℕ) (baseRatio : ℝ)
    (beta : V → ℝ) (v z : ℝ) (omega : RivalProfile m V) : RowState :=
  let W := rivalInverseSum (1/(d:ℝ)) beta omega
  let s := logShare (1/(d:ℝ)) W z
  ![((1+activeCount omega-c:ℕ):ℝ)*s, s, Real.exp z, v, baseRatio]

theorem finiteRowScore_eq_sourceStateScore {m : ℕ} {V : Type*} (d c : ℕ)
    (a : UserTariff) (G : Schedule (d+1)) (p0 baseRatio : ℝ)
    (beta : V → ℝ) (v z : ℝ) (omega : RivalProfile m V) :
    finiteRowScore d c a G p0 baseRatio beta v z omega =
      sourceStateScore d a G p0 (finiteRowState d c baseRatio beta v z omega) := by
  dsimp [finiteRowScore, score, logVelocity, logAllocation, finiteRowState, sourceStateScore,
    normalizedR, sourceSFirst, sourceHFirst]
  ring

theorem hasDerivAt_finiteRowScore {m : ℕ} {V : Type*} (d c : ℕ)
    (a : UserTariff) (G : Schedule (d+1)) (p0 baseRatio : ℝ)
    (beta : V → ℝ) (v z : ℝ) (omega : RivalProfile m V) :
    HasDerivAt (fun x => finiteRowScore d c a G p0 baseRatio beta v x omega)
      (-sourceStateCurvature d a G p0 (finiteRowState d c baseRatio beta v z omega)) z := by
  have h := hasDerivAt_score (1/(d:ℝ)) ((1+activeCount omega-c:ℕ):ℝ)
    (rivalInverseSum (1/(d:ℝ)) beta omega)
    (v*sourceValueFactor d a p0) (baseRatio*sourceValueFactor d a p0) z
    (rivalInverseSum_nonneg _ _ omega)
    (polynomialFirst (d+1) successIndicator) (polynomialSecond (d+1) successIndicator)
    (binomialPolynomial (d+1) a.charge) (polynomialFirst (d+1) a.charge)
    (polynomialSecond (d+1) a.charge) (polynomialFirst (d+1) G.charge)
    (polynomialSecond (d+1) G.charge)
    (hasDerivAt_polynomialFirst _ _ _) (hasDerivAt_binomialPolynomial _ _ _)
    (hasDerivAt_polynomialFirst _ _ _) (hasDerivAt_polynomialFirst _ _ _)
  apply h.congr_deriv
  dsimp [sourceStateCurvature, normalizedCurvature, normalizedR, sourceSFirst, sourceSSecond,
    sourceHFirst, sourceHSecond, finiteRowState, logAllocation, ownHessian]
  ring

theorem actualCross_eq_sourceStateInfluence {m : ℕ} {V : Type*} (d c : ℕ)
    (a : UserTariff) (G : Schedule (d+1)) (p0 baseRatio : ℝ)
    (beta : V → ℝ) (v z : ℝ) (omega : RivalProfile m V) :
    actualCross (1/(d:ℝ)) ((1+activeCount omega-c:ℕ):ℝ)
      (rivalInverseSum (1/(d:ℝ)) beta omega)
      (v*sourceValueFactor d a p0) (baseRatio*sourceValueFactor d a p0) z
      (polynomialFirst (d+1) successIndicator) (polynomialSecond (d+1) successIndicator)
      (polynomialFirst (d+1) a.charge) (polynomialSecond (d+1) a.charge)
      (polynomialFirst (d+1) G.charge) (polynomialSecond (d+1) G.charge) =
    sourceStateInfluence d a G p0 (finiteRowState d c baseRatio beta v z omega) := by
  dsimp [actualCross, sourceStateInfluence, normalizedInfluence, normalizedR, sourceSFirst,
    sourceSSecond, sourceHFirst, sourceHSecond, finiteRowState, logAllocation, crossCoefficient]
  ring

theorem continuous_finiteRowState {m : ℕ} {V : Type*} [TopologicalSpace V]
    (d c : ℕ) (baseRatio : ℝ) (beta : V → ℝ) (hbeta : Continuous beta) (v z : ℝ) :
    Continuous (finiteRowState (m := m) d c baseRatio beta v z) := by
  have hW := continuous_rivalInverseSum (m := m) (1/(d:ℝ)) beta hbeta
  have hden : Continuous (fun omega : RivalProfile m V =>
      rivalInverseSum (1/(d:ℝ)) beta omega+Real.exp (-(1/(d:ℝ))*z)) := hW.add_const _
  have hdenpos (omega : RivalProfile m V) :
      0 < rivalInverseSum (1/(d:ℝ)) beta omega+Real.exp (-(1/(d:ℝ))*z) :=
    add_pos_of_nonneg_of_pos (rivalInverseSum_nonneg _ _ omega) (Real.exp_pos _)
  have hs : Continuous (fun omega : RivalProfile m V =>
      logShare (1/(d:ℝ)) (rivalInverseSum (1/(d:ℝ)) beta omega) z) :=
    continuous_const.div hden (fun omega => (hdenpos omega).ne')
  have hN : Continuous (fun omega : RivalProfile m V => ((1+activeCount omega-c:ℕ):ℝ)) :=
    (continuous_of_discreteTopology : Continuous (fun N : ℕ => ((1+N-c:ℕ):ℝ))).comp
      continuous_activeCount
  apply continuous_pi
  intro i
  fin_cases i
  · exact hN.mul hs
  · exact hs
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const

theorem continuous_finiteRowScore {m : ℕ} {V : Type*} [TopologicalSpace V]
    (d c : ℕ) (a : UserTariff) (G : Schedule (d+1)) (p0 baseRatio : ℝ)
    (beta : V → ℝ) (hbeta : Continuous beta) (v z : ℝ) :
    Continuous (finiteRowScore (m := m) d c a G p0 baseRatio beta v z) := by
  have he : finiteRowScore (m := m) d c a G p0 baseRatio beta v z =
      sourceStateScore d a G p0 ∘ finiteRowState d c baseRatio beta v z :=
    funext (finiteRowScore_eq_sourceStateScore d c a G p0 baseRatio beta v z)
  rw [he]
  exact (continuous_sourceStateScore d a G p0).comp
    (continuous_finiteRowState d c baseRatio beta hbeta v z)

theorem integrable_finiteRowScore {m : ℕ} {V : Type*} [TopologicalSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [CompactSpace V]
    (d c : ℕ) (a : UserTariff) (G : Schedule (d+1)) (p0 baseRatio : ℝ)
    (h : unitInterval) (nu : Measure V) [IsProbabilityMeasure nu]
    (beta : V → ℝ) (hbeta : Continuous beta) (v z : ℝ) :
    Integrable (finiteRowScore (m := m) d c a G p0 baseRatio beta v z) (iidRivalLaw m h nu) := by
  have hc := continuous_finiteRowScore (m := m) d c a G p0 baseRatio beta hbeta v z
  obtain ⟨B, _hB, hB⟩ := compact_curvature_bounds _ _ hc hc Set.univ isCompact_univ
  apply Integrable.of_bound hc.measurable.aestronglyMeasurable B
  filter_upwards [] with omega
  simpa only [Real.norm_eq_abs] using (hB omega (Set.mem_univ _)).1

theorem finiteExpectedScore_affine {m : ℕ} {V : Type*} [TopologicalSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [CompactSpace V]
    (d c : ℕ) (eta : ℝ) (G : Schedule (d+1)) (p0 baseRatio : ℝ)
    (h : unitInterval) (nu : Measure V) [IsProbabilityMeasure nu]
    (beta : V → ℝ) (hbeta : Continuous beta) (v z : ℝ) :
    finiteExpectedScore (m := m) d c (.affine eta) G p0 baseRatio h nu beta v z =
      (1-eta)*finiteExpectedScore (m := m) d c (.affine 0) G p0 baseRatio h nu beta v z+
        eta*finiteExpectedScore (m := m) d c (.affine 1) G p0 baseRatio h nu beta v z := by
  unfold finiteExpectedScore
  have he := funext (finiteRowScore_affine (m := m) d c eta G p0 baseRatio beta v z)
  rw [he, integral_add
    ((integrable_finiteRowScore d c (.affine 0) G p0 baseRatio h nu beta hbeta v z).const_mul _)
    ((integrable_finiteRowScore d c (.affine 1) G p0 baseRatio h nu beta hbeta v z).const_mul _),
    integral_const_mul, integral_const_mul]

end FCAppendix.Exclusive.Narrow.Existence
