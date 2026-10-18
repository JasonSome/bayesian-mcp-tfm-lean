import FCAppendix.Exclusive.NarrowExistenceGameScore
import FCAppendix.Exclusive.NarrowExistenceNeighborhood

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Existence
open MeasureTheory Set Filter Topology

theorem successFirst_eq (d : ℕ) (p : ℝ) :
    polynomialFirst (d+1) successIndicator p = ((d+1:ℕ):ℝ)*(1-p)^d := by
  have he : binomialPolynomial (d+1) successIndicator = PayOnce.success (d+1) :=
    funext (binomialPolynomial_once (d+1))
  have hd := hasDerivAt_binomialPolynomial (d+1) successIndicator p
  rw [he] at hd
  exact hd.unique (hasDerivAt_success d p)

theorem successSecond_eq (d : ℕ) (hd : 1 ≤ d) (p : ℝ) (hp : p < 1) :
    polynomialSecond (d+1) successIndicator p =
      -((d+1:ℕ):ℝ)*(d:ℝ)*(1-p)^d/(1-p) := by
  have he : polynomialFirst (d+1) successIndicator =
      fun x : ℝ => ((d+1:ℕ):ℝ)*(1-x)^d := funext (successFirst_eq d)
  change deriv (polynomialFirst (d+1) successIndicator) p = _
  rw [he]
  have h := (hasDerivAt_failurePower d hd p hp).const_mul ((d+1:ℕ):ℝ)
  rw [h.deriv]
  ring

def sourceSFirst (d : ℕ) (a : UserTariff) (p0 : ℝ) (p : ℝ) : ℝ :=
  sourceValueFactor d a p0*polynomialFirst (d+1) successIndicator p
def sourceSSecond (d : ℕ) (a : UserTariff) (p0 : ℝ) (p : ℝ) : ℝ :=
  sourceValueFactor d a p0*polynomialSecond (d+1) successIndicator p
def sourceHFirst (d : ℕ) (a : UserTariff) (G : Schedule (d+1)) (p0 p : ℝ) : ℝ :=
  sourceValueFactor d a p0*polynomialFirst (d+1) G.charge p
def sourceHSecond (d : ℕ) (a : UserTariff) (G : Schedule (d+1)) (p0 p : ℝ) : ℝ :=
  sourceValueFactor d a p0*polynomialSecond (d+1) G.charge p

def sourceStateScore (d : ℕ) (a : UserTariff) (G : Schedule (d+1)) (p0 : ℝ)
    (x : RowState) : ℝ :=
  (1/(d:ℝ))*x 0*(1-x 1)*normalizedR
    (sourceSFirst d a p0) (polynomialFirst (d+1) a.charge) (sourceHFirst d a G p0) x -
    x 2*binomialPolynomial (d+1) a.charge (1-x 0)

def sourceStateCurvature (d : ℕ) (a : UserTariff) (G : Schedule (d+1)) (p0 : ℝ) : RowState → ℝ :=
  normalizedCurvature (1/(d:ℝ)) (sourceSFirst d a p0) (sourceSSecond d a p0)
    (binomialPolynomial (d+1) a.charge) (polynomialFirst (d+1) a.charge)
    (polynomialSecond (d+1) a.charge) (sourceHFirst d a G p0) (sourceHSecond d a G p0)

def sourceStateInfluence (d : ℕ) (a : UserTariff) (G : Schedule (d+1)) (p0 : ℝ) : RowState → ℝ :=
  normalizedInfluence (1/(d:ℝ)) (sourceSFirst d a p0) (sourceSSecond d a p0)
    (polynomialFirst (d+1) a.charge) (polynomialSecond (d+1) a.charge)
    (sourceHFirst d a G p0) (sourceHSecond d a G p0)

def sourceReferenceState (p0 : ℝ) : RowState := ![1-p0, 0, 1, 1, 0]

theorem source_reference_firstOrder (d : ℕ) (hd : 1 ≤ d) (a : UserTariff)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    sourceValueFactor d a p*(((d+1:ℕ):ℝ)*(1-p)^d) =
      polynomialFirst (d+1) a.charge p+
        (d:ℝ)*binomialPolynomial (d+1) a.charge p/(1-p) := by
  dsimp only [polynomialFirst]
  rw [binomialPolynomial_tariff_first_eq d hd a p hp0 hp1,
    binomialPolynomial_tariff_eq d a p hp0.le hp1.le,
    tariff_marginal_identity d a p hp1]
  dsimp [sourceValueFactor]
  ring

theorem sourceStateScore_reference (d : ℕ) (hd : 1 ≤ d) (a : UserTariff)
    (G : Schedule (d+1)) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    sourceStateScore d a G p (sourceReferenceState p) = 0 := by
  have hF := source_reference_firstOrder d hd a p hp0 hp1
  have hdne : (d:ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hq : 1-p ≠ 0 := (sub_pos.mpr hp1).ne'
  dsimp [sourceStateScore, sourceReferenceState, normalizedR, sourceSFirst, sourceHFirst]
  simp only [zero_mul, one_mul, sub_zero, sub_sub_cancel]
  rw [successFirst_eq, hF]
  field_simp [hdne, hq]
  ring

theorem sourceStateCurvature_reference (d : ℕ) (hd : 1 ≤ d) (a : UserTariff)
    (G : Schedule (d+1)) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    sourceStateCurvature d a G p (sourceReferenceState p) = literalReferenceCurvature d a p ∧
      sourceStateInfluence d a G p (sourceReferenceState p) = literalReferenceCross d a p := by
  have hF := source_reference_firstOrder d hd a p hp0 hp1
  have hdne : (d:ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hq : 1-p ≠ 0 := (sub_pos.mpr hp1).ne'
  have h := reference_at_firstOrder (d:ℝ) (1-p) 1 (sourceValueFactor d a p)
    (((d+1:ℕ):ℝ)*(1-p)^d)
    (binomialPolynomial (d+1) a.charge p) (polynomialFirst (d+1) a.charge p)
    (polynomialSecond (d+1) a.charge p) hdne hq (by simpa only [one_mul] using hF)
  dsimp [sourceStateCurvature, sourceStateInfluence, normalizedCurvature, normalizedInfluence,
    normalizedR, sourceSFirst, sourceSSecond, sourceHFirst, sourceHSecond,
    sourceReferenceState, literalReferenceCurvature, literalReferenceCross]
  simp only [zero_mul, one_mul, sub_zero, sub_sub_cancel,
    successFirst_eq, successSecond_eq d hd p hp1]
  have hRp : sourceValueFactor d a p*(-((d+1:ℕ):ℝ)*(d:ℝ)*(1-p)^d/(1-p)) =
      -sourceValueFactor d a p*(d:ℝ)*(((d+1:ℕ):ℝ)*(1-p)^d)/(1-p) := by ring
  rw [hRp]
  simpa only [one_mul, polynomialFirst, polynomialSecond] using h

theorem continuous_polynomialFirst (n : ℕ) (f : ℕ → ℝ) :
    Continuous (polynomialFirst n f) := (contDiff_binomialPolynomialDerivative n f).continuous

theorem continuous_polynomialSecond (n : ℕ) (f : ℕ → ℝ) :
    Continuous (polynomialSecond n f) :=
  (contDiff_binomialPolynomialDerivative n f).continuous_deriv (by simp)

theorem continuous_sourceStateScore (d : ℕ) (a : UserTariff)
    (G : Schedule (d+1)) (p0 : ℝ) : Continuous (sourceStateScore d a G p0) := by
  have hS : Continuous (sourceSFirst d a p0) :=
    (continuous_polynomialFirst (d+1) successIndicator).const_mul _
  have hT := continuous_polynomialFirst (d+1) a.charge
  have hG : Continuous (sourceHFirst d a G p0) :=
    (continuous_polynomialFirst (d+1) G.charge).const_mul _
  have hR := continuous_normalizedR (sourceSFirst d a p0) (polynomialFirst (d+1) a.charge)
    (sourceHFirst d a G p0) hS hT hG
  have hP := (contDiff_binomialPolynomial (d+1) a.charge).continuous
  unfold sourceStateScore
  fun_prop

theorem continuous_sourceStateCurvature (d : ℕ) (a : UserTariff)
    (G : Schedule (d+1)) (p0 : ℝ) : Continuous (sourceStateCurvature d a G p0) := by
  exact continuous_normalizedCurvature _ _ _ _ _ _ _ _
    ((continuous_polynomialFirst (d+1) successIndicator).const_mul _)
    ((continuous_polynomialSecond (d+1) successIndicator).const_mul _)
    (contDiff_binomialPolynomial (d+1) a.charge).continuous
    (continuous_polynomialFirst (d+1) a.charge)
    (continuous_polynomialSecond (d+1) a.charge)
    ((continuous_polynomialFirst (d+1) G.charge).const_mul _)
    ((continuous_polynomialSecond (d+1) G.charge).const_mul _)

theorem continuous_sourceStateInfluence (d : ℕ) (a : UserTariff)
    (G : Schedule (d+1)) (p0 : ℝ) : Continuous (sourceStateInfluence d a G p0) := by
  exact continuous_normalizedInfluence _ _ _ _ _ _ _
    ((continuous_polynomialFirst (d+1) successIndicator).const_mul _)
    ((continuous_polynomialSecond (d+1) successIndicator).const_mul _)
    (continuous_polynomialFirst (d+1) a.charge)
    (continuous_polynomialSecond (d+1) a.charge)
    ((continuous_polynomialFirst (d+1) G.charge).const_mul _)
    ((continuous_polynomialSecond (d+1) G.charge).const_mul _)

theorem source_endpoint_neighborhood (d : ℕ) (hd : 1 ≤ d)
    (a : UserTariff) (ha : a.Allowed) (G : Schedule (d+1))
    (p0 scoreTolerance : ℝ) (hp0 : 0 < p0) (hp1 : p0 < 1) (htol : 0 < scoreTolerance) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ x : RowState,
      dist x (sourceReferenceState p0) < delta →
        |sourceStateCurvature d a G p0 x-literalReferenceCurvature d a p0| <
          literalReferenceCurvature d a p0/12 ∧
        |sourceStateInfluence d a G p0 x-literalReferenceCross d a p0| <
          literalReferenceCurvature d a p0/24 ∧
        |sourceStateScore d a G p0 x| < scoreTolerance := by
  have hpos := (literal_reference_bounds d hd a ha p0 hp0 hp1).1
  have href := sourceStateCurvature_reference d hd a G p0 hp0 hp1
  have hS0 := sourceStateScore_reference d hd a G p0 hp0 hp1
  have hc1 := (continuous_sourceStateCurvature d a G p0).tendsto (sourceReferenceState p0)
  have hc2 := (continuous_sourceStateInfluence d a G p0).tendsto (sourceReferenceState p0)
  have hc3 := (continuous_sourceStateScore d a G p0).tendsto (sourceReferenceState p0)
  rw [href.1] at hc1
  rw [href.2] at hc2
  rw [hS0] at hc3
  have h1 := hc1.eventually
    (Metric.ball_mem_nhds (literalReferenceCurvature d a p0) (by positivity : 0 < literalReferenceCurvature d a p0/12))
  have h2 := hc2.eventually
    (Metric.ball_mem_nhds (literalReferenceCross d a p0) (by positivity : 0 < literalReferenceCurvature d a p0/24))
  have h3 := hc3.eventually
    (Metric.ball_mem_nhds (0:ℝ) htol)
  obtain ⟨delta, hdelt, hball⟩ := Metric.mem_nhds_iff.mp (h1.and (h2.and h3))
  refine ⟨delta, hdelt, ?_⟩
  intro x hx
  have h := hball hx
  simpa only [Set.mem_setOf_eq, Metric.mem_ball, Real.dist_eq, sub_zero] using h

end FCAppendix.Exclusive.Narrow.Existence
