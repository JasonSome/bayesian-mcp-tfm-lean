import FCAppendix.Affine.Uniform06.RelativeRootWindow
import FCAppendix.Affine.Uniform06.ClampedMomentBounds
import FCAppendix.Affine.Uniform06.DerivativeUntilting
import FCAppendix.Affine.Uniform06.SourceCoarseIntegral

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.PhysicalSourceMoments

open MeasureTheory ProbabilityTheory Set LowBody
open scoped BigOperators
open Uniform07 LiteralExperiment LiteralCoarsePath LiteralKernelIdentity
open RawMixedSource RawTiltedSource RawMarkedLaplace RawMomentPartition
open RawPathAdapter ZeroWeightFocal RawPathRootReplacement FiniteSampledLaplace
open FCAppendix.Affine.ClippedResidual FCAppendix.Affine.WeightedSampling
open FixedPriceRawDerivative

variable {N : ℕ} [Nonempty (Fin N)]

def physicalMoment (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) (b θ : ℝ) (q : ℕ) (ω : Fin N → RowRival) : ℝ :=
  let T := patternTemplate c (fun j => (ω j).1)
  let B := rowBids b ω
  let g' := {g with countMargin := cm (fun j => (ω j).1)}
  Real.exp (-θ*((c:ℝ)-FiniteMarkedExchangeability.sumX (demand (xi i) b) ω))*
    branchWeight (xi i) g' T B*
      (pathLaw (weights (xi i) g' T B) (imbalance T) ∅).expect
        (fun p => (complementMarginal (xi i) T B (finalSet (imbalance T) ∅ p) 0)^q)

def tiltedPhysical (i : Row) (G : Measure (ℝ × ℝ)) (N c : ℕ) [Nonempty (Fin N)]
    (g : GuardData) (cm : (Fin N → Fin 4) → ℝ) (b θ : ℝ) (q : ℕ) : ℝ :=
  ∫ ω : Fin N → RowRival,physicalMoment i c g cm b θ q ω
    ∂Measure.pi (fun _ : Fin N => tiltedSource i G b θ)

omit [Nonempty (Fin N)] in
theorem measurable_physicalMoment (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) (b θ : ℝ) (q : ℕ) :
    Measurable (physicalMoment i c g cm b θ q) := by
  classical
  have hξ1 : xi i<1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  have hc : Measurable (fun ω : Fin N → RowRival =>
      Real.exp (-θ*deficit i b c ω)) :=
    ((measurable_deficit i b c).const_mul (-θ)).exp
  apply LiteralCoarseMeasurable.measurable_pattern_choice
    (fun kind ω => Real.exp (-θ*deficit i b c ω)*
      branchWeight (xi i) {g with countMargin:=cm kind}
        (patternTemplate c kind) (rowBids b ω)*
      (pathLaw (weights (xi i) {g with countMargin:=cm kind}
        (patternTemplate c kind) (rowBids b ω))
          (imbalance (patternTemplate c kind)) ∅).expect
        (fun p => complementMarginal (xi i) (patternTemplate c kind)
          (rowBids b ω) (finalSet (imbalance (patternTemplate c kind)) ∅ p) 0^q))
  intro kind
  let T := patternTemplate c kind
  let g' := {g with countMargin:=cm kind}
  have hB := LiteralCoarseMeasurable.measurable_raw_rowBids N b
  have hα : Measurable (fun ω : Fin N → RowRival => branchWeight (xi i) g' T (rowBids b ω)) := by
    by_cases he : T.residual₀=T.residual₁
    · simpa only [branchWeight,if_pos he] using
        (measurable_const : Measurable (fun _ : Fin N → RowRival => (1:ℝ)))
    · simpa only [branchWeight,if_neg he] using
        LiteralCoarseMeasurable.measurable_guard (xi i) g' T (rowBids b) hB
  apply (hc.mul hα).mul
  unfold FCAppendix.FiniteLaw.expect
  apply Finset.measurable_sum
  intro p _
  exact (LiteralCoarseMeasurable.measurable_path_mass
    (fun ω => weights (xi i) g' T (rowBids b ω))
    (LiteralCoarseMeasurable.measurable_weights (xi i) g' T (rowBids b) hB)
      (imbalance T) ∅ p).mul
    ((LiteralCoarseMeasurable.measurable_complement (xi_pos i) hξ1 T (rowBids b)
      hB (finalSet (imbalance T) ∅ p) 0).pow_const q)

theorem physicalMoment_eq_rival (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) {b : ℝ} (hbL : b≤ g.multiplier)
    (hr : 0< g.requiredDemand) (θ : ℝ) (q : ℕ) (ω : Fin N → RowRival)
    (hc : ValidCounts c ω)
    (hW : ((imbalanceSum ω).natAbs:ℝ)<
      totalWeight (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω)) :
    physicalMoment i c g cm b θ q ω=
      Real.exp (-θ*deficit i b c ω)*
        branchWeight (xi i) {g with countMargin:=cm (fun j => (ω j).1)}
          (patternTemplate c (fun j => (ω j).1)) (rowBids b ω)*
        (pathLaw (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω)
          (imbalanceSum ω).natAbs ∅).expect
            (fun p => selectedResponse i c b ω (imbalanceSum ω).natAbs p^q) := by
  let T := patternTemplate c (fun j => (ω j).1)
  let B := rowBids b ω
  let g' := {g with countMargin:=cm (fun j => (ω j).1)}
  have hk : imbalance T=(imbalanceSum ω).natAbs := literal_imbalance_eq c ω hc
  unfold physicalMoment
  dsimp only
  rw [hk,actual_rival_path_transport (xi i) g' c b hbL hr ω _ hW]
  congr 1
  apply FCAppendix.FiniteLaw.expect_congr
  intro p
  rw [show (∅:Finset (Fin (N+1)))=liftSet (∅:Finset (Fin N)) by simp [liftSet],
    finalSet_lift]
  rfl

theorem literalMoment_eq_rival_expect (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) {b : ℝ} (hb : 0< b) (hbL : b≤ g.multiplier)
    (hr : 0< g.requiredDemand) (θ : ℝ) (q : ℕ) (ω : Fin N → RowRival)
    (hc : ValidCounts c ω)
    (hW : ((imbalanceSum ω).natAbs:ℝ)<
      totalWeight (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω)) :
    literalMoment i c g cm b θ q ω=
      Real.exp (-θ*deficit i b c ω)*
        branchWeight (xi i) {g with countMargin:=cm (fun j => (ω j).1)}
          (patternTemplate c (fun j => (ω j).1)) (rowBids b ω)*
        (pathLaw (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω)
          (imbalanceSum ω).natAbs ∅).expect
            (fun p => strictPower q (selectedDeficit i c b ω (imbalanceSum ω).natAbs p)) := by
  let T := patternTemplate c (fun j => (ω j).1)
  let B := rowBids b ω
  let g' := {g with countMargin:=cm (fun j => (ω j).1)}
  have hk : imbalance T=(imbalanceSum ω).natAbs := literal_imbalance_eq c ω hc
  unfold literalMoment
  dsimp only
  rw [hk,actual_rival_path_transport (xi i) g' c b hbL hr ω _ hW]
  congr 1
  apply RawMomentPartition.expect_eq_of_support
  intro p hp
  rw [show (∅:Finset (Fin (N+1)))=liftSet (∅:Finset (Fin N)) by simp [liftSet],
    finalSet_lift]
  have hd := selected_deficit_identity i c g hb ω hc _ rfl hW p hp
  have hm := masked_demand_eq (ξ := xi i) T B (liftSet (finalSet _ ∅ p)) 0 hb
    (rowBids_outside c b ω)
  have he : focalDeficit (xi i) T B (liftSet (finalSet _ ∅ p)) 0=
      selectedDeficit i c b ω (imbalanceSum ω).natAbs p := by
    change (small T:ℝ)-remainingDemand (xi i)
      (maskedBids T B (liftSet (finalSet _ ∅ p))) {0} b=
        selectedDeficit i c b ω (imbalanceSum ω).natAbs p at hd
    rw [hm] at hd
    exact hd
  rw [he]

lemma complement_positive_deficit {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (T : PureTemplate ι) (B : ι → ℝ) (E : Finset ι) (j : ι)
    (hb : 0< B j) (hout : ∀ k,k ∉ T.support → B k=0)
    (hp : 0< complementMarginal ξ T B E j) : 0< focalDeficit ξ T B E j := by
  have hj : j ∈ T.support\E := by
    by_contra hn
    rw [MaskedRootDerivative.complement_zero_absent ξ T B E j hn] at hp
    exact lt_irrefl 0 hp
  have hBj : maskedBids T B E j=B j := by simp only [maskedBids,if_pos hj]
  have hh := CanonicalCoarse.actual_positive_implies_deficit_positive hξ hξ1 (small T)
    (maskedBids T B E) j (by simpa only [hBj] using hb) hp
  simpa only [hBj,masked_demand_eq (ξ := ξ) T B E j hb hout,focalDeficit] using hh

omit [Nonempty (Fin N)] in

theorem physicalMoment_le_strict_zero (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) {b : ℝ} (hb : 0< b) (θ : ℝ)
    (q : ℕ) (hq : 0< q) (ω : Fin N → RowRival) :
    0≤ physicalMoment i c g cm b θ q ω ∧
      physicalMoment i c g cm b θ q ω≤ literalMoment i c g cm b θ 0 ω := by
  have hξ1 : xi i<1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  let T := patternTemplate c (fun j => (ω j).1)
  let B := rowBids b ω
  let g' := {g with countMargin := cm (fun j => (ω j).1)}
  let P := pathLaw (weights (xi i) g' T B) (imbalance T) ∅
  have hpos : 0≤ Real.exp (-θ*((c:ℝ)-FiniteMarkedExchangeability.sumX (demand (xi i) b) ω))*
      branchWeight (xi i) g' T B :=
    mul_nonneg (Real.exp_pos _).le (branchWeight_bounds _ _ _ _).1
  have hpoint (p : Path (Fin (N+1)) (imbalance T)) :
      (complementMarginal (xi i) T B (finalSet (imbalance T) ∅ p) 0)^q≤
        strictPower 0 (focalDeficit (xi i) T B (finalSet (imbalance T) ∅ p) 0) := by
    have hp := LiteralPrefixStieltjes.complement_bounds (xi_pos i) hξ1 T B (finalSet (imbalance T) ∅ p) 0
    by_cases hD : 0< focalDeficit (xi i) T B (finalSet (imbalance T) ∅ p) 0
    · simp only [strictPower,if_pos hD,pow_zero]
      exact pow_le_one₀ hp.1 hp.2
    · have hp0 : complementMarginal (xi i) T B (finalSet (imbalance T) ∅ p) 0=0 := by
        apply le_antisymm _ hp.1
        by_contra hn
        exact hD (complement_positive_deficit (xi_pos i) hξ1 T B _ 0
          (by simpa only [B,rowBids,Fin.cons_zero] using hb)
          (rowBids_outside c b ω) (lt_of_not_ge hn))
      simp only [hp0,zero_pow hq.ne',strictPower,if_neg hD,le_refl]
  refine ⟨mul_nonneg hpos (FCAppendix.FiniteLaw.expect_nonneg P
      (fun p => pow_nonneg (LiteralPrefixStieltjes.complement_bounds (xi_pos i) hξ1 T B _ 0).1 q)),?_⟩
  exact mul_le_mul_of_nonneg_left (FCAppendix.FiniteLaw.expect_mono P hpoint) hpos

omit [Nonempty (Fin N)] in

theorem physicalMoment_one_two (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) {b : ℝ} (hbL : b≤ g.multiplier) (θ : ℝ)
    (hε : 0< g.margin) (hM : 0< g.population) (hr : 0< g.requiredDemand)
    (ω : Fin N → RowRival) :
    physicalMoment i c g cm b θ 1 ω=
      Real.exp (-θ*deficit i b c ω)*originalRowMarginal (xi i) c g cm b ω ∧
    physicalMoment i c g cm b θ 2 ω=
      Real.exp (-θ*deficit i b c ω)*originalRowDuplicate (xi i) c g cm b ω := by
  have hξ1 : xi i<1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  have hh := original_row_path_moments (xi_pos i) hξ1 c g cm b hε hM hr hbL ω
  dsimp only at hh
  constructor
  · rw [hh.1]
    simp only [physicalMoment,pow_one,deficit,FCAppendix.ExponentialTilt.iidSum,
      FiniteMarkedExchangeability.sumX,mul_assoc]
  · rw [hh.2]
    simp only [physicalMoment,deficit,FCAppendix.ExponentialTilt.iidSum,
      FiniteMarkedExchangeability.sumX,mul_assoc]

theorem tiltedPhysical_one_two (i : Row) (G : Measure (ℝ × ℝ))
    (m : ℕ) [Nonempty (Fin (m-1))] (g : GuardData)
    (cm : (Fin (m-1) → Fin 4) → ℝ) {b : ℝ} (hbL : b≤ g.multiplier) (θ : ℝ)
    (hε : 0< g.margin) (hM : 0< g.population) (hr : 0< g.requiredDemand) :
    tiltedPhysical i G (m-1) (capacity m) g cm b θ 1=SourceCoarseIntegral.tiltedC i m G g cm b θ ∧
    tiltedPhysical i G (m-1) (capacity m) g cm b θ 2=SourceCoarseIntegral.tiltedR i m G g cm b θ := by
  constructor
  · exact integral_congr_ae (ae_of_all _ fun ω => (physicalMoment_one_two i _ g cm hbL θ hε hM hr ω).1)
  · exact integral_congr_ae (ae_of_all _ fun ω => (physicalMoment_one_two i _ g cm hbL θ hε hM hr ω).2)

end FCAppendix.Affine.Uniform06.PhysicalSourceMoments
