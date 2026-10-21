import FCAppendix.Affine.Multiple07.SourceRateCertificate
import FCAppendix.Affine.Multiple07.SourceMeasureLifts
import FCAppendix.Affine.LowBody.ActualLowBidEquilibrium
import FCAppendix.Affine.Hybrid.UpperLaw
import FCAppendix.Affine.Hybrid.UpperFiniteError

noncomputable section
namespace FCAppendix.Affine.Multiple07
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology
open Existence.RankEnvelope

theorem eventually_source_low_component (r : Partition) :
    ∀ᶠ m : ℕ in atTop,
      ∃ L : LowBody.ActualAtomlessLowLimit (m - 1) lowCeiling xi (marketCapacity m)
          (sourceCategoryLaw r) sourceLowValueLaw,
        ∀ᵐ x ∂(L.joint.1 : Measure (LowBody.LowValue lowCeiling × LowBody.LowValue lowCeiling)),
          ∀ b : ℝ, 0 ≤ b →
            LowBody.exactExpectedPayoff (m - 1) lowCeiling xi (marketCapacity m)
              (sourceCategoryLaw r) (L.joint.1.map measurable_snd.aemeasurable)
                ((x.1 : ℝ), b) ≤
            LowBody.exactExpectedPayoff (m - 1) lowCeiling xi (marketCapacity m)
              (sourceCategoryLaw r) (L.joint.1.map measurable_snd.aemeasurable)
                ((x.1 : ℝ), (x.2 : ℝ)) := by
  simpa only [sourceCategoryLaw] using LowBody.eventually_exists_actual_low_bid_equilibrium
    (by norm_num [lowCeiling] : (0 : ℝ) ≤ lowCeiling)
    (by norm_num [xi] : (0 : ℝ) < xi) (by norm_num [xi] : xi ≤ (1 / 2 : ℝ))
    (3 / 200) (activeMass r) (upperMass r)
    (by norm_num) (by cases r <;> norm_num [activeMass])
    (by cases r <;> norm_num [upperMass])
    (by cases r <;> norm_num [activeMass, upperMass]) (bandLaw .low)
    marketCapacity rho (by norm_num [rho])
    (by cases r <;> norm_num [rho, activeMass, upperMass])
    marketCapacity_density (source_joint_rate_gap r)
    sourceLowValueLaw sourceLowValueLaw_positive

def sourceUpperProbabilityMeasure (r : Partition) : ProbabilityMeasure ℝ :=
  ⟨upperValueLaw r, inferInstance⟩

instance sourceUpperProbabilityMeasure_atomless (r : Partition) :
    NullSingletonClass (sourceUpperProbabilityMeasure r : Measure ℝ) := by
  change NullSingletonClass (upperValueLaw r)
  infer_instance

def weightedUpperLaw (r : Partition) : Measure ℝ :=
  ENNReal.ofReal (upperMass r) • upperValueLaw r

instance weightedUpperLaw_finite (r : Partition) : IsFiniteMeasure (weightedUpperLaw r) := by
  constructor
  simp only [weightedUpperLaw, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  exact ENNReal.ofReal_lt_top

instance weightedUpperLaw_atomless (r : Partition) : NullSingletonClass (weightedUpperLaw r) := by
  constructor
  intro y
  change (ENNReal.ofReal (upperMass r) • upperValueLaw r) {y}=0
  simp only [Measure.smul_apply,smul_eq_mul,measure_singleton,mul_zero]

theorem weightedUpperLaw_mass (r : Partition) : (weightedUpperLaw r).real univ = upperMass r := by
  have hh : 0 ≤ upperMass r := by cases r <;> norm_num [upperMass]
  simp only [weightedUpperLaw, Measure.real, Measure.smul_apply, smul_eq_mul,
    measure_univ, mul_one, ENNReal.toReal_ofReal hh]

theorem weightedUpperLaw_mass_le_one (r : Partition) : (weightedUpperLaw r).real univ ≤ 1 := by
  rw [weightedUpperLaw_mass]
  cases r <;> norm_num [upperMass]

def sourceUpperRank (r : Partition) (m : ℕ) (v : ℝ) : ℝ :=
  rank (weightedUpperLaw r) (m - 1) (marketCapacity m) 2 v

def sourceUpperBid (r : Partition) (m : ℕ) : ℝ → ℝ :=
  bid (sourceUpperRank r m) (upperLower r) (upperFloor r)

def sourceUpperError (r : Partition) (m : ℕ) : ℝ :=
  error (sourceUpperRank r m) (upperLower r) (upperFloor r)

theorem sourceCapacity_le_users (m : ℕ) : marketCapacity m ≤ m := by
  unfold marketCapacity
  omega

theorem sourceCapacity_lt_users (m : ℕ) (hm : 0 < m) : marketCapacity m < m := by
  unfold marketCapacity
  omega

theorem sourceCapacity_le_rivals_add_one (m : ℕ) : marketCapacity m ≤ m - 1 + 1 := by
  have h := sourceCapacity_le_users m
  omega

theorem sourceCapacity_density_with_rivals :
    Tendsto (fun m : ℕ => (marketCapacity m : ℝ) / (((m - 1 : ℕ) : ℝ) + 1))
      atTop (𝓝 rho) := by
  apply marketCapacity_density.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  rw [Nat.cast_sub hm]
  norm_num

theorem eventually_source_upper_component (r : Partition) :
    ∀ᶠ m : ℕ in atTop, ∃ PH : ProbabilityMeasure (ℝ × JointAction 2),
      (PH : Measure (ℝ × JointAction 2)).map Prod.fst = upperValueLaw r ∧
      (PH : Measure (ℝ × JointAction 2)).map (fun x => x.2.bid) =
        (upperValueLaw r).map (sourceUpperBid r m) ∧
      (∀ᵐ x ∂(PH : Measure (ℝ × JointAction 2)),
        upperFloor r ≤ x.2.bid ∧ x.2.routeCount = 1) ∧
      (∀ y : ℝ, (PH : Measure (ℝ × JointAction 2)) {x | x.2.bid = y} = 0) := by
  filter_upwards [marketCapacity_tendsto.eventually (eventually_ge_atTop (1 : ℕ)),
    eventually_ge_atTop (3 : ℕ)] with m hc hm
  have hcr : marketCapacity m ≤ m - 2 + 1 := by
    have h := sourceCapacity_lt_users m (by omega)
    omega
  have hmEq : m - 2 + 1 = m - 1 := by omega
  have h := Hybrid.exists_upper_joint (sourceUpperProbabilityMeasure r)
    (upperMass r) (by cases r <;> norm_num [upperMass])
    (by cases r <;> norm_num [upperMass]) (m - 2) (marketCapacity m) hc hcr
    (upperLower r) (upperFloor r) (2301 / 2000)
    (by cases r <;> norm_num [upperFloor])
    (by cases r <;> norm_num [upperFloor, upperLower]) (upperValueLaw_support r)
  obtain ⟨PH,hF,hB,hrest⟩ := h
  have hval : (sourceUpperProbabilityMeasure r : Measure ℝ)=upperValueLaw r := rfl
  rw [hval] at hF hB
  refine ⟨PH,hF,?_,hrest⟩
  have hq : sourceUpperRank r m =
      rank (weightedUpperLaw r) (m-1) (marketCapacity m) 2 := by
    funext v
    rfl
  dsimp only [sourceUpperBid]
  rw [hq]
  simpa only [hmEq,weightedUpperLaw] using hB

theorem sourceUpper_contact_subcritical (r : Partition) (v : ℝ) :
    contactTail (weightedUpperLaw r) 2 v < rho := by
  have htail : (weightedUpperLaw r).real (Ioi v) ≤ upperMass r := by
    rw [← weightedUpperLaw_mass r]
    exact measureReal_mono (subset_univ _)
  have hhalf : upperMass r / 2 < rho := by cases r <;> norm_num [upperMass, rho]
  exact (div_le_div_of_nonneg_right htail (by norm_num)).trans_lt hhalf

theorem sourceUpperRank_tendsto (r : Partition) (v : ℝ) :
    Tendsto (fun m => sourceUpperRank r m v) atTop (𝓝 1) :=
  Hybrid.rank_floor_tendsto_one (weightedUpperLaw r) (weightedUpperLaw_mass_le_one r)
    (fun m : ℕ => m - 1) marketCapacity (tendsto_sub_atTop_nat 1)
    sourceCapacity_le_rivals_add_one rho v sourceCapacity_density_with_rivals
    (sourceUpper_contact_subcritical r v)

theorem sourceUpperError_tendsto (r : Partition) :
    Tendsto (sourceUpperError r) atTop (𝓝 0) := by
  have hc : Tendsto
      (fun k : ℕ => (marketCapacity (k + 3) : ℝ) / (((k + 2 : ℕ) : ℝ) + 1))
      atTop (𝓝 rho) := by
    apply (marketCapacity_density.comp (tendsto_add_atTop_nat 3)).congr'
    exact Eventually.of_forall fun k => by
      change (marketCapacity (k+3):ℝ)/(k+3:ℕ)=
        (marketCapacity (k+3):ℝ)/((k+2:ℕ)+1:ℝ)
      norm_num only [Nat.cast_add,Nat.cast_ofNat]
      congr 1
      ring
  have h := Hybrid.upper_error_tendsto_zero (weightedUpperLaw r)
    (weightedUpperLaw_mass_le_one r) (fun k : ℕ => k + 2)
    (fun k => marketCapacity (k + 3)) (tendsto_add_atTop_nat 2)
    (by intro k; unfold marketCapacity; omega)
    (by intro k; have h := sourceCapacity_lt_users (k + 3) (by omega); omega)
    rho (upperLower r) (upperFloor r) (2301 / 2000)
    (by cases r <;> norm_num [upperLower, upperFloor])
    (by cases r <;> norm_num [upperLower])
    (Measure.ae_smul_measure ((upperValueLaw_support r).mono (fun _ hv => hv.2)) _)
    hc (sourceUpper_contact_subcritical r (upperLower r))
  apply (tendsto_add_atTop_iff_nat 3).mp
  convert! h using 1

theorem eventually_source_upper_hidden_guard (r : Partition) :
    ∀ᶠ m : ℕ in atTop,
      sourceUpperError r m < eta * upperFloor r *
        (1 - 2 * (1 - sourceUpperRank r m (upperLower r))) := by
  apply Hybrid.eventually_upper_hidden_guard (sourceUpperError_tendsto r)
  · simpa only [sub_self] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub (sourceUpperRank_tendsto r (upperLower r))
  · norm_num [eta]
  · cases r <;> norm_num [upperFloor]

end FCAppendix.Affine.Multiple07
