import FCAppendix.Affine.Multiple07.NativeAssembly
import FCAppendix.Affine.Uniform07Finishing.Native.OriginalLawTransport

noncomputable section
namespace FCAppendix.Affine.Multiple07
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology
open scoped BigOperators

variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def zeroStrategy (Γ : FiniteGame m 2 c Seed) : Kernel ℝ (JointAction 2) :=
  Uniform07Finishing.patchStrategy Γ {0} (measurableSet_singleton _)
    (fun _ => Interim.abstain 2) measurable_const

instance zeroStrategy_markov (Γ : FiniteGame m 2 c Seed) : IsMarkovKernel (zeroStrategy Γ) := by
  unfold zeroStrategy
  infer_instance

def normalizeZero (Γ : FiniteGame m 2 c Seed) : FiniteGame m 2 c Seed :=
  Uniform07Finishing.withStrategy Γ (zeroStrategy Γ)

theorem source_zero_null (Γ : FiniteGame m 2 c Seed) (hF : Γ.F = sourceValueLaw) :
    Γ.F {0} = 0 := by
  rw [hF]
  exact measure_singleton _

theorem zeroStrategy_ae (Γ : FiniteGame m 2 c Seed) (hF : Γ.F = sourceValueLaw) :
    zeroStrategy Γ =ᵐ[Γ.F] Γ.σ :=
  Uniform07Finishing.patchStrategy_ae_eq Γ {0} (measurableSet_singleton _)
    (source_zero_null Γ hF) _ measurable_const

theorem normalizeZero_joint_law (Γ : FiniteGame m 2 c Seed) (hF : Γ.F = sourceValueLaw) :
    (normalizeZero Γ).F ⊗ₘ (normalizeZero Γ).σ = Γ.F ⊗ₘ Γ.σ :=
  Uniform07Finishing.withStrategy_joint_law Γ (zeroStrategy Γ) (zeroStrategy_ae Γ hF)

theorem normalizeZero_equilibrium (Γ : FiniteGame m 2 c Seed) (hF : Γ.F = sourceValueLaw)
    (hΓ : IsBayesianEquilibrium Γ) : IsBayesianEquilibrium (normalizeZero Γ) :=
  Uniform07Finishing.withStrategy_bayesian_equilibrium Γ (zeroStrategy Γ)
    (zeroStrategy_ae Γ hF) hΓ

theorem normalizeZero_physicalBidLaw (Γ : FiniteGame m 2 c Seed) (hF : Γ.F = sourceValueLaw) :
    physicalBidLaw (normalizeZero Γ) = physicalBidLaw Γ := by
  unfold physicalBidLaw normalizeZero
  rw [Uniform07Finishing.withStrategy_user_law Γ (zeroStrategy Γ) (zeroStrategy_ae Γ hF)]

theorem normalizeZero_fixed_zero_best_response (Γ : FiniteGame m 2 c Seed)
    (hF : Γ.F = sourceValueLaw) :
    ∀ᵐ a ∂(normalizeZero Γ).σ 0, ∀ i : Fin m, ∀ a' : JointAction 2,
      (problem (normalizeZero Γ) i).payoff 0 a' ≤ (problem (normalizeZero Γ) i).payoff 0 a := by
  apply Uniform07Finishing.patched_fixed_value_best_response Γ {0}
    (measurableSet_singleton _) (source_zero_null Γ hF)
    (fun _ => Interim.abstain 2) measurable_const (by simp)
  intro i a'
  rw [Interim.Problem.payoff_abstain]
  have h := (problem Γ i).payoff_upper 0 a'
  have hz : max (0 - Γ.g) 0 = 0 := max_eq_right (by linarith [Γ.g_nonneg])
  change (problem Γ i).payoff 0 a' ≤ max (0 - Γ.g) 0 at h
  simpa only [hz] using h

private theorem uniformAverage_constant (hm : 0 < m) (Q : CountLaw 2) :
    FiniteLaw.uniformAverage hm (fun _ : Fin m => Q) = Q := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  apply FiniteLaw.ext
  intro j
  change (∑ _i : Fin m, Q.mass j) / (m : ℝ) = Q.mass j
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hmR]

theorem normalizeZero_conditional_zero (Γ : FiniteGame m 2 c Seed)
    (hF : Γ.F = sourceValueLaw) (hm : 0 < m) :
    conditionalTypeCountLaw (normalizeZero Γ) hm 0 = FiniteLaw.dirac 0 := by
  rw [show normalizeZero Γ = Uniform07Finishing.withStrategy Γ
      (Uniform07Finishing.patchStrategy Γ {0} (measurableSet_singleton _)
        (fun _ => Interim.abstain 2) measurable_const) from rfl]
  rw [Uniform07Finishing.patched_conditional_count_law Γ hm {0}
    (measurableSet_singleton _) (source_zero_null Γ hF)
    (fun _ => Interim.abstain 2) measurable_const (by simp)]
  have he : (fun i : Fin m => (problem Γ i).outcome (Interim.abstain 2)) =
      (fun _ : Fin m => (FiniteLaw.dirac 0 : CountLaw 2)) := by
    funext i
    exact (problem Γ i).abstention
  rw [he, uniformAverage_constant]

theorem normalizeZero_conditional_nonzero (Γ : FiniteGame m 2 c Seed)
    (hF : Γ.F = sourceValueLaw) (hm : 0 < m) {v : ℝ} (hv : v ≠ 0) :
    conditionalTypeCountLaw (normalizeZero Γ) hm v = conditionalTypeCountLaw Γ hm v :=
  Uniform07Finishing.unpatched_conditional_count_law Γ hm {0}
    (measurableSet_singleton _) (source_zero_null Γ hF)
    (fun _ => Interim.abstain 2) measurable_const (by simpa using hv)

theorem normalizeZero_aggregates (Γ : FiniteGame m 2 c Seed)
    (hF : Γ.F = sourceValueLaw) (hm : 0 < m) :
    finiteCoverage (normalizeZero Γ) = finiteCoverage Γ ∧
    finiteLoad (normalizeZero Γ) = finiteLoad Γ ∧
    finiteMultiplicity (normalizeZero Γ) = finiteMultiplicity Γ :=
  ⟨Uniform07Finishing.withStrategy_finite_coverage Γ (zeroStrategy Γ) (zeroStrategy_ae Γ hF) hm,
    Uniform07Finishing.withStrategy_finite_load Γ (zeroStrategy Γ) (zeroStrategy_ae Γ hF) hm,
    Uniform07Finishing.withStrategy_finite_multiplicity Γ (zeroStrategy Γ) (zeroStrategy_ae Γ hF) hm⟩

theorem normalizeZero_all_band_limits (r : Partition)
    (Γ : ∀ k, MultipleGame k) (hF : ∀ k, (Γ k).F = sourceValueLaw)
    (hlim : ∀ b v, v ∈ Icc (bandLower b) (bandUpper b) → 0 < v → ∀ j : Fin 3,
      Tendsto (fun k => (conditionalTypeCountLaw (Γ k) (Nat.succ_pos k) v).mass j)
        atTop (𝓝 ((limitingLaw r v).mass j))) :
    ∀ b v, v ∈ Icc (bandLower b) (bandUpper b) → ∀ j : Fin 3,
      Tendsto (fun k => (conditionalTypeCountLaw (normalizeZero (Γ k)) (Nat.succ_pos k) v).mass j)
        atTop (𝓝 ((limitingLaw r v).mass j)) := by
  intro b v hv j
  by_cases hv0 : v = 0
  · subst v
    have he : limitingLaw r 0 = FiniteLaw.dirac 0 := limitingLaw_low (by norm_num)
    have hh : ∀ k, conditionalTypeCountLaw (normalizeZero (Γ k)) (Nat.succ_pos k) 0 =
        FiniteLaw.dirac 0 := fun k => normalizeZero_conditional_zero (Γ k) (hF k) (Nat.succ_pos k)
    simp only [hh, he]
    exact tendsto_const_nhds
  · have hl : 0 ≤ bandLower b := by cases b <;> norm_num [bandLower]
    have hpos : 0 < v := lt_of_le_of_ne (hl.trans hv.1) (Ne.symm hv0)
    apply (hlim b v hv hpos j).congr'
    exact Eventually.of_forall fun k => by
      dsimp only
      rw [normalizeZero_conditional_nonzero (Γ k) (hF k) (Nat.succ_pos k) hv0]

end FCAppendix.Affine.Multiple07
