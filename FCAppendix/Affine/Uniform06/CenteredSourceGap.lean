import FCAppendix.Affine.Uniform06.MixedIntervalLLT
import FCAppendix.Affine.Uniform06.CharacteristicWeakConvergence

noncomputable section

namespace FCAppendix.Affine.Uniform06.CenteredSourceGap

open MeasureTheory Filter Set
open scoped Topology
open CharacteristicExpansion MixedFourierInversion BoundedMixedGaussian
open MixedCharacteristicGap CharacteristicWeakConvergence
open MixedSpectralLimit MixedIntervalLLT
open FCAppendix.Affine.Uniform07

variable {Ω : Type*} [MeasurableSpace Ω]

def uncenteredRow (A : CenteredArray Ω) (U : ℕ → Ω → ℝ)
    (hU : ∀ n, Measurable (U n)) (n : ℕ) : ProbabilityMeasure Pair :=
  ⟨(A.law n).map (fun ω => (U n ω, A.realY n ω)),
    Measure.isProbabilityMeasure_map ((hU n).prodMk (A.measurable_realY n)).aemeasurable⟩

lemma uncenteredRow_bounded (A : CenteredArray Ω) (U : ℕ → Ω → ℝ)
    (hU : ∀ n, Measurable (U n))
    (hbU : ∀ n, ∀ᵐ ω ∂A.law n, |U n ω| ≤ 1) :
    ∀ n, ∀ᵐ p ∂(uncenteredRow A U hU n : Measure Pair),
      |p.1| ≤ 1 ∧ |p.2| ≤ 1 := by
  intro n
  apply (ae_map_iff ((hU n).prodMk (A.measurable_realY n)).aemeasurable
    (by measurability)).mpr
  filter_upwards [hbU n, A.bounded n] with ω hω hA
  exact ⟨hω, hA.2⟩

lemma centered_characteristic_norm (A : CenteredArray Ω) (U : ℕ → Ω → ℝ)
    (hU : ∀ n, Measurable (U n)) (r : ℕ → ℝ)
    (hcenter : ∀ n, ∀ᵐ ω ∂A.law n, A.X n ω = U n ω - r n)
    (n : ℕ) (q : Pair) :
    ‖rowCharacteristic (A.law n) (projection (A.X n) (A.realY n) q)‖ =
      ‖jointCharacteristic (uncenteredRow A U hU n : Measure Pair) q‖ := by
  have hmap : jointCharacteristic (uncenteredRow A U hU n : Measure Pair) q =
      ∫ ω, phase (q.1 * U n ω + q.2 * A.realY n ω) ∂A.law n := by
    unfold jointCharacteristic
    change (∫ p : Pair, jointPhase q p ∂(A.law n).map (fun ω => (U n ω,A.realY n ω))) = _
    rw [integral_map ((hU n).prodMk (A.measurable_realY n)).aemeasurable
        (continuous_jointPhase_right q).aestronglyMeasurable]
    rfl
  have heq : rowCharacteristic (A.law n) (projection (A.X n) (A.realY n) q) =
      phase (-q.1 * r n) *
        jointCharacteristic (uncenteredRow A U hU n : Measure Pair) q := by
    rw [hmap, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hcenter n] with ω hω
    dsimp [projection]
    rw [hω, show q.1 * (U n ω - r n) + q.2 * A.realY n ω =
      -q.1 * r n + (q.1 * U n ω + q.2 * A.realY n ω) by ring,
      phase_add]
  rw [heq, norm_mul, norm_phase, one_mul]

def closedBandExterior (T : ℝ) : Set Pair :=
  bandRectangle T ∩ {q | (1 : ℝ) / 4 ≤ |q.1| + |q.2|}

lemma isCompact_closedBandExterior (T : ℝ) : IsCompact (closedBandExterior T) :=
  (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_le continuous_const (continuous_fst.abs.add continuous_snd.abs))

lemma bandExterior_subset_closed (T : ℝ) : bandExterior T ⊆ closedBandExterior T := by
  intro q hq
  refine ⟨hq.1, ?_⟩
  have h : ¬ |q.1| + |q.2| ≤ (1 : ℝ) / 4 := by
    simpa only [originRegion, mem_setOf_eq, one_mul] using hq.2
  exact (lt_of_not_ge h).le

lemma zero_not_mem_closedBandExterior (T : ℝ) : (0 : Pair) ∉ closedBandExterior T := by
  intro h
  have hh := h.2
  norm_num at hh

theorem compactGap_of_uncentered_source_limit (A : CenteredArray Ω)
    (U : ℕ → Ω → ℝ) (hU : ∀ n, Measurable (U n)) (r : ℕ → ℝ)
    (hbU : ∀ n, ∀ᵐ ω ∂A.law n, |U n ω| ≤ 1)
    (hcenter : ∀ n, ∀ᵐ ω ∂A.law n, A.X n ω = U n ω - r n)
    (i : Row) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (P₀ : ProbabilityMeasure Pair)
    (hweak : Tendsto (uncenteredRow A U hU) atTop (𝓝 P₀))
    (hback : MixedLaw.law i μ ≪ (P₀ : Measure Pair))
    {a b : ℝ} (hab : a < b) (hcomponent : volume.restrict (Ioo a b) ≪ μ) :
    A.CompactGap := by
  intro T _hT
  obtain ⟨δ, hδ0, hδ1, hδ⟩ := eventual_source_gap_of_weak_convergence i μ
    (uncenteredRow_bounded A U hU hbU) hweak hback hab hcomponent
    (isCompact_closedBandExterior T) (fun q hq => hq.1.2)
    (zero_not_mem_closedBandExterior T)
  refine ⟨δ, hδ0, hδ1, ?_⟩
  filter_upwards [hδ] with n hn q hq
  rw [centered_characteristic_norm A U hU r hcenter n q]
  exact hn q (bandExterior_subset_closed T hq)

theorem source_relative_interval (A : CenteredArray Ω)
    (U : ℕ → Ω → ℝ) (hU : ∀ n, Measurable (U n)) (r : ℕ → ℝ)
    (hbU : ∀ n, ∀ᵐ ω ∂A.law n, |U n ω| ≤ 1)
    (hcenter : ∀ n, ∀ᵐ ω ∂A.law n, A.X n ω = U n ω - r n)
    (i : Row) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (P₀ : ProbabilityMeasure Pair)
    (hweak : Tendsto (uncenteredRow A U hU) atTop (𝓝 P₀))
    (hback : MixedLaw.law i μ ≪ (P₀ : Measure Pair))
    {a₀ b₀ : ℝ} (hab₀ : a₀ < b₀)
    (hcomponent : volume.restrict (Ioo a₀ b₀) ≪ μ)
    (c : ℕ → ℝ) (j y : ℕ → ℤ)
    (hc : Tendsto (fun n => A.d n * c n) atTop (𝓝 0))
    (he : Tendsto (fun n => A.d n * ((j n - y n : ℤ) : ℝ)) atTop (𝓝 0))
    {a b : ℝ} (hab : a < b) :
    Tendsto (fun n => (A.cell c j y n).real (Icc a b) /
      (((b - a) * density A.vX A.vY) / (A.N n : ℝ))) atTop (𝓝 1) :=
  tendsto_relative_interval A
    (compactGap_of_uncentered_source_limit A U hU r hbU hcenter i μ P₀
      hweak hback hab₀ hcomponent) c j y hc he hab

end FCAppendix.Affine.Uniform06.CenteredSourceGap
