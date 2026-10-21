import FCAppendix.Affine.Uniform07Finishing.Crossover.PhysicalFamilies
import FCAppendix.Affine.Uniform07Finishing.Native.NativeConditional

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover
open MeasureTheory ProbabilityTheory Bayes Game Set Filter Topology
namespace Physical

theorem sourceProductMarginal_eq_native_probability
    (row : Uniform07.Row) {b : ℝ} (hb : b∈Icc (0:ℝ) (Early.bidCap row)) :
    sourceProductMarginal row b=sourceProductProbability row b := by
  by_cases hbl : b≤ Uniform07.entry row
  · rw [sourceProductMarginal,ClippedResidual.exposure_zero hbl]
    simp only [sourceProductProbability,if_pos hbl]
  · have hclip : (1-Uniform07.xi row)*b≤ Uniform07.entry row := by
      have hκ : 1-Uniform07.xi row=Uniform07.kappa row := by
        linarith [source_kappa_add_xi row]
      rw [hκ]
      exact (mul_le_mul_of_nonneg_left hb.2 (source_kappa_positive row).le).trans
        (source_product_cap_guard row).le
    rw [sourceProductMarginal,
      ClippedResidual.exposure_of_between (Uniform07.xi_pos row)
        (source_entry_positive row) (lt_of_not_ge hbl) hclip,
      sourceProductProbability,if_neg hbl]

variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem sourceLowerBroadcastAction_native_moments
    (Γ : FiniteGame m 2 c Seed) (i : Fin m) (U : ℝ) (b : Icc (0:ℝ) U) :
    ((problem Γ i).outcome (sourceLowerBroadcastAction U b)).load=2*q Γ i b ∧
    ((problem Γ i).outcome (sourceLowerBroadcastAction U b)).duplicates=
      duplicate Γ i b := by
  constructor
  · have h := load_eq_mean Γ (by norm_num : 0<2) i
      (sourceLowerBroadcastAction U b)
    simpa only [sourceLowerBroadcastAction,q,Nat.cast_ofNat] using h
  · rw [sourceLowerBroadcastAction_eq_two]
    rfl

theorem ProductKernels05.native_moments
    {row : Uniform07.Row} {Γ : FiniteGame m 2 c Seed} {i : Fin m}
    {R error : ℝ} (E : ProductKernels05 row Γ i R error)
    (he : 0≤ error) (hR : Early.bidCap row< R)
    (b : Icc (0:ℝ) (Early.bidCap row)) :
    |((problem Γ i).outcome (sourceLowerBroadcastAction (Early.bidCap row) b)).load-
        2*sourceProductProbability row b|≤ 2*error ∧
    |((problem Γ i).outcome (sourceLowerBroadcastAction (Early.bidCap row) b)).duplicates-
        (sourceProductProbability row b)^2|≤ 2*error := by
  have hm := sourceLowerBroadcastAction_native_moments Γ i (Early.bidCap row) b
  have hp := sourceProductMarginal_eq_native_probability row b.2
  have hq := E.marginal b ⟨b.2.1,b.2.2.trans_lt hR⟩
  have hd := E.duplicate b ⟨b.2.1,b.2.2.trans_lt hR⟩
  rw [hp] at hq hd
  constructor
  · rw [hm.1,←mul_sub,abs_mul]
    norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact mul_le_mul_of_nonneg_left hq (by norm_num)
  · rw [hm.2]
    exact hd.trans (by linarith)

theorem ProductKernels05.native_moments_of_raw_outcome_eq
    {row : Uniform07.Row} {Γ Δ : FiniteGame m 2 c Seed} {i : Fin m}
    {R error : ℝ} (E : ProductKernels05 row Γ i R error)
    (he : 0≤ error) (hR : Early.bidCap row< R)
    (hout : ∀ a : JointAction 2, (problem Δ i).outcome a=(problem Γ i).outcome a)
    (b : Icc (0:ℝ) (Early.bidCap row)) :
    |((problem Δ i).outcome (sourceLowerBroadcastAction (Early.bidCap row) b)).load-
        2*sourceProductProbability row b|≤ 2*error ∧
    |((problem Δ i).outcome (sourceLowerBroadcastAction (Early.bidCap row) b)).duplicates-
        (sourceProductProbability row b)^2|≤ 2*error := by
  rw [hout]
  exact E.native_moments he hR b

section Families
variable {population : ℕ→ℕ} {SeedFamily : ℕ→ Type*}
    [∀ k, MeasurableSpace (SeedFamily k)]
variable {Γ Δ : ∀ k,
    FiniteGame (population k) 2 (Uniform07.capacity (population k)) (SeedFamily k)}

def ProductFamily05.nativeMomentError {row : Uniform07.Row} {upper : ℕ→ℝ}
    (E : ProductFamily05 Γ row upper) (k : ℕ) : ℝ := 2*|E.error k|

theorem ProductFamily05.nativeMomentError_nonneg
    {row : Uniform07.Row} {upper : ℕ→ℝ} (E : ProductFamily05 Γ row upper) (k : ℕ) :
    0≤ E.nativeMomentError k := mul_nonneg (by norm_num) (abs_nonneg _)

theorem ProductFamily05.nativeMomentError_tendsto
    {row : Uniform07.Row} {upper : ℕ→ℝ} (E : ProductFamily05 Γ row upper) :
    Tendsto E.nativeMomentError atTop (𝓝 0) := by
  change Tendsto (fun k => 2*|E.error k|) atTop (𝓝 0)
  simpa only [abs_zero,mul_zero] using
    E.errorSmall.abs.const_mul (2:ℝ)

theorem ProductFamily05.eventually_native_moments
    {row : Uniform07.Row} {upper : ℕ→ℝ} (E : ProductFamily05 Γ row upper) :
    ∀ᶠ k in atTop, ∀ i : Fin (population k),
      ∀ b : Icc (0:ℝ) (Early.bidCap row),
      |((problem (Γ k) i).outcome (sourceLowerBroadcastAction (Early.bidCap row) b)).load-
          2*sourceProductProbability row b|≤ E.nativeMomentError k ∧
      |((problem (Γ k) i).outcome (sourceLowerBroadcastAction (Early.bidCap row) b)).duplicates-
          (sourceProductProbability row b)^2|≤ E.nativeMomentError k := by
  filter_upwards [E.errorNonnegative,E.floorAboveCap,E.kernels] with k he hR hK
  intro i b
  obtain ⟨K⟩ := hK i
  simpa only [ProductFamily05.nativeMomentError,abs_of_nonneg he] using
    K.native_moments he hR b

theorem ProductFamily05.eventually_native_moments_of_raw_outcome_eq
    {row : Uniform07.Row} {upper : ℕ→ℝ} (E : ProductFamily05 Γ row upper)
    (hout : ∀ᶠ k in atTop, ∀ i : Fin (population k), ∀ a : JointAction 2,
      (problem (Δ k) i).outcome a=(problem (Γ k) i).outcome a) :
    ∀ᶠ k in atTop, ∀ i : Fin (population k),
      ∀ b : Icc (0:ℝ) (Early.bidCap row),
      |((problem (Δ k) i).outcome (sourceLowerBroadcastAction (Early.bidCap row) b)).load-
          2*sourceProductProbability row b|≤ E.nativeMomentError k ∧
      |((problem (Δ k) i).outcome (sourceLowerBroadcastAction (Early.bidCap row) b)).duplicates-
          (sourceProductProbability row b)^2|≤ E.nativeMomentError k := by
  filter_upwards [E.eventually_native_moments,hout] with k hK hEq
  intro i b
  rw [hEq i]
  exact hK i b

end Families
end Physical
end FCAppendix.Affine.Uniform07Finishing.Crossover
