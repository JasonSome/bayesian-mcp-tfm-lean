import FCAppendix.Affine.Hybrid.ActiveNoisyCompactLimit

noncomputable section
namespace FCAppendix.Affine.Tail04
open MeasureTheory ProbabilityTheory Set Filter Topology
open Existence.Distributional
open Hybrid

abbrev Population := Fin 3

theorem exists_joint_noisy_compact_sequence
    (vLo vHi L U : Population → ℝ)
    (hL : ∀ i, 0 < L i) (hLU : ∀ i, L i ≤ U i)
    (μ : ∀ i, Measure (ActiveValue (vLo i) (vHi i)))
    [∀ i, IsProbabilityMeasure (μ i)]
    (u : unitInterval → ∀ i,
      Profile (fun i => ActiveValue (vLo i) (vHi i))
        (fun i => ActiveBaseBid (L i) (U i)) μ ×
          (ActiveValue (vLo i) (vHi i) × ActiveBaseBid (L i) (U i)) → ℝ)
    (hu : ∀ eps : unitInterval, 0 < (eps : ℝ) → ∀ i, Continuous (u eps i))
    (epsBudget : ℝ) (hbudget : 0 < epsBudget) (hbudget1 : epsBudget ≤ 1) :
    ∃ (eps : ℕ → unitInterval)
      (π : ℕ → Profile (fun i => ActiveValue (vLo i) (vHi i))
        (fun i => ActiveBaseBid (L i) (U i)) μ)
      (π₀ : Profile (fun i => ActiveValue (vLo i) (vHi i))
        (fun i => ActiveBaseBid (L i) (U i)) μ),
      (∀ j, 0 < (eps j : ℝ) ∧ (eps j : ℝ) < epsBudget) ∧
      Tendsto eps atTop (𝓝 0) ∧
      (∀ j, ∃ σ : ∀ i, Kernel (ActiveValue (vLo i) (vHi i))
          (ActiveBaseBid (L i) (U i)),
        (∀ i, IsMarkovKernel (σ i)) ∧
        (∀ i, μ i ⊗ₘ σ i = ((π j i).1 : Measure
          (ActiveValue (vLo i) (vHi i) × ActiveBaseBid (L i) (U i)))) ∧
        (∀ i, AllActionOptimal (π j i) (fun x => u (eps j) i (π j, x))) ∧
        (∀ i, ∀ᵐ v ∂μ i, ∀ᵐ b ∂σ i v, ∀ b' : ActiveBaseBid (L i) (U i),
          u (eps j) i (π j, (v, b')) ≤ u (eps j) i (π j, (v, b)))) ∧
      Tendsto π atTop (𝓝 π₀) ∧
      (∀ i, Tendsto
        (fun j => activeUniversalNoisyLaw (hL i) (hLU i) (μ i) (eps j, π j i))
        atTop (𝓝 (activeUniversalNoisyLaw (hL i) (hLU i) (μ i) (0, π₀ i)))) := by
  letI (i : Population) : Nonempty (ActiveBaseBid (L i) (U i)) :=
    ⟨⟨L i, le_rfl, hLU i⟩⟩
  let epsR : ℕ → ℝ := fun j => (epsBudget / 4) / (j + 1)
  have hpos : ∀ j, 0 < epsR j := by
    intro j
    dsimp [epsR]
    positivity
  have hquarter : ∀ j, epsR j ≤ epsBudget / 4 := by
    intro j
    dsimp [epsR]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < j + 1)).mpr
    have hn : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith [mul_nonneg (by linarith : 0 ≤ epsBudget/4) hn]
  have hsmall : ∀ j, epsR j ≤ 1 := by
    intro j
    exact (hquarter j).trans (by linarith)
  let eps : ℕ → unitInterval := fun j => ⟨epsR j, (hpos j).le, hsmall j⟩
  have heps0 : Tendsto eps atTop (𝓝 0) := by
    apply tendsto_subtype_rng.mpr
    have hc : Tendsto (fun _ : ℕ => epsBudget / 4) atTop (𝓝 (epsBudget / 4)) :=
      tendsto_const_nhds
    convert! hc.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) using 1
    · funext j
      dsimp [eps, epsR]
      ring
    · simp
  choose π σ hmark hdis hjoint hopt using fun j =>
    exists_population_laws (fun i => ActiveValue (vLo i) (vHi i))
      (fun i => ActiveBaseBid (L i) (U i)) μ (u (eps j)) (hu (eps j) (hpos j))
  obtain ⟨π₀, phi, hphi, hlim⟩ := CompactSpace.tendsto_subseq π
  refine ⟨eps ∘ phi, π ∘ phi, π₀, ?_, heps0.comp hphi.tendsto_atTop, ?_, hlim, ?_⟩
  · intro j
    exact ⟨hpos (phi j), (hquarter (phi j)).trans_lt (by linarith)⟩
  · intro j
    exact ⟨σ (phi j), hmark (phi j), hdis (phi j), hjoint (phi j), hopt (phi j)⟩
  · intro i
    have hcoord : Tendsto (fun j => π (phi j) i) atTop (𝓝 (π₀ i)) :=
      (continuous_apply i).continuousAt.tendsto.comp hlim
    exact (continuous_activeUniversalNoisyLaw (hL i) (hLU i) (μ i)).continuousAt.tendsto.comp
      ((heps0.comp hphi.tendsto_atTop).prodMk_nhds hcoord)

end FCAppendix.Affine.Tail04
