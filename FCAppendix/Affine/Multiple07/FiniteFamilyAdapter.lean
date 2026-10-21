import FCAppendix.Affine.Multiple07.ZeroVersion
import FCAppendix.Affine.Multiple07.PrimitiveComponents

noncomputable section
namespace FCAppendix.Affine.Multiple07
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical

def unusedPrefixGame (M : ℕ) : FiniteGame M 2 (marketCapacity M) unitInterval where
  F := sourceValueLaw
  hF := inferInstance
  σ := Kernel.deterministic (fun _ : ℝ => Interim.abstain 2) measurable_const
  hσ := inferInstance
  seedLaw := volume
  hseed := inferInstance
  policy := fun _ _ _ => ⟨∅, by simp⟩
  policy_measurable := fun _ => measurable_const
  A := affineSchedule
  G := Schedule.once 2
  g := 0
  g_nonneg := le_rfl

def extendTailGames (N : ℕ)
    (Γ : ∀ M, N ≤ M → FiniteGame M 2 (marketCapacity M) unitInterval)
    (k : ℕ) : MultipleGame k :=
  if h : N ≤ k + 1 then Γ (k + 1) h else unusedPrefixGame (k + 1)

theorem extendTailGames_on (N : ℕ)
    (Γ : ∀ M, N ≤ M → FiniteGame M 2 (marketCapacity M) unitInterval)
    (k : ℕ) (hk : N ≤ k + 1) : extendTailGames N Γ k = Γ (k + 1) hk := by
  simp only [extendTailGames, dif_pos hk]

theorem extendTailGames_parameters (N : ℕ)
    (Γ : ∀ M, N ≤ M → FiniteGame M 2 (marketCapacity M) unitInterval)
    (hp : ∀ M hM, (Γ M hM).F = sourceValueLaw ∧ (Γ M hM).A = affineSchedule ∧
      (Γ M hM).g = 0 ∧ (Γ M hM).seedLaw = volume) (k : ℕ) :
    (extendTailGames N Γ k).F = sourceValueLaw ∧
    (extendTailGames N Γ k).A = affineSchedule ∧
    (extendTailGames N Γ k).g = 0 ∧
    (extendTailGames N Γ k).seedLaw = volume := by
  by_cases hk : N ≤ k + 1
  · rw [extendTailGames_on N Γ k hk]
    exact hp _ _
  · simp [extendTailGames, hk, unusedPrefixGame]

theorem extendTailGames_count_limit (N : ℕ) (hN : 0 < N)
    (Γ : ∀ M, N ≤ M → FiniteGame M 2 (marketCapacity M) unitInterval)
    (v : ℝ) (j : Fin 3) (ell : ℝ)
    (hlim : Tendsto (fun k => (conditionalTypeCountLaw
      (Γ (N + k) (by omega)) (by omega) v).mass j) atTop (𝓝 ell)) :
    Tendsto (fun k => (conditionalTypeCountLaw (extendTailGames N Γ k)
      (Nat.succ_pos k) v).mass j) atTop (𝓝 ell) := by
  have hindex (M M' : ℕ) (hM : 0<M) (hM' : 0<M') (hNM : N≤M) (hNM' : N≤M')
      (he : M=M') : (conditionalTypeCountLaw (Γ M hNM) hM v).mass j=
        (conditionalTypeCountLaw (Γ M' hNM') hM' v).mass j := by
    subst M'
    rfl
  apply (tendsto_add_atTop_iff_nat (N - 1)).mp
  apply hlim.congr'
  exact Eventually.of_forall fun k => by
    have hk : N ≤ k + (N - 1) + 1 := by omega
    have he : k + (N - 1) + 1 = N + k := by omega
    dsimp only
    simp only [extendTailGames,he,dif_pos (show N≤N+k by omega)]
    exact hindex _ _ (by omega) (by omega) (by omega) hk he.symm

theorem extendTailGames_native (r : Partition) (N : ℕ)
    (Γ : ∀ M, N ≤ M → FiniteGame M 2 (marketCapacity M) unitInterval)
    (hn : ∀ M hM,
      IsBayesianEquilibrium (Γ M hM) ∧ NullSingletonClass (physicalBidLaw (Γ M hM)) ∧
      (∀ᵐ x ∂((Γ M hM).F ⊗ₘ (Γ M hM).σ),
        x.2.routeCount = if x.1 ∈ upperSet r then 1 else 2)) :
    ∀ᶠ k in atTop,
      IsBayesianEquilibrium (extendTailGames N Γ k) ∧
      NullSingletonClass (physicalBidLaw (extendTailGames N Γ k)) ∧
      (∀ᵐ x ∂((extendTailGames N Γ k).F ⊗ₘ (extendTailGames N Γ k).σ),
        x.2.routeCount = if x.1 ∈ upperSet r then 1 else 2) := by
  filter_upwards [eventually_ge_atTop N] with k hk
  have hk' : N ≤ k + 1 := by omega
  rw [extendTailGames_on N Γ k hk']
  exact hn _ _

def sourceFamily_from_producer_tail (r : Partition) (N : ℕ) (hN : 2 ≤ N)
    (Γ : ∀ M, N ≤ M → FiniteGame M 2 (marketCapacity M) unitInterval)
    (hp : ∀ M hM, (Γ M hM).F = sourceValueLaw ∧ (Γ M hM).A = affineSchedule ∧
      (Γ M hM).g = 0 ∧ (Γ M hM).seedLaw = volume)
    (hn : ∀ M hM,
      IsBayesianEquilibrium (Γ M hM) ∧ NullSingletonClass (physicalBidLaw (Γ M hM)) ∧
      (∀ᵐ x ∂((Γ M hM).F ⊗ₘ (Γ M hM).σ),
        x.2.routeCount = if x.1 ∈ upperSet r then 1 else 2))
    (hc : ∀ b v, v ∈ Icc (bandLower b) (bandUpper b) → 0 < v → ∀ j : Fin 3,
      Tendsto (fun k => (conditionalTypeCountLaw
        (Γ (N + k) (by omega)) (by omega) v).mass j)
        atTop (𝓝 ((limitingLaw r v).mass j))) : NativeFamily r := by
  let E := extendTailGames N Γ
  have hE : ∀ k, (E k).F = sourceValueLaw :=
    fun k => (extendTailGames_parameters N Γ hp k).1
  refine
    { game := fun k => normalizeZero (E k)
      common_values := hE
      coefficient := fun k => (extendTailGames_parameters N Γ hp k).2.1
      zero_base := fun k => (extendTailGames_parameters N Γ hp k).2.2.1
      private_seed := fun k => (extendTailGames_parameters N Γ hp k).2.2.2
      native := ?_
      conditional := ?_ }
  · filter_upwards [extendTailGames_native r N Γ hn] with k hk
    have heq := normalizeZero_equilibrium (E k) (hE k) hk.1
    refine ⟨heq.users, heq.beliefs, ?_, ?_⟩
    · rw [normalizeZero_physicalBidLaw (E k) (hE k)]
      exact hk.2.1
    · rw [normalizeZero_joint_law (E k) (hE k)]
      exact hk.2.2
  · apply normalizeZero_all_band_limits r E hE
    intro b v hv hv0 j
    exact extendTailGames_count_limit N (by omega) Γ v j _ (hc b v hv hv0 j)

end FCAppendix.Affine.Multiple07
