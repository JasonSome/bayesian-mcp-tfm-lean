import FCAppendix.Affine.Multiple07.Native02FamilyAdapter

noncomputable section
namespace FCAppendix.Affine.Multiple07
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical

theorem ex_multiple :
    sourceValueLaw.real (Iic (1 / 150 : ℝ)) = 1 / 100 ∧
      sourceValueLaw.real (Ioi (1 / 150 : ℝ)) = 99 / 100 ∧
      HasDerivAt (fun t => sourceValueLaw.real (Iic t)) (3 / 2) (1 / 150) ∧
    ∃ Γ : Partition → ∀ m, MultipleGame m,
      (∀ r m, (Γ r m).F = sourceValueLaw ∧ (Γ r m).A = affineSchedule ∧
        (Γ r m).g = 0 ∧ (Γ r m).seedLaw = volume) ∧
      (∀ r b v, v ∈ Icc (bandLower b) (bandUpper b) → ∀ j : Fin 3,
        Tendsto
          (fun m => (conditionalTypeCountLaw (Γ r m) (Nat.succ_pos m) v).mass j)
          atTop (𝓝 ((limitingLaw r v).mass j))) ∧
      (∀ r,
        Tendsto (fun m => finiteCoverage (Γ r m)) atTop (𝓝 (limitingCoverage r)) ∧
        Tendsto (fun m => finiteLoad (Γ r m)) atTop (𝓝 (99 / 100 : ℝ)) ∧
        Tendsto (fun m => finiteLoad (Γ r m) - finiteCoverage (Γ r m))
          atTop (𝓝 (limitingDuplicates r)) ∧
        Tendsto (fun m => finiteMultiplicity (Γ r m))
          atTop (𝓝 (limitingMultiplicity r))) ∧
      (∃ N, ∀ m ≥ N,
        (∀ r,
          (∀ᵐ v ∂(Γ r m).F, ∀ᵐ a ∂(Γ r m).σ v, ∀ i,
            ∀ dev : JointAction 2,
            (problem (Γ r m) i).payoff v dev ≤ (problem (Γ r m) i).payoff v a) ∧
          (∃ B : PosteriorSystem (Γ r m),
            ∀ j ℓ s, Finite.Optimal (marketCapacity (m + 1))
              (beliefReceipts (Γ r m).A (posteriorCountBelief (Γ r m) B j ℓ) ℓ)
              ((Γ r m).policy j ℓ s).val) ∧
          NullSingletonClass (physicalBidLaw (Γ r m)) ∧
          VisibleAtomless (Γ r m) ∧
          (∀ᵐ x ∂((Γ r m).F ⊗ₘ (Γ r m).σ),
            x.2.routeCount = if x.1 ∈ upperSet r then 1 else 2)) ∧
        0 < finiteCoverage (Γ .row335 m) ∧ 0 < finiteCoverage (Γ .row665 m) ∧
        finiteCoverage (Γ .row665 m) < finiteCoverage (Γ .row335 m) ∧
        finiteLoad (Γ .row335 m) - finiteCoverage (Γ .row335 m) <
          finiteLoad (Γ .row665 m) - finiteCoverage (Γ .row665 m) ∧
        finiteMultiplicity (Γ .row335 m) < finiteMultiplicity (Γ .row665 m)) ∧
      ((86268664220 / 10^12 : ℝ) < limitingDuplicates .row335 ∧
        limitingDuplicates .row335 < 86268664221 / 10^12 ∧
        (169168480288 / 10^12 : ℝ) < limitingDuplicates .row665 ∧
        limitingDuplicates .row665 < 169168480289 / 10^12) ∧
      ((903731335779 / 10^12 : ℝ) < limitingCoverage .row335 ∧
        limitingCoverage .row335 < 903731335780 / 10^12 ∧
        (820831519711 / 10^12 : ℝ) < limitingCoverage .row665 ∧
        limitingCoverage .row665 < 820831519712 / 10^12) ∧
      ((10954583080 / 10^10 : ℝ) < limitingMultiplicity .row335 ∧
        limitingMultiplicity .row335 < 10954583081 / 10^10 ∧
        (12060940354 / 10^10 : ℝ) < limitingMultiplicity .row665 ∧
        limitingMultiplicity .row665 < 12060940355 / 10^10) ∧
      (∃ N, ∀ᵐ v ∂sourceValueLaw, ∀ r m, N≤ m → ∀ᵐ a ∂(Γ r m).σ v,
        ∀ i, ∀ dev : JointAction 2,
          (problem (Γ r m) i).payoff v dev≤(problem (Γ r m) i).payoff v a) := by
  obtain ⟨E₁⟩ := source_native_family .row335
  obtain ⟨E₂⟩ := source_native_family .row665
  refine ⟨efficient_cutoff_and_density.1, efficient_cutoff_and_density.2.1,
    efficient_cutoff_and_density.2.2,?_⟩
  obtain ⟨Γ,hp,hc,ha,ht,hd,hQ,hmu⟩ :=
    multiple_source_assembly_of_native_families E₁ E₂
  refine ⟨Γ,hp,hc,ha,ht,hd,hQ,hmu,?_⟩
  obtain ⟨N,hN⟩ := ht
  exact ⟨N,common_conull_across_native_markets Γ N
    (fun r m => (hp r m).1) (fun r m hm => ((hN m hm).1 r).1)⟩

end FCAppendix.Affine.Multiple07
