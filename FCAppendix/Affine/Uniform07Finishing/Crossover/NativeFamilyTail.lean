import FCAppendix.Affine.Uniform07Finishing.Native.MatchedScalarData

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover
open MeasureTheory ProbabilityTheory Bayes Game Set Filter Topology
namespace Physical

def castUniformMarket {row : Uniform07.Row} {m n : ℕ} (h : m=n)
    (D : UniformMarketData row m) : UniformMarketData row n := h ▸ D

def castUniformLowerChain {row : Uniform07.Row} {m n : ℕ} (h : m=n)
    {D : UniformMarketData row m} (C : UniformLowerChain D) :
    UniformLowerChain (castUniformMarket h D) := by
  cases h
  exact C

theorem castUniformMarket_moments
    {row : Uniform07.Row} {m n : ℕ} (h : m=n)
    (D : UniformMarketData row m) (ε : ℝ)
    (hmom : ∀ u : Fin m, ∀ b : Icc (0:ℝ) (Early.bidCap row),
      |((problem D.native u).outcome (sourceLowerBroadcastAction (Early.bidCap row) b)).load-
          2*sourceProductProbability row b|≤ε ∧
      |((problem D.native u).outcome (sourceLowerBroadcastAction (Early.bidCap row) b)).duplicates-
          (sourceProductProbability row b)^2|≤ε) :
    ∀ u : Fin n, ∀ b : Icc (0:ℝ) (Early.bidCap row),
      |((problem (castUniformMarket h D).native u).outcome
        (sourceLowerBroadcastAction (Early.bidCap row) b)).load-2*sourceProductProbability row b|≤ε ∧
      |((problem (castUniformMarket h D).native u).outcome
        (sourceLowerBroadcastAction (Early.bidCap row) b)).duplicates-(sourceProductProbability row b)^2|≤ε := by
  cases h
  exact hmom

def uniformNativePair_from_eventual_matched_chains
    (D : UniformAuxiliaryData05) (K : UniformAuxiliaryKernels05_06 D)
    (hchain : ∀ᶠ k in atTop, ∀ row : Uniform07.Row,
      ∃ h : MatchedScalarGuards D row k,
        Nonempty (UniformLowerChain (matchedMarket D row k h))) :
    UniformNativePair := by
  classical
  have hboth := hchain.and (D.eventually_matched_routes_and_moments K)
  let shift : ℕ := Classical.choose (eventually_atTop.1 hboth)
  have hshift := Classical.choose_spec (eventually_atTop.1 hboth)
  have htail (k : ℕ) := hshift (shift+k) (by omega)
  let guards (row : Uniform07.Row) (k : ℕ) : MatchedScalarGuards D row (shift+k) :=
    Classical.choose ((htail k).1 row)
  let chains (row : Uniform07.Row) (k : ℕ) :
      UniformLowerChain (matchedMarket D row (shift+k) (guards row k)) :=
    Classical.choice (Classical.choose_spec ((htail k).1 row))
  let populations (k : ℕ) : D.start+(shift+k)=(D.start+shift)+k :=
    (Nat.add_assoc D.start shift k).symm
  let markets (row : Uniform07.Row) (k : ℕ) :
      UniformMarketData row ((D.start+shift)+k) :=
    castUniformMarket (populations k) (matchedMarket D row (shift+k) (guards row k))
  let completedChains (row : Uniform07.Row) (k : ℕ) : UniformLowerChain (markets row k) :=
    castUniformLowerChain (populations k) (chains row k)
  let ε (row : Uniform07.Row) (k : ℕ) : ℝ :=
    (K.physical row).product.nativeMomentError (shift+k)
  apply uniformNativePair_from_lower_chains (D.start+shift)
    (by have := D.start_ge_two; omega) markets completedChains ε
  · intro row k
    exact (K.physical row).product.nativeMomentError_nonneg (shift+k)
  · intro row
    exact (K.physical row).product.nativeMomentError_tendsto.comp (tail_population_tendsto shift)
  · intro row
    apply Eventually.of_forall
    intro k
    exact castUniformMarket_moments (populations k)
      (matchedMarket D row (shift+k) (guards row k)) (ε row k)
      (((htail k).2 row (guards row k)).2)

theorem aff_uniform_result_from_eventual_matched_chains
    (D : UniformAuxiliaryData05) (K : UniformAuxiliaryKernels05_06 D)
    (hchain : ∀ᶠ k in atTop, ∀ row : Uniform07.Row,
      ∃ h : MatchedScalarGuards D row k,
        Nonempty (UniformLowerChain (matchedMarket D row k h))) :
    AffUniformResult :=
  aff_uniform_result_of_native_pair (uniformNativePair_from_eventual_matched_chains D K hchain)

end Physical
end FCAppendix.Affine.Uniform07Finishing.Crossover
