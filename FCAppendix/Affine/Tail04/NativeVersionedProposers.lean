import FCAppendix.Affine.Tail04.NativeVersionedUsers

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeVersionedSource
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes
open Hybrid Hybrid.Native02 OriginalValues CoefficientOne NativeVersionedRows

lemma closed_posterior_eq {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (G : FiniteGame m 2 c Seed) (R : ℝ)
    (hfull : ∀ᵐ d ∂userProfileLaw G,d ∈ ClosedUpperPriority.closedProfiles m R) :
    ClosedUpperPriority.closedPosterior G R hfull =
      Native02.closedUpperPosterior G R hfull := rfl

lemma source_proposers_closed {p : PrimitiveInput} {A : FrozenActiveFamily p}
    (S : SourceFamily p A) (k : ℕ)
    (hfull : ∀ᵐ d ∂userProfileLaw (S.game k),d ∈ ClosedUpperPriority.closedProfiles (S.M k) p.R) :
    ∀ j X,FeasibleObservedList j X → ∀ seed,
      Finite.Optimal (S.C k)
        (beliefReceipts (S.game k).A
          (posteriorCountBelief (S.game k) (ClosedUpperPriority.closedPosterior (S.game k) p.R hfull) j X) X)
        ((S.game k).policy j X seed).val :=
  S.proposer_all_lists_seeds k

lemma source_proposers_closed_of_eq {p : PrimitiveInput} {A : FrozenActiveFamily p}
    (S : SourceFamily p A) (k : ℕ) (G : FiniteGame (S.M k) 2 (S.C k) unitInterval)
    (he : G = S.game k)
    (hfull : ∀ᵐ d ∂userProfileLaw G,d ∈ ClosedUpperPriority.closedProfiles (S.M k) p.R) :
    ∀ j X,FeasibleObservedList j X → ∀ seed,
      Finite.Optimal (S.C k)
        (beliefReceipts G.A
          (posteriorCountBelief G (ClosedUpperPriority.closedPosterior G p.R hfull) j X) X)
        (G.policy j X seed).val := by
  subst G
  exact source_proposers_closed S k hfull

variable {P : ValueParameters} (s : BoundedSource P) (hs : BoundedSourceGuards s)
  (V : NativeImplementation (NativeSource.input s hs))

lemma bounded_proposers (k : ℕ) (hk : 200 ≤ V.toNativeFamilyData.M k)
    (err : ℝ) (herr : 0 ≤ err) :
    let row := boundedRow s hs V k hk err herr
    ∀ j X,FeasibleObservedList j X → ∀ seed,
      Finite.Optimal (marketCapacity (V.toNativeFamilyData.M k))
        (beliefReceipts row.reference.A
          (posteriorCountBelief row.reference row.referencePosterior j X) X)
        (row.reference.policy j X seed).val := by
  dsimp only
  unfold BoundedRow.referencePosterior
  exact source_proposers_closed_of_eq V.source (V.toNativeFamilyData.index k)
    (boundedRow s hs V k hk err herr).reference (bounded_reference_eq s hs V k hk err herr) _

def originalPosterior (k : ℕ) (hk : 200 ≤ V.toNativeFamilyData.M k) :
    PosteriorSystem (data s hs V k hk).original :=
  ConditionalVersions.withStrategy_posterior (data s hs V k hk).baseOriginal
    (data s hs V k hk).originalKernel (data s hs V k hk).original_kernel_ae
    (P.originalFixedPosterior hk (context s hs V k) s.scalar.U s.scalar.R s.scalar.floor_pos
      s.scalar.floor_below_upper (data s hs V k hk).PL (data s hs V k hk).PA
      s.scalar.eta s.scalar.eta_pos.le s.scalar.eta_lt_one
      (boundedRow s hs V k hk 0 le_rfl).low_closed
      (boundedRow s hs V k hk 0 le_rfl).active_closed)

lemma original_proposers (k : ℕ) (hk : 200 ≤ V.toNativeFamilyData.M k) :
    ∀ j X,FeasibleObservedList j X → ∀ seed,
      Finite.Optimal (marketCapacity (V.toNativeFamilyData.M k))
        (beliefReceipts (data s hs V k hk).original.A
          (posteriorCountBelief (data s hs V k hk).original (originalPosterior s hs V k hk) j X) X)
        ((data s hs V k hk).original.policy j X seed).val := by
  exact P.originalFixedGame_feasible_proposers_transfer hk (context s hs V k)
    s.scalar.U s.scalar.R s.scalar.floor_pos s.scalar.floor_below_upper
    (data s hs V k hk).PL (data s hs V k hk).PA s.scalar.eta s.scalar.eta_pos.le
    s.scalar.eta_lt_one (data s hs V k hk).PH
    (boundedRow s hs V k hk 0 le_rfl).low_closed
    (boundedRow s hs V k hk 0 le_rfl).active_closed
    (upper_shape s hs V k) (bounded_proposers s hs V k hk 0 le_rfl)

def normalizedGame (k : ℕ) : FiniteGame (V.toNativeFamilyData.M (k+200)) 2
    (marketCapacity (V.toNativeFamilyData.M (k+200))) unitInterval :=
  FeasibleListNormalization.game (originalGame s hs V k)

theorem eventually_normalized_equilibrium :
    ∀ᶠ k in atTop,IsBayesianEquilibrium (normalizedGame s hs V k) := by
  filter_upwards [eventually_original_users s hs V] with k hk
  exact FeasibleListNormalization.equilibrium (originalGame s hs V k) hk
    (originalPosterior s hs V (k+200) (large s hs V k))
    (original_proposers s hs V (k+200) (large s hs V k))

lemma normalized_count_eq (k : ℕ) (v : ℝ) :
    conditionalTypeCountLaw (normalizedGame s hs V k) (by have := large s hs V k;omega) v =
      conditionalTypeCountLaw (originalGame s hs V k) (by have := large s hs V k;omega) v :=
  FeasibleListNormalization.conditionalCount_eq _ _ v

end FCAppendix.Affine.Tail04.NativeVersionedSource
