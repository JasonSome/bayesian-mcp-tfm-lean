import FCAppendix.Affine.Multiple07.ActualOutcomes
import FCAppendix.Affine.Multiple07.OutcomeCertificate
import FCAppendix.Affine.Multiple07.MenuAdapter

noncomputable section
namespace FCAppendix.Affine.Multiple07

open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open scoped BigOperators

abbrev MultipleGame (m : ℕ) := FiniteGame (m + 1) 2 (marketCapacity (m + 1)) unitInterval

def physicalBidLaw {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m n c Seed) : Measure ℝ :=
  (userLaw Γ).map (fun d => d.1.2.bid)

theorem visibleAtomless_of_physicalBidLaw
    {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m n c Seed) [NullSingletonClass (physicalBidLaw Γ)] :
    VisibleAtomless Γ := by
  intro j b
  have h : userLaw Γ {d | d.1.2.bid = b} = 0 := by
    have hz := measure_singleton (μ := physicalBidLaw Γ) b
    rw [physicalBidLaw, Measure.map_apply
      (show Measurable (fun d : UserDraw n => d.1.2.bid) from
        (measurable_bid n).comp (measurable_snd.comp measurable_fst))
      (measurableSet_singleton b)] at hz
    exact hz
  exact measure_mono_null (fun _ hd => hd.2) h

structure NativeFamily (r : Partition) where
  game : ∀ m, MultipleGame m
  common_values : ∀ m, (game m).F = sourceValueLaw
  coefficient : ∀ m, (game m).A = affineSchedule
  zero_base : ∀ m, (game m).g = 0
  private_seed : ∀ m, (game m).seedLaw = volume
  native : ∀ᶠ m in atTop,
    UsersOptimal (game m) ∧
      (∃ B : PosteriorSystem (game m), PosteriorProposerOptimal (game m) B) ∧
      NullSingletonClass (physicalBidLaw (game m)) ∧
      (∀ᵐ x ∂((game m).F ⊗ₘ (game m).σ),
        x.2.routeCount = if x.1 ∈ upperSet r then 1 else 2)
  conditional : ∀ b v, v ∈ Icc (bandLower b) (bandUpper b) → ∀ j : Fin 3,
    Tendsto
      (fun m => (conditionalTypeCountLaw (game m) (Nat.succ_pos m) v).mass j)
      atTop (𝓝 ((limitingLaw r v).mass j))

abbrev NativeProducerOutput := ∀ r : Partition, Nonempty (NativeFamily r)

theorem common_conull_users_all_raw_actions
    {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m n c Seed) (h : UsersOptimal Γ) :
    ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v, ∀ i, ∀ dev : JointAction n,
      (problem Γ i).payoff v dev ≤ (problem Γ i).payoff v a := by
  have hv : ∀ᵐ v ∂Γ.F, ∀ i,
      ∀ᵐ a ∂Γ.σ v, (problem Γ i).BestResponse v a := ae_all_iff.mpr h
  filter_upwards [hv] with v hv
  exact ae_all_iff.mpr hv

theorem family_ae_conditional (r : Partition) (E : NativeFamily r) :
    ∀ᵐ v ∂sourceValueLaw, ∀ j : Fin 3,
      Tendsto
        (fun m => (conditionalTypeCountLaw (E.game m) (Nat.succ_pos m) v).mass j)
        atTop (𝓝 ((limitingLaw r v).mass j)) := by
  have hb (b : Band) : ∀ᵐ v ∂bandLaw b, ∀ j : Fin 3,
      Tendsto
        (fun m => (conditionalTypeCountLaw (E.game m) (Nat.succ_pos m) v).mass j)
        atTop (𝓝 ((limitingLaw r v).mass j)) := by
    filter_upwards [bandLaw_support b] with v hv
    exact E.conditional b v hv
  unfold sourceValueLaw
  rw [ae_add_measure_iff, ae_add_measure_iff, ae_add_measure_iff]
  exact ⟨⟨⟨Measure.ae_smul_measure (hb .low) _,
    Measure.ae_smul_measure (hb .first) _⟩,
    Measure.ae_smul_measure (hb .second) _⟩,
    Measure.ae_smul_measure (hb .third) _⟩

theorem family_aggregate_limits (r : Partition) (E : NativeFamily r) :
    Tendsto (fun m => finiteCoverage (E.game m)) atTop (𝓝 (limitingCoverage r)) ∧
      Tendsto (fun m => finiteLoad (E.game m)) atTop (𝓝 (99 / 100 : ℝ)) ∧
      Tendsto (fun m => finiteLoad (E.game m) - finiteCoverage (E.game m))
        atTop (𝓝 (limitingDuplicates r)) ∧
      Tendsto (fun m => finiteMultiplicity (E.game m))
        atTop (𝓝 (limitingMultiplicity r)) := by
  have h := actual_aggregate_limits E.game Nat.succ_pos sourceValueLaw
    E.common_values (limitingLaw r) (family_ae_conditional r E)
  rw [(source_profile_integrals r).1, (source_profile_integrals r).2.1,
    (source_profile_integrals r).2.2] at h
  exact ⟨h.1, h.2.1, h.2.2,
    (actual_multiplicity_limit E.game h.1 h.2.1 (limitingCoverage_pos r)).1⟩

theorem family_fixed_value_outcomes (r : Partition) (E : NativeFamily r)
    (b : Band) (v : ℝ) (hv : v ∈ Icc (bandLower b) (bandUpper b)) :
    Tendsto (fun m => (conditionalTypeCountLaw (E.game m) (Nat.succ_pos m) v).success)
        atTop (𝓝 ((limitingLaw r v).success)) ∧
      Tendsto (fun m => (conditionalTypeCountLaw (E.game m) (Nat.succ_pos m) v).load)
        atTop (𝓝 ((limitingLaw r v).load)) ∧
      Tendsto (fun m => (conditionalTypeCountLaw (E.game m) (Nat.succ_pos m) v).duplicates)
        atTop (𝓝 ((limitingLaw r v).duplicates)) ∧
      (0 < (limitingLaw r v).success →
        Tendsto
          (fun m => conditionalMultiplicity
            (conditionalTypeCountLaw (E.game m) (Nat.succ_pos m) v).success
            (conditionalTypeCountLaw (E.game m) (Nat.succ_pos m) v).load)
          atTop (𝓝 (conditionalMultiplicity
            (limitingLaw r v).success (limitingLaw r v).load))) :=
  actual_fixed_value_outcomes E.game Nat.succ_pos v (limitingLaw r v)
    (E.conditional b v hv)

theorem family_common_strict_tail
    (E₁ : NativeFamily .row335) (E₂ : NativeFamily .row665) :
    ∃ N, ∀ m ≥ N,
      0 < finiteCoverage (E₁.game m) ∧ 0 < finiteCoverage (E₂.game m) ∧
      finiteCoverage (E₂.game m) < finiteCoverage (E₁.game m) ∧
      finiteLoad (E₁.game m) - finiteCoverage (E₁.game m) <
        finiteLoad (E₂.game m) - finiteCoverage (E₂.game m) ∧
      finiteMultiplicity (E₁.game m) < finiteMultiplicity (E₂.game m) := by
  have h₁ := family_aggregate_limits .row335 E₁
  have h₂ := family_aggregate_limits .row665 E₂
  exact common_actual_strict_outcomes E₁.game E₂.game h₁.1 h₂.1
    h₁.2.2.1 h₂.2.2.1 h₁.2.1 h₂.2.1 (limitingCoverage_pos .row665)
    strict_source_outcomes.2.1 strict_source_outcomes.1 (by norm_num)

theorem multiple_source_assembly_of_native_families
    (E₁ : NativeFamily .row335) (E₂ : NativeFamily .row665) :
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
        limitingMultiplicity .row665 < 12060940355 / 10^10) := by
  let E : ∀ r : Partition, NativeFamily r
    | .row335 => E₁
    | .row665 => E₂
  refine ⟨fun r => (E r).game, ?_, ?_, ?_, ?_,
    duplicate_enclosures, coverage_enclosures, multiplicity_enclosures⟩
  · intro r m
    exact ⟨(E r).common_values m, (E r).coefficient m,
      (E r).zero_base m, (E r).private_seed m⟩
  · intro r b v hv
    exact (E r).conditional b v hv
  · intro r
    exact family_aggregate_limits r (E r)
  · obtain ⟨N, hN⟩ := family_common_strict_tail E₁ E₂
    have hall : ∀ᶠ m in atTop, ∀ r : Partition,
        UsersOptimal ((E r).game m) ∧
          (∃ B : PosteriorSystem ((E r).game m), PosteriorProposerOptimal ((E r).game m) B) ∧
          NullSingletonClass (physicalBidLaw ((E r).game m)) ∧
          (∀ᵐ x ∂(((E r).game m).F ⊗ₘ ((E r).game m).σ),
            x.2.routeCount = if x.1 ∈ upperSet r then 1 else 2) := by
      filter_upwards [E₁.native, E₂.native] with m h₁ h₂ r
      cases r
      · exact h₁
      · exact h₂
    apply eventually_atTop.mp
    filter_upwards [hall, eventually_ge_atTop N] with m hm hNm
    refine ⟨?_, hN m hNm⟩
    intro r
    obtain ⟨hu, hp, hb, hr⟩ := hm r
    letI : NullSingletonClass (physicalBidLaw ((E r).game m)) := hb
    exact ⟨common_conull_users_all_raw_actions _ hu, hp, hb,
      visibleAtomless_of_physicalBidLaw _, hr⟩

end FCAppendix.Affine.Multiple07
