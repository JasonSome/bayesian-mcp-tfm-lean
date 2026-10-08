import FCAppendix.Ample.SlackEndpoint

noncomputable section
namespace FCAppendix.Bayes.FreeBaseAmpleSequence
open MeasureTheory ProbabilityTheory Game Set Finset Filter Topology Real
open scoped BigOperators
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
  {M C : ℕ → ℕ} {Γ : ∀ t, FiniteGame (M t) n (C t) Seed}
  {B : ∀ t, PosteriorSystem (Γ t)} {F : Measure ℝ} {g ρ : ℝ}
  (h : FreeBaseAmpleSequence M C Γ B F g ρ)
include h

lemma contactLaw_limit_of_multi_zero
    (hmulti : Tendsto (fun t => positiveRouteMass (Γ t) (fun k => 2 ≤ k)) atTop (𝓝 0)) :
    ∀ j ∈ Finset.Icc 1 n,
      Tendsto (fun t => visibleClassMass (Γ t) 0 j) atTop
        (𝓝 (Ample.singletonOnly (F.real (Ioi g)) j)) := by
  have hsing : Tendsto (fun t => positiveRouteMass (Γ t) (fun k => k = 1)) atTop
      (𝓝 (F.real (Ioi g))) := by
    have hh := h.positiveParticipation_tendsto.sub hmulti
    simp only [sub_zero] at hh
    convert hh using 1
    funext t
    have hs := positiveRouteMass_split (Γ t)
    linarith
  intro j hj
  by_cases hj1 : j = 1
  · subst j
    simpa [Ample.singletonOnly,
      positiveRouteMass_class_eq (Γ _) (by omega : 1 ≤ 1)] using hsing
  · have hj2 : 2 ≤ j := by have := (Finset.mem_Icc.mp hj).1; omega
    have hzero : Tendsto (fun t => visibleClassMass (Γ t) 0 j) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmulti
      · intro t
        exact (visibleClassMass_valid (Γ t) 0).nonneg j hj
      · intro t
        change visibleClassMass (Γ t) 0 j ≤ positiveRouteMass (Γ t) (fun k => 2 ≤ k)
        rw [← positiveRouteMass_class_eq (Γ t) (by omega : 1 ≤ j)]
        exact positiveRouteMass_mono (Γ t) (fun k _ _ hk => by omega)
    simpa only [Ample.singletonOnly, if_neg hj1] using hzero

theorem not_multiroute_mass_tendsto_zero
    (hmulti : Tendsto (fun t => positiveRouteMass (Γ t) (fun k => 2 ≤ k)) atTop (𝓝 0)) :
    False := by
  let p : ℝ := F.real (Ioi g)
  let piMass : ℕ → ℝ := fun t => positiveRouteMass (Γ t) (fun k => k = 1)
  let lawWeights : ℕ → ℝ := Ample.singletonOnly p
  let lama : ℕ → ℕ → ℝ := fun t => Ample.singletonOnly (piMass t)
  have hn := h.proposers_pos
  have hlam : Ample.ValidLaw n lawWeights := Ample.singletonOnly_valid hn h.active_pos.le h.active_le_one
  have hlama : ∀ t, Ample.ValidLaw n (lama t) := fun t =>
    Ample.singletonOnly_valid hn (positiveRouteMass_nonneg (Γ t) _)
      (positiveRouteMass_le_one (Γ t) _)
  have hactual := h.contactLaw_limit_of_multi_zero hmulti
  have hpiMass : Tendsto piMass atTop (𝓝 p) := by
    have hh := hactual 1 (Finset.mem_Icc.mpr ⟨le_rfl, hn⟩)
    simpa [piMass, p, Ample.singletonOnly,
      positiveRouteMass_class_eq (Γ _) (by omega : 1 ≤ 1)] using hh
  have hconv : ∀ j ∈ Finset.Icc 1 n, Tendsto (fun t => lama t j) atTop (𝓝 (lawWeights j)) := by
    intro j _
    by_cases hj : j = 1
    · simpa [lama, lawWeights, Ample.singletonOnly, hj] using hpiMass
    · simp [lama, lawWeights, Ample.singletonOnly, hj]
  have hslack : Ample.contactMarginal n lawWeights < ρ := by
    change Ample.contactMarginal n (Ample.singletonOnly p) < ρ
    rw [Ample.singletonOnly_marginal hn]
    exact (div_lt_iff₀ (Nat.cast_pos.mpr hn)).mpr (by simpa only [mul_comm] using h.ample)
  have htop : ∃ j ∈ Finset.Icc 1 n, 0 < lawWeights j ∧ (1 : ℝ) * ρ < (min 1 j : ℕ) := by
    refine ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hn⟩, ?_, ?_⟩
    · simpa [lawWeights, Ample.singletonOnly] using h.active_pos
    · simpa using h.ratio_lt_one
  obtain ⟨hpos, hrate⟩ := Ample.ample_event_rate (by omega : 1 ≤ 1) hn hlama hlam hconv
    h.population_grows h.capacity_ratio hslack (by simpa only [Nat.cast_one] using htop)
  obtain ⟨θ, d, hθ, hId, hdθ⟩ := Ample.singleton_entropy_separation h.two_proposers
    h.active_pos h.active_le_one h.ample h.ratio_lt_one
  have hu := Ample.eventually_event_bound_of_chernoff h.two_proposers
    (fun t => visibleClassMass_valid (Γ t) 0) hlam hactual h.population_grows
    h.capacity_ratio hθ hdθ
  have hbound : ∀ᶠ t in atTop,
      d ≤ -log (Ample.congestProb n (M t - 1) (C t) 1 (lama t)) / M t := by
    filter_upwards [h.eventually_finite_guards, hpos, hu] with t ht hp hupper
    let i : Fin (M t) := ⟨0, by omega⟩
    have hAM := ppi_AM3_positive (Γ t) (by omega) hn ht.2.1 (h.ppi t) (h.free t)
      (h.visible_atomless t) (h.feasible_continuations t) (h.users t) (h.abstention t) i
    have hbin : Ample.congestProb n (M t - 1) (C t) 1 (lama t) =
        1 - binomBelow (M t - 1) (piMass t / n) (C t) := by
      rw [Ample.congest_one_eq_binomial hn (by omega) (hlama t)]
      change 1 - binomBelow (M t - 1)
        (Ample.contactMarginal n (Ample.singletonOnly (piMass t))) (C t) = _
      rw [Ample.singletonOnly_marginal hn]
    have hPall : Ample.congestProb n (M t - 1) (C t) 1 (lama t) ≤
        Ample.congestProb n (M t - 1) (C t) n (visibleClassMass (Γ t) 0) := by
      rw [hbin, ← allPositiveCongestion_eq_source (Γ t) (by omega) i]
      exact hAM
    have hmono := Ample.congestProb_anti (n := n) (N := M t - 1) (c := C t)
      (visibleClassMass_valid (Γ t) 0) h.two_proposers
    have hupper' := hPall.trans (hmono.trans hupper)
    have hlog := log_le_log hp hupper'
    rw [log_exp] at hlog
    have hMR : (0 : ℝ) < M t := by exact_mod_cast (show 0 < M t by omega)
    exact (le_div_iff₀ hMR).mpr (by linarith)
  have hdI := ge_of_tendsto hrate hbound
  exact hId.not_ge hdI

theorem multiroute_floor :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ᶠ t in atTop,
      a₂ ≤ positiveRouteMass (Γ t) (fun k => 2 ≤ k) := by
  apply Ample.positive_floor_of_no_vanishing_subsequence
    (fun t => positiveRouteMass (Γ t) (fun k => 2 ≤ k))
    (fun t => positiveRouteMass_nonneg (Γ t) _)
  intro φ hφ hzero
  exact (h.along φ hφ).not_multiroute_mass_tendsto_zero hzero

end FCAppendix.Bayes.FreeBaseAmpleSequence
