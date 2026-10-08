import FCAppendix.PayOnce.InactiveSaturatedGroup
import FCAppendix.PayOnce.EffectiveVanishingBid

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Filter Topology Set Game CommonList
open PayOnce PayOnce.KernelLawConvergence PayOnce.CompactifiedBidLaws
open scoped BigOperators ProbabilityTheory

theorem effective_bid_tail_le_bounded_group {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m n c Seed)
    {ε R : ℝ} :
    (CompactifiedBidLaws.bidLaw Γ : Measure ENNReal) (Ioi (ENNReal.ofReal ε)) ≤
      (Γ.F ⊗ₘ Γ.σ) {x : ℝ × JointAction n | ε ≤ (effectiveBid x.2) ∧ x.1-Γ.g ≤ R} + Γ.F (Ioi R) := by
  have hb : Measurable (fun x : ℝ × JointAction n => (effectiveBid x.2)) := (measurable_effectiveBid n).comp measurable_snd
  have he : Measurable (fun x : ℝ × JointAction n => ENNReal.ofReal (effectiveBid x.2)) := ENNReal.measurable_ofReal.comp hb
  rw [compactifiedBidLaw_eq_map_effectiveBidLaw Γ, realEffectiveBidLaw_eq_action_map,
    Measure.map_map ENNReal.measurable_ofReal hb]
  change (Measure.map (fun x : ℝ × JointAction n => ENNReal.ofReal (effectiveBid x.2)) (Γ.F ⊗ₘ Γ.σ)) _ ≤ _
  rw [Measure.map_apply he measurableSet_Ioi]
  have hsub : (fun x : ℝ × JointAction n => ENNReal.ofReal (effectiveBid x.2)) ⁻¹' Ioi (ENNReal.ofReal ε) ⊆
      {x : ℝ × JointAction n | ε ≤ (effectiveBid x.2) ∧ x.1-Γ.g ≤ R} ∪ {x | R < x.1} := by
    intro x hx
    have hb : ε < (effectiveBid x.2) := by
      by_contra h
      exact (not_lt_of_ge (ENNReal.ofReal_le_ofReal (le_of_not_gt h))) hx
    by_cases hv : x.1-Γ.g ≤ R
    · exact Or.inl ⟨hb.le,hv⟩
    · exact Or.inr (show R < x.1 by linarith [Γ.g_nonneg])
  have htail : (Γ.F ⊗ₘ Γ.σ) {x : ℝ × JointAction n | R < x.1} = Γ.F (Ioi R) := by
    have hp : MeasurePreserving (Prod.fst : ℝ × JointAction n → ℝ) (Γ.F ⊗ₘ Γ.σ) Γ.F :=
      ⟨measurable_fst, Measure.fst_compProd Γ.F Γ.σ⟩
    exact hp.measure_preimage measurableSet_Ioi.nullMeasurableSet
  exact ((measure_mono hsub).trans (measure_union_le _ _)).trans_eq (by rw [htail])

theorem inactive_limit_saturated_tail_zero
    {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (hk : 1 ≤ k) (hc : ∀ t, 0 < C t) (hcm : ∀ t, C t < M t)
    (hM : Tendsto M atTop atTop)
    (hA : ∀ t, (Γ t).A = Schedule.once (k+1)) (hG : ∀ t, (Γ t).G = Schedule.once (k+1))
    (hu : ∀ t, UsersOptimal (Γ t)) (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, PosteriorProposerOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t))
    (hvalue : ∀ t, PositiveValueAtomless (Γ t)) (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    (hinactive : ∀ t, InactiveAbstain (Γ t))
    (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ∀ t, (Γ t).F = F)
    {g : ℝ} (hg : ∀ t, (Γ t).g = g)
    {G : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => CompactifiedBidLaws.bidLaw (Γ t)) atTop (𝓝 G))
    {ρ : ℝ} (hρ : Tendsto (fun t => (C t : ℝ)/(M t)) atTop (𝓝 ρ))
    (hρπ : ρ ≤ F.real (Ioi g))
    {L : ℝ} (hL : 0 < L) (hD : KernelDemand.demand (k+1) (G : Measure ENNReal) L ≤ ρ) :
    (G : Measure ENNReal) (Ioi (ENNReal.ofReal (((k+1:ℕ):ℝ)*L))) = 0 := by
  have hload := dummy_profile_marginal_mean_L1 Γ hk hc hcm hM hA hG hu B hB hsym hvalue F hF hg hρ hρπ
  let ε := ((k+1:ℕ):ℝ)*L
  have hε : 0 < ε := mul_pos (Nat.cast_pos.mpr (by omega)) hL
  have hbound (R : ℝ) (hR : 0 ≤ R) :
      (G : Measure ENNReal) (Ioi (ENNReal.ofReal ε)) ≤ F (Ioi R) := by
    have hzero := tendsto_inactive_saturated_group_mass_zero Γ hk hc hcm hM hA hG hu B hB hsym hvalue hatom hinactive
      hweak hload hL hε hR le_rfl hD
    let E := fun t => {x : ℝ × JointAction (k+1) | ε ≤ (effectiveBid x.2) ∧ x.1-(Γ t).g ≤ R}
    have hz : Tendsto (fun t => ((Γ t).F ⊗ₘ (Γ t).σ) (E t)) atTop (𝓝 (0:ENNReal)) := by
      have hh := ENNReal.continuous_ofReal.tendsto (0:ℝ) |>.comp hzero
      simpa only [ENNReal.ofReal_zero, measureReal_def, Function.comp_def,
        ENNReal.ofReal_toReal (measure_ne_top _ _), E] using hh
    have hle (t : ℕ) := effective_bid_tail_le_bounded_group (Γ t) (R := R) (ε := ε)
    simp only [hF] at hle
    have hl := Filter.liminf_le_liminf (f := atTop) (Eventually.of_forall hle)
    have hp := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak
      (isOpen_Ioi (a := ENNReal.ofReal ε))
    have hlim : liminf (fun t => ((Γ t).F ⊗ₘ (Γ t).σ) (E t)+F (Ioi R)) atTop = F (Ioi R) := by
      have hh := hz.add_const (F (Ioi R))
      simpa only [zero_add] using hh.liminf_eq
    simp only [hF, E] at hlim
    exact hp.trans (hl.trans_eq hlim)
  have hreal : (G : Measure ENNReal).real (Ioi (ENNReal.ofReal ε)) ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds (TailQuantile.tail_tendsto_zero F)
      ((eventually_ge_atTop (0:ℝ)).mono fun R hR => ENNReal.toReal_mono (measure_ne_top F _) (hbound R hR))
  by_contra hne
  exact (ENNReal.toReal_pos hne (measure_ne_top _ _)).not_ge hreal

end FCAppendix.Bayes
