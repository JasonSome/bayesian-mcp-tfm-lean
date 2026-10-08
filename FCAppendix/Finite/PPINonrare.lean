import FCAppendix.Finite.NearPPITheorem

noncomputable section

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter Set Topology

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem rank_probability_monotone_bid (Γ : FiniteGame m n c Seed)
    (i : Fin m) (j : Fin n) {b t : ℝ} (hbt : b ≤ t) :
    binomBelow (m - 1) (alphaGt Γ j b) c ≤
      binomBelow (m - 1) (alphaGt Γ j t) c := by
  classical
  unfold alphaGt
  rw [← prob_rivals_lt Γ i _ (measurableSet_aboveAt j b) c,
    ← prob_rivals_lt Γ i _ (measurableSet_aboveAt j t) c]
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  simp only [mem_setOf_eq] at hω ⊢
  apply lt_of_le_of_lt _ hω
  rw [rivals_eq_card, rivals_eq_card]
  apply Finset.card_le_card
  intro l hl
  simp only [Finset.mem_filter] at hl ⊢
  exact ⟨hl.1, hl.2.1, hbt.trans_lt hl.2.2⟩

theorem rank_price_gap_mul_le_envelope {N : ℕ} (Γ : FiniteGame (N + 1) n c Seed)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (i : Fin (N + 1)) (j : Fin n) (b t p : ℝ) (ht : 0 < t)
    (hbt : b ≤ t) :
    (p - t) * binomBelow N (alphaGt Γ j b) c ≤ (problem Γ i).envelope (Γ.g + p) := by
  have hmono := rank_probability_monotone_bid Γ i j hbt
  simp only [Nat.add_sub_cancel] at hmono
  have hq : 0 ≤ binomBelow N (alphaGt Γ j b) c := by
    have he := prob_rivals_lt Γ i _ (measurableSet_aboveAt j b) c
    simp only [Nat.add_sub_cancel] at he
    unfold alphaGt
    rw [← he]
    exact measureReal_nonneg
  apply nonrare_price_gap_mul_le_envelope Γ (Nat.zero_lt_of_lt j.isLt) i t p _ ht.le hq
  rw [ppi_meanAcceptProb_eq_rank Γ hA hatom hj i j t ht]
  exact hmono

theorem rank_nonrare_bids_eventually_pos
    (N C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (N k + 1) n (C k) Seed)
    (i : ∀ k, Fin (N k + 1)) (j : Fin n)
    (hA : ∀ k, (Γ k).A = Schedule.ppi n)
    (hatom : ∀ k, PositiveVisibleAtomless (Γ k))
    (hj : ∀ k j, ProposerRationalAtFeasibleLists (Γ k) j)
    (p : ℝ) (hp : 0 < p)
    (hcut : Tendsto (fun k => (problem (Γ k) (i k)).envelope ((Γ k).g + p)) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ b : ℝ,
      ε ≤ binomBelow (N k) (alphaGt (Γ k) j b) (C k) → p / 2 < b := by
  filter_upwards [hcut.eventually (eventually_lt_nhds (mul_pos (half_pos hp) hε))] with k hk
  intro b hb
  by_contra hnot
  have hh := rank_price_gap_mul_le_envelope (Γ k) (hA k) (hatom k) (hj k) (i k) j
    b (p / 2) p (half_pos hp) (le_of_not_gt hnot)
  have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ p - p / 2 by linarith)
  nlinarith

theorem uniform_nonrare_ppi_duplicates_pos_all_bids
    (hn : 2 ≤ n) (N C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (N k + 1) n (C k) Seed)
    (i : ∀ k, Fin (N k + 1))
    (hA : ∀ k, (Γ k).A = Schedule.ppi n)
    (hatom : ∀ k, PositiveVisibleAtomless (Γ k))
    (hj : ∀ k j, ProposerRationalAtFeasibleLists (Γ k) j)
    (hN : Tendsto N atTop atTop) (hC : ∀ k, C k ≤ N k + 1)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (hc : Tendsto (fun k => (C k : ℝ) / N k) atTop (𝓝 ρ))
    (p : ℝ) (hp : 0 < p)
    (hcut : Tendsto (fun k => (problem (Γ k) (i k)).envelope ((Γ k).g + p)) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ k in atTop, ∀ act : JointAction n,
      2 ≤ act.routeCount →
      ε ≤ binomBelow (N k) (alphaGt (Γ k) (⟨0, by omega⟩ : Fin n) act.bid) (C k) →
      d ≤ ((problem (Γ k) (i k)).outcome act).duplicates := by
  obtain ⟨d, hd, hdup⟩ := uniform_nonrare_ppi_duplicates_pos hn N C Γ i hA hatom hj hN hC
    hρ0 hρ1 hc ε hε
  refine ⟨d, hd, ?_⟩
  filter_upwards [hdup, rank_nonrare_bids_eventually_pos N C Γ i (⟨0, by omega⟩ : Fin n)
    hA hatom hj p hp hcut ε hε] with k hk hpos
  intro act hroute hq
  exact hk act ((half_pos hp).trans (hpos act.bid hq)) hroute hq

namespace NearPPIAssumptions

variable {N C : ℕ → ℕ} {Γ : ∀ k, FiniteGame (N k + 1) n (C k) Seed}
  {F : Measure ℝ} [IsProbabilityMeasure F] [NullSingletonClass F]
  {g ρ vstar : ℝ} {a : ℕ → ℝ}

omit [IsProbabilityMeasure F] [NullSingletonClass F] in
private theorem opponent_population_grows
    (h : NearPPIAssumptions (fun k => N k + 1) C Γ F g a ρ vstar) :
    Tendsto N atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [h.population_grows.eventually_ge_atTop (b + 1)] with k hk
  omega

omit [IsProbabilityMeasure F] [NullSingletonClass F] in
private theorem opponent_capacity_ratio
    (h : NearPPIAssumptions (fun k => N k + 1) C Γ F g a ρ vstar) :
    Tendsto (fun k => (C k : ℝ) / N k) atTop (𝓝 ρ) := by
  have hinv : Tendsto (fun k => (N k : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp h.opponent_population_grows)
  have hfac : Tendsto (fun k => 1 + (N k : ℝ)⁻¹) atTop (𝓝 1) := by
    simpa only [add_zero] using hinv.const_add 1
  have ht := h.capacity_ratio.mul hfac
  simp only [mul_one] at ht
  apply ht.congr'
  filter_upwards [h.opponent_population_grows.eventually_ge_atTop 1] with k hk
  have hN : (N k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hN1 : (N k : ℝ) + 1 ≠ 0 := by positivity
  simp only [Nat.cast_add, Nat.cast_one]
  field_simp

omit [NullSingletonClass F] in
private theorem ratio_lt_half
    (h : NearPPIAssumptions (fun k => N k + 1) C Γ F g a ρ vstar) : ρ < 1 / 2 := by
  have hmass : F.real (Ioi g) ≤ 1 := measureReal_le_one
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast h.proposers_two
  have hp := h.ratio_pos
  have hs := h.scarcity
  nlinarith

private theorem cutoff_utility_tendsto_zero
    (h : NearPPIAssumptions (fun k => N k + 1) C Γ F g a ρ vstar)
    (i : ∀ k, Fin (N k + 1)) :
    Tendsto (fun k => (problem (Γ k) (i k)).envelope ((Γ k).g + (vstar - g)))
      atTop (𝓝 0) := by
  simp_rw [h.common_fee, add_sub_cancel]
  simpa only [sub_self, max_self] using h.utility_limit i vstar

theorem ppi_rank_nonrare_bids_pos
    (h : NearPPIAssumptions (fun k => N k + 1) C Γ F g a ρ vstar)
    (i : ∀ k, Fin (N k + 1)) (hA : ∀ k, (Γ k).A = Schedule.ppi n)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ b : ℝ,
      ε ≤ binomBelow (N k) (alphaGt (Γ k) (⟨0, by have hn := h.proposers_two; omega⟩ : Fin n) b)
        (C k) → (vstar - g) / 2 < b :=
  rank_nonrare_bids_eventually_pos N C Γ i _ hA h.visible_atomless h.feasible_continuations
    (vstar - g) h.price_pos (h.cutoff_utility_tendsto_zero i) ε hε

theorem ppi_nonrare_bids_uniform_on_compact
    (h : NearPPIAssumptions (fun k => N k + 1) C Γ F g a ρ vstar)
    (i : ∀ k, Fin (N k + 1)) (hA : ∀ k, (Γ k).A = Schedule.ppi n)
    {V : Set ℝ} (hV : IsCompact V) (ε : ℝ) (hε : 0 < ε) :
    ∀ η > 0, ∀ᶠ k in atTop, ∀ v ∈ V, ∀ act : JointAction n,
      (problem (Γ k) (i k)).BestResponse v act → 1 ≤ act.routeCount →
      ε ≤ binomBelow (N k) (alphaGt (Γ k) (⟨0, by have hn := h.proposers_two; omega⟩ : Fin n)
        act.bid) (C k) → |act.bid - (vstar - g)| < η := by
  have hcut := (h.cutoff_utility_tendsto_zero i).div_const ε
  simp only [zero_div] at hcut
  intro η hη
  have hu := (Metric.tendstoUniformlyOn_iff.mp (h.utility_uniformOn_compact i hV))
    (η / 2) (half_pos hη)
  filter_upwards [hu, hcut.eventually (eventually_lt_nhds (half_pos hη)),
    h.ppi_rank_nonrare_bids_pos i hA ε hε] with k hU hcutR hpos
  intro v hv act hbr hroute hq
  have hbpos : 0 < act.bid := (half_pos h.price_pos).trans (hpos act.bid hq)
  have hlower : max (v - (Γ k).g - (vstar - g)) 0 - η / 2 ≤
      (problem (Γ k) (i k)).envelope v := by
    have hh := hU v hv
    rw [Real.dist_eq] at hh
    rw [h.common_fee]
    have he : v - g - (vstar - g) = v - vstar := by ring
    rw [he]
    linarith [le_abs_self (max (v - vstar) 0 - (problem (Γ k) (i k)).envelope v)]
  have hh := nonrare_bestResponse_bid_error (Γ k) (by have hn := h.proposers_two; omega)
    (i k) v (vstar - g) (η / 2) ε (half_pos hη).le hε act hbr hroute
    (by rwa [ppi_meanAcceptProb_eq_rank (Γ k) (hA k) (h.visible_atomless k)
      (h.feasible_continuations k) (i k) (⟨0, by have hn := h.proposers_two; omega⟩ : Fin n)
      act.bid hbpos]) hlower
  linarith

theorem ppi_nonrare_duplicates
    (h : NearPPIAssumptions (fun k => N k + 1) C Γ F g a ρ vstar)
    (i : ∀ k, Fin (N k + 1)) (hA : ∀ k, (Γ k).A = Schedule.ppi n)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ k in atTop, ∀ act : JointAction n,
      2 ≤ act.routeCount →
      ε ≤ binomBelow (N k) (alphaGt (Γ k) (⟨0, by have hn := h.proposers_two; omega⟩ : Fin n)
        act.bid) (C k) → d ≤ ((problem (Γ k) (i k)).outcome act).duplicates :=
  uniform_nonrare_ppi_duplicates_pos_all_bids h.proposers_two N C Γ i hA
    h.visible_atomless h.feasible_continuations h.opponent_population_grows
    (fun k => (h.capacity_lt_population k).le) h.ratio_pos h.ratio_lt_half
    h.opponent_capacity_ratio (vstar - g) h.price_pos (h.cutoff_utility_tendsto_zero i) ε hε

theorem ppi_nonrare_one_route_uniform_on_compact
    (h : NearPPIAssumptions (fun k => N k + 1) C Γ F g a ρ vstar)
    (i : ∀ k, Fin (N k + 1)) (hA : ∀ k, (Γ k).A = Schedule.ppi n)
    {V : Set ℝ} (hV : IsCompact V) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ v ∈ V, ∀ act : JointAction n,
      (problem (Γ k) (i k)).BestResponse v act → 1 ≤ act.routeCount →
      ε ≤ binomBelow (N k) (alphaGt (Γ k) (⟨0, by have hn := h.proposers_two; omega⟩ : Fin n)
        act.bid) (C k) → act.routeCount = 1 := by
  obtain ⟨d, hd, hdup⟩ := h.ppi_nonrare_duplicates i hA ε hε
  let e := (vstar - g) * d / 8
  have he : 0 < e := by dsimp [e]; exact div_pos (mul_pos h.price_pos hd) (by norm_num)
  have hu := (Metric.tendstoUniformlyOn_iff.mp (h.utility_uniformOn_compact i hV)) e he
  filter_upwards [hdup, hu, h.ppi_nonrare_bids_uniform_on_compact i hA hV ε hε e he,
    h.ppi_rank_nonrare_bids_pos i hA ε hε] with k hD hU hb hpos
  intro v hv act hbr hroute hq
  have hbid := hb v hv act hbr hroute hq
  have hbpos := hpos act.bid hq
  have hlower : max (v - (Γ k).g - (vstar - g)) 0 - e ≤
      (problem (Γ k) (i k)).envelope v := by
    have hh := hU v hv
    rw [Real.dist_eq] at hh
    rw [h.common_fee]
    have heq : v - g - (vstar - g) = v - vstar := by ring
    rw [heq]
    linarith [le_abs_self (max (v - vstar) 0 - (problem (Γ k) (i k)).envelope v)]
  have hpen := (problem (Γ k) (i k)).bestResponse_duplicate_penalty_le v (vstar - g) e 1
    act hbr (fun r _ _ => by change (1 : ℝ) * r ≤ (Γ k).A.charge r; simp [hA k, Schedule.ppi]) hlower
  simp only [one_mul, abs_sub_comm (vstar - g) act.bid] at hpen
  have hn2 : ¬ 2 ≤ act.routeCount := by
    intro hk
    have hbound := hD act hk hq
    have hm := mul_le_mul hbpos.le hbound hd.le act.bid_nonneg
    dsimp only [e] at hbid hpen
    have hpd : 0 < (vstar - g) * d := mul_pos h.price_pos hd
    nlinarith
  omega

theorem ppi_above_cutoff_one_route
    (h : NearPPIAssumptions (fun k => N k + 1) C Γ F g a ρ vstar)
    (i : ∀ k, Fin (N k + 1)) (hA : ∀ k, (Γ k).A = Schedule.ppi n)
    (v : ℝ) (hv : vstar < v) :
    ∀ᶠ k in atTop, ∀ act : JointAction n,
      (problem (Γ k) (i k)).BestResponse v act → act.routeCount = 1 := by
  apply eventually_all_bestResponses_one_route_of_envelope h.proposers_two N C Γ i v g
    (vstar - g) h.price_pos (by linarith) h.common_fee hA h.visible_atomless
    h.feasible_continuations h.opponent_population_grows
    (fun k => (h.capacity_lt_population k).le) h.ratio_pos h.ratio_lt_half h.opponent_capacity_ratio
  intro w
  have he : w - g - (vstar - g) = w - vstar := by ring
  simpa only [he] using h.utility_limit i w

end NearPPIAssumptions

theorem ppi_nonrare
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed)
    (F : Measure ℝ) [IsProbabilityMeasure F] [NullSingletonClass F]
    (g ρ vstar : ℝ) (h : CongestedAssumptions M C Γ F g ρ vstar)
    (hA : ∀ k, (Γ k).A = Schedule.ppi n) (i : ∀ k, Fin (M k))
    {V : Set ℝ} (hV : IsCompact V) (ε : ℝ) (hε : 0 < ε) :
    (∃ d : ℝ, 0 < d ∧ ∀ᶠ k in atTop, ∀ act : JointAction n,
      2 ≤ act.routeCount →
      ε ≤ binomBelow (M k - 1) (alphaGt (Γ k) (⟨0, by have hn := h.proposers_two; omega⟩ : Fin n)
        act.bid) (C k) → d ≤ ((problem (Γ k) (i k)).outcome act).duplicates) ∧
    (∀ η > 0, ∀ᶠ k in atTop, ∀ v ∈ V, ∀ act : JointAction n,
      (problem (Γ k) (i k)).BestResponse v act → 1 ≤ act.routeCount →
      ε ≤ binomBelow (M k - 1) (alphaGt (Γ k) (⟨0, by have hn := h.proposers_two; omega⟩ : Fin n)
        act.bid) (C k) → |act.bid - (vstar - g)| < η) ∧
    (∀ᶠ k in atTop, ∀ v ∈ V, ∀ act : JointAction n,
      (problem (Γ k) (i k)).BestResponse v act → 1 ≤ act.routeCount →
      ε ≤ binomBelow (M k - 1) (alphaGt (Γ k) (⟨0, by have hn := h.proposers_two; omega⟩ : Fin n)
        act.bid) (C k) → act.routeCount = 1) ∧
    (∀ v > vstar, ∀ᶠ k in atTop, ∀ act : JointAction n,
      (problem (Γ k) (i k)).BestResponse v act → act.routeCount = 1) := by
  generalize hN : (fun k => M k - 1) = N
  have he : M = (fun k => N k + 1) := by
    funext k
    have hk := congrFun hN k
    have hpos := h.capacity_lt_population k
    omega
  subst M
  let hn := h.nearPPI_of_ppi hA
  simpa only [Nat.add_sub_cancel] using
    And.intro (hn.ppi_nonrare_duplicates i hA ε hε)
      (And.intro (hn.ppi_nonrare_bids_uniform_on_compact i hA hV ε hε)
        (And.intro (hn.ppi_nonrare_one_route_uniform_on_compact i hA hV ε hε)
          (fun v hv => hn.ppi_above_cutoff_one_route i hA v hv)))

end FCAppendix.Bayes
