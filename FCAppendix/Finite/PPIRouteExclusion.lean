import FCAppendix.Finite.PairDuplicates
import FCAppendix.Finite.SingletonDeviation

noncomputable section

namespace FCAppendix.CountLaw

theorem utility_le_max_sub_duplicate_penalty {n : ℕ} (μ : CountLaw n)
    (v b g a : ℝ) (A G : Schedule n) (hb : 0 ≤ b) (hg : 0 ≤ g)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ A.charge r) :
    μ.utility v b g A G ≤ max (v - g - a * b) 0 - a * b * μ.duplicates := by
  have hcharge : a * μ.load ≤ μ.charge A := by
    rw [load, charge, ← FiniteLaw.expect_const_mul]
    apply μ.expect_mono
    intro r
    by_cases hr : r.val = 0
    · simp [hr, A.zero]
    · exact hA r.val (Nat.pos_of_ne_zero hr) (by omega)
  have hB := mul_le_mul_of_nonneg_left hcharge hb
  have hG := mul_le_mul_of_nonneg_left (μ.success_le_charge G) hg
  have hS : (v - g - a * b) * μ.success ≤ max (v - g - a * b) 0 := by
    by_cases hpos : 0 ≤ v - g - a * b
    · rw [max_eq_left hpos]
      nlinarith [μ.success_le_one]
    · rw [max_eq_right (le_of_not_ge hpos)]
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hpos) μ.success_nonneg
  rw [utility_eq, duplicates]
  nlinarith

end FCAppendix.CountLaw

namespace FCAppendix.Interim.Problem

open Filter Topology

variable {n : ℕ}

theorem bestResponse_duplicate_penalty_le (P : Interim.Problem n)
    (v p e a : ℝ) (act : Game.JointAction n) (hbr : P.BestResponse v act)
    (hA : ∀ k : ℕ, 0 < k → k ≤ n → a * (k : ℝ) ≤ P.A.charge k)
    (hlower : max (v - P.g - p) 0 - e ≤ P.envelope v) :
    a * act.bid * (P.outcome act).duplicates ≤ e + |p - a * act.bid| := by
  have hu := CountLaw.utility_le_max_sub_duplicate_penalty (P.outcome act)
    v act.bid P.g a P.A P.G act.bid_nonneg P.g_nonneg hA
  change P.payoff v act ≤ _ at hu
  rw [P.bestResponse_iff_attains v act |>.mp hbr] at hu
  have hmax : max (v - P.g - a * act.bid) 0 ≤
      max (v - P.g - p) 0 + |p - a * act.bid| := by
    apply max_le
    · have hm := le_max_left (v - P.g - p) 0
      have hab := le_abs_self (p - a * act.bid)
      linarith
    · exact add_nonneg (le_max_right _ _) (abs_nonneg _)
  linarith

theorem bestResponse_duplicates_le (P : Interim.Problem n)
    (v p e a : ℝ) (act : Game.JointAction n) (hbr : P.BestResponse v act)
    (hA : ∀ k : ℕ, 0 < k → k ≤ n → a * (k : ℝ) ≤ P.A.charge k)
    (hlower : max (v - P.g - p) 0 - e ≤ P.envelope v) (hpos : 0 < a * act.bid) :
    (P.outcome act).duplicates ≤ (e + |p - a * act.bid|) / (a * act.bid) := by
  apply (le_div_iff₀ hpos).mpr
  simpa only [mul_comm] using P.bestResponse_duplicate_penalty_le v p e a act hbr hA hlower

theorem supported_duplicates_tendsto_zero_varying_values
    (P : ℕ → Interim.Problem n) (v : ℕ → ℝ) (act : ℕ → Game.JointAction n)
    (a δ : ℕ → ℝ) (p : ℝ) (hp : 0 < p)
    (hA : ∀ r k, 0 < k → k ≤ n → a r * (k : ℝ) ≤ (P r).A.charge k)
    (ha : Tendsto a atTop (𝓝 1)) (hb : Tendsto (fun r => (act r).bid) atTop (𝓝 p))
    (hδ : Tendsto δ atTop (𝓝 0)) (hbr : ∀ r, (P r).BestResponse (v r) (act r))
    (hlower : ∀ᶠ r in atTop, max (v r - (P r).g - p) 0 - δ r ≤ (P r).envelope (v r)) :
    Tendsto (fun r => ((P r).outcome (act r)).duplicates) atTop (𝓝 0) := by
  have hab : Tendsto (fun r => a r * (act r).bid) atTop (𝓝 p) := by
    simpa only [one_mul] using ha.mul hb
  have habs : Tendsto (fun r => |p - a r * (act r).bid|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using ((tendsto_const_nhds (x := p)).sub hab).abs
  have herr : Tendsto (fun r => (δ r + |p - a r * (act r).bid|) / (a r * (act r).bid))
      atTop (𝓝 0) := by
    have hh := (hδ.add habs).mul (hab.inv₀ hp.ne')
    simpa only [zero_add, zero_mul, div_eq_mul_inv] using hh
  refine squeeze_zero' (Filter.Eventually.of_forall fun r => CountLaw.duplicates_nonneg _) ?_ herr
  filter_upwards [hlower, hab.eventually (eventually_gt_nhds hp)] with r hr hpos
  exact (P r).bestResponse_duplicates_le (v r) p (δ r) (a r) (act r) (hbr r) (hA r) hr hpos

theorem supported_duplicates_tendsto_zero
    (P : ℕ → Interim.Problem n) (act : ℕ → Game.JointAction n) (a δ : ℕ → ℝ)
    (v g p : ℝ) (hp : 0 < p) (hvp : p < v - g)
    (hg : ∀ r, (P r).g = g)
    (hA : ∀ r k, 0 < k → k ≤ n → a r * (k : ℝ) ≤ (P r).A.charge k)
    (ha : Tendsto a atTop (𝓝 1)) (hb : Tendsto (fun r => (act r).bid) atTop (𝓝 p))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hbr : ∀ r, (P r).BestResponse v (act r))
    (hlower : ∀ᶠ r in atTop, v - g - p - δ r ≤ (P r).envelope v) :
    Tendsto (fun r => ((P r).outcome (act r)).duplicates) atTop (𝓝 0) := by
  have hab : Tendsto (fun r => a r * (act r).bid) atTop (𝓝 p) := by
    simpa only [one_mul] using ha.mul hb
  have hmax : Tendsto (fun r => max (v - g - a r * (act r).bid) 0)
      atTop (𝓝 (v - g - p)) := by
    have hh := ((tendsto_const_nhds (x := v - g)).sub hab).max (tendsto_const_nhds (x := (0 : ℝ)))
    simpa only [max_eq_left (by linarith : 0 ≤ v - g - p)] using hh
  have hnum : Tendsto (fun r => max (v - g - a r * (act r).bid) 0 -
      (v - g - p) + δ r) atTop (𝓝 0) := by
    simpa only [sub_self, zero_add] using (hmax.sub (tendsto_const_nhds (x := v - g - p))).add hδ
  have hboundlim : Tendsto (fun r => (max (v - g - a r * (act r).bid) 0 -
      (v - g - p) + δ r) / (a r * (act r).bid)) atTop (𝓝 0) := by
    have hh := hnum.mul (hab.inv₀ hp.ne')
    simpa only [div_eq_mul_inv, zero_mul] using hh
  refine squeeze_zero' ?_ ?_ hboundlim
  · exact Filter.Eventually.of_forall fun r => CountLaw.duplicates_nonneg _
  · filter_upwards [hlower, hab.eventually (eventually_gt_nhds hp)] with r hr hpos
    have hu := CountLaw.utility_le_max_sub_duplicate_penalty ((P r).outcome (act r))
      v (act r).bid (P r).g (a r) (P r).A (P r).G (act r).bid_nonneg (P r).g_nonneg (hA r)
    change (P r).payoff v (act r) ≤ _ at hu
    rw [hg r, (P r).bestResponse_iff_attains v (act r) |>.mp (hbr r)] at hu
    apply (le_div_iff₀ hpos).mpr
    nlinarith

end FCAppendix.Interim.Problem

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter Topology

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem supported_duplicates_tendsto_zero_of_bid_limit
    (M C : ℕ → ℕ) (Γ : (r : ℕ) → FiniteGame (M r) n (C r) Seed)
    (i : (r : ℕ) → Fin (M r)) (act : ℕ → JointAction n) (a δ : ℕ → ℝ)
    (v g p : ℝ) (hp : 0 < p) (hvp : p < v - g)
    (hg : ∀ r, (Γ r).g = g)
    (hA : ∀ r k, 0 < k → k ≤ n → a r * (k : ℝ) ≤ (Γ r).A.charge k)
    (ha : Tendsto a atTop (𝓝 1)) (hb : Tendsto (fun r => (act r).bid) atTop (𝓝 p))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hbr : ∀ r, (problem (Γ r) (i r)).BestResponse v (act r))
    (hlower : ∀ᶠ r in atTop, v - g - p - δ r ≤ (problem (Γ r) (i r)).envelope v) :
    Tendsto (fun r => ((problem (Γ r) (i r)).outcome (act r)).duplicates) atTop (𝓝 0) :=
  Interim.Problem.supported_duplicates_tendsto_zero (fun r => problem (Γ r) (i r)) act a δ
    v g p hp hvp hg hA ha hb hδ hbr hlower

lemma ppi_meanAcceptProb_eq_rank {N c : ℕ} (Γ : FiniteGame (N + 1) n c Seed)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (i : Fin (N + 1)) (j : Fin n) (b : ℝ) (hb : 0 < b) :
    meanAcceptProb Γ i b = binomBelow N (alphaGt Γ j b) c := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt j.isLt)
  have he (l : Fin n) : acceptProb Γ i b l = binomBelow N (alphaGt Γ j b) c := by
    rw [ppi_acceptProb_eq_binomBelow Γ hA hatom i l (hj l) b hb, alphaGt_eq Γ l j]
  unfold meanAcceptProb
  simp_rw [he]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem eventually_one_route_of_bid_limit
    (hn : 2 ≤ n) (M C : ℕ → ℕ) (Γ : (r : ℕ) → FiniteGame (M r + 1) n (C r) Seed)
    (i : (r : ℕ) → Fin (M r + 1)) (act : ℕ → JointAction n) (δ : ℕ → ℝ)
    (v g p : ℝ) (hp : 0 < p) (hvp : p < v - g)
    (hg : ∀ r, (Γ r).g = g) (hA : ∀ r, (Γ r).A = Schedule.ppi n)
    (hatom : ∀ r, PositiveVisibleAtomless (Γ r))
    (hj : ∀ r j, ProposerRationalAtFeasibleLists (Γ r) j)
    (hM : Tendsto M atTop atTop) (hC : ∀ r, C r ≤ M r + 1)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (hc : Tendsto (fun r => (C r : ℝ) / M r) atTop (𝓝 ρ))
    (hb : Tendsto (fun r => (act r).bid) atTop (𝓝 p)) (hδ : Tendsto δ atTop (𝓝 0))
    (hbr : ∀ r, (problem (Γ r) (i r)).BestResponse v (act r))
    (hlower : ∀ᶠ r in atTop, v - g - p - δ r ≤ (problem (Γ r) (i r)).envelope v) :
    ∀ᶠ r in atTop, (act r).routeCount = 1 := by
  let ε := (v - g - p) / (2 * (n : ℝ) * (v - g))
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hw : 0 < v - g := hp.trans hvp
  have hε : 0 < ε := div_pos (sub_pos.mpr hvp) (by positivity)
  obtain ⟨d, hd, hdup⟩ := uniform_nonrare_ppi_duplicates_pos hn M C Γ i hA hatom hj hM hC hρ0 hρ1 hc ε hε
  have hcharge (r k : ℕ) (_hk : 0 < k) (_hkn : k ≤ n) : (1 : ℝ) * k ≤ (Γ r).A.charge k := by
    simp [hA r, Schedule.ppi]
  have hD := supported_duplicates_tendsto_zero_of_bid_limit (fun r => M r + 1) C Γ i act
    (fun _ => 1) δ v g p hp hvp hg hcharge tendsto_const_nhds hb hδ hbr hlower
  have hsmall := hδ.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < (v - g - p) / 2))
  filter_upwards [hlower, hsmall, hdup, hD.eventually (eventually_lt_nhds hd),
    hb.eventually (eventually_gt_nhds hp)] with r hlowerR hδR hdupR hDR hbR
  have henv : (v - g - p) / 2 < (problem (Γ r) (i r)).envelope v := by linarith
  have henv0 : 0 < (problem (Γ r) (i r)).envelope v := by linarith
  have hu := CountLaw.utility_le_bid_net_success ((problem (Γ r) (i r)).outcome (act r))
    v (act r).bid (Γ r).g (Γ r).A (Γ r).G (act r).bid_nonneg (Γ r).g_nonneg
  change (problem (Γ r) (i r)).payoff v (act r) ≤ _ at hu
  rw [hg r, (problem (Γ r) (i r)).bestResponse_iff_attains v (act r) |>.mp (hbr r)] at hu
  have hU : (problem (Γ r) (i r)).envelope v ≤
      (v - g) * ((problem (Γ r) (i r)).outcome (act r)).success := by
    nlinarith [mul_nonneg (act r).bid_nonneg (((problem (Γ r) (i r)).outcome (act r)).success_nonneg)]
  have hS0 : 0 < ((problem (Γ r) (i r)).outcome (act r)).success := by nlinarith
  have hk0 : 0 < (act r).routeCount := by
    by_contra hnot
    have he : (act r).routeCount = 0 := by omega
    have hh := load_le_routeCount_mul_success (Γ r) (i r) (act r)
    rw [he, Nat.cast_zero, zero_mul] at hh
    have hs := ((problem (Γ r) (i r)).outcome (act r)).success_le_load
    linarith
  have hS := success_le_n_meanAcceptProb (Γ r) (by omega) (i r) (act r)
  rw [ppi_meanAcceptProb_eq_rank (Γ r) (hA r) (hatom r) (hj r) (i r)
    (⟨0, by omega⟩ : Fin n) (act r).bid hbR] at hS
  have hq : ε ≤ binomBelow (M r) (alphaGt (Γ r) (⟨0, by omega⟩ : Fin n) (act r).bid) (C r) := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (n : ℝ) * (v - g))).mpr
    have hh := mul_le_mul_of_nonneg_left hS hw.le
    nlinarith
  have hk2 : ¬ 2 ≤ (act r).routeCount := fun hk =>
    not_le_of_gt hDR (hdupR (act r) hbR hk hq)
  omega

theorem uniform_supported_nonrare_routes_le_one
    (hn : 2 ≤ n) (M C : ℕ → ℕ) (Γ : (r : ℕ) → FiniteGame (M r + 1) n (C r) Seed)
    (i : (r : ℕ) → Fin (M r + 1)) (V : Set ℝ) (δ η : ℕ → ℝ)
    (p : ℝ) (hp : 0 < p) (hA : ∀ r, (Γ r).A = Schedule.ppi n)
    (hatom : ∀ r, PositiveVisibleAtomless (Γ r))
    (hj : ∀ r j, ProposerRationalAtFeasibleLists (Γ r) j)
    (hM : Tendsto M atTop atTop) (hC : ∀ r, C r ≤ M r + 1)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (hc : Tendsto (fun r => (C r : ℝ) / M r) atTop (𝓝 ρ))
    (ε : ℝ) (hε : 0 < ε) (hδ : Tendsto δ atTop (𝓝 0)) (hη : Tendsto η atTop (𝓝 0))
    (hlower : ∀ᶠ r in atTop, ∀ v ∈ V,
      max (v - (Γ r).g - p) 0 - δ r ≤ (problem (Γ r) (i r)).envelope v)
    (hbid : ∀ᶠ r in atTop, ∀ v ∈ V, ∀ act : JointAction n,
      (problem (Γ r) (i r)).BestResponse v act → 1 ≤ act.routeCount →
      ε ≤ binomBelow (M r) (alphaGt (Γ r) (⟨0, by omega⟩ : Fin n) act.bid) (C r) →
      |act.bid - p| ≤ η r) :
    ∀ᶠ r in atTop, ∀ v ∈ V, ∀ act : JointAction n,
      (problem (Γ r) (i r)).BestResponse v act →
      ε ≤ binomBelow (M r) (alphaGt (Γ r) (⟨0, by omega⟩ : Fin n) act.bid) (C r) →
      act.routeCount ≤ 1 := by
  obtain ⟨d, hd, hdup⟩ := uniform_nonrare_ppi_duplicates_pos hn M C Γ i hA hatom hj hM hC hρ0 hρ1 hc ε hε
  have herr : Tendsto (fun r => δ r + η r) atTop (𝓝 0) := by simpa using hδ.add hη
  have hpd : 0 < (p / 2) * d := mul_pos (half_pos hp) hd
  filter_upwards [hlower, hbid, hdup, hη.eventually (eventually_lt_nhds (half_pos hp)),
    herr.eventually (eventually_lt_nhds hpd)] with r hr hb hdR hηR herrR
  intro v hv act hbr hq
  by_contra hnot
  have hk : 2 ≤ act.routeCount := by omega
  have hab := hb v hv act hbr (by omega) hq
  have hbpos : p / 2 ≤ act.bid := by
    have h := neg_abs_le (act.bid - p)
    linarith
  have hD := hdR act ((half_pos hp).trans_le hbpos) hk hq
  have hpen := (problem (Γ r) (i r)).bestResponse_duplicate_penalty_le v p (δ r) 1 act hbr
    (fun k _ _ => by change (1 : ℝ) * k ≤ (Γ r).A.charge k; simp [hA r, Schedule.ppi]) (hr v hv)
  simp only [one_mul, abs_sub_comm p act.bid] at hpen
  have hmul := mul_le_mul hbpos hD hd.le act.bid_nonneg
  linarith

end FCAppendix.Bayes
