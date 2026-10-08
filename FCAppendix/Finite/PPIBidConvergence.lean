import FCAppendix.Finite.PPIRouteExclusion
import FCAppendix.Probability.CountLimits

noncomputable section

namespace FCAppendix.Interim.Problem

open Filter Topology

variable {n : ℕ}

theorem bestResponse_bid_le_price_error (P : Interim.Problem n) (v p e : ℝ)
    (he : 0 ≤ e) (act : Game.JointAction n) (hbr : P.BestResponse v act)
    (hS : 0 < (P.outcome act).success)
    (hlower : max (v - P.g - p) 0 - e ≤ P.envelope v) : act.bid ≤ p + e := by
  have hu := (P.outcome act).utility_le_bid_net_success v act.bid P.g P.A P.G
    act.bid_nonneg P.g_nonneg
  change P.payoff v act ≤ _ at hu
  rw [P.bestResponse_iff_attains v act |>.mp hbr] at hu
  have hU := P.envelope_nonneg v
  have hnet : 0 ≤ v - P.g - act.bid := by nlinarith
  by_cases hb : act.bid ≤ p
  · linarith
  · have hmargin : 0 ≤ v - P.g - p := by linarith
    rw [max_eq_left hmargin] at hlower
    have hs := mul_le_mul_of_nonneg_left (P.outcome act).success_le_one hnet
    nlinarith

theorem all_bestResponses_success_error (P : Interim.Problem n) (v h : ℝ) (hh : 0 < h)
    (act : Game.JointAction n) (hbr : P.BestResponse v act) :
    |(P.outcome act).success - 1| ≤
      |1 - (P.envelope v - P.envelope (v - h)) / h| := by
  rw [abs_of_nonpos (sub_nonpos.mpr (P.outcome act).success_le_one)]
  have hs := (P.bestResponse_secants v h hh act hbr).1
  have hab := le_abs_self (1 - (P.envelope v - P.envelope (v - h)) / h)
  linarith

theorem supported_success_tendsto_one_of_envelope
    (P : ℕ → Interim.Problem n) (act : ℕ → Game.JointAction n)
    (v g p : ℝ) (hvp : p < v - g)
    (hbr : ∀ r, (P r).BestResponse v (act r))
    (hU : ∀ w, Tendsto (fun r => (P r).envelope w) atTop (𝓝 (max (w - g - p) 0))) :
    Tendsto (fun r => ((P r).outcome (act r)).success) atTop (𝓝 1) := by
  let h := (v - g - p) / 2
  have hh : 0 < h := half_pos (sub_pos.mpr hvp)
  have hv0 : 0 ≤ v - g - p := (sub_pos.mpr hvp).le
  have hvl : 0 ≤ v - h - g - p := by dsimp [h]; linarith
  have hsec : Tendsto (fun r => ((P r).envelope v - (P r).envelope (v - h)) / h)
      atTop (𝓝 1) := by
    have ht := ((hU v).sub (hU (v - h))).div_const h
    have he : (max (v - g - p) 0 - max (v - h - g - p) 0) / h = 1 := by
      rw [max_eq_left hv0, max_eq_left hvl]
      have hn : v - g - p - (v - h - g - p) = h := by ring
      rw [hn, div_self hh.ne']
    rwa [he] at ht
  have he : Tendsto (fun r => |1 - ((P r).envelope v - (P r).envelope (v - h)) / h|)
      atTop (𝓝 0) := by simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hsec).abs
  apply (tendsto_iff_dist_tendsto_zero).mpr
  simp only [Real.dist_eq]
  exact squeeze_zero (fun r => abs_nonneg _) (fun r =>
    (P r).all_bestResponses_success_error v h hh (act r) (hbr r)) he

end FCAppendix.Interim.Problem

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter Topology

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem nonrare_price_gap_mul_le_envelope (Γ : FiniteGame m n c Seed) (hn : 0 < n)
    (i : Fin m) (b p ε : ℝ) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (hq : ε ≤ meanAcceptProb Γ i b) :
    (p - b) * ε ≤ (problem Γ i).envelope (Γ.g + p) := by
  by_cases hgap : 0 ≤ p - b
  · let act : JointAction n := ⟨b, hb, 1, hn⟩
    have hu := (problem Γ i).action_le_envelope (Γ.g + p) act
    rw [singleton_payoff Γ hn i act rfl] at hu
    have hm := mul_le_mul_of_nonneg_left hq hgap
    dsimp only [act] at hu
    nlinarith
  · have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hgap) hε
    exact hm.trans ((problem Γ i).envelope_nonneg _)

theorem nonrare_bestResponse_bid_error (Γ : FiniteGame m n c Seed) (hn : 0 < n)
    (i : Fin m) (v p e ε : ℝ) (he : 0 ≤ e) (hε : 0 < ε)
    (act : JointAction n) (hbr : (problem Γ i).BestResponse v act)
    (hk : 1 ≤ act.routeCount) (hq : ε ≤ meanAcceptProb Γ i act.bid)
    (hlower : max (v - Γ.g - p) 0 - e ≤ (problem Γ i).envelope v) :
    |act.bid - p| ≤ e + (problem Γ i).envelope (Γ.g + p) / ε := by
  have hS : 0 < ((problem Γ i).outcome act).success :=
    hε.trans_le (hq.trans (meanAcceptProb_le_success Γ hn i act hk))
  have hupper := (problem Γ i).bestResponse_bid_le_price_error v p e he act hbr hS hlower
  have hlowerbid := nonrare_price_gap_mul_le_envelope Γ hn i act.bid p ε act.bid_nonneg hε.le hq
  have hquot : p - act.bid ≤ (problem Γ i).envelope (Γ.g + p) / ε :=
    (le_div_iff₀ hε).mpr hlowerbid
  have hquot0 := div_nonneg ((problem Γ i).envelope_nonneg (Γ.g + p)) hε.le
  rw [abs_le]
  constructor <;> linarith

theorem nonrare_supported_bids_tendsto
    (M C : ℕ → ℕ) (Γ : (r : ℕ) → FiniteGame (M r) n (C r) Seed)
    (hn : 0 < n) (i : (r : ℕ) → Fin (M r)) (v : ℕ → ℝ) (act : ℕ → JointAction n)
    (p ε : ℝ) (hε : 0 < ε) (δ : ℕ → ℝ) (hδ : ∀ r, 0 ≤ δ r)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hcut : Tendsto (fun r => (problem (Γ r) (i r)).envelope ((Γ r).g + p)) atTop (𝓝 0))
    (hbr : ∀ r, (problem (Γ r) (i r)).BestResponse (v r) (act r))
    (hk : ∀ᶠ r in atTop, 1 ≤ (act r).routeCount)
    (hq : ∀ᶠ r in atTop, ε ≤ meanAcceptProb (Γ r) (i r) (act r).bid)
    (hlower : ∀ᶠ r in atTop, max (v r - (Γ r).g - p) 0 - δ r ≤
      (problem (Γ r) (i r)).envelope (v r)) :
    Tendsto (fun r => (act r).bid) atTop (𝓝 p) := by
  have he : Tendsto (fun r => δ r + (problem (Γ r) (i r)).envelope ((Γ r).g + p) / ε)
      atTop (𝓝 0) := by simpa using hδ0.add (hcut.div_const ε)
  apply (tendsto_iff_dist_tendsto_zero).mpr
  simp only [Real.dist_eq]
  refine squeeze_zero' (Eventually.of_forall fun r => abs_nonneg _) ?_ he
  filter_upwards [hk, hq, hlower] with r hkR hqR hlR
  exact nonrare_bestResponse_bid_error (Γ r) hn (i r) (v r) p (δ r) ε (hδ r) hε
    (act r) (hbr r) hkR hqR hlR

theorem supported_bid_and_count_limits_of_envelope
    (M C : ℕ → ℕ) (Γ : (r : ℕ) → FiniteGame (M r) n (C r) Seed)
    (hn : 0 < n) (i : (r : ℕ) → Fin (M r)) (act : ℕ → JointAction n)
    (a : ℕ → ℝ) (v g p : ℝ) (hp : 0 < p) (hvp : p < v - g)
    (hg : ∀ r, (Γ r).g = g)
    (hA : ∀ r k, 0 < k → k ≤ n → a r * (k : ℝ) ≤ (Γ r).A.charge k)
    (ha : Tendsto a atTop (𝓝 1))
    (hbr : ∀ r, (problem (Γ r) (i r)).BestResponse v (act r))
    (hU : ∀ w, Tendsto (fun r => (problem (Γ r) (i r)).envelope w)
      atTop (𝓝 (max (w - g - p) 0))) :
    Tendsto (fun r => ((problem (Γ r) (i r)).outcome (act r)).success) atTop (𝓝 1) ∧
    Tendsto (fun r => (act r).bid) atTop (𝓝 p) ∧
    Tendsto (fun r => ((problem (Γ r) (i r)).outcome (act r)).duplicates) atTop (𝓝 0) ∧
    Tendsto (fun r => ((problem (Γ r) (i r)).outcome (act r)).load) atTop (𝓝 1) ∧
    Tendsto (fun r => ((problem (Γ r) (i r)).outcome (act r)).prob (fun k => k.val ≠ 1))
      atTop (𝓝 0) := by
  have hS := Interim.Problem.supported_success_tendsto_one_of_envelope
    (fun r => problem (Γ r) (i r)) act v g p hvp hbr hU
  let δ := fun r => |(problem (Γ r) (i r)).envelope v - (v - g - p)|
  have hδ0 : Tendsto δ atTop (𝓝 0) := by
    have hh := ((hU v).sub_const (v - g - p)).abs
    simpa only [max_eq_left (sub_pos.mpr hvp).le, sub_self, abs_zero] using hh
  have hδ : ∀ r, 0 ≤ δ r := fun r => abs_nonneg _
  have hlower (r : ℕ) : max (v - (Γ r).g - p) 0 - δ r ≤ (problem (Γ r) (i r)).envelope v := by
    rw [hg r, max_eq_left (sub_pos.mpr hvp).le]
    have hh := neg_abs_le ((problem (Γ r) (i r)).envelope v - (v - g - p))
    dsimp only [δ]
    linarith
  let ε := 1 / (2 * (n : ℝ))
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hSpos : ∀ᶠ r in atTop, (1 : ℝ) / 2 < ((problem (Γ r) (i r)).outcome (act r)).success :=
    hS.eventually (eventually_gt_nhds (by norm_num))
  have hk : ∀ᶠ r in atTop, 1 ≤ (act r).routeCount := by
    filter_upwards [hSpos] with r hr
    by_contra hh
    have hk0 : (act r).routeCount = 0 := by omega
    have hl := load_le_routeCount_mul_success (Γ r) (i r) (act r)
    rw [hk0, Nat.cast_zero, zero_mul] at hl
    linarith [CountLaw.success_le_load ((problem (Γ r) (i r)).outcome (act r))]
  have hq : ∀ᶠ r in atTop, ε ≤ meanAcceptProb (Γ r) (i r) (act r).bid := by
    filter_upwards [hSpos] with r hr
    have hh := success_le_n_meanAcceptProb (Γ r) hn (i r) (act r)
    apply (div_le_iff₀ (by positivity : 0 < 2 * (n : ℝ))).mpr
    nlinarith
  have hcut : Tendsto (fun r => (problem (Γ r) (i r)).envelope ((Γ r).g + p)) atTop (𝓝 0) := by
    simp_rw [hg]
    convert hU (g + p) using 1
    simp
  have hb := nonrare_supported_bids_tendsto M C Γ hn i (fun _ => v) act p ε hε δ hδ hδ0 hcut hbr hk hq
    (Eventually.of_forall hlower)
  have hD := Interim.Problem.supported_duplicates_tendsto_zero_varying_values
    (fun r => problem (Γ r) (i r)) (fun _ => v) act a δ p hp hA ha hb hδ0 hbr
    (Eventually.of_forall hlower)
  refine ⟨hS, hb, hD, ?_, CountLaw.tendsto_unit_count _ hS hD⟩
  have hh := hD.add hS
  simpa only [CountLaw.duplicates, sub_add_cancel, zero_add] using hh

theorem uniform_nonrare_supported_bid_convergence
    (M C : ℕ → ℕ) (Γ : (r : ℕ) → FiniteGame (M r) n (C r) Seed)
    (hn : 0 < n) (i : (r : ℕ) → Fin (M r)) (V : Set ℝ)
    (p ε : ℝ) (hε : 0 < ε) (δ : ℕ → ℝ) (hδ : ∀ r, 0 ≤ δ r)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hcut : Tendsto (fun r => (problem (Γ r) (i r)).envelope ((Γ r).g + p)) atTop (𝓝 0))
    (hlower : ∀ᶠ r in atTop, ∀ v ∈ V, max (v - (Γ r).g - p) 0 - δ r ≤
      (problem (Γ r) (i r)).envelope v) :
    ∀ η > 0, ∀ᶠ r in atTop, ∀ v ∈ V, ∀ act : JointAction n,
      (problem (Γ r) (i r)).BestResponse v act → 1 ≤ act.routeCount →
      ε ≤ meanAcceptProb (Γ r) (i r) act.bid → |act.bid - p| < η := by
  have he : Tendsto (fun r => δ r + (problem (Γ r) (i r)).envelope ((Γ r).g + p) / ε)
      atTop (𝓝 0) := by simpa using hδ0.add (hcut.div_const ε)
  intro η hη
  filter_upwards [hlower, he.eventually (eventually_lt_nhds hη)] with r hr heR
  intro v hv act hbr hk hq
  exact (nonrare_bestResponse_bid_error (Γ r) hn (i r) v p (δ r) ε (hδ r) hε act hbr hk hq
    (hr v hv)).trans_lt heR

theorem eventually_one_route_of_envelope
    (hn : 2 ≤ n) (M C : ℕ → ℕ) (Γ : (r : ℕ) → FiniteGame (M r + 1) n (C r) Seed)
    (i : (r : ℕ) → Fin (M r + 1)) (act : ℕ → JointAction n)
    (v g p : ℝ) (hp : 0 < p) (hvp : p < v - g)
    (hg : ∀ r, (Γ r).g = g) (hA : ∀ r, (Γ r).A = Schedule.ppi n)
    (hatom : ∀ r, PositiveVisibleAtomless (Γ r))
    (hj : ∀ r j, ProposerRationalAtFeasibleLists (Γ r) j)
    (hM : Tendsto M atTop atTop) (hC : ∀ r, C r ≤ M r + 1)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (hc : Tendsto (fun r => (C r : ℝ) / M r) atTop (𝓝 ρ))
    (hbr : ∀ r, (problem (Γ r) (i r)).BestResponse v (act r))
    (hU : ∀ w, Tendsto (fun r => (problem (Γ r) (i r)).envelope w)
      atTop (𝓝 (max (w - g - p) 0))) :
    ∀ᶠ r in atTop, (act r).routeCount = 1 := by
  have hcharge (r k : ℕ) (_hk : 0 < k) (_hkn : k ≤ n) : (1 : ℝ) * k ≤ (Γ r).A.charge k := by
    simp [hA r, Schedule.ppi]
  have hlim := supported_bid_and_count_limits_of_envelope (fun r => M r + 1) C Γ (by omega) i act
    (fun _ => 1) v g p hp hvp hg hcharge tendsto_const_nhds hbr hU
  let δ := fun r => |(problem (Γ r) (i r)).envelope v - (v - g - p)|
  have hδ0 : Tendsto δ atTop (𝓝 0) := by
    have hh := ((hU v).sub_const (v - g - p)).abs
    simpa only [max_eq_left (sub_pos.mpr hvp).le, sub_self, abs_zero] using hh
  apply eventually_one_route_of_bid_limit hn M C Γ i act δ v g p hp hvp hg hA hatom hj hM hC
    hρ0 hρ1 hc hlim.2.1 hδ0 hbr
  apply Eventually.of_forall
  intro r
  have hh := neg_abs_le ((problem (Γ r) (i r)).envelope v - (v - g - p))
  dsimp only [δ]
  linarith

theorem all_bestResponses_bid_and_count_converge
    (M C : ℕ → ℕ) (Γ : (r : ℕ) → FiniteGame (M r) n (C r) Seed)
    (hn : 0 < n) (i : (r : ℕ) → Fin (M r))
    (a : ℕ → ℝ) (v g p : ℝ) (hp : 0 < p) (hvp : p < v - g)
    (hg : ∀ r, (Γ r).g = g)
    (hA : ∀ r k, 0 < k → k ≤ n → a r * (k : ℝ) ≤ (Γ r).A.charge k)
    (ha : Tendsto a atTop (𝓝 1))
    (hU : ∀ w, Tendsto (fun r => (problem (Γ r) (i r)).envelope w)
      atTop (𝓝 (max (w - g - p) 0))) :
    ∀ η > 0, ∀ᶠ r in atTop, ∀ act : JointAction n,
      (problem (Γ r) (i r)).BestResponse v act →
      |((problem (Γ r) (i r)).outcome act).success - 1| < η ∧
      |act.bid - p| < η ∧ ((problem (Γ r) (i r)).outcome act).duplicates < η ∧
      |((problem (Γ r) (i r)).outcome act).load - 1| < η ∧
      ((problem (Γ r) (i r)).outcome act).prob (fun k => k.val ≠ 1) < η := by
  classical
  intro η hη
  by_contra hnot
  have hex : ∀ k : ℕ, ∃ r : ℕ, k ≤ r ∧ ∃ act : JointAction n,
      (problem (Γ r) (i r)).BestResponse v act ∧ ¬(
      |((problem (Γ r) (i r)).outcome act).success - 1| < η ∧
      |act.bid - p| < η ∧ ((problem (Γ r) (i r)).outcome act).duplicates < η ∧
      |((problem (Γ r) (i r)).outcome act).load - 1| < η ∧
      ((problem (Γ r) (i r)).outcome act).prob (fun k => k.val ≠ 1) < η) := by
    simpa only [eventually_atTop, not_exists, not_forall, Classical.not_imp, exists_prop] using hnot
  choose f hf act hbr hbad using hex
  have hft : Tendsto f atTop atTop := tendsto_atTop_mono hf tendsto_id
  obtain ⟨hS, hb, hD, hL, hK⟩ := supported_bid_and_count_limits_of_envelope (M ∘ f) (C ∘ f)
    (fun r => Γ (f r)) hn (fun r => i (f r)) act (a ∘ f) v g p hp hvp (fun r => hg (f r))
    (fun r => hA (f r)) (ha.comp hft) hbr (fun w => (hU w).comp hft)
  have hSe : Tendsto (fun r => |((problem (Γ (f r)) (i (f r))).outcome (act r)).success - 1|)
      atTop (𝓝 0) := by simpa using (hS.sub_const 1).abs
  have hbe : Tendsto (fun r => |(act r).bid - p|) atTop (𝓝 0) := by simpa using (hb.sub_const p).abs
  have hLe : Tendsto (fun r => |((problem (Γ (f r)) (i (f r))).outcome (act r)).load - 1|)
      atTop (𝓝 0) := by simpa using (hL.sub_const 1).abs
  have hfalse : ∀ᶠ r : ℕ in atTop, False := by
    filter_upwards [hSe.eventually (eventually_lt_nhds hη), hbe.eventually (eventually_lt_nhds hη),
      hD.eventually (eventually_lt_nhds hη), hLe.eventually (eventually_lt_nhds hη),
      hK.eventually (eventually_lt_nhds hη)] with r hSr hbr hDr hLr hKr
    exact hbad r ⟨hSr, hbr, hDr, hLr, hKr⟩
  exact hfalse.exists.elim (fun _ hh => hh)

theorem eventually_all_bestResponses_one_route_of_envelope
    (hn : 2 ≤ n) (M C : ℕ → ℕ) (Γ : (r : ℕ) → FiniteGame (M r + 1) n (C r) Seed)
    (i : (r : ℕ) → Fin (M r + 1)) (v g p : ℝ) (hp : 0 < p) (hvp : p < v - g)
    (hg : ∀ r, (Γ r).g = g) (hA : ∀ r, (Γ r).A = Schedule.ppi n)
    (hatom : ∀ r, PositiveVisibleAtomless (Γ r))
    (hj : ∀ r j, ProposerRationalAtFeasibleLists (Γ r) j)
    (hM : Tendsto M atTop atTop) (hC : ∀ r, C r ≤ M r + 1)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (hc : Tendsto (fun r => (C r : ℝ) / M r) atTop (𝓝 ρ))
    (hU : ∀ w, Tendsto (fun r => (problem (Γ r) (i r)).envelope w)
      atTop (𝓝 (max (w - g - p) 0))) :
    ∀ᶠ r in atTop, ∀ act : JointAction n,
      (problem (Γ r) (i r)).BestResponse v act → act.routeCount = 1 := by
  classical
  by_contra hnot
  have hex : ∀ k : ℕ, ∃ r : ℕ, k ≤ r ∧ ∃ act : JointAction n,
      (problem (Γ r) (i r)).BestResponse v act ∧ act.routeCount ≠ 1 := by
    simpa only [eventually_atTop, not_exists, not_forall, Classical.not_imp, exists_prop] using hnot
  choose f hf act hbr hbad using hex
  have hft : Tendsto f atTop atTop := tendsto_atTop_mono hf tendsto_id
  have hone := eventually_one_route_of_envelope hn (M ∘ f) (C ∘ f) (fun r => Γ (f r))
    (fun r => i (f r)) act v g p hp hvp (fun r => hg (f r)) (fun r => hA (f r))
    (fun r => hatom (f r)) (fun r => hj (f r)) (hM.comp hft) (fun r => hC (f r))
    hρ0 hρ1 (hc.comp hft) hbr (fun w => (hU w).comp hft)
  obtain ⟨r, hr⟩ := hone.exists
  exact hbad r hr

end FCAppendix.Bayes
