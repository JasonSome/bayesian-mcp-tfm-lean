import FCAppendix.PayOnce.ActualVanishingWindow

namespace FCAppendix.PayOnce.VanishingBidIC
open MeasureTheory Set Filter Topology

theorem tendsto_bid_ratio_zero_of_window_mass
    (F : Measure ℝ) (b : ℕ → ℝ → ℝ) (hmono : ∀ t, Monotone (b t))
    {x y g : ℝ} (hbx : ∀ t, 0 ≤ b t x) (hby : ∀ t, 0 < b t y)
    (hmass : 0 < F (Icc x y))
    (hwindow : ∀ ε : ℝ, 0 < ε → Tendsto
      (fun t => F {v | x-g ≤ v-g ∧ b t v / b t y ∈ Icc ε 1}) atTop (𝓝 0)) :
    Tendsto (fun t => b t x / b t y) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro r hr
    exact Filter.Eventually.of_forall fun t => hr.trans_le (div_nonneg (hbx t) (hby t).le)
  · intro ε hε
    have ht := (hwindow ε hε).eventually_lt_const hmass
    filter_upwards [ht] with t ht
    by_contra hn
    have hsub : Icc x y ⊆ {v | x-g ≤ v-g ∧ b t v / b t y ∈ Icc ε 1} := by
      intro v hv
      refine ⟨sub_le_sub_right hv.1 g, ?_, ?_⟩
      · exact (le_of_not_gt hn).trans
          (div_le_div_of_nonneg_right (hmono t hv.1) (hby t).le)
      · exact (div_le_one (hby t)).mpr (hmono t hv.2)
    exact ht.not_ge (measure_mono hsub)

end FCAppendix.PayOnce.VanishingBidIC

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open PayOnce PayOnce.CompactifiedBidLaws
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem compProd_bid_window_eq (Γ : FiniteGame m n c Seed)
    (b : ℝ → ℝ) (hb : Measurable b)
    (heq : ∀ᵐ z ∂(Γ.F ⊗ₘ Γ.σ), z.2.bid = b z.1)
    (a v g : ℝ) {K : Set ℝ} (hK : MeasurableSet K) :
    (Γ.F ⊗ₘ Γ.σ) {z | v ≤ z.1-g ∧ z.2.bid/a ∈ K} =
      Γ.F {x | v ≤ x-g ∧ b x/a ∈ K} := by
  let E := {x : ℝ | v ≤ x-g ∧ b x/a ∈ K}
  have hE : MeasurableSet E :=
    (measurableSet_le measurable_const (measurable_id.sub_const g)).inter ((hb.div_const a) hK)
  calc
    _ = (Γ.F ⊗ₘ Γ.σ) (Prod.fst ⁻¹' E) := by
      apply measure_congr
      filter_upwards [heq] with z hz
      change (v ≤ z.1-g ∧ z.2.bid/a ∈ K) = (v ≤ z.1-g ∧ b z.1/a ∈ K)
      rw [hz]
    _ = Γ.F E := by rw [← Measure.fst_apply hE, Measure.fst_compProd]

theorem payOnce_vanishing_bid_ratio_zero
    {N C : ℕ → ℕ} {k : ℕ}
    (Γ : ∀ t, FiniteGame (N t+1) (k+1) (C t) Seed)
    (hk : 1 ≤ k) (hc : ∀ t, 0 < C t) (hcm : ∀ t, C t < N t+1)
    (hN : Tendsto N atTop atTop)
    (hA : ∀ t, (Γ t).A = Schedule.once (k+1)) (hG : ∀ t, (Γ t).G = Schedule.once (k+1))
    (hu : ∀ t, UsersOptimal (Γ t)) (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, PosteriorProposerOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t)) (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    (F : Measure ℝ) [IsProbabilityMeasure F] [NullSingletonClass F]
    (hF : ∀ t, (Γ t).F = F) {g : ℝ} (hg : ∀ t, (Γ t).g = g)
    (hactive : ∀ᵐ v ∂F, g < v)
    {ρ : ℝ} (hρ : Tendsto (fun t => (C t : ℝ)/(N t+1)) atTop (𝓝 ρ))
    (hρb : ρ ∈ Ioo (0:ℝ) 1) {Gorig : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => bidLaw (Γ t)) atTop (𝓝 Gorig))
    (b : ℕ → ℝ → ℝ) (hmono : ∀ t, Monotone (b t)) (hbm : ∀ t, Measurable (b t))
    (heq : ∀ t, ∀ᵐ z ∂((Γ t).F ⊗ₘ (Γ t).σ), z.2.bid = b t z.1)
    {x y : ℝ} (hx : g < x) (hbx : ∀ t, 0 ≤ b t x) (hby : ∀ t, 0 < b t y)
    (hmass : 0 < F (Icc x y)) (hby0 : Tendsto (fun t => b t y) atTop (𝓝 0)) :
    Tendsto (fun t => b t x / b t y) atTop (𝓝 0) := by
  apply VanishingBidIC.tendsto_bid_ratio_zero_of_window_mass F b hmono hbx hby hmass
  intro ε hε
  have hh := payOnce_vanishing_window_mass_zero Γ hk hc hcm hN hA hG hu B hB hsym hatom
    F hF hg hactive hρ hρb hweak (fun t => b t y) hby hby0 isCompact_Icc
    (fun v hv => hε.trans_le hv.1 : Icc ε 1 ⊆ Ioi 0) (sub_pos.mpr hx)
  have he t := compProd_bid_window_eq (Γ t) (b t) (hbm t) (heq t) (b t y) (x-g) g
    (K := Icc ε 1) measurableSet_Icc
  apply hh.congr
  intro t
  exact (he t).trans (by rw [hF t])

end FCAppendix.Bayes
