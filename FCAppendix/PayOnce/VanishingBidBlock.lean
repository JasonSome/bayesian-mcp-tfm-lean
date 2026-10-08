import FCAppendix.PayOnce.VanishingBidLaw
import FCAppendix.PayOnce.AnalyticalRareSuccess

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open scoped ProbabilityTheory BigOperators

theorem tendsto_success_ratio_one_of_bid_zero
    {M C : ℕ → ℕ} {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : ∀ t, FiniteGame (M t) n (C t) Seed) (i : ∀ t, Fin (M t))
    (hA : ∀ t, (Γ t).A = Schedule.once n) (hG : ∀ t, (Γ t).G = Schedule.once n)
    {g v w : ℝ} (hg : ∀ t, (Γ t).g = g) (hv : g < v) (hvw : v < w)
    (a b : ℕ → JointAction n)
    (ha : ∀ t, (problem (Γ t) (i t)).BestResponse v (a t))
    (hb : ∀ t, (problem (Γ t) (i t)).BestResponse w (b t))
    (hQ : ∀ t, 0 < ((problem (Γ t) (i t)).outcome (a t)).success)
    (hbid : Tendsto (fun t => (b t).bid) atTop (𝓝 0)) :
    Tendsto (fun t => ((problem (Γ t) (i t)).outcome (b t)).success /
      ((problem (Γ t) (i t)).outcome (a t)).success) atTop (𝓝 1) := by
  let Q := fun t => ((problem (Γ t) (i t)).outcome (a t)).success
  let R := fun t => ((problem (Γ t) (i t)).outcome (b t)).success
  have hv0 : 0 < v-g := sub_pos.mpr hv
  have hsmall : ∀ᶠ t in atTop, (b t).bid < v-g := hbid.eventually_lt_const hv0
  have hlim : Tendsto (fun t => (v-g)/(v-g-(b t).bid)) atTop (𝓝 1) := by
    have hh := (tendsto_const_nhds (x := v-g)).div
      ((tendsto_const_nhds (x := v-g)).sub hbid) (by simpa using hv0.ne')
    change Tendsto (fun t => (v-g)/(v-g-(b t).bid)) atTop (𝓝 ((v-g)/(v-g-0))) at hh
    simpa only [sub_zero,div_self hv0.ne'] using hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · exact Filter.Eventually.of_forall fun t => by
      apply (le_div_iff₀ (hQ t)).mpr
      simpa only [one_mul] using (problem (Γ t) (i t)).success_order v w hvw (a t) (b t) (ha t) (hb t)
  · filter_upwards [hsmall] with t ht
    have hic := ha t (b t)
    rw [payoff_once (Γ t) (hA t) (hG t),payoff_once (Γ t) (hA t) (hG t),hg t] at hic
    have hnon := mul_nonneg (a t).bid_nonneg (hQ t).le
    have hden : 0 < v-g-(b t).bid := sub_pos.mpr ht
    apply (div_le_div_iff₀ (hQ t) hden).mpr
    change R t * (v-g-(b t).bid) ≤ (v-g)*Q t
    change (v-(b t).bid-g)*R t ≤ (v-(a t).bid-g)*Q t at hic
    nlinarith

end FCAppendix.Bayes

namespace FCAppendix.PayOnce.VanishingBidIC
open MeasureTheory ProbabilityTheory Set Filter Topology

theorem tendsto_bid_zero_at_lower_quantile
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (bid : ℕ → ℝ → ℝ) (hmono : ∀ t, Monotone (bid t)) (hpos : ∀ t v, 0 ≤ bid t v)
    (K : ℕ → ProbabilityMeasure ENNReal) (G : ProbabilityMeasure ENNReal)
    (hmap : ∀ t, (K t : Measure ENNReal) = F.map (fun v => ENNReal.ofReal (bid t v)))
    (hweak : Tendsto K atTop (𝓝 G)) {v : ℝ}
    (hv : (G : Measure ENNReal) ({0}ᶜ) < F (Ici v)) :
    Tendsto (fun t => bid t v) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun t => ha.trans_le (hpos t v)
  · intro ε hε
    have he : Ici (ENNReal.ofReal ε) ⊆ ({0}ᶜ : Set ENNReal) := by
      intro b hb hz
      have hh : 0 < b := (ENNReal.ofReal_pos.mpr hε).trans_le hb
      exact hh.ne' hz
    have hh := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hweak
      (isClosed_Ici (a := ENNReal.ofReal ε))
    have ht := eventually_lt_of_limsup_lt ((hh.trans (measure_mono he)).trans_lt hv)
    filter_upwards [ht] with t ht
    by_contra hn
    have hincl : Ici v ⊆ (fun w => ENNReal.ofReal (bid t w)) ⁻¹' Ici (ENNReal.ofReal ε) := by
      intro w hw
      exact ENNReal.ofReal_le_ofReal ((le_of_not_gt hn).trans (hmono t hw))
    rw [hmap t, Measure.map_apply (show Measurable (fun v => ENNReal.ofReal (bid t v)) from
      ENNReal.measurable_ofReal.comp (hmono t).measurable) measurableSet_Ici] at ht
    exact ht.not_ge (measure_mono hincl)

end FCAppendix.PayOnce.VanishingBidIC

namespace FCAppendix.PayOnce.VanishingBidIC
open MeasureTheory ProbabilityTheory Set Filter Topology

theorem exists_supported_draw_subsequence
    {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)]
    (P : ∀ t, Measure (Ω t)) [∀ t, IsProbabilityMeasure (P t)]
    (f : ∀ t, Ω t → ℝ) (hf : ∀ t, Measurable (f t))
    (K : ℕ → ProbabilityMeasure ENNReal) (G : ProbabilityMeasure ENNReal)
    (hmap : ∀ t, (K t : Measure ENNReal) = (P t).map (fun x => ENNReal.ofReal (f t x)))
    (hweak : Tendsto K atTop (𝓝 G))
    {x₀ : ℝ} (hx₀ : 0 < x₀) (hsupport : ENNReal.ofReal x₀ ∈ (G : Measure ENNReal).support)
    (Good : ∀ t, Ω t → Prop) (hgood : ∀ t, ∀ᵐ x ∂P t, Good t x) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x : ∀ j, Ω (φ j),
      (∀ j, Good (φ j) (x j)) ∧ Tendsto (fun j => f (φ j) (x j)) atTop (𝓝 x₀) := by
  let δ := fun j : ℕ => min (x₀/2) (1/((j:ℝ)+1))
  have hδ j : 0 < δ j := lt_min (half_pos hx₀) (by positivity)
  have hlo j : 0 < x₀-δ j := by have := min_le_left (x₀/2) (1/((j:ℝ)+1)); dsimp only [δ]; linarith
  let W := fun j => Ioo (ENNReal.ofReal (x₀-δ j)) (ENNReal.ofReal (x₀+δ j))
  have hW j : ENNReal.ofReal x₀ ∈ W j := by
    constructor
    · exact ENNReal.ofReal_lt_ofReal_iff hx₀ |>.mpr (by linarith [hδ j])
    · exact ENNReal.ofReal_lt_ofReal_iff (by linarith [hδ j] : 0 < x₀ + δ j) |>.mpr (by linarith [hδ j])
  have hmass j : 0 < (G : Measure ENNReal) (W j) :=
    (Measure.mem_support_iff_forall _).mp hsupport _ (isOpen_Ioo.mem_nhds (hW j))
  have hevent j : ∀ᶠ t in atTop, ∃ x : Ω t, Good t x ∧ |f t x-x₀| < δ j := by
    have hp := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak
      (isOpen_Ioo (a := ENNReal.ofReal (x₀-δ j)) (b := ENNReal.ofReal (x₀+δ j)))
    have ht := eventually_lt_of_lt_liminf ((hmass j).trans_le hp)
    filter_upwards [ht] with t ht
    rw [hmap t, Measure.map_apply (show Measurable (fun x => ENNReal.ofReal (f t x)) from
      ENNReal.measurable_ofReal.comp (hf t)) measurableSet_Ioo] at ht
    have hfreq : ∃ᵐ x ∂P t, ENNReal.ofReal (f t x) ∈ W j := frequently_ae_iff.mpr ht.ne'
    obtain ⟨x,hxW,hxgood⟩ := (hfreq.and_eventually (hgood t)).exists
    refine ⟨x,hxgood,?_⟩
    have hl : x₀-δ j < f t x := lt_of_not_ge (fun h => hxW.1.not_ge (ENNReal.ofReal_le_ofReal h))
    have hpos : 0 < f t x := (hlo j).trans hl
    have hu : f t x < x₀+δ j := (ENNReal.ofReal_lt_ofReal_iff (by linarith [hδ j] : 0 < x₀ + δ j)).mp hxW.2
    exact abs_lt.mpr ⟨by linarith,by linarith⟩
  choose N hN using fun j => eventually_atTop.mp (hevent j)
  let φ : ℕ → ℕ := Nat.rec (N 0) (fun j r => max (N (j+1)) (r+1))
  have hφN j : N j ≤ φ j := by
    cases j with
    | zero => exact le_rfl
    | succ j => exact le_max_left _ _
  have hφ : StrictMono φ := strictMono_nat_of_lt_succ fun j => by
    exact (Nat.lt_succ_self (φ j)).trans_le (le_max_right _ _)
  choose x hxgood hxdist using fun j => hN j (φ j) (hφN j)
  refine ⟨φ,hφ,x,hxgood,?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) (fun j => ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  rw [Real.dist_eq]
  exact (hxdist j).le.trans (min_le_right _ _)

end FCAppendix.PayOnce.VanishingBidIC
