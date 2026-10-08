import FCAppendix.Ample.RouteIdentificationCore
import FCAppendix.Ample.ActualRouteCompactness

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology Real
open scoped ENNReal BigOperators
open Ample Ample.DownstreamNormalizationCore

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma real_event_error_of_agree_off {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (s t E : Set Ω)
    (h : ∀ x, x ∉ E → (x ∈ s ↔ x ∈ t)) :
    |μ.real s - μ.real t| ≤ μ.real E := by
  have hst : s ⊆ t ∪ E := by
    intro x hx
    by_cases he : x ∈ E
    · exact Or.inr he
    · exact Or.inl ((h x he).mp hx)
  have hts : t ⊆ s ∪ E := by
    intro x hx
    by_cases he : x ∈ E
    · exact Or.inr he
    · exact Or.inl ((h x he).mpr hx)
  have h₁ := (measureReal_mono hst).trans (measureReal_union_le t E (μ := μ))
  have h₂ := (measureReal_mono hts).trans (measureReal_union_le s E (μ := μ))
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma routed_event_real_le_active (Γ : FiniteGame m n c Seed)
    (ha : NonpositiveAbstention Γ) (hpos : 0 < Γ.F.real (Ioi Γ.g))
    (s : Set (ℝ × JointAction n)) (hs : ∀ x ∈ s, 0 < x.2.routeCount) :
    (Γ.F ⊗ₘ Γ.σ).real s ≤ (activeDrawLaw Γ).real s := by
  let A : Set (ℝ × JointAction n) := {x | Γ.g < x.1}
  have hA : MeasurableSet A := measurableSet_lt measurable_const measurable_fst
  have he : (Γ.F ⊗ₘ Γ.σ).real s = (Γ.F ⊗ₘ Γ.σ).real (s ∩ A) := by
    apply measureReal_congr
    filter_upwards [ha] with x hx
    apply propext
    constructor
    · intro hxs
      refine ⟨hxs, ?_⟩
      by_contra hn
      have hz := hx (le_of_not_gt hn)
      exact (Nat.ne_of_gt (hs x hxs)) hz
    · exact fun hxs => hxs.1
  have hformula : (activeDrawLaw Γ).real s =
      (Γ.F ⊗ₘ Γ.σ).real s / Γ.F.real (Ioi Γ.g) := by
    rw [activeDrawLaw, measureReal_ennreal_smul_apply,
      measureReal_restrict_apply' hA, ENNReal.toReal_inv, ← he]
    simp only [Measure.real, div_eq_mul_inv, mul_comm]
  rw [hformula]
  apply (le_div_iff₀ hpos).2
  exact mul_le_of_le_one_right measureReal_nonneg (measureReal_le_one (μ := Γ.F))

def routedTierError (_Γ : FiniteGame m n c Seed) (scale δ : ℝ) :
    Set (ℝ × JointAction n) :=
  {x | 0 < x.2.routeCount ∧
    δ < |(x.2.routeCount : ℝ) * x.2.bid / scale - 1|}

lemma measurableSet_routedTierError (Γ : FiniteGame m n c Seed) (scale δ : ℝ) :
    MeasurableSet (routedTierError Γ scale δ) := by
  have hK : Measurable (fun x : ℝ × JointAction n => (x.2.routeCount : ℝ)) :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
      ((measurable_routeCount n).comp measurable_snd)
  have hB : Measurable (fun x : ℝ × JointAction n => x.2.bid) :=
    (measurable_bid n).comp measurable_snd
  exact (measurableSet_lt measurable_const
    ((measurable_routeCount n).comp measurable_snd)).inter
      (measurableSet_lt measurable_const (((hK.mul hB).div_const scale).sub_const 1).abs)

lemma tierGood_of_not_error (Γ : FiniteGame m n c Seed) (scale δ : ℝ)
    {x : ℝ × JointAction n} (hk : 0 < x.2.routeCount)
    (he : x ∉ routedTierError Γ scale δ) :
    TierGood n δ (fun y : ℝ × JointAction n => y.2.routeCount)
      (fun y => y.2.bid / scale) x := by
  refine ⟨hk, x.2.routeCount_le, ?_⟩
  have hh : |(x.2.routeCount : ℝ) * x.2.bid / scale - 1| ≤ δ := by
    exact le_of_not_gt (fun hlt => he ⟨hk, hlt⟩)
  simpa only [mul_div_assoc] using hh

lemma bid_pos_of_tierGood (_Γ : FiniteGame m n c Seed)
    {scale δ : ℝ} (hs : 0 < scale) (hδ : δ < 1)
    {x : ℝ × JointAction n}
    (hx : TierGood n δ (fun y : ℝ × JointAction n => y.2.routeCount)
      (fun y => y.2.bid / scale) x) : 0 < x.2.bid := by
  have hk : (0 : ℝ) < x.2.routeCount := by exact_mod_cast hx.1
  have he := (abs_le.mp hx.2.2).1
  have hp : 0 < (x.2.routeCount : ℝ) * (x.2.bid / scale) := by linarith
  by_contra hnot
  have hdiv : x.2.bid / scale ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hnot) hs.le
  exact (not_le_of_gt hp) (mul_nonpos_of_nonneg_of_nonpos hk.le hdiv)

theorem routedTierError_tendsto_zero {M C : ℕ → ℕ}
    (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (scale : ℕ → ℝ) (ha : ∀ t, NonpositiveAbstention (Γ t))
    (hp : ∀ t, 0 < (Γ t).F.real (Ioi (Γ t).g))
    (hnorm : ProbZero (fun t => activeDrawLaw (Γ t))
      (fun t x => (x.2.routeCount : ℝ) * x.2.bid / scale t - 1))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun t => ((Γ t).F ⊗ₘ (Γ t).σ).real
      (routedTierError (Γ t) (scale t) δ)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := hnorm δ hδ ε hε
  filter_upwards [he] with t ht
  have hset : routedTierError (Γ t) (scale t) δ ⊆
      {x | δ < |(x.2.routeCount : ℝ) * x.2.bid / scale t - 1|} :=
    fun _ hx => hx.2
  have hlt : (activeDrawLaw (Γ t)) (routedTierError (Γ t) (scale t) δ) <
      ENNReal.ofReal ε := (measure_mono hset).trans_lt ht
  have htop : (activeDrawLaw (Γ t)) (routedTierError (Γ t) (scale t) δ) ≠ ∞ :=
    ne_of_lt (hlt.trans_le le_top)
  have hreal : (activeDrawLaw (Γ t)).real
      (routedTierError (Γ t) (scale t) δ) < ε := by
    have hh := (ENNReal.toReal_lt_toReal htop ENNReal.ofReal_ne_top).mpr hlt
    simpa only [Measure.real, ENNReal.toReal_ofReal hε.le] using hh
  have hh := (routed_event_real_le_active (Γ t) (ha t) (hp t)
    (routedTierError (Γ t) (scale t) δ) (fun _ hx => hx.1)).trans_lt hreal
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] using hh

lemma actual_off_tier_error (Γ : FiniteGame m n c Seed)
    {scale δ x : ℝ} {k j : ℕ} (hs : 0 < scale) (hj : 1 ≤ j)
    (hx : 0 ≤ x) (hlo : 1 + δ < x * ((k : ℝ)+1))
    (hhi : x * (k : ℝ) < 1 - δ) :
    |visibleClassMass Γ (x*scale) j -
      (if j ≤ k then actualRouteMass Γ j else 0)| ≤
        (Γ.F ⊗ₘ Γ.σ).real (routedTierError Γ scale δ) := by
  classical
  rw [visibleClassMass_eq_compProd Γ (x*scale) hj]
  let S : Set (ℝ × JointAction n) := {y | x*scale < y.2.bid ∧ y.2.routeCount = j}
  let T : Set (ℝ × JointAction n) := {y | y.2.routeCount = j ∧ j ≤ k}
  have ht : (Γ.F ⊗ₘ Γ.σ).real T =
      if j ≤ k then actualRouteMass Γ j else 0 := by
    by_cases hjk : j ≤ k <;> simp [T, hjk, actualRouteMass]
  rw [← ht]
  apply real_event_error_of_agree_off (Γ.F ⊗ₘ Γ.σ) S T
    (routedTierError Γ scale δ)
  intro y hy
  by_cases hyj : y.2.routeCount = j
  · have hypos : 0 < y.2.routeCount := by omega
    have hg := tierGood_of_not_error Γ scale δ hypos hy
    have he := off_tier_prefix (fun z : ℝ × JointAction n => z.2.routeCount)
      (fun z => z.2.bid/scale) hx hlo hhi hg
    have hscale : x*scale < y.2.bid ↔ x < y.2.bid/scale :=
      (lt_div_iff₀ hs).symm
    simpa [S, T, hyj, hscale] using he
  · simp [S, T, hyj]

lemma off_tier_tolerance {k : ℕ} (hk : 1 ≤ k) {x : ℝ}
    (hxlo : 1/((k : ℝ)+1) < x) (hxhi : x < 1/(k : ℝ)) :
    ∃ δ > 0, 1 + δ < x*((k : ℝ)+1) ∧ x*(k : ℝ) < 1-δ := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkp : (0 : ℝ) < (k : ℝ)+1 := by linarith
  have h₁ : 0 < x*((k : ℝ)+1)-1 := by
    have hh := (div_lt_iff₀ hkp).mp hxlo
    linarith
  have h₂ : 0 < 1-x*(k : ℝ) := by
    have hh := (lt_div_iff₀ hkR).mp hxhi
    linarith
  obtain ⟨δ, hδ, hsmall⟩ := exists_between (lt_min h₁ h₂)
  exact ⟨δ, hδ, by linarith [hsmall.trans_le (min_le_left _ _)],
    by linarith [hsmall.trans_le (min_le_right _ _)]⟩

theorem actual_off_tier_marked_law {M C : ℕ → ℕ}
    (Γ : ∀ t, FiniteGame (M t) n (C t) Seed) (scale : ℕ → ℝ)
    (ha : ∀ t, NonpositiveAbstention (Γ t))
    (hpactive : ∀ t, 0 < (Γ t).F.real (Ioi (Γ t).g))
    (hnorm : ProbZero (fun t => activeDrawLaw (Γ t))
      (fun t x => (x.2.routeCount : ℝ)*x.2.bid/scale t-1))
    (hscale : ∀ᶠ t in atTop, 0 < scale t)
    {pi : ℕ → ℝ} (hp : RouteLimit Γ pi) {k : ℕ} (hk : 1 ≤ k)
    {x : ℝ} (hxlo : 1/((k : ℝ)+1) < x) (hxhi : x < 1/(k : ℝ)) :
    ∀ j ∈ Finset.Icc 1 n, Tendsto
      (fun t => visibleClassMass (Γ t) (x*scale t) j) atTop (𝓝 (prefixLaw pi k j)) := by
  obtain ⟨δ, hδ, hlo, hhi⟩ := off_tier_tolerance hk hxlo hxhi
  have he := routedTierError_tendsto_zero Γ scale ha hpactive hnorm hδ
  have hx : 0 ≤ x := le_of_lt ((by positivity : 0 < 1/((k : ℝ)+1)).trans hxlo)
  intro j hj
  have hy : Tendsto (fun t => if j ≤ k then actualRouteMass (Γ t) j else 0)
      atTop (𝓝 (prefixLaw pi k j)) := by
    by_cases hjk : j ≤ k
    · simpa only [hjk, if_true, prefixLaw] using
        hp j (Finset.mem_Icc.mpr ⟨Nat.zero_le j, (Finset.mem_Icc.mp hj).2⟩)
    · simpa only [hjk, if_false, prefixLaw] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  apply squeeze_count_error hy he
  filter_upwards [hscale] with t ht
  exact actual_off_tier_error (Γ t) ht (Finset.mem_Icc.mp hj).1 hx hlo hhi

theorem eventually_scale_pos_of_actual_tiers {M C : ℕ → ℕ}
    (Γ : ∀ t, FiniteGame (M t) n (C t) Seed) (scale : ℕ → ℝ)
    (ha : ∀ t, NonpositiveAbstention (Γ t))
    (hpactive : ∀ t, 0 < (Γ t).F.real (Ioi (Γ t).g))
    (hnorm : ProbZero (fun t => activeDrawLaw (Γ t))
      (fun t x => (x.2.routeCount : ℝ)*x.2.bid/scale t-1))
    {pi : ℕ → ℝ} (hp : RouteLimit Γ pi) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 n) (hpk : 0 < pi k) :
    ∀ᶠ t in atTop, 0 < scale t := by
  have he := routedTierError_tendsto_zero Γ scale ha hpactive hnorm
    (by norm_num : (0 : ℝ) < 1/2)
  have hp' := hp k (Finset.mem_Icc.mpr ⟨Nat.zero_le k, (Finset.mem_Icc.mp hk).2⟩)
  filter_upwards [he.eventually_lt_const (half_pos hpk),
    hp'.eventually_const_lt (show pi k/2 < pi k by linarith)] with t het hpt
  by_contra hs
  have hs0 : scale t ≤ 0 := le_of_not_gt hs
  have hsub : {x : ℝ × JointAction n | x.2.routeCount = k} ⊆
      routedTierError (Γ t) (scale t) (1/2) := by
    intro x hx
    change x.2.routeCount = k at hx
    have hxpos : 0 < x.2.routeCount := by
      have := (Finset.mem_Icc.mp hk).1
      omega
    have hn : 0 ≤ (x.2.routeCount : ℝ) * x.2.bid :=
      mul_nonneg (Nat.cast_nonneg _) x.2.bid_nonneg
    have hq : (x.2.routeCount : ℝ)*x.2.bid/scale t ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos hn hs0
    refine ⟨hxpos, ?_⟩
    rw [abs_of_nonpos (by linarith :
      (x.2.routeCount : ℝ)*x.2.bid/scale t-1 ≤ 0)]
    linarith
  have hm := measureReal_mono (μ := (Γ t).F ⊗ₘ (Γ t).σ) hsub
  change actualRouteMass (Γ t) k ≤ _ at hm
  linarith

theorem actual_positive_route_mass_tendsto {M C : ℕ → ℕ}
    (Γ : ∀ t, FiniteGame (M t) n (C t) Seed) (scale : ℕ → ℝ)
    (ha : ∀ t, NonpositiveAbstention (Γ t))
    (hpactive : ∀ t, 0 < (Γ t).F.real (Ioi (Γ t).g))
    (hnorm : ProbZero (fun t => activeDrawLaw (Γ t))
      (fun t x => (x.2.routeCount : ℝ)*x.2.bid/scale t-1))
    (hscale : ∀ᶠ t in atTop, 0 < scale t)
    {pi : ℕ → ℝ} (hp : RouteLimit Γ pi) {k : ℕ} (hk : k ∈ Finset.Icc 1 n) :
    Tendsto (fun t => positiveRouteMass (Γ t) (fun j => j=k)) atTop (𝓝 (pi k)) := by
  have he := routedTierError_tendsto_zero Γ scale ha hpactive hnorm
    (by norm_num : (0 : ℝ) < 1/2)
  apply squeeze_count_error
    (hp k (Finset.mem_Icc.mpr ⟨Nat.zero_le k, (Finset.mem_Icc.mp hk).2⟩)) he
  filter_upwards [hscale] with t ht
  apply real_event_error_of_agree_off ((Γ t).F ⊗ₘ (Γ t).σ)
    {x | 0 < x.2.bid ∧ 0 < x.2.routeCount ∧ x.2.routeCount=k}
    {x | x.2.routeCount=k} (routedTierError (Γ t) (scale t) (1/2))
  intro x hx
  constructor
  · exact fun hh => hh.2.2
  · intro hxk
    change x.2.routeCount = k at hxk
    have hk0 : 0 < x.2.routeCount := by have := (Finset.mem_Icc.mp hk).1; omega
    exact ⟨bid_pos_of_tierGood (Γ t) ht (by norm_num)
      (tierGood_of_not_error (Γ t) (scale t) (1/2) hk0 hx), hk0, hxk⟩

end FCAppendix.Bayes
