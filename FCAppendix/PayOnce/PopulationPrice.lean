import FCAppendix.PayOnce.KernelDemand
import Mathlib.MeasureTheory.Measure.Portmanteau

namespace FCAppendix.PayOnce.KernelDemand
open MeasureTheory ProbabilityTheory Filter Topology Set Real CommonList
open KernelLawConvergence KernelTailEvent

noncomputable def populationPrice (n : ℕ) (G : Measure ENNReal) (ρ : ℝ) : ℝ := by
  classical
  exact if h : ∃ L, 0 < L ∧ demand n G L = ρ then h.choose else 0

theorem populationPrice_spec {n : ℕ} {G : Measure ENNReal} {ρ : ℝ}
    (h : ∃ L, 0 < L ∧ demand n G L = ρ) :
    0 < populationPrice n G ρ ∧ demand n G (populationPrice n G ρ) = ρ := by
  simpa only [populationPrice,dif_pos h] using h.choose_spec

theorem demand_bracket_of_unique_root {n : ℕ} (hn : 2 ≤ n)
    (G : ProbabilityMeasure ENNReal) {L ρ ℓ u : ℝ}
    (hL : 0 < L) (hroot : demand n (G : Measure ENNReal) L = ρ)
    (huniq : ∀ T, 0 < T → demand n (G : Measure ENNReal) T = ρ → T = L)
    (hℓ : 0 < ℓ) (hℓL : ℓ < L) (hLu : L < u) :
    demand n (G : Measure ENNReal) u < ρ ∧ ρ < demand n (G : Measure ENNReal) ℓ := by
  constructor
  · have hle := demand_antitone hn (G : Measure ENNReal) hL (hL.trans hLu) hLu.le
    rw [hroot] at hle
    refine lt_of_le_of_ne hle ?_
    intro he
    exact hLu.ne' (huniq u (hL.trans hLu) he)
  · have hle := demand_antitone hn (G : Measure ENNReal) hℓ hL hℓL.le
    rw [hroot] at hle
    refine lt_of_le_of_ne hle ?_
    intro he
    exact hℓL.ne (huniq ℓ hℓ he.symm)

theorem roots_in_bracket {n : ℕ} (hn : 2 ≤ n) (G : ProbabilityMeasure ENNReal)
    {ρ ℓ u : ℝ} (hℓ : 0 < ℓ) (hℓu : ℓ < u)
    (hlo : ρ < demand n (G : Measure ENNReal) ℓ)
    (hhi : demand n (G : Measure ENNReal) u < ρ) :
    (∃ T, 0 < T ∧ demand n (G : Measure ENNReal) T = ρ) ∧
      ∀ T, 0 < T → demand n (G : Measure ENNReal) T = ρ → T ∈ Ioo ℓ u := by
  have hu : 0 < u := hℓ.trans hℓu
  have hall : ∀ T, 0 < T → demand n (G : Measure ENNReal) T = ρ → T ∈ Ioo ℓ u := by
    intro T hT hroot
    constructor
    · by_contra h
      have hh := demand_antitone hn (G : Measure ENNReal) hT hℓ (le_of_not_gt h)
      rw [hroot] at hh
      exact hlo.not_ge hh
    · by_contra h
      have hh := demand_antitone hn (G : Measure ENNReal) hu hT (le_of_not_gt h)
      rw [hroot] at hh
      exact hhi.not_ge hh
  obtain ⟨T,hT,hroot⟩ := intermediate_value_Icc' hℓu.le
    ((continuousOn_demand hn G).mono (fun _ hx => hℓ.trans_le hx.1)) ⟨hhi.le,hlo.le⟩
  exact ⟨⟨T,hℓ.trans_le hT.1,hroot⟩,hall⟩

theorem eventually_roots_in_bracket {n : ℕ} (hn : 2 ≤ n)
    {G : ℕ → ProbabilityMeasure ENNReal} {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto G atTop (𝓝 G₀)) {ρm : ℕ → ℝ} {ρ L ℓ u : ℝ}
    (hρ : Tendsto ρm atTop (𝓝 ρ)) (hL : 0 < L)
    (hroot : demand n (G₀ : Measure ENNReal) L = ρ)
    (huniq : ∀ T, 0 < T → demand n (G₀ : Measure ENNReal) T = ρ → T = L)
    (hℓ : 0 < ℓ) (hℓL : ℓ < L) (hLu : L < u) :
    ∀ᶠ m in atTop,
      (∃ T, 0 < T ∧ demand n (G m : Measure ENNReal) T = ρm m) ∧
      ∀ T, 0 < T → demand n (G m : Measure ENNReal) T = ρm m → T ∈ Ioo ℓ u := by
  have hd := demand_bracket_of_unique_root hn G₀ hL hroot huniq hℓ hℓL hLu
  have hlo := tendsto_demand hn hweak (fun _ => hℓ) hℓ tendsto_const_nhds
  have hhi := tendsto_demand hn hweak (fun _ => hL.trans hLu) (hL.trans hLu) tendsto_const_nhds
  filter_upwards [hhi.eventually_lt hρ hd.1,
    hρ.eventually_lt hlo hd.2] with m hmhi hmlo
  exact roots_in_bracket hn (G m) hℓ (hℓL.trans hLu) hmlo hmhi

theorem root_unique_of_interior_window {n : ℕ} (hn : 2 ≤ n)
    (G : ProbabilityMeasure ENNReal) {ℓ u a z T U ρ : ℝ}
    (hℓ : 0 < ℓ) (hT : T ∈ Icc ℓ u) (hU : U ∈ Icc ℓ u)
    (hua : u < a) (hz : z < (n:ℝ)*ℓ)
    (hwin : 0 < (G : Measure ENNReal) (Ioo (ENNReal.ofReal a) (ENNReal.ofReal z)))
    (hrT : demand n (G : Measure ENNReal) T = ρ)
    (hrU : demand n (G : Measure ENNReal) U = ρ) : T = U := by
  have hposT : 0 < T := hℓ.trans_le hT.1
  have hposU : 0 < U := hℓ.trans_le hU.1
  have hno (R : ℝ) (hR : R ∈ Icc ℓ u) :
      ¬ (∀ᵐ b ∂(G : Measure ENNReal), compactKernel n b R = 0 ∨ compactKernel n b R = 1) := by
    intro he
    have hRpos : 0 < R := hℓ.trans_le hR.1
    have hne : ∀ᵐ b ∂(G : Measure ENNReal), b ∉ Ioo (ENNReal.ofReal a) (ENNReal.ofReal z) := by
      filter_upwards [he] with b hb hbw
      have htop : b ≠ ⊤ := ne_top_of_lt hbw.2
      have ha : 0 < a := (hℓ.trans_le hR.1).trans (hR.2.trans_lt hua)
      have haz : a < b.toReal := by
        have hh := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top htop).mpr hbw.1
        simpa only [ENNReal.toReal_ofReal ha.le] using hh
      have hzz : b.toReal < z := by
        have hzpos : 0 < z := by
          have h := hbw.1.trans hbw.2
          exact ha.trans (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha.le |>.mp h)
        have hh := (ENNReal.toReal_lt_toReal htop ENNReal.ofReal_ne_top).mpr hbw.2
        simpa only [ENNReal.toReal_ofReal hzpos.le] using hh
      have hbpos : 0 < b.toReal := ha.trans haz
      have hbR : R < b.toReal := (hR.2.trans_lt hua).trans haz
      have hnR : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
      have hbn : b.toReal < (n:ℝ)*R := hzz.trans (hz.trans_le
        (mul_le_mul_of_nonneg_left hR.1 hnR.le))
      simp only [compactKernel,if_neg htop] at hb
      rcases hb with hb | hb
      · exact hbR.not_ge ((kernel_eq_zero_iff n hn hbpos hRpos).mp hb)
      · have hh := (kernel_eq_one_iff n (by omega) hbpos hRpos).mp hb
        have hhh := (le_div_iff₀ hnR).mp hh
        nlinarith
    apply hwin.ne'
    have hh := hne
    rw [ae_iff] at hh
    simpa only [not_not,Set.setOf_mem_eq] using hh
  rcases lt_trichotomy T U with h | h | h
  · exact False.elim (hno T hT (ae_endpoints_of_two_roots hn G hposT h hrT hrU))
  · exact h
  · exact False.elim (hno U hU (ae_endpoints_of_two_roots hn G hposU h hrU hrT))

theorem eventually_unique_population_price {n : ℕ} (hn : 2 ≤ n)
    {G : ℕ → ProbabilityMeasure ENNReal} {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto G atTop (𝓝 G₀)) {ρm : ℕ → ℝ} {ρ L : ℝ}
    (hρ : Tendsto ρm atTop (𝓝 ρ)) (hL : 0 < L)
    (hroot : demand n (G₀ : Measure ENNReal) L = ρ)
    (huniq : ∀ T, 0 < T → demand n (G₀ : Measure ENNReal) T = ρ → T = L)
    (hwindow : ∃ a z : ℝ, L < a ∧ a < z ∧ z < (n:ℝ)*L ∧
      0 < (G₀ : Measure ENNReal) (Ioo (ENNReal.ofReal a) (ENNReal.ofReal z))) :
    ∀ᶠ m in atTop, ∃! T, 0 < T ∧ demand n (G m : Measure ENNReal) T = ρm m := by
  obtain ⟨a,z,ha,_haz,hz,hwin⟩ := hwindow
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  obtain ⟨ℓ,hℓ,hℓL⟩ := exists_between (show max (z/(n:ℝ)) 0 < L from
    max_lt ((div_lt_iff₀ hnR).mpr (by nlinarith)) hL)
  have hℓpos : 0 < ℓ := (le_max_right _ _).trans_lt hℓ
  have hzℓ : z < (n:ℝ)*ℓ := by
    have hh := (div_lt_iff₀ hnR).mp ((le_max_left _ _).trans_lt hℓ)
    nlinarith
  obtain ⟨u,hLu,hua⟩ := exists_between ha
  have hport := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak
    (isOpen_Ioo (a := ENNReal.ofReal a) (b := ENNReal.ofReal z))
  have hmwin := eventually_lt_of_lt_liminf (hwin.trans_le hport)
  filter_upwards [eventually_roots_in_bracket hn hweak hρ hL hroot huniq hℓpos hℓL hLu,
    hmwin] with m hm hw
  obtain ⟨T,hT,hD⟩ := hm.1
  refine ⟨T,⟨hT,hD⟩,fun U hU => ?_⟩
  exact root_unique_of_interior_window hn (G m) hℓpos
    (Ioo_subset_Icc_self (hm.2 U hU.1 hU.2)) (Ioo_subset_Icc_self (hm.2 T hT hD))
    hua hzℓ hw hU.2 hD

theorem tendsto_population_price {n : ℕ} (hn : 2 ≤ n)
    {G : ℕ → ProbabilityMeasure ENNReal} {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto G atTop (𝓝 G₀)) {ρm : ℕ → ℝ} {ρ L : ℝ}
    (hρ : Tendsto ρm atTop (𝓝 ρ)) (hL : 0 < L)
    (hroot : demand n (G₀ : Measure ENNReal) L = ρ)
    (huniq : ∀ T, 0 < T → demand n (G₀ : Measure ENNReal) T = ρ → T = L) :
    Tendsto (fun m => populationPrice n (G m : Measure ENNReal) (ρm m)) atTop (𝓝 L) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ := min (L/2) (ε/2)
  have hδ : 0 < δ := lt_min (half_pos hL) (half_pos hε)
  have hlo : 0 < L-δ := by dsimp only [δ]; linarith [min_le_left (L/2) (ε/2)]
  have hδε : δ < ε := (min_le_right (L/2) (ε/2)).trans_lt (by linarith)
  filter_upwards [eventually_roots_in_bracket hn hweak hρ hL hroot huniq hlo
    (by linarith : L-δ<L) (by linarith : L<L+δ)] with m hm
  have hp := populationPrice_spec hm.1
  have hb := hm.2 _ hp.1 hp.2
  rw [Real.dist_eq,abs_lt]
  constructor <;> linarith [hb.1,hb.2]

end FCAppendix.PayOnce.KernelDemand
