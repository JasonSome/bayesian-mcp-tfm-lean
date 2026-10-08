import FCAppendix.PayOnce.KernelLawConvergence
import FCAppendix.Finite.NoOverbidAE
import FCAppendix.Finite.VisibleQuantiles
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Portmanteau

namespace FCAppendix.PayOnce.CompactifiedBidLaws
open MeasureTheory ProbabilityTheory Filter Topology Set

noncomputable def scaledLaw (G : ProbabilityMeasure ℝ) (a : ℝ) : ProbabilityMeasure ENNReal :=
  G.map (ENNReal.measurable_ofReal.comp (measurable_id.div_const a)).aemeasurable

theorem exists_scaled_subsequence (G : ℕ → ProbabilityMeasure ℝ) (a : ℕ → ℝ) :
    ∃ μ : ProbabilityMeasure ENNReal, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun m => scaledLaw (G (φ m)) (a (φ m))) atTop (𝓝 μ) := by
  exact CompactSpace.tendsto_subseq (fun m => scaledLaw (G m) (a m))

theorem infinity_mass_zero_of_uniform_tails
    {G : ℕ → ProbabilityMeasure ENNReal} {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto G atTop (𝓝 G₀))
    (htails : ∀ ε : ENNReal, 0 < ε → ∃ R : ENNReal, R < ⊤ ∧
      ∀ m, (G m : Measure ENNReal) (Ioi R) ≤ ε) :
    (G₀ : Measure ENNReal) {⊤} = 0 := by
  apply le_antisymm ?_ bot_le
  apply le_of_forall_gt
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := exists_between hε
  obtain ⟨R, hR, htail⟩ := htails δ hδ
  have hport := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak
    (isOpen_Ioi (a := R))
  have hlim : liminf (fun m => (G m : Measure ENNReal) (Ioi R)) atTop ≤ δ :=
    liminf_le_of_frequently_le (Filter.Eventually.of_forall htail).frequently
  have hsub : ({⊤} : Set ENNReal) ⊆ Ioi R := by
    intro b hb
    simpa only [mem_singleton_iff.mp hb, mem_Ioi] using hR
  exact ((measure_mono hsub).trans (hport.trans hlim)).trans_lt hδε

open FCAppendix.Game FCAppendix.Bayes

noncomputable def effectiveBid {n : ℕ} (a : JointAction n) : ℝ :=
  if a.routeCount = 0 then 0 else a.bid

theorem measurable_effectiveBid (n : ℕ) : Measurable (@effectiveBid n) :=
  Measurable.ite ((measurable_routeCount n) (measurableSet_singleton 0))
    measurable_const (measurable_bid n)

noncomputable def bidLaw {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m n c Seed) : ProbabilityMeasure ENNReal :=
  ProbabilityMeasure.map (⟨userLaw Γ, inferInstance⟩ : ProbabilityMeasure (UserDraw n))
    (f := fun d => ENNReal.ofReal (effectiveBid d.1.2))
    (((ENNReal.measurable_ofReal.comp (measurable_effectiveBid n)).comp
      (measurable_snd.comp measurable_fst)).aemeasurable)

theorem bidLaw_tail_le_value {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m n c Seed) (hm : 0 < m) (hc : 0 < c) (hΓ : IsAEEquilibrium Γ)
    {M : ℝ} (hM : 0 ≤ M) :
    (bidLaw Γ : Measure ENNReal) (Ioi (ENNReal.ofReal M)) ≤ Γ.F (Ioi M) := by
  have hmeas : Measurable (fun d : UserDraw n => ENNReal.ofReal (effectiveBid d.1.2)) :=
    (ENNReal.measurable_ofReal.comp (measurable_effectiveBid n)).comp
      (measurable_snd.comp measurable_fst)
  change (Measure.map (fun d : UserDraw n => ENNReal.ofReal (effectiveBid d.1.2))
    (userLaw Γ)) (Ioi (ENNReal.ofReal M)) ≤ Γ.F (Ioi M)
  rw [Measure.map_apply hmeas measurableSet_Ioi]
  have hsub : {d : UserDraw n | ENNReal.ofReal M < ENNReal.ofReal (effectiveBid d.1.2)} ≤ᵐ[userLaw Γ]
      {d : UserDraw n | M < d.1.1} := by
    filter_upwards [ae_no_overbid_userLaw_onPath Γ hm hc hΓ] with d hd hb
    have hbid : M < effectiveBid d.1.2 := lt_of_not_ge
      (fun hle => hb.not_ge (ENNReal.ofReal_le_ofReal hle))
    by_cases hk : d.1.2.routeCount = 0
    · simp only [effectiveBid, hk, if_pos] at hbid
      exact (hbid.not_ge hM).elim
    · have hno := hd (Nat.pos_of_ne_zero hk)
      simp only [effectiveBid, hk, if_false] at hbid
      rcases (lt_max_iff).mp (hbid.trans_le hno) with h | h
      · change M < d.1.1
        linarith [Γ.g_nonneg]
      · exact (h.not_ge hM).elim
  have hh := measure_mono_ae hsub
  have he : userLaw Γ {d : UserDraw n | M < d.1.1} = Γ.F (Ioi M) := by
    rw [← userLaw_value_map Γ, Measure.map_apply
      (show Measurable (fun d : UserDraw n => d.1.1) from
        measurable_fst.comp measurable_fst) measurableSet_Ioi]
    rfl
  exact hh.trans_eq he

theorem equilibrium_limit_no_infinity
    {m n c : ℕ → ℕ} {Seed : ℕ → Type*} [∀ j, MeasurableSpace (Seed j)]
    (Γ : ∀ j, FiniteGame (m j) (n j) (c j) (Seed j))
    (hm : ∀ j, 0 < m j) (hc : ∀ j, 0 < c j) (hΓ : ∀ j, IsAEEquilibrium (Γ j))
    (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ∀ j, (Γ j).F = F)
    {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun j => bidLaw (Γ j)) atTop (𝓝 G₀)) :
    (G₀ : Measure ENNReal) {⊤} = 0 := by
  apply infinity_mass_zero_of_uniform_tails hweak
  intro ε hε
  by_cases hεtop : ε = ⊤
  · exact ⟨0, by simp, fun _ => hεtop ▸ le_top⟩
  · have hεR : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
    obtain ⟨M, hM, htail⟩ := ((eventually_ge_atTop (0 : ℝ)).and
      ((TailQuantile.tail_tendsto_zero F).eventually_lt_const hεR)).exists
    refine ⟨ENNReal.ofReal M, ENNReal.ofReal_lt_top, fun j => ?_⟩
    have hbound := bidLaw_tail_le_value (Γ j) (hm j) (hc j) (hΓ j) hM
    rw [hF j] at hbound
    exact hbound.trans ((ENNReal.toReal_le_toReal (measure_ne_top F _) hεtop).mp htail.le)

theorem equilibrium_bidLaw_subsequence
    {m n c : ℕ → ℕ} {Seed : ℕ → Type*} [∀ j, MeasurableSpace (Seed j)]
    (Γ : ∀ j, FiniteGame (m j) (n j) (c j) (Seed j))
    (hm : ∀ j, 0 < m j) (hc : ∀ j, 0 < c j) (hΓ : ∀ j, IsAEEquilibrium (Γ j))
    (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ∀ j, (Γ j).F = F) :
    ∃ G₀ : ProbabilityMeasure ENNReal, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun j => bidLaw (Γ (φ j))) atTop (𝓝 G₀) ∧
      (G₀ : Measure ENNReal) {⊤} = 0 := by
  obtain ⟨G₀, φ, hφ, hweak⟩ := CompactSpace.tendsto_subseq (fun j => bidLaw (Γ j))
  exact ⟨G₀, φ, hφ, hweak, equilibrium_limit_no_infinity (fun j => Γ (φ j))
    (fun j => hm (φ j)) (fun j => hc (φ j)) (fun j => hΓ (φ j)) F
    (fun j => hF (φ j)) hweak⟩

end FCAppendix.PayOnce.CompactifiedBidLaws
