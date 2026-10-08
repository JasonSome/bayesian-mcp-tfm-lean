import FCAppendix.PayOnce.CompactifiedBidLaws

namespace FCAppendix.PayOnce.BidScaling
open MeasureTheory ProbabilityTheory Filter Topology Set
open FCAppendix.PayOnce.CompactifiedBidLaws

theorem iInter_nat_upper_tails :
    (⋂ k : ℕ, Ici (ENNReal.ofReal (k : ℝ))) = ({⊤} : Set ENNReal) := by
  ext b
  simp only [mem_iInter, mem_Ici, mem_singleton_iff]
  constructor
  · intro hb
    by_contra hbt
    obtain ⟨k, hk⟩ := exists_nat_gt b.toReal
    have hh := ENNReal.toReal_mono hbt (hb k)
    rw [ENNReal.toReal_ofReal (Nat.cast_nonneg k)] at hh
    exact hk.not_ge hh
  · intro hb
    subst b
    exact fun _ => le_top

theorem infinity_mass_ge_of_eventual_tails
    {G : ℕ → ProbabilityMeasure ENNReal} {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto G atTop (𝓝 G₀)) {q : ENNReal}
    (htail : ∀ k : ℕ, ∀ᶠ m in atTop,
      q ≤ (G m : Measure ENNReal) (Ici (ENNReal.ofReal (k : ℝ)))) :
    q ≤ (G₀ : Measure ENNReal) {⊤} := by
  have hbound (k : ℕ) : q ≤ (G₀ : Measure ENNReal) (Ici (ENNReal.ofReal (k : ℝ))) :=
    (le_limsup_of_frequently_le (htail k).frequently).trans
      (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hweak isClosed_Ici)
  have hanti : Antitone (fun k : ℕ => Ici (ENNReal.ofReal (k : ℝ))) := by
    intro i j hij
    exact Ici_subset_Ici.mpr (ENNReal.ofReal_le_ofReal (by exact_mod_cast hij))
  have hi := hanti.measure_iInter
    (fun _ => measurableSet_Ici.nullMeasurableSet) (μ := (G₀ : Measure ENNReal))
    ⟨0, measure_ne_top _ _⟩
  rw [iInter_nat_upper_tails] at hi
  rw [hi]
  exact le_iInf hbound

theorem scaled_infinity_mass_ge
    {G : ℕ → ProbabilityMeasure ℝ} {a : ℕ → ℝ} {G₀ : ProbabilityMeasure ENNReal}
    (ha : ∀ m, 0 < a m) (ha0 : Tendsto a atTop (𝓝 0))
    (hweak : Tendsto (fun m => scaledLaw (G m) (a m)) atTop (𝓝 G₀))
    {u : ℝ} (hu : 0 < u) {q : ENNReal}
    (htail : ∀ᶠ m in atTop, q ≤ (G m : Measure ℝ) (Ioi u)) :
    q ≤ (G₀ : Measure ENNReal) {⊤} := by
  apply infinity_mass_ge_of_eventual_tails hweak
  intro k
  have hsmall : ∀ᶠ m in atTop, (k : ℝ) * a m ≤ u :=
    (ha0.const_mul (k : ℝ)).eventually_le_const (by simpa using hu)
  filter_upwards [htail, hsmall] with m hm hma
  apply hm.trans
  change (G m : Measure ℝ) (Ioi u) ≤
    (Measure.map (fun b : ℝ => ENNReal.ofReal (b / a m)) (G m : Measure ℝ))
      (Ici (ENNReal.ofReal (k : ℝ)))
  rw [Measure.map_apply (show Measurable (fun b : ℝ => ENNReal.ofReal (b / a m)) from
    ENNReal.measurable_ofReal.comp (measurable_id.div_const (a m))) measurableSet_Ici]
  apply measure_mono
  intro b hb
  exact ENNReal.ofReal_le_ofReal ((le_div_iff₀ (ha m)).mpr (hma.trans hb.le))

theorem scaledLaw_one_tail (G : ProbabilityMeasure ℝ) {u : ℝ} (hu : 0 ≤ u) :
    (scaledLaw G 1 : Measure ENNReal) (Ioi (ENNReal.ofReal u)) = (G : Measure ℝ) (Ioi u) := by
  change (Measure.map (fun b : ℝ => ENNReal.ofReal (b / 1)) (G : Measure ℝ))
    (Ioi (ENNReal.ofReal u)) = _
  rw [Measure.map_apply (show Measurable (fun b : ℝ => ENNReal.ofReal (b / 1)) from
    ENNReal.measurable_ofReal.comp (measurable_id.div_const 1)) measurableSet_Ioi]
  congr 1
  ext b
  simp only [mem_preimage, mem_Ioi, div_one, ENNReal.ofReal_lt_ofReal_iff_of_nonneg hu]

theorem scaled_infinity_mass_ge_of_original_weak
    {G : ℕ → ProbabilityMeasure ℝ} {a : ℕ → ℝ}
    {Gorig Gscaled : ProbabilityMeasure ENNReal}
    (ha : ∀ m, 0 < a m) (ha0 : Tendsto a atTop (𝓝 0))
    (hweakOrig : Tendsto (fun m => scaledLaw (G m) 1) atTop (𝓝 Gorig))
    (hweakScaled : Tendsto (fun m => scaledLaw (G m) (a m)) atTop (𝓝 Gscaled))
    {u : ℝ} (hu : 0 < u) {q : ENNReal}
    (hq : q < (Gorig : Measure ENNReal) (Ioi (ENNReal.ofReal u))) :
    q ≤ (Gscaled : Measure ENNReal) {⊤} := by
  have hport := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweakOrig
    (isOpen_Ioi (a := ENNReal.ofReal u))
  have he := eventually_lt_of_lt_liminf (hq.trans_le hport)
  apply scaled_infinity_mass_ge ha ha0 hweakScaled hu
  filter_upwards [he] with m hm
  rw [scaledLaw_one_tail (G m) hu.le] at hm
  exact hm.le

theorem scaled_infinity_mass_gt_capacity
    {G : ℕ → ProbabilityMeasure ℝ} {a : ℕ → ℝ}
    {Gorig Gscaled : ProbabilityMeasure ENNReal}
    (ha : ∀ m, 0 < a m) (ha0 : Tendsto a atTop (𝓝 0))
    (hweakOrig : Tendsto (fun m => scaledLaw (G m) 1) atTop (𝓝 Gorig))
    (hweakScaled : Tendsto (fun m => scaledLaw (G m) (a m)) atTop (𝓝 Gscaled))
    {u ρ : ℝ} (hu : 0 < u) (hρ : 0 ≤ ρ)
    (hmass : ρ < (Gorig : Measure ENNReal).real (Ioi (ENNReal.ofReal u))) :
    ρ < (Gscaled : Measure ENNReal).real {⊤} := by
  have hmassE : ENNReal.ofReal ρ < (Gorig : Measure ENNReal) (Ioi (ENNReal.ofReal u)) := by
    apply (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top (measure_ne_top _ _)).mp
    simpa only [Measure.real, ENNReal.toReal_ofReal hρ] using hmass
  obtain ⟨q, hρq, hq⟩ := exists_between hmassE
  have hh := hρq.trans_le
    (scaled_infinity_mass_ge_of_original_weak ha ha0 hweakOrig hweakScaled hu hq)
  have hr := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top (measure_ne_top _ _)).mpr hh
  simpa only [Measure.real, ENNReal.toReal_ofReal hρ] using hr

open FCAppendix.Game FCAppendix.Bayes

noncomputable def realBidLaw {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m n c Seed) : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map (⟨userLaw Γ, inferInstance⟩ : ProbabilityMeasure (UserDraw n))
    (f := fun d => effectiveBid d.1.2)
    ((measurable_effectiveBid n).comp (measurable_snd.comp measurable_fst)).aemeasurable

theorem scaled_realBidLaw_one {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m n c Seed) : scaledLaw (realBidLaw Γ) 1 = bidLaw Γ := by
  apply Subtype.ext
  change Measure.map (fun b : ℝ => ENNReal.ofReal (b / 1))
    (Measure.map (fun d : UserDraw n => effectiveBid d.1.2) (userLaw Γ)) =
      Measure.map (fun d : UserDraw n => ENNReal.ofReal (effectiveBid d.1.2)) (userLaw Γ)
  rw [Measure.map_map (show Measurable (fun b : ℝ => ENNReal.ofReal (b / 1)) from
    ENNReal.measurable_ofReal.comp (measurable_id.div_const 1))
    (show Measurable (fun d : UserDraw n => effectiveBid d.1.2) from
      (measurable_effectiveBid n).comp (measurable_snd.comp measurable_fst))]
  simp only [Function.comp_def, div_one]

theorem actual_scaled_subsequence_infinity
    {m n c : ℕ → ℕ} {Seed : ℕ → Type*} [∀ j, MeasurableSpace (Seed j)]
    (Γ : ∀ j, FiniteGame (m j) (n j) (c j) (Seed j))
    {Gorig : ProbabilityMeasure ENNReal}
    (hweakOrig : Tendsto (fun j => bidLaw (Γ j)) atTop (𝓝 Gorig))
    {a : ℕ → ℝ} (ha : ∀ j, 0 < a j) (ha0 : Tendsto a atTop (𝓝 0))
    {u ρ : ℝ} (hu : 0 < u) (hρ : 0 ≤ ρ)
    (hmass : ρ < (Gorig : Measure ENNReal).real (Ioi (ENNReal.ofReal u))) :
    ∃ Gscaled : ProbabilityMeasure ENNReal, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun j => scaledLaw (realBidLaw (Γ (φ j))) (a (φ j))) atTop (𝓝 Gscaled) ∧
      ρ < (Gscaled : Measure ENNReal).real {⊤} := by
  obtain ⟨Gscaled, φ, hφ, hweakScaled⟩ := exists_scaled_subsequence (fun j => realBidLaw (Γ j)) a
  have horig : Tendsto (fun j => scaledLaw (realBidLaw (Γ (φ j))) 1) atTop (𝓝 Gorig) := by
    simpa only [scaled_realBidLaw_one, Function.comp_def] using hweakOrig.comp hφ.tendsto_atTop
  exact ⟨Gscaled, φ, hφ, hweakScaled, scaled_infinity_mass_gt_capacity
    (fun j => ha (φ j)) (ha0.comp hφ.tendsto_atTop) horig hweakScaled hu hρ hmass⟩

end FCAppendix.PayOnce.BidScaling
