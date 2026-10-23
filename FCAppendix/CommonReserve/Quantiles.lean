import FCAppendix.CommonReserve.UniformTies
import FCAppendix.Finite.VisibleQuantiles
import FCAppendix.Probability.PiBinomialMoments

noncomputable section
namespace FCAppendix.CommonReserve
open Game MeasureTheory ProbabilityTheory Filter Set Topology
variable {m n c : ℕ} {r : ℝ} {Seed : Type*} [MeasurableSpace Seed]

def aboveAt (j : Fin n) (b : ℝ) : Set (UserDraw n r) :=
  {d | d.2.val j ≠ none ∧ b < Bayes.entryBid (d.2.val j)}

theorem mem_aboveAt_iff (j : Fin n) (b : ℝ) (d : UserDraw n r) :
    d ∈ aboveAt j b ↔ ∃ t, d.2.val j = some t ∧ b < t := by
  cases he : d.2.val j <;> simp [aboveAt, he, Bayes.entryBid]

theorem measurable_coordinate (j : Fin n) :
    Measurable (fun d : UserDraw n r => d.2.val j) :=
  (measurable_pi_apply j).comp (measurable_subtype_coe.comp measurable_snd)

theorem measurable_coordinateBid (j : Fin n) :
    Measurable (fun d : UserDraw n r => Bayes.entryBid (d.2.val j)) :=
  Bayes.measurable_entryBid.comp (measurable_coordinate j)

theorem measurableSet_aboveAt (j : Fin n) (b : ℝ) : MeasurableSet (aboveAt (r := r) j b) :=
  ((measurable_coordinate j) (measurableSet_singleton none)).compl.inter
    (measurableSet_lt measurable_const (measurable_coordinateBid j))

def bidTail (Γ : FiniteGame m n c r Seed) (j : Fin n) (b : ℝ) : ℝ :=
  Γ.userLaw.real (aboveAt j b)

theorem bidTail_nonneg (Γ : FiniteGame m n c r Seed) (j : Fin n) (b : ℝ) :
    0 ≤ bidTail Γ j b := measureReal_nonneg

theorem bidTail_le_one (Γ : FiniteGame m n c r Seed) (j : Fin n) (b : ℝ) :
    bidTail Γ j b ≤ 1 := measureReal_le_one

theorem bidTail_antitone (Γ : FiniteGame m n c r Seed) (j : Fin n) : Antitone (bidTail Γ j) := by
  intro b d hbd
  exact measureReal_mono (fun _ h => ⟨h.1, hbd.trans_lt h.2⟩)

theorem measurable_bidTail (Γ : FiniteGame m n c r Seed) (j : Fin n) :
    Measurable (bidTail Γ j) := (bidTail_antitone Γ j).measurable

theorem bidTail_tendsto_zero (Γ : FiniteGame m n c r Seed) (j : Fin n) :
    Tendsto (bidTail Γ j) atTop (𝓝 0) := by
  let f : UserDraw n r → ℝ := fun d => Bayes.entryBid (d.2.val j)
  have hf : Measurable f := measurable_coordinateBid j
  haveI : IsProbabilityMeasure (Γ.userLaw.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  have ht := TailQuantile.tail_tendsto_zero (Γ.userLaw.map f)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (bidTail_nonneg Γ j)
  intro b
  change Γ.userLaw.real (aboveAt j b) ≤ (Γ.userLaw.map f).real (Ioi b)
  have hmap : (Γ.userLaw.map f).real (Ioi b) = Γ.userLaw.real (f ⁻¹' Ioi b) := by
    simp only [Measure.real, Measure.map_apply hf measurableSet_Ioi]
  rw [hmap]
  exact measureReal_mono (fun _ h => h.2)

namespace ReserveQuantile

def quantile (α : ℝ → ℝ) (r q : ℝ) : ℝ := sInf {b | r ≤ b ∧ α b ≤ q}

theorem nonempty {α : ℝ → ℝ} {r q : ℝ} (hq : 0 < q)
    (ht : Tendsto α atTop (𝓝 0)) : {b | r ≤ b ∧ α b ≤ q}.Nonempty := by
  obtain ⟨b, hb, hα⟩ := ((eventually_ge_atTop r).and (ht.eventually (gt_mem_nhds hq))).exists
  exact ⟨b, hb, hα.le⟩

theorem reserve_le {α : ℝ → ℝ} {r q : ℝ}
    (hne : {b | r ≤ b ∧ α b ≤ q}.Nonempty) : r ≤ quantile α r q :=
  le_csInf hne (fun _ h => h.1)

theorem le_of_tail_le {α : ℝ → ℝ} {r q b : ℝ} (hb : r ≤ b) (hα : α b ≤ q) :
    quantile α r q ≤ b := csInf_le ⟨r, fun _ h => h.1⟩ ⟨hb, hα⟩

theorem tail_le_above {α : ℝ → ℝ} (hα : Antitone α) {r q : ℝ}
    (hne : {b | r ≤ b ∧ α b ≤ q}.Nonempty) {d : ℝ} (hd : 0 < d) :
    α (quantile α r q + d) ≤ q := by
  obtain ⟨b, hb, hlt⟩ := exists_lt_of_csInf_lt hne
    (show quantile α r q < quantile α r q + d by linarith)
  exact (hα hlt.le).trans hb.2

theorem lt_tail_below {α : ℝ → ℝ} {r q b : ℝ} (hb : r ≤ b)
    (hlt : b < quantile α r q) : q < α b := by
  by_contra h
  exact (not_le_of_gt hlt) (le_of_tail_le hb (le_of_not_gt h))

end ReserveQuantile

def quantile (Γ : FiniteGame m n c r Seed) (j : Fin n) (δ : ℝ) : ℝ :=
  ReserveQuantile.quantile (bidTail Γ j) r ((c : ℝ) / m - δ)

def price (Γ : FiniteGame m n c r Seed) (δ : ℝ) : ℝ :=
  sInf (Set.range (fun j : Fin n => quantile Γ j δ))

theorem price_le_quantile (Γ : FiniteGame m n c r Seed) (δ : ℝ) (j : Fin n) :
    price Γ δ ≤ quantile Γ j δ :=
  csInf_le (Set.finite_range _).bddBelow ⟨j, rfl⟩

theorem exists_price_minimizer (Γ : FiniteGame m n c r Seed) (δ : ℝ) (hn : 0 < n) :
    ∃ j : Fin n, price Γ δ = quantile Γ j δ := by
  classical
  obtain ⟨j, _, hj⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin n))
    (fun j => quantile Γ j δ) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  refine ⟨j, le_antisymm (price_le_quantile Γ δ j) ?_⟩
  apply le_csInf (show (Set.range (fun l : Fin n => quantile Γ l δ)).Nonempty from
    ⟨quantile Γ j δ, ⟨j, rfl⟩⟩)
  rintro _ ⟨l, rfl⟩
  exact hj l (Finset.mem_univ l)

theorem reserve_le_quantile (Γ : FiniteGame m n c r Seed) (j : Fin n) (δ : ℝ)
    (hδκ : δ < (c : ℝ) / m) : r ≤ quantile Γ j δ :=
  ReserveQuantile.reserve_le (ReserveQuantile.nonempty (sub_pos.mpr hδκ) (bidTail_tendsto_zero Γ j))

theorem quantile_mono_slack (Γ : FiniteGame m n c r Seed) (j : Fin n)
    {δ ε : ℝ} (hδε : δ ≤ ε) (hεκ : ε < (c : ℝ) / m) :
    quantile Γ j δ ≤ quantile Γ j ε := by
  apply le_csInf (ReserveQuantile.nonempty (sub_pos.mpr hεκ) (bidTail_tendsto_zero Γ j))
  intro b hb
  apply ReserveQuantile.le_of_tail_le hb.1
  exact hb.2.trans (by linarith)

theorem measurable_quantile_slack (Γ : FiniteGame m n c r Seed) (j : Fin n) :
    Measurable (fun δ : Iio ((c : ℝ) / m) => quantile Γ j δ.val) := by
  apply Monotone.measurable
  intro δ ε hδε
  exact quantile_mono_slack Γ j hδε ε.property

theorem reserve_le_price (Γ : FiniteGame m n c r Seed) (δ : ℝ) (hn : 0 < n)
    (hδκ : δ < (c : ℝ) / m) : r ≤ price Γ δ := by
  obtain ⟨j, hj⟩ := exists_price_minimizer Γ δ hn
  rw [hj]
  exact reserve_le_quantile Γ j δ hδκ

theorem price_nonneg (Γ : FiniteGame m n c r Seed) (δ : ℝ) (hn : 0 < n)
    (hδκ : δ < (c : ℝ) / m) : 0 ≤ price Γ δ :=
  Γ.reserve_nonneg.trans (reserve_le_price Γ δ hn hδκ)

theorem quantile_tail_above (Γ : FiniteGame m n c r Seed) (j : Fin n) (δ d : ℝ)
    (hδκ : δ < (c : ℝ) / m) (hd : 0 < d) :
    bidTail Γ j (quantile Γ j δ + d) ≤ (c : ℝ) / m - δ :=
  ReserveQuantile.tail_le_above (bidTail_antitone Γ j)
    (ReserveQuantile.nonempty (sub_pos.mpr hδκ) (bidTail_tendsto_zero Γ j)) hd

theorem price_tail_below (Γ : FiniteGame m n c r Seed) (δ b : ℝ)
    (hb : r ≤ b) (hbp : b < price Γ δ) (j : Fin n) :
    (c : ℝ) / m - δ < bidTail Γ j b :=
  ReserveQuantile.lt_tail_below hb (hbp.trans_le (price_le_quantile Γ δ j))

end FCAppendix.CommonReserve
