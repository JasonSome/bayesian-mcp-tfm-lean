import FCAppendix.Ample.RouteIdentificationTierLaw
import FCAppendix.Ample.RankMeasureBasics
import FCAppendix.Ample.BoundaryRankAlgebra

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology Real
open scoped ENNReal BigOperators
open Ample Ample.DownstreamNormalizationCore

namespace RouteIdentificationDetails
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma sum_Icc_head {k n : ℕ} (hk : k ≤ n) (p : ℕ → ℝ) :
    (∑ j ∈ Finset.Icc k n, p j) = p k + ∑ j ∈ Finset.Icc (k+1) n, p j := by
  classical
  have he : Finset.Icc k n = insert k (Finset.Icc (k+1) n) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [he, Finset.sum_insert]
  simp only [Finset.mem_Icc]
  omega

lemma suffix_nonneg {n : ℕ} {p : ℕ → ℝ}
    (hp : ∀ j ∈ Finset.Icc 1 n, 0 ≤ p j) {a : ℕ} (ha : 1 ≤ a) :
    0 ≤ ∑ j ∈ Finset.Icc a n, p j := by
  apply Finset.sum_nonneg
  intro j hj
  exact hp j (Finset.mem_Icc.mpr
    ⟨ha.trans (Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2⟩)

lemma suffix_mono {n : ℕ} {p : ℕ → ℝ}
    (hp : ∀ j ∈ Finset.Icc 1 n, 0 ≤ p j) {a b : ℕ}
    (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ j ∈ Finset.Icc b n, p j) ≤ ∑ j ∈ Finset.Icc a n, p j := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    exact Finset.mem_Icc.mpr ⟨hab.trans (Finset.mem_Icc.mp hj).1,
      (Finset.mem_Icc.mp hj).2⟩
  · intro j hj _
    exact hp j (Finset.mem_Icc.mpr
      ⟨ha.trans (Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2⟩)

lemma edge_bounds {n k : ℕ} {p : ℕ → ℝ} {h : ℝ}
    (hk : k ∈ Finset.Icc 1 n) (hp : ∀ j ∈ Finset.Icc 1 n, 0 ≤ p j)
    (hmass : (∑ j ∈ Finset.Icc 1 n, p j) = h) :
    0 ≤ rankLowerEdge n k p ∧
      rankLowerEdge n k p ≤ rankLowerEdge n k p + p k ∧
      rankLowerEdge n k p + p k ≤ h := by
  have hk1 := (Finset.mem_Icc.mp hk).1
  have hkn := (Finset.mem_Icc.mp hk).2
  refine ⟨suffix_nonneg hp (by omega), le_add_of_nonneg_right (hp k hk), ?_⟩
  rw [← hmass, add_comm, rankLowerEdge, ← sum_Icc_head hkn p]
  exact suffix_mono hp le_rfl hk1

lemma route_mass_finset (Γ : FiniteGame m n c Seed) (s : Finset ℕ) :
    (∑ j ∈ s, actualRouteMass Γ j) =
      (Γ.F ⊗ₘ Γ.σ).real {x | x.2.routeCount ∈ s} := by
  have hh := sum_measureReal_preimage_singleton (μ := Γ.F ⊗ₘ Γ.σ) s
    (f := fun x : ℝ × JointAction n => x.2.routeCount)
    (fun j _ => ((measurable_routeCount n).comp measurable_snd)
      (measurableSet_singleton j))
  simpa only [actualRouteMass, Set.preimage, Set.mem_singleton_iff,
    Set.mem_setOf_eq, Finset.mem_coe] using hh

lemma route_suffix_open (Γ : FiniteGame m n c Seed) (k : ℕ) :
    (∑ j ∈ Finset.Icc (k+1) n, actualRouteMass Γ j) =
      (Γ.F ⊗ₘ Γ.σ).real {x | k < x.2.routeCount} := by
  rw [route_mass_finset]
  congr 1
  ext x
  have hxn := x.2.routeCount_le
  simp only [mem_setOf_eq, Finset.mem_Icc]
  omega

lemma route_suffix_closed (Γ : FiniteGame m n c Seed) (k : ℕ) :
    (∑ j ∈ Finset.Icc k n, actualRouteMass Γ j) =
      (Γ.F ⊗ₘ Γ.σ).real {x | k ≤ x.2.routeCount} := by
  rw [route_mass_finset]
  congr 1
  ext x
  have hxn := x.2.routeCount_le
  simp only [mem_setOf_eq, Finset.mem_Icc]
  omega

lemma rank_monotone (Γ : FiniteGame m n c Seed) : Monotone (ascendingBidRank Γ) := by
  intro b d hbd
  exact measureReal_mono (fun x hx => ⟨hx.1, hx.2.1.trans hbd, hx.2.2⟩)

lemma rank_measurable (Γ : FiniteGame m n c Seed) : Measurable (ascendingBidRank Γ) :=
  (rank_monotone Γ).measurable

lemma rankClass_tail (Γ : FiniteGame m n c Seed) (k : ℕ) (u : ℝ) :
    (rankClassLaw Γ k).real (Ioi u) =
      (Γ.F ⊗ₘ Γ.σ).real
        {x | 0 < x.2.bid ∧ x.2.routeCount = k ∧ u < ascendingBidRank Γ x.2.bid} := by
  have hmeas := (rank_measurable Γ).comp ((measurable_bid n).comp
    (measurable_snd : Measurable (Prod.snd : ℝ × JointAction n → JointAction n)))
  change Measurable (fun x : ℝ × JointAction n => ascendingBidRank Γ x.2.bid) at hmeas
  unfold rankClassLaw
  rw [map_measureReal_apply hmeas measurableSet_Ioi,
    measureReal_restrict_apply]
  · congr 1
    ext x
    simp only [mem_preimage, mem_Ioi, mem_inter_iff, mem_setOf_eq]
    tauto
  · exact hmeas measurableSet_Ioi

lemma rankClass_tail_le_route (Γ : FiniteGame m n c Seed) (k : ℕ) (u : ℝ) :
    (rankClassLaw Γ k).real (Ioi u) ≤ actualRouteMass Γ k := by
  rw [rankClass_tail]
  exact measureReal_mono (fun _ hx => hx.2.1)

lemma finite_rank_sandwich (Γ : FiniteGame m n c Seed)
    {scale δ : ℝ} (hs : 0 < scale) (hδ0 : 0 ≤ δ)
    (hδn : δ ≤ 1/(4*(n : ℝ))) (hδ1 : δ < 1)
    {k : ℕ} (hk : k ∈ Finset.Icc 1 n) {x : ℝ × JointAction n}
    (hxk : x.2.routeCount = k) (hx : x ∉ routedTierError Γ scale δ) :
    (∑ j ∈ Finset.Icc (k+1) n, actualRouteMass Γ j) -
        (Γ.F ⊗ₘ Γ.σ).real (routedTierError Γ scale δ) ≤ ascendingBidRank Γ x.2.bid ∧
      ascendingBidRank Γ x.2.bid ≤
        (∑ j ∈ Finset.Icc k n, actualRouteMass Γ j) +
          (Γ.F ⊗ₘ Γ.σ).real (routedTierError Γ scale δ) := by
  have hk0 : 0 < k := by have := (Finset.mem_Icc.mp hk).1; omega
  have hx0 : 0 < x.2.routeCount := by omega
  have hxg := tierGood_of_not_error Γ scale δ hx0 hx
  have hxerr : |(k : ℝ)*(x.2.bid/scale)-1| ≤ δ := by simpa [hxk] using hxg.2.2
  let R : Set (ℝ × JointAction n) :=
    {y | 0 < y.2.bid ∧ y.2.bid ≤ x.2.bid ∧ 0 < y.2.routeCount}
  let E := routedTierError Γ scale δ
  have hlo : {y : ℝ × JointAction n | k < y.2.routeCount} ⊆ R ∪ E := by
    intro y hy
    by_cases he : y ∈ E
    · exact Or.inr he
    · have hy0 : 0 < y.2.routeCount := lt_trans hk0 hy
      have hyg := tierGood_of_not_error Γ scale δ hy0 he
      have horder := tier_separation hk0 hy y.2.routeCount_le hδ0 hδn hxerr hyg.2.2
      have hbid : y.2.bid < x.2.bid := (div_lt_div_iff_of_pos_right hs).mp horder
      exact Or.inl ⟨bid_pos_of_tierGood Γ hs hδ1 hyg, hbid.le, hy0⟩
  have hup : R ⊆ {y : ℝ × JointAction n | k ≤ y.2.routeCount} ∪ E := by
    intro y hy
    by_cases he : y ∈ E
    · exact Or.inr he
    · left
      by_contra hnot
      have hlt : y.2.routeCount < k := lt_of_not_ge hnot
      have hyg := tierGood_of_not_error Γ scale δ hy.2.2 he
      have horder := tier_separation hy.2.2 hlt (Finset.mem_Icc.mp hk).2
        hδ0 hδn hyg.2.2 hxerr
      have hbid : x.2.bid < y.2.bid := (div_lt_div_iff_of_pos_right hs).mp horder
      exact (not_lt_of_ge hy.2.1) hbid
  have hl := (measureReal_mono (μ := Γ.F ⊗ₘ Γ.σ) hlo).trans (measureReal_union_le R E)
  have hu := (measureReal_mono (μ := Γ.F ⊗ₘ Γ.σ) hup).trans
    (measureReal_union_le {y | k ≤ y.2.routeCount} E)
  rw [← route_suffix_open Γ k] at hl
  rw [← route_suffix_closed Γ k] at hu
  change (∑ j ∈ Finset.Icc (k+1) n, actualRouteMass Γ j) ≤
    ascendingBidRank Γ x.2.bid + (Γ.F ⊗ₘ Γ.σ).real E at hl
  exact ⟨by dsimp [E] at *; linarith, hu⟩

lemma finite_rank_tail_lower (Γ : FiniteGame m n c Seed)
    {scale δ u : ℝ} (hs : 0 < scale) (hδ0 : 0 ≤ δ)
    (hδn : δ ≤ 1/(4*(n : ℝ))) (hδ1 : δ < 1)
    {k : ℕ} (hk : k ∈ Finset.Icc 1 n)
    (hu : u < (∑ j ∈ Finset.Icc (k+1) n, actualRouteMass Γ j) -
      (Γ.F ⊗ₘ Γ.σ).real (routedTierError Γ scale δ)) :
    actualRouteMass Γ k ≤ (rankClassLaw Γ k).real (Ioi u) +
      (Γ.F ⊗ₘ Γ.σ).real (routedTierError Γ scale δ) := by
  rw [rankClass_tail]
  have hsub : {x : ℝ × JointAction n | x.2.routeCount = k} ⊆
      {x | 0 < x.2.bid ∧ x.2.routeCount = k ∧ u < ascendingBidRank Γ x.2.bid} ∪
        routedTierError Γ scale δ := by
    intro x hx
    change x.2.routeCount = k at hx
    by_cases he : x ∈ routedTierError Γ scale δ
    · exact Or.inr he
    · have hxpos : 0 < x.2.routeCount := by have := (Finset.mem_Icc.mp hk).1; omega
      exact Or.inl ⟨bid_pos_of_tierGood Γ hs hδ1 (tierGood_of_not_error Γ scale δ hxpos he),
        hx, hu.trans_le (finite_rank_sandwich Γ hs hδ0 hδn hδ1 hk hx he).1⟩
  exact (measureReal_mono hsub).trans (measureReal_union_le _ _)

lemma finite_rank_tail_upper (Γ : FiniteGame m n c Seed)
    {scale δ u : ℝ} (hs : 0 < scale) (hδ0 : 0 ≤ δ)
    (hδn : δ ≤ 1/(4*(n : ℝ))) (hδ1 : δ < 1)
    {k : ℕ} (hk : k ∈ Finset.Icc 1 n)
    (hu : (∑ j ∈ Finset.Icc k n, actualRouteMass Γ j) +
      (Γ.F ⊗ₘ Γ.σ).real (routedTierError Γ scale δ) < u) :
    (rankClassLaw Γ k).real (Ioi u) ≤
      (Γ.F ⊗ₘ Γ.σ).real (routedTierError Γ scale δ) := by
  rw [rankClass_tail]
  refine measureReal_mono (fun x hx => ?_)
  by_contra he
  have hb := (finite_rank_sandwich Γ hs hδ0 hδn hδ1 hk hx.2.1 he).2
  exact (not_lt_of_ge hb) (hu.trans hx.2.2)

lemma finite_measure_real_mono {Ω : Type*} [MeasurableSpace Ω]
    {μ ν : Measure Ω} [IsFiniteMeasure ν] (hle : μ ≤ ν) (s : Set Ω) :
    μ.real s ≤ ν.real s :=
  ENNReal.toReal_mono (measure_ne_top ν s) (Measure.le_iff'.mp hle s)

lemma finite_measure_eq_of_le_total {Ω : Type*} [MeasurableSpace Ω]
    {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hle : μ ≤ ν) (htotal : μ.real univ = ν.real univ) : μ = ν := by
  apply Measure.ext
  intro s hs
  have h₁ := finite_measure_real_mono hle s
  have h₂ := finite_measure_real_mono hle sᶜ
  have hm := measureReal_add_measureReal_compl (μ := μ) hs
  have hn := measureReal_add_measureReal_compl (μ := ν) hs
  apply (measureReal_eq_measureReal_iff (measure_ne_top μ s) (measure_ne_top ν s)).mp
  linarith

lemma interval_volume_real {a b : ℝ} (hab : a ≤ b) :
    volume.real (Ioc a b) = b-a := by
  simp only [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

lemma interval_dom_finite {μ : Measure ℝ} {h : ℝ}
    (hd : μ ≤ volume.restrict (Ioc 0 h)) : IsFiniteMeasure μ := by
  refine ⟨(Measure.le_iff'.mp hd univ).trans_lt ?_⟩
  simp only [Measure.restrict_apply_univ, Real.volume_Ioc]
  exact ENNReal.ofReal_lt_top

lemma interval_dom_support {μ : Measure ℝ} {h : ℝ}
    (hd : μ ≤ volume.restrict (Ioc 0 h)) : ∀ᵐ u ∂μ, u ∈ Ioc 0 h := by
  have hh := Measure.le_iff'.mp hd (Ioc 0 h)ᶜ
  have hz : μ (Ioc 0 h)ᶜ = 0 := by
    have hle : μ (Ioc 0 h)ᶜ ≤ 0 := by
      simpa only [Measure.restrict_apply measurableSet_Ioc.compl,
        compl_inter_self, measure_empty] using hh
    exact le_antisymm hle bot_le
  exact ae_iff.mpr hz

lemma interval_dom_tail_zero {μ : Measure ℝ} {h : ℝ}
    (hd : μ ≤ volume.restrict (Ioc 0 h)) : μ.real (Ioc 0 h) = μ.real univ := by
  apply measureReal_congr
  filter_upwards [interval_dom_support hd] with u hu
  apply propext
  exact ⟨fun _ => mem_univ u, fun _ => hu⟩

lemma interval_dom_tail_difference {μ : Measure ℝ} {h u v : ℝ}
    (hd : μ ≤ volume.restrict (Ioc 0 h)) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ h) :
    μ.real (Ioc u h) - μ.real (Ioc v h) ≤ v-u := by
  letI : IsFiniteMeasure μ := interval_dom_finite hd
  letI : IsFiniteMeasure (volume.restrict (Ioc 0 h)) := interval_dom_finite le_rfl
  rw [Ample.CompletionDraft.tail_difference huv hv]
  have hh := finite_measure_real_mono hd (Ioc u v)
  have hsub : Ioc u v ⊆ Ioc 0 h := fun _ hx => ⟨hu.trans_lt hx.1, hx.2.trans hv⟩
  rw [measureReal_restrict_apply measurableSet_Ioc, inter_eq_left.mpr hsub,
    interval_volume_real huv] at hh
  exact hh

lemma interval_dom_edge_tails {μ : Measure ℝ} {h L U p : ℝ}
    (hd : μ ≤ volume.restrict (Ioc 0 h)) (hL : 0 ≤ L) (hLU : L ≤ U) (hU : U ≤ h)
    (hm : μ.real univ = p)
    (hlo : ∀ u ∈ Icc 0 h, u < L → μ.real (Ioc u h) = p)
    (hhi : ∀ u ∈ Icc 0 h, U < u → μ.real (Ioc u h) = 0) :
    μ.real (Ioc L h) = p ∧ μ.real (Ioc U h) = 0 := by
  letI : IsFiniteMeasure μ := interval_dom_finite hd
  have htaille (u : ℝ) : μ.real (Ioc u h) ≤ p := by
    rw [← hm]
    exact measureReal_mono (subset_univ _)
  constructor
  · apply le_antisymm (htaille L)
    by_contra hn
    have hg : 0 < p - μ.real (Ioc L h) := sub_pos.mpr (lt_of_not_ge hn)
    by_cases he : L = 0
    · have ht := interval_dom_tail_zero hd
      rw [he, ht, hm] at hn
      exact hn le_rfl
    · have hLp : 0 < L := lt_of_le_of_ne hL (Ne.symm he)
      obtain ⟨ε, hε, hsmall⟩ := exists_between (lt_min hLp hg)
      let u := L-ε
      have hu0 : 0 ≤ u := by dsimp [u]; linarith [hsmall.trans_le (min_le_left _ _)]
      have huL : u < L := by dsimp [u]; linarith
      have huh : u ≤ h := huL.le.trans (hLU.trans hU)
      have htail := hlo u ⟨hu0, huh⟩ huL
      have hdif := interval_dom_tail_difference hd hu0 huL.le (hLU.trans hU)
      rw [htail] at hdif
      dsimp [u] at hdif
      linarith [hsmall.trans_le (min_le_right _ _)]
  · apply le_antisymm _ measureReal_nonneg
    by_contra hn
    have hp : 0 < μ.real (Ioc U h) := lt_of_not_ge hn
    by_cases he : U = h
    · simp [he] at hp
    · have hUh : U < h := lt_of_le_of_ne hU he
      obtain ⟨ε, hε, hsmall⟩ := exists_between (lt_min (sub_pos.mpr hUh) hp)
      let u := U+ε
      have hUu : U < u := by dsimp [u]; linarith
      have huh : u ≤ h := by dsimp [u]; linarith [hsmall.trans_le (min_le_left _ _)]
      have hu0 : 0 ≤ u := hL.trans (hLU.trans hUu.le)
      have htail := hhi u ⟨hu0, huh⟩ hUu
      have hdif := interval_dom_tail_difference hd (hL.trans hLU) hUu.le huh
      rw [htail] at hdif
      dsimp [u] at hdif
      linarith [hsmall.trans_le (min_le_right _ _)]

lemma interval_dom_identification {μ : Measure ℝ} {h L p : ℝ}
    (hd : μ ≤ volume.restrict (Ioc 0 h)) (hL : 0 ≤ L) (hp : 0 ≤ p) (hU : L+p ≤ h)
    (hm : μ.real univ = p) (hlo : μ.real (Ioc L h) = p)
    (hhi : μ.real (Ioc (L+p) h) = 0) :
    μ = volume.restrict (Ioc L (L+p)) := by
  let I := Ioc L (L+p)
  have hLI : L ≤ L+p := le_add_of_nonneg_right hp
  letI : IsFiniteMeasure μ := interval_dom_finite hd
  have hmass : μ.real I = p := by
    have hh := Ample.CompletionDraft.tail_difference (μ := μ) hLI hU
    rw [hlo, hhi, sub_zero] at hh
    exact hh.symm
  have hnull : μ Iᶜ = 0 := by
    apply (measureReal_eq_zero_iff (measure_ne_top μ Iᶜ)).mp
    have hh := measureReal_add_measureReal_compl (μ := μ)
      (show MeasurableSet I from measurableSet_Ioc)
    rw [hmass, hm] at hh
    linarith
  have hsupp : ∀ᵐ u ∂μ, u ∈ I := ae_iff.mpr hnull
  have hsub : I ⊆ Ioc 0 h := fun _ hx => ⟨hL.trans_lt hx.1, hx.2.trans hU⟩
  have hle : μ ≤ volume.restrict I := by
    rw [← Measure.restrict_eq_self_of_ae_mem hsupp]
    have hh := Measure.restrict_mono_measure hd I
    rwa [Measure.restrict_restrict_of_subset hsub] at hh
  letI : IsFiniteMeasure (volume.restrict I) := by
    refine ⟨?_⟩
    simp only [Measure.restrict_apply_univ, I, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  apply finite_measure_eq_of_le_total hle
  rw [hm, measureReal_restrict_apply_univ, interval_volume_real hLI]
  ring

end RouteIdentificationDetails

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem actual_rank_tier_localization {M C : ℕ → ℕ}
    (Γ : ∀ t, FiniteGame (M t) n (C t) Seed) (scale : ℕ → ℝ)
    (ha : ∀ t, NonpositiveAbstention (Γ t))
    (hpactive : ∀ t, 0 < (Γ t).F.real (Ioi (Γ t).g))
    (hnorm : ProbZero (fun t => activeDrawLaw (Γ t))
      (fun t x => (x.2.routeCount : ℝ)*x.2.bid/scale t-1))
    (hscale : ∀ᶠ t in atTop, 0 < scale t)
    {pi : ℕ → ℝ} {h : ℝ} {nu : ℕ → Measure ℝ}
    (hp : RouteLimit Γ pi) (hr : RankLimit Γ pi h nu)
    (hmass : (∑ j ∈ Finset.Icc 1 n, pi j) = h) :
    ∀ k ∈ Finset.Icc 1 n,
      nu k = volume.restrict (Ioc (rankLowerEdge n k pi)
        (rankLowerEdge n k pi + pi k)) := by
  intro k hk
  have hk1 := (Finset.mem_Icc.mp hk).1
  have hkn := (Finset.mem_Icc.mp hk).2
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpnonneg : ∀ j ∈ Finset.Icc 1 n, 0 ≤ pi j := by
    intro j hj
    exact le_of_tendsto_of_tendsto tendsto_const_nhds
      (hp j (Finset.mem_Icc.mpr ⟨Nat.zero_le j, (Finset.mem_Icc.mp hj).2⟩))
      (Eventually.of_forall (fun _ => measureReal_nonneg))
  let δ : ℝ := min (1/2) (1/(4*(n : ℝ)))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδn : δ ≤ 1/(4*(n : ℝ)) := min_le_right _ _
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  let e := fun t => ((Γ t).F ⊗ₘ (Γ t).σ).real (routedTierError (Γ t) (scale t) δ)
  have he : Tendsto e atTop (𝓝 0) :=
    routedTierError_tendsto_zero Γ scale ha hpactive hnorm hδ
  have hloLim : Tendsto
      (fun t => ∑ j ∈ Finset.Icc (k+1) n, actualRouteMass (Γ t) j)
      atTop (𝓝 (rankLowerEdge n k pi)) := by
    apply tendsto_finsetSum
    intro j hj
    exact hp j (Finset.mem_Icc.mpr ⟨Nat.zero_le j, (Finset.mem_Icc.mp hj).2⟩)
  have hhiLim : Tendsto
      (fun t => ∑ j ∈ Finset.Icc k n, actualRouteMass (Γ t) j)
      atTop (𝓝 (rankLowerEdge n k pi + pi k)) := by
    have hh : Tendsto
        (fun t => ∑ j ∈ Finset.Icc k n, actualRouteMass (Γ t) j)
        atTop (𝓝 (∑ j ∈ Finset.Icc k n, pi j)) := by
      apply tendsto_finsetSum
      intro j hj
      exact hp j (Finset.mem_Icc.mpr ⟨Nat.zero_le j, (Finset.mem_Icc.mp hj).2⟩)
    have heq : (∑ j ∈ Finset.Icc k n, pi j) = rankLowerEdge n k pi + pi k := by
      rw [RouteIdentificationDetails.sum_Icc_head hkn]
      exact add_comm _ _
    rwa [heq] at hh
  have hpLim := hp k (Finset.mem_Icc.mpr ⟨Nat.zero_le k, hkn⟩)
  have htailLim (u : ℝ) (hu : u ∈ Icc 0 h) :
      Tendsto (fun t => (rankClassLaw (Γ t) k).real (Ioi u)) atTop
        (𝓝 ((nu k).real (Ioc u h))) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hr.tails ε hε] with t ht
    simpa only [Real.dist_eq, rankTail] using ht k hk u hu
  letI : IsFiniteMeasure (nu k) :=
    RouteIdentificationDetails.interval_dom_finite (hr.dominated k hk)
  have hlo : ∀ u ∈ Icc 0 h, u < rankLowerEdge n k pi →
      (nu k).real (Ioc u h) = pi k := by
    intro u hu huL
    have hlim : Tendsto
        (fun t => (∑ j ∈ Finset.Icc (k+1) n, actualRouteMass (Γ t) j)-e t)
        atTop (𝓝 (rankLowerEdge n k pi)) := by
      simpa only [sub_zero] using hloLim.sub he
    have hb : ∀ᶠ t in atTop, actualRouteMass (Γ t) k ≤
        (rankClassLaw (Γ t) k).real (Ioi u) + e t := by
      filter_upwards [hscale, hlim.eventually_const_lt huL] with t ht htu
      exact RouteIdentificationDetails.finite_rank_tail_lower (Γ t) ht hδ.le hδn hδ1 hk htu
    have hh := le_of_tendsto_of_tendsto hpLim ((htailLim u hu).add he) hb
    have hle : (nu k).real (Ioc u h) ≤ pi k := by
      rw [← hr.mass k hk]
      exact measureReal_mono (subset_univ _)
    exact le_antisymm hle (by simpa only [add_zero] using hh)
  have hhi : ∀ u ∈ Icc 0 h, rankLowerEdge n k pi + pi k < u →
      (nu k).real (Ioc u h) = 0 := by
    intro u hu hUu
    have hlim : Tendsto
        (fun t => (∑ j ∈ Finset.Icc k n, actualRouteMass (Γ t) j)+e t)
        atTop (𝓝 (rankLowerEdge n k pi + pi k)) := by
      simpa only [add_zero] using hhiLim.add he
    have hb : ∀ᶠ t in atTop, (rankClassLaw (Γ t) k).real (Ioi u) ≤ e t := by
      filter_upwards [hscale, hlim.eventually_lt_const hUu] with t ht htu
      exact RouteIdentificationDetails.finite_rank_tail_upper (Γ t) ht hδ.le hδn hδ1 hk htu
    exact le_antisymm (le_of_tendsto_of_tendsto (htailLim u hu) he hb) measureReal_nonneg
  obtain ⟨hL, hLU, hU⟩ := RouteIdentificationDetails.edge_bounds hk hpnonneg hmass
  obtain ⟨htL, htU⟩ := RouteIdentificationDetails.interval_dom_edge_tails
    (hr.dominated k hk) hL hLU hU (hr.mass k hk) hlo hhi
  exact RouteIdentificationDetails.interval_dom_identification
    (hr.dominated k hk) hL (hpnonneg k hk) hU (hr.mass k hk) htL htU

end FCAppendix.Bayes
