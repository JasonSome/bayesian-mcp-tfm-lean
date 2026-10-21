import FCAppendix.Ample.RankDistributionTransform
import FCAppendix.Finite.BinomialLogBounds

noncomputable section

namespace FCAppendix.Affine.Uniform06.Rank

open MeasureTheory Set Filter
open scoped Topology

def payoff (η v b S D : ℝ) : ℝ := (v-b)*S-η*b*D

theorem two_type_IC_allocation_monotone
    {η v w a b Sa Sb Da Db : ℝ} (hvw : v < w)
    (hv : payoff η v b Sb Db ≤ payoff η v a Sa Da)
    (hw : payoff η w a Sa Da ≤ payoff η w b Sb Db) : Sa ≤ Sb := by
  unfold payoff at hv hw
  by_contra h
  have hh := mul_pos (sub_pos.mpr hvw) (sub_pos.mpr (lt_of_not_ge h))
  nlinarith

theorem equal_positive_success_strict_cost
    {η v a b Sa Sb Da Db : ℝ}
    (hη : 0 ≤ η) (ha : 0 ≤ a) (hab : a < b)
    (hSa : 0 < Sa) (hS : Sb = Sa) (hDa : 0 ≤ Da) (hD : Da ≤ Db) :
    payoff η v b Sb Db < payoff η v a Sa Da := by
  have hb : 0 ≤ b := ha.trans hab.le
  have hload : 0 < Sa+η*Da := by
    nlinarith [mul_nonneg hη hDa]
  have hmain := mul_pos (sub_pos.mpr hab) hload
  have hcorr := mul_nonneg hb (mul_nonneg hη (sub_nonneg.mpr hD))
  unfold payoff
  rw [hS]
  nlinarith

theorem reversed_bids_mutually_feasible
    {lo hi : ℝ → ℝ} (hlo : Monotone lo) (hhi : Monotone hi)
    {v w a b : ℝ} (hvw : v ≤ w)
    (ha : a ∈ Icc (lo v) (hi v)) (hb : b ∈ Icc (lo w) (hi w))
    (hba : b ≤ a) :
    b ∈ Icc (lo v) (hi v) ∧ a ∈ Icc (lo w) (hi w) := by
  exact ⟨⟨(hlo hvw).trans hb.1, hba.trans ha.2⟩,
    ⟨hb.1.trans hba, ha.2.trans (hhi hvw)⟩⟩

theorem used_bid_sorted_on_prefix
    {η K : ℝ} {lo hi S D : ℝ → ℝ}
    (hη : 0 ≤ η) (hlo : Monotone lo) (hhi : Monotone hi)
    (hS : MonotoneOn S (Icc 0 K)) (hD : MonotoneOn D (Icc 0 K))
    {v w a b : ℝ} (hvw : v < w)
    (ha : a ∈ Icc (lo v) (hi v)) (hb : b ∈ Icc (lo w) (hi w))
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (haK : a ≤ K)
    (hSa : 0 < S a) (hDb : 0 ≤ D b)
    (hvIC : ∀ d ∈ Icc (lo v) (hi v),
      payoff η v d (S d) (D d) ≤ payoff η v a (S a) (D a))
    (hwIC : ∀ d ∈ Icc (lo w) (hi w),
      payoff η w d (S d) (D d) ≤ payoff η w b (S b) (D b)) : a ≤ b := by
  by_contra h
  have hba : b < a := lt_of_not_ge h
  have hswap := reversed_bids_mutually_feasible hlo hhi hvw.le ha hb hba.le
  have halloc := two_type_IC_allocation_monotone hvw
    (hvIC b hswap.1) (hwIC a hswap.2)
  have hseq : S a = S b := le_antisymm halloc
    (hS ⟨hb0,hba.le.trans haK⟩ ⟨ha0,haK⟩ hba.le)
  have hdeq := hD ⟨hb0,hba.le.trans haK⟩ ⟨ha0,haK⟩ hba.le
  have hcost := equal_positive_success_strict_cost (v := v)
    hη hb0 hba (hseq ▸ hSa) hseq hDb hdeq
  exact (not_lt_of_ge (hvIC b hswap.1)) hcost

def unconditionalRank {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (B : Ω → ℝ) (b : ℝ) : ℝ := μ.real {ω | B ω ≤ b}

section JointLaw

variable {Ω : Type*} [MeasurableSpace Ω]

theorem lower_value_marginal
    (π : Measure Ω) {V : Ω → ℝ} (hV : Measurable V)
    (hπ : π.map V = volume.restrict (Ioc (0 : ℝ) 1))
    {t : ℝ} (ht : t ≤ 1) :
    (π.restrict {ω | V ω ≤ t}).map V = volume.restrict (Ioc 0 t) := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hV hs, Measure.restrict_apply (hV hs)]
  have he : V ⁻¹' s ∩ {ω | V ω ≤ t} = V ⁻¹' (s ∩ Iic t) := by
    ext ω
    simp only [mem_preimage,mem_inter_iff,mem_setOf_eq,mem_Iic]
  rw [he, ← Measure.map_apply hV (hs.inter measurableSet_Iic), hπ,
    Measure.restrict_apply (hs.inter measurableSet_Iic), Measure.restrict_apply hs]
  congr 1
  ext x
  simp only [mem_inter_iff,mem_Iic,mem_Ioc]
  constructor
  · rintro ⟨⟨hxs,hxt⟩,hx0,_⟩
    exact ⟨hxs,hx0,hxt⟩
  · rintro ⟨hxs,hx0,hxt⟩
    exact ⟨⟨hxs,hxt⟩,hx0,hxt.trans ht⟩

theorem unconditionalRank_restrict_lower
    (π : Measure Ω) [IsFiniteMeasure π]
    {V B : Ω → ℝ} (hB : Measurable B) (t b : ℝ) :
    unconditionalRank (π.restrict {ω | V ω ≤ t}) B b =
      π.real {ω | V ω ≤ t ∧ B ω ≤ b} := by
  unfold unconditionalRank
  have hmeas : MeasurableSet {ω | B ω ≤ b} :=
    hB measurableSet_Iic
  rw [measureReal_restrict_apply hmeas]
  congr 1
  ext ω
  simp only [mem_inter_iff,mem_setOf_eq]
  tauto

theorem uniform_value_level_null
    (μ : Measure Ω) {V : Ω → ℝ} (hV : Measurable V)
    {t : ℝ} (hmarg : μ.map V = volume.restrict (Ioc (0 : ℝ) t))
    (v : ℝ) : μ {ω | V ω = v} = 0 := by
  have h := congrArg (fun ν : Measure ℝ => ν {v}) hmarg
  rw [Measure.map_apply hV (measurableSet_singleton v),
    Measure.restrict_apply (measurableSet_singleton v)] at h
  calc
    μ {ω | V ω = v} = volume ({v} ∩ Ioc 0 t) := h
    _ = 0 := measure_mono_null inter_subset_left (by simp)

theorem original_uniform_rank_identity_on_common_set
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {V B : Ω → ℝ} (hV : Measurable V)
    {t K : ℝ} (ht : 0 ≤ t)
    (hmarg : μ.map V = volume.restrict (Ioc (0 : ℝ) t))
    (hatom : ∀ b : ℝ, μ {ω | B ω = b} = 0)
    {G : Set Ω} (hG : ∀ᵐ ω ∂μ, ω ∈ G)
    (hvalue : ∀ ω ∈ G, V ω ∈ Icc 0 t)
    (hsort : ∀ x ∈ G, V x < K → ∀ y ∈ G,
      V x < V y → B x ≤ B y) :
    ∀ x ∈ G, V x < K → unconditionalRank μ B (B x) = V x := by
  intro x hx hxK
  have hbn : ∀ᵐ y ∂μ, B y ≠ B x := by
    rw [ae_iff]
    simpa using hatom (B x)
  have hvn : ∀ᵐ y ∂μ, V y ≠ V x := by
    rw [ae_iff]
    simpa using uniform_value_level_null μ hV hmarg (V x)
  have he : μ.real {y | B y ≤ B x} = μ.real {y | V y ≤ V x} := by
    apply measureReal_congr
    filter_upwards [hG,hbn,hvn] with y hy hby hvy
    change (B y ≤ B x) = (V y ≤ V x)
    apply propext
    constructor
    · intro hbyx
      by_contra hbad
      have hxy : V x < V y := lt_of_not_ge hbad
      exact hby (le_antisymm hbyx (hsort x hx hxK y hy hxy))
    · intro hvyx
      have hlt : V y < V x := lt_of_le_of_ne hvyx hvy
      exact hsort y hy (hlt.trans hxK) x hx hlt
  unfold unconditionalRank
  rw [he]
  have hmap : (μ.map V).real (Iic (V x)) = μ.real {y | V y ≤ V x} :=
    map_measureReal_apply hV measurableSet_Iic
  rw [hmarg] at hmap
  rw [← hmap, Ample.RankMeasureTools.volume_restrict_Ioc_Iic_real ht]
  rw [min_eq_right (hvalue x hx).2, max_eq_right (hvalue x hx).1]

theorem original_uniform_rank_identity_ae
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {V B : Ω → ℝ} (hV : Measurable V)
    {t K : ℝ} (ht : 0 ≤ t)
    (hmarg : μ.map V = volume.restrict (Ioc (0 : ℝ) t))
    (hatom : ∀ b : ℝ, μ {ω | B ω = b} = 0)
    {G : Set Ω} (hG : ∀ᵐ ω ∂μ, ω ∈ G)
    (hvalue : ∀ ω ∈ G, V ω ∈ Icc 0 t)
    (hsort : ∀ x ∈ G, V x < K → ∀ y ∈ G,
      V x < V y → B x ≤ B y) :
    ∀ᵐ x ∂μ, V x < K → unconditionalRank μ B (B x) = V x := by
  filter_upwards [hG] with x hx
  exact original_uniform_rank_identity_on_common_set μ hV ht hmarg
    hatom hG hvalue hsort x hx

end JointLaw

end FCAppendix.Affine.Uniform06.Rank
