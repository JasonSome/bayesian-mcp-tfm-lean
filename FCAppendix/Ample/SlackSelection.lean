import FCAppendix.Finite.PPIVisibleRanks
import FCAppendix.Finite.ScarcityBounds
import FCAppendix.Ample.VisibleContactLaw

noncomputable section
namespace FCAppendix.Ample
open MeasureTheory Set Filter Topology

structure BidStratum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (bid : Ω → ℝ) where
  carrier : Set Ω
  measurable_carrier : MeasurableSet carrier
  positive : ∀ x ∈ carrier, 0 < bid x
  atomless : ∀ b : ℝ, μ (carrier ∩ {x | bid x = b}) = 0

namespace BidStratum
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {bid : Ω → ℝ} (E : BidStratum μ bid) (hb : Measurable bid)

def mass : ℝ := μ.real E.carrier

def tail (b : ℝ) : ℝ := μ.real (E.carrier ∩ {x | b < bid x})

def bidMeasure (_hb : Measurable bid) : Measure ℝ := (μ.restrict E.carrier).map bid

instance : IsFiniteMeasure (E.bidMeasure hb) := by
  unfold bidMeasure
  infer_instance

omit [IsFiniteMeasure μ] in
lemma bidMeasure_tail (b : ℝ) :
    (E.bidMeasure hb).real (Ioi b) = E.tail b := by
  unfold bidMeasure tail Measure.real
  rw [Measure.map_apply hb measurableSet_Ioi,
    Measure.restrict_apply (hb measurableSet_Ioi)]
  congr 2
  ext x
  simp only [mem_preimage, mem_Ioi, mem_inter_iff, mem_setOf_eq]
  tauto

omit [IsFiniteMeasure μ] in
lemma bidMeasure_atom (b : ℝ) : E.bidMeasure hb {b} = 0 := by
  unfold bidMeasure
  rw [Measure.map_apply hb (measurableSet_singleton b),
    Measure.restrict_apply (hb (measurableSet_singleton b))]
  change μ ({x | bid x = b} ∩ E.carrier) = 0
  rw [inter_comm]
  exact E.atomless b

omit [IsFiniteMeasure μ] in
lemma tail_zero : E.tail 0 = E.mass := by
  unfold tail mass
  congr 1
  exact inter_eq_left.mpr E.positive

omit [IsFiniteMeasure μ] in
lemma tail_nonneg (b : ℝ) : 0 ≤ E.tail b := measureReal_nonneg

lemma tail_le_mass (b : ℝ) : E.tail b ≤ E.mass :=
  measureReal_mono inter_subset_left

lemma tail_antitone : Antitone E.tail := by
  intro b d hbd
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro x hx
  exact ⟨hx.1, hbd.trans_lt hx.2⟩

include hb

lemma continuous_tail : Continuous E.tail := by
  apply continuous_iff_continuousAt.mpr
  intro b
  simpa only [E.bidMeasure_tail hb] using
    Bayes.continuousAt_real_tail_of_no_atom (E.bidMeasure hb) b (E.bidMeasure_atom hb b)

omit [IsFiniteMeasure μ] in
lemma tail_tendsto_zero : Tendsto E.tail atTop (𝓝 0) := by
  have h := tendsto_integral_Ioi_zero (f := fun _ : ℝ => (1 : ℝ))
    (μ := E.bidMeasure hb) tendsto_id
  simpa only [setIntegral_const, smul_eq_mul, mul_one, E.bidMeasure_tail hb, id_eq] using h

theorem exists_threshold {q : ℝ} (hq : 0 < q) (hqm : q < E.mass) :
    ∃ b : ℝ, 0 < b ∧ E.tail b = q := by
  obtain ⟨B, hB, hBt⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    ((E.tail_tendsto_zero hb).eventually_lt_const hq)).exists
  obtain ⟨b, hbB, he⟩ := intermediate_value_Icc' hB.le
    (E.continuous_tail hb).continuousOn
    (show q ∈ Icc (E.tail B) (E.tail 0) by rw [E.tail_zero]; exact ⟨hBt.le, hqm.le⟩)
  have hne : b ≠ 0 := by
    intro hz
    rw [hz, E.tail_zero] at he
    exact hqm.ne he.symm
  exact ⟨b, lt_of_le_of_ne hbB.1 hne.symm, he⟩

theorem exists_band {lo hi : ℝ} (hlo : 0 < lo) (hlh : lo < hi)
    (hhi : hi < E.mass) :
    ∃ B : Set Ω, MeasurableSet B ∧ μ.real B = hi - lo ∧
      ∀ x ∈ B, x ∈ E.carrier ∧ lo ≤ E.tail (bid x) ∧ E.tail (bid x) ≤ hi := by
  obtain ⟨b, _, hbq⟩ := E.exists_threshold hb (hlo.trans hlh) hhi
  obtain ⟨t, _, htq⟩ := E.exists_threshold hb hlo (hlh.trans hhi)
  have hbt : b < t := by
    by_contra hnot
    have h := E.tail_antitone (le_of_not_gt hnot)
    rw [hbq, htq] at h
    exact hlh.not_ge h
  let B := (E.carrier ∩ {x | b < bid x}) \ (E.carrier ∩ {x | t < bid x})
  have hsub : E.carrier ∩ {x | t < bid x} ⊆ E.carrier ∩ {x | b < bid x} :=
    fun x hx => ⟨hx.1, hbt.trans hx.2⟩
  refine ⟨B, (E.measurable_carrier.inter (measurableSet_lt measurable_const hb)).diff
    (E.measurable_carrier.inter (measurableSet_lt measurable_const hb)), ?_, ?_⟩
  · dsimp [B]
    rw [measureReal_sdiff hsub
      (E.measurable_carrier.inter (measurableSet_lt measurable_const hb))]
    change E.tail b - E.tail t = _
    rw [hbq, htq]
  · intro x hx
    have hxt : bid x ≤ t := by
      by_contra hh
      exact hx.2 ⟨hx.1.1, lt_of_not_ge hh⟩
    refine ⟨hx.1.1, ?_, ?_⟩
    · rw [← htq]
      exact E.tail_antitone hxt
    · rw [← hbq]
      exact E.tail_antitone hx.1.2.le

theorem exists_good_in_band {lo hi : ℝ} (hlo : 0 < lo) (hlh : lo < hi)
    (hhi : hi < E.mass) (Bad : Set Ω) (hbad : μ.real Bad < hi - lo)
    (P : Ω → Prop) (hP : ∀ᵐ x ∂μ, P x) :
    ∃ x, x ∈ E.carrier ∧ lo ≤ E.tail (bid x) ∧ E.tail (bid x) ≤ hi ∧
      x ∉ Bad ∧ P x := by
  classical
  obtain ⟨B, _, hB, hpoint⟩ := E.exists_band hb hlo hlh hhi
  by_contra hex
  have hsub : B ≤ᵐ[μ] Bad := by
    filter_upwards [hP] with x hx hxB
    by_contra hxBad
    have hx' := hpoint x hxB
    exact hex ⟨x, hx'.1, hx'.2.1, hx'.2.2, hxBad, hx⟩
  have hm : μ.real B ≤ μ.real Bad :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  rw [hB] at hm
  exact hbad.not_ge hm

end BidStratum

theorem exists_compact_positive_band (F : Measure ℝ) [IsProbabilityMeasure F]
    (g : ℝ) {d : ℝ} (hd : 0 < d) :
    ∃ ε H : ℝ, 0 < ε ∧ ε < H ∧
      F.real {v | g < v ∧ v - g ∉ Icc ε H} < d := by
  obtain ⟨ε, hε, hlow⟩ := Bayes.exists_positive_tail_margin F g
    (F.real (Ioi g) - d / 2) (by linarith)
  have htail : Tendsto (fun t : ℝ => F.real (Ioi t)) atTop (𝓝 0) := by
    simpa only [setIntegral_const, smul_eq_mul, mul_one, id_eq] using
      (tendsto_integral_Ioi_zero (f := fun _ : ℝ => (1 : ℝ)) (μ := F) tendsto_id)
  obtain ⟨T, hT, htop⟩ := ((eventually_gt_atTop (g + ε)).and
    (htail.eventually_lt_const (show 0 < d / 2 by linarith))).exists
  have hl : F.real (Ioi g \ Ioi (g + ε)) < d / 2 := by
    rw [measureReal_sdiff (Ioi_subset_Ioi (by linarith)) measurableSet_Ioi]
    linarith
  refine ⟨ε, T - g, hε, by linarith, ?_⟩
  have hsub : {v | g < v ∧ v - g ∉ Icc ε (T - g)} ⊆
      (Ioi g \ Ioi (g + ε)) ∪ Ioi T := by
    intro v hv
    by_cases hT' : T < v
    · exact Or.inr hT'
    · left
      refine ⟨hv.1, ?_⟩
      intro hvε
      change g + ε < v at hvε
      exact hv.2 ⟨by linarith, by linarith⟩
  exact (measureReal_mono hsub).trans_lt
    ((measureReal_union_le _ _).trans_lt (by linarith))

end FCAppendix.Ample

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def NonpositiveAbstention (Γ : FiniteGame m n c Seed) : Prop :=
  ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.1 ≤ Γ.g → x.2.routeCount = 0

theorem ae_positive_routed_bid_ne (Γ : FiniteGame m n c Seed)
    (hatom : PositiveVisibleAtomless Γ) {b : ℝ} (hb : 0 < b) :
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.routeCount → x.2.bid ≠ b := by
  have hdraw : ∀ᵐ d ∂userLaw Γ, 0 < d.1.2.routeCount → d.1.2.bid ≠ b := by
    have hj : ∀ᵐ d ∂userLaw Γ, ∀ j : Fin n,
        ¬ (j ∈ firstK d.2 d.1.2.routeCount ∧ d.1.2.bid = b) := by
      apply ae_all_iff.mpr
      intro j
      exact measure_eq_zero_iff_ae_notMem.mp (hatom j b hb)
    filter_upwards [hj] with d hd hk he
    have hcard : 0 < (firstK d.2 d.1.2.routeCount).card := by
      rwa [card_firstK _ _ d.1.2.routeCount_le]
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hcard
    exact hd j ⟨hj, he⟩
  have h := Measure.ae_ae_of_ae_prod hdraw
  filter_upwards [h] with x hx
  obtain ⟨τ, hτ⟩ := hx.exists
  exact hτ

def positiveBidStratum (Γ : FiniteGame m n c Seed)
    (hatom : PositiveVisibleAtomless Γ) (P : ℕ → Prop) :
    Ample.BidStratum (Γ.F ⊗ₘ Γ.σ) (fun x : ℝ × JointAction n => x.2.bid) where
  carrier := {x | 0 < x.2.bid ∧ 0 < x.2.routeCount ∧ P x.2.routeCount}
  measurable_carrier := by
    have hm : Measurable (fun x : ℝ × JointAction n => x.2.routeCount) :=
      (measurable_routeCount n).comp measurable_snd
    exact (measurableSet_lt measurable_const ((measurable_bid n).comp measurable_snd)).inter
      ((measurableSet_lt measurable_const hm).inter (hm (Set.to_countable _).measurableSet))
  positive := fun _ hx => hx.1
  atomless := by
    intro b
    apply measure_eq_zero_iff_ae_notMem.mpr
    by_cases hb : 0 < b
    · filter_upwards [ae_positive_routed_bid_ne Γ hatom hb] with x hx hE
      exact hx hE.1.2.1 hE.2
    · exact ae_of_all _ fun x hx => hb (hx.2 ▸ hx.1.1)

def positiveRouteMass (Γ : FiniteGame m n c Seed) (P : ℕ → Prop) : ℝ :=
  (Γ.F ⊗ₘ Γ.σ).real {x | 0 < x.2.bid ∧ 0 < x.2.routeCount ∧ P x.2.routeCount}

def positiveRouteTail (Γ : FiniteGame m n c Seed) (P : ℕ → Prop) (b : ℝ) : ℝ :=
  (Γ.F ⊗ₘ Γ.σ).real {x | 0 < x.2.bid ∧ 0 < x.2.routeCount ∧
    P x.2.routeCount ∧ b < x.2.bid}

lemma positiveBidStratum_mass (Γ : FiniteGame m n c Seed)
    (hatom : PositiveVisibleAtomless Γ) (P : ℕ → Prop) :
    (positiveBidStratum Γ hatom P).mass = positiveRouteMass Γ P := rfl

lemma positiveBidStratum_tail (Γ : FiniteGame m n c Seed)
    (hatom : PositiveVisibleAtomless Γ) (P : ℕ → Prop) (b : ℝ) :
    (positiveBidStratum Γ hatom P).tail b = positiveRouteTail Γ P b := by
  unfold Ample.BidStratum.tail positiveRouteTail positiveBidStratum
  congr 1
  ext x
  simp only [mem_inter_iff, mem_setOf_eq]
  tauto

lemma joint_value_probability (Γ : FiniteGame m n c Seed) (S : Set ℝ)
    (hS : MeasurableSet S) :
    (Γ.F ⊗ₘ Γ.σ).real {x | x.1 ∈ S} = Γ.F.real S := by
  have he : (Γ.F ⊗ₘ Γ.σ) {x | x.1 ∈ S} = Γ.F S := by
    calc
      _ = (Γ.F ⊗ₘ Γ.σ).fst S := by
        rw [Measure.fst, Measure.map_apply measurable_fst hS]
        rfl
      _ = _ := by rw [Measure.fst_compProd]
  exact congrArg ENNReal.toReal he

theorem exists_supported_route_band (Γ : FiniteGame m n c Seed)
    (hatom : PositiveVisibleAtomless Γ) (hu : UsersOptimal Γ)
    (hact : NonpositiveAbstention Γ) (i : Fin m) (P : ℕ → Prop)
    {lo hi ε H : ℝ} (hlo : 0 < lo) (hlh : lo < hi)
    (hhi : hi < positiveRouteMass Γ P)
    (Bad : Set (ℝ × JointAction n))
    (hbad : (Γ.F ⊗ₘ Γ.σ).real Bad < hi - lo)
    (hcompact : ∀ x, Γ.g < x.1 → x ∉ Bad → x.1 - Γ.g ∈ Icc ε H) :
    ∃ x : ℝ × JointAction n,
      (problem Γ i).BestResponse x.1 x.2 ∧ 0 < x.2.bid ∧
      0 < x.2.routeCount ∧ P x.2.routeCount ∧
      lo ≤ positiveRouteTail Γ P x.2.bid ∧ positiveRouteTail Γ P x.2.bid ≤ hi ∧
      x.1 - Γ.g ∈ Icc ε H ∧ x ∉ Bad := by
  have hgood : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ),
      (problem Γ i).BestResponse x.1 x.2 ∧ (x.1 ≤ Γ.g → x.2.routeCount = 0) :=
    (ae_bestResponse_compProd Γ hu i).and hact
  obtain ⟨x, hx, hxl, hxh, hxB, hxg⟩ :=
    (positiveBidStratum Γ hatom P).exists_good_in_band
      ((measurable_bid n).comp measurable_snd) hlo hlh hhi Bad hbad _ hgood
  have hv : Γ.g < x.1 := by
    by_contra hnot
    have hz := hxg.2 (le_of_not_gt hnot)
    have hk : 0 < x.2.routeCount := hx.2.1
    omega
  refine ⟨x, hxg.1, hx.1, hx.2.1, hx.2.2, ?_, ?_, hcompact x hv hxB, hxB⟩
  · simpa only [positiveBidStratum_tail] using hxl
  · simpa only [positiveBidStratum_tail] using hxh

theorem select_supported_route_band (Γ : FiniteGame m n c Seed)
    (hatom : PositiveVisibleAtomless Γ) (hu : UsersOptimal Γ)
    (hact : NonpositiveAbstention Γ) (i : Fin m) (P : ℕ → Prop)
    {lo hi ε H : ℝ} (hlo : 0 < lo) (hlh : lo < hi)
    (hhi : hi < positiveRouteMass Γ P)
    (htight : Γ.F.real {v | Γ.g < v ∧ v - Γ.g ∉ Icc ε H} < hi - lo) :
    ∃ w : ℝ, ∃ a : JointAction n,
      w ∈ Icc ε H ∧ (problem Γ i).BestResponse (w + Γ.g) a ∧
      0 < a.bid ∧ 0 < a.routeCount ∧ P a.routeCount ∧
      lo ≤ positiveRouteTail Γ P a.bid ∧ positiveRouteTail Γ P a.bid ≤ hi := by
  let Bad : Set (ℝ × JointAction n) :=
    {x | Γ.g < x.1 ∧ x.1 - Γ.g ∉ Icc ε H}
  have hBad : (Γ.F ⊗ₘ Γ.σ).real Bad < hi - lo := by
    have hm : MeasurableSet {v : ℝ | Γ.g < v ∧ v - Γ.g ∉ Icc ε H} :=
      (measurableSet_lt measurable_const measurable_id).inter
        (((measurable_id.sub_const Γ.g) measurableSet_Icc).compl)
    change (Γ.F ⊗ₘ Γ.σ).real {x | x.1 ∈ {v : ℝ | Γ.g < v ∧ v - Γ.g ∉ Icc ε H}} < _
    rw [joint_value_probability Γ _ hm]
    exact htight
  obtain ⟨x, hbr, hb, hk, hP, hl, hh, hx, _⟩ :=
    exists_supported_route_band Γ hatom hu hact i P hlo hlh hhi Bad hBad
      (fun x hv hn => by
        by_contra hnot
        exact hn ⟨hv, hnot⟩)
  refine ⟨x.1 - Γ.g, x.2, hx, ?_, hb, hk, hP, hl, hh⟩
  simpa only [sub_add_cancel] using hbr

end FCAppendix.Bayes
