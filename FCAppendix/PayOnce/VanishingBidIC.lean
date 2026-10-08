import FCAppendix.PayOnce.SaturatedBounds

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open scoped ProbabilityTheory BigOperators
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem success_gap_le_bid_over_netvalue (Γ : FiniteGame m n c Seed)
    (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (i : Fin m) {v w : ℝ} (hv : Γ.g < v) (hvw : v < w)
    {a b : JointAction n} (ha : (problem Γ i).BestResponse v a)
    (hb : (problem Γ i).BestResponse w b) :
    0 ≤ ((problem Γ i).outcome b).success - ((problem Γ i).outcome a).success ∧
      ((problem Γ i).outcome b).success - ((problem Γ i).outcome a).success ≤ b.bid/(v-Γ.g) := by
  have hsort := (problem Γ i).success_order v w hvw a b ha hb
  refine ⟨sub_nonneg.mpr hsort, ?_⟩
  have hic := ha b
  rw [payoff_once Γ hA hG, payoff_once Γ hA hG] at hic
  have hlow := mul_nonneg a.bid_nonneg (CountLaw.success_nonneg ((problem Γ i).outcome a))
  have hhigh := mul_le_of_le_one_right b.bid_nonneg (CountLaw.success_le_one ((problem Γ i).outcome b))
  apply (le_div_iff₀ (sub_pos.mpr hv)).mpr
  nlinarith

theorem tendsto_success_gap_zero_of_bid_zero {m c : ℕ → ℕ} {n : ℕ}
    (Γ : ∀ t, FiniteGame (m t) n (c t) Seed) (i : ∀ t, Fin (m t))
    (hA : ∀ t, (Γ t).A = Schedule.once n) (hG : ∀ t, (Γ t).G = Schedule.once n)
    {g v w : ℝ} (hbase : ∀ t, (Γ t).g = g) (hv : g < v) (hvw : v < w)
    (a b : ℕ → JointAction n)
    (ha : ∀ t, (problem (Γ t) (i t)).BestResponse v (a t))
    (hb : ∀ t, (problem (Γ t) (i t)).BestResponse w (b t))
    (hbid : Tendsto (fun t => (b t).bid) atTop (𝓝 0)) :
    Tendsto (fun t => ((problem (Γ t) (i t)).outcome (b t)).success -
      ((problem (Γ t) (i t)).outcome (a t)).success) atTop (𝓝 0) := by
  have hbound (t : ℕ) := success_gap_le_bid_over_netvalue (Γ t) (hA t) (hG t)
    (i t) (by rwa [hbase t]) hvw (ha t) (hb t)
  apply squeeze_zero (fun t => (hbound t).1)
    (fun t => by simpa only [hbase t] using (hbound t).2)
  simpa using hbid.div_const (v-g)

end FCAppendix.Bayes

namespace FCAppendix.PayOnce.VanishingBidIC
open MeasureTheory Set Filter Topology

theorem tendsto_bid_zero_of_monotone_tail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (b : ℕ → ℝ → ℝ) (hmono : ∀ t, Monotone (b t)) (hpos : ∀ t v, 0 ≤ b t v)
    (htail : ∀ ε : ℝ, 0 < ε → Tendsto (fun t => μ.real {v | ε ≤ b t v}) atTop (𝓝 0))
    {v : ℝ} (hv : 0 < μ.real (Ici v)) : Tendsto (fun t => b t v) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun t => ha.trans_le (hpos t v)
  · intro ε hε
    have ht := (htail ε hε).eventually_lt_const hv
    filter_upwards [ht] with t ht
    by_contra hnot
    have he : Ici v ⊆ {w | ε ≤ b t w} := by
      intro w hw
      exact (le_of_not_gt hnot).trans (hmono t hw)
    exact ht.not_ge (measureReal_mono he)

end FCAppendix.PayOnce.VanishingBidIC

namespace FCAppendix.PayOnce.VanishingBidIC
open MeasureTheory Set Filter Topology

theorem ae_real_Ici_pos (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∀ᵐ v ∂μ, 0 < μ.real (Ici v) := by
  let S : Set ℝ := {v | ∀ q : ℚ, μ (Ioi (q : ℝ)) = 0 → v ≤ q}
  have hS : ∀ᵐ v ∂μ, v ∈ S := by
    apply ae_all_iff.mpr
    intro q
    by_cases hq : μ (Ioi (q : ℝ)) = 0
    · have hh := measure_eq_zero_iff_ae_notMem.mp hq
      filter_upwards [hh] with v hv _
      exact le_of_not_gt hv
    · exact Filter.Eventually.of_forall fun _ h => (hq h).elim
  let N : Set ℝ := {v | μ (Ici v) = 0 ∧ v ∈ S}
  have hN : N.Countable := by
    apply (countable_setOf_isolated_right_within (s := S)).mono
    intro v hv
    refine ⟨hv.2, ?_⟩
    have he : S ∩ Ioi v = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro w hw
      obtain ⟨q, hvq, hqw⟩ := exists_rat_btwn (show v < w from hw.2)
      have hq : μ (Ioi (q : ℝ)) = 0 := measure_mono_null (fun u hu => (hvq.trans hu).le) hv.1
      exact hqw.not_ge (hw.1 q hq)
    rw [he]
    exact nhdsWithin_empty v
  have hNzero : μ N = 0 := by
    have he : N = ⋃ v ∈ N, ({v} : Set ℝ) := by ext v; simp
    rw [he]
    apply (measure_biUnion_null_iff hN).mpr
    intro v hv
    exact measure_mono_null (singleton_subset_iff.mpr (le_refl v)) hv.1
  have havoid := measure_eq_zero_iff_ae_notMem.mp hNzero
  filter_upwards [hS, havoid] with v hv hnot
  exact ENNReal.toReal_pos (fun hz => hnot ⟨hz, hv⟩) (measure_ne_top _ _)

theorem ae_tendsto_bid_zero_of_monotone_tail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (b : ℕ → ℝ → ℝ) (hmono : ∀ t, Monotone (b t)) (hpos : ∀ t v, 0 ≤ b t v)
    (htail : ∀ ε : ℝ, 0 < ε → Tendsto (fun t => μ.real {v | ε ≤ b t v}) atTop (𝓝 0)) :
    ∀ᵐ v ∂μ, Tendsto (fun t => b t v) atTop (𝓝 0) := by
  filter_upwards [ae_real_Ici_pos μ] with v hv
  exact tendsto_bid_zero_of_monotone_tail μ b hmono hpos htail hv

end FCAppendix.PayOnce.VanishingBidIC

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open scoped ProbabilityTheory BigOperators
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem exists_monotone_bid_bestResponse_all {k : ℕ} (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hvalue : PositiveValueAtomless Γ) (hactive : ∀ᵐ v ∂Γ.F, Γ.g < v) :
    ∃ bid : ℝ → ℝ, Monotone bid ∧ Measurable bid ∧
      (∀ v, 0 ≤ bid v ∧ bid v ≤ max (v-Γ.g) 0) ∧
      ∀ᵐ v ∂Γ.F, 0 < bid v ∧ bid v < v-Γ.g ∧
        (∀ i, (problem Γ i).BestResponse v (safeFullBid (k+1) (bid v))) ∧
        ∀ᵐ a ∂Γ.σ v, a = safeFullBid (k+1) (bid v) := by
  let i : Fin m := ⟨0, by omega⟩
  obtain ⟨bid, hmono, hmeas, hbound, htype⟩ :=
    exists_monotone_pure_bid Γ hk hc hcm hA hG hu B hB hsym hvalue i
  refine ⟨bid, hmono, hmeas, hbound, ?_⟩
  have hall := ae_all_iff.mpr hu
  filter_upwards [htype, hactive, hall] with v hv hactive hbest
  obtain ⟨hb, hbw, hpure⟩ := hv hactive
  have he : ∀ᵐ a ∂Γ.σ v, a = safeFullBid (k+1) (bid v) := by
    filter_upwards [hpure] with a ha
    exact (ha.1 ▸ safeFullBid_eq_of_fullRoute a ha.2).symm
  refine ⟨hb, hbw, ?_, he⟩
  intro j
  obtain ⟨a, ha, hea⟩ := ((hbest j).and he).exists
  exact hea ▸ ha

end FCAppendix.Bayes

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open scoped ProbabilityTheory BigOperators
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem realBidLaw_eq_map_of_pure (Γ : FiniteGame m n c Seed) (bid : ℝ → ℝ)
    (hmeas : Measurable bid) (hpos : ∀ v, 0 ≤ bid v)
    (hpure : ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v, a = safeFullBid n (bid v)) :
    realBidLaw Γ = Γ.F.map bid := by
  rw [realBidLaw_eq_action_map]
  have he : (fun x : ℝ × JointAction n => x.2.bid) =ᵐ[Γ.F ⊗ₘ Γ.σ] fun x => bid x.1 := by
    apply Measure.ae_compProd_of_ae_ae
      (measurableSet_eq_fun ((measurable_bid n).comp measurable_snd) (hmeas.comp measurable_fst))
    filter_upwards [hpure] with v hv
    filter_upwards [hv] with a ha
    simp only [Function.comp_apply, ha, safeFullBid, fullBid, max_eq_left (hpos v)]
  rw [Measure.map_congr he]
  change (Γ.F ⊗ₘ Γ.σ).map (bid ∘ Prod.fst) = _
  rw [← Measure.map_map hmeas measurable_fst]
  change Measure.map bid (Measure.fst (Γ.F ⊗ₘ Γ.σ)) = _
  rw [Measure.fst_compProd]

noncomputable def averageTypeSuccess (Γ : FiniteGame m n c Seed) (bid : ℝ → ℝ) (v : ℝ) : ℝ :=
  (∑ i, ((problem Γ i).outcome (safeFullBid n (bid v))).success) / m

theorem averageTypeSuccess_bounds (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (bid : ℝ → ℝ) (v : ℝ) : averageTypeSuccess Γ bid v ∈ Icc (0 : ℝ) 1 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨div_nonneg (Finset.sum_nonneg fun i _ => CountLaw.success_nonneg _) hmR.le, ?_⟩
  apply (div_le_one hmR).mpr
  simpa using Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
    (fun i _ => CountLaw.success_le_one ((problem Γ i).outcome (safeFullBid n (bid v))))

theorem measurable_averageTypeSuccess (Γ : FiniteGame m n c Seed) {bid : ℝ → ℝ}
    (hb : Measurable bid) : Measurable (averageTypeSuccess Γ bid) := by
  apply Measurable.div_const
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_success Γ i).comp ((measurable_safeFullBid n).comp hb)

theorem averageTypeSuccess_gap_le (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (bid : ℝ → ℝ) {v w : ℝ} (hv : Γ.g < v) (hvw : v < w) (hbw : 0 ≤ bid w)
    (hbestv : ∀ i, (problem Γ i).BestResponse v (safeFullBid n (bid v)))
    (hbestw : ∀ i, (problem Γ i).BestResponse w (safeFullBid n (bid w))) :
    0 ≤ averageTypeSuccess Γ bid w - averageTypeSuccess Γ bid v ∧
      averageTypeSuccess Γ bid w - averageTypeSuccess Γ bid v ≤ bid w/(v-Γ.g) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hh (i : Fin m) := success_gap_le_bid_over_netvalue Γ hA hG i hv hvw (hbestv i) (hbestw i)
  have hsum0 := Finset.sum_nonneg (s := (Finset.univ : Finset (Fin m))) (fun i _ => (hh i).1)
  have hsum1 := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) (fun i _ => (hh i).2)
  have hwb : (safeFullBid n (bid w)).bid = bid w := max_eq_left hbw
  simp only [hwb, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum0 hsum1
  constructor
  · exact sub_nonneg.mpr (div_le_div_of_nonneg_right (sub_nonneg.mp hsum0) hmR.le)
  · unfold averageTypeSuccess
    rw [← sub_div]
    exact (div_le_iff₀ hmR).mpr (by simpa only [mul_comm] using hsum1)

end FCAppendix.Bayes
