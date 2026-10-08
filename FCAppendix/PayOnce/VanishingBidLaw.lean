import FCAppendix.PayOnce.VanishingBidIC
import FCAppendix.PayOnce.CompactifiedBidLaws

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open scoped ProbabilityTheory BigOperators
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem compactifiedBidLaw_eq_map_realBidLaw (Γ : FiniteGame m n c Seed) (hn : 0 < n)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = n) :
    (PayOnce.CompactifiedBidLaws.bidLaw Γ : Measure ENNReal) =
      (realBidLaw Γ).map ENNReal.ofReal := by
  change (userLaw Γ).map (fun d => ENNReal.ofReal (PayOnce.CompactifiedBidLaws.effectiveBid d.1.2)) = _
  unfold realBidLaw
  rw [Measure.map_map ENNReal.measurable_ofReal measurable_drawBid]
  apply Measure.map_congr
  have hr := (measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ) (ν := permLaw n)).quasiMeasurePreserving.ae hroute
  filter_upwards [hr] with d hd
  simp only [Function.comp_apply, PayOnce.CompactifiedBidLaws.effectiveBid, hd, if_neg (Nat.ne_of_gt hn)]

end FCAppendix.Bayes

namespace FCAppendix.PayOnce.VanishingBidIC
open MeasureTheory ProbabilityTheory Set Filter Topology

theorem tendsto_real_tails_zero_of_compactified_weak_zero
    (G : ℕ → Measure ℝ) (K : ℕ → ProbabilityMeasure ENNReal)
    (hmap : ∀ t, (K t : Measure ENNReal) = (G t).map ENNReal.ofReal)
    (hweak : Tendsto K atTop (𝓝 (⟨Measure.dirac 0, inferInstance⟩ : ProbabilityMeasure ENNReal)))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun t => (G t).real (Ici ε)) atTop (𝓝 0) := by
  have hεE : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  have hz : (Measure.dirac (0 : ENNReal)) (Ici (ENNReal.ofReal ε)) = 0 := by
    simp only [Measure.dirac_apply' _ measurableSet_Ici, mem_Ici, not_le_of_gt hεE,
      not_false_eq_true, indicator_of_notMem]
  have hf : (Measure.dirac (0 : ENNReal)) (frontier (Ici (ENNReal.ofReal ε))) = 0 :=
    measure_mono_null isClosed_Ici.frontier_subset hz
  have ht := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hweak hf
  change Tendsto (fun t => (K t : Measure ENNReal) (Ici (ENNReal.ofReal ε))) atTop
    (𝓝 ((Measure.dirac (0 : ENNReal)) (Ici (ENNReal.ofReal ε)))) at ht
  rw [hz] at ht
  have he (t : ℕ) : (K t : Measure ENNReal) (Ici (ENNReal.ofReal ε)) = (G t) (Ici ε) := by
    rw [hmap t, Measure.map_apply ENNReal.measurable_ofReal measurableSet_Ici]
    congr 1
    ext b
    simp only [mem_preimage, mem_Ici, ENNReal.ofReal_le_ofReal_iff', not_le_of_gt hε, or_false]
  simp_rw [he] at ht
  simpa only [measureReal_def, ENNReal.toReal_zero, Function.comp_def] using
    (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp ht

theorem ae_bid_zero_of_actual_weak_zero {m c : ℕ → ℕ} {n : ℕ}
    {Seed : Type*} [MeasurableSpace Seed]
    (Γ : ∀ t, Bayes.FiniteGame (m t) n (c t) Seed) (hn : 0 < n)
    (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ∀ t, (Γ t).F = F)
    (bid : ℕ → ℝ → ℝ) (hmono : ∀ t, Monotone (bid t)) (hpos : ∀ t v, 0 ≤ bid t v)
    (hpure : ∀ t, ∀ᵐ v ∂(Γ t).F, ∀ᵐ a ∂(Γ t).σ v,
      a = Bayes.safeFullBid n (bid t v))
    (hroute : ∀ t, ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ), x.2.routeCount = n)
    (hweak : Tendsto (fun t => CompactifiedBidLaws.bidLaw (Γ t)) atTop
      (𝓝 (⟨Measure.dirac 0, inferInstance⟩ : ProbabilityMeasure ENNReal))) :
    ∀ᵐ v ∂F, Tendsto (fun t => bid t v) atTop (𝓝 0) := by
  apply ae_tendsto_bid_zero_of_monotone_tail F bid hmono hpos
  intro ε hε
  have ht := tendsto_real_tails_zero_of_compactified_weak_zero
    (fun t => Bayes.realBidLaw (Γ t)) (fun t => CompactifiedBidLaws.bidLaw (Γ t))
    (fun t => Bayes.compactifiedBidLaw_eq_map_realBidLaw (Γ t) hn (hroute t)) hweak hε
  have he (t : ℕ) : (Bayes.realBidLaw (Γ t)).real (Ici ε) = F.real {v | ε ≤ bid t v} := by
    rw [Bayes.realBidLaw_eq_map_of_pure (Γ t) (bid t) (hmono t).measurable (hpos t) (hpure t), hF t]
    unfold Measure.real
    rw [Measure.map_apply (hmono t).measurable measurableSet_Ici]
    rfl
  simpa only [he] using ht

end FCAppendix.PayOnce.VanishingBidIC

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open scoped ProbabilityTheory BigOperators

theorem ae_pair_average_success_gap_zero {m c : ℕ → ℕ} {n : ℕ}
    {Seed : Type*} [MeasurableSpace Seed]
    (Γ : ∀ t, FiniteGame (m t) n (c t) Seed) (hm : ∀ t, 0 < m t)
    (hA : ∀ t, (Γ t).A = Schedule.once n) (hG : ∀ t, (Γ t).G = Schedule.once n)
    (F : Measure ℝ) [IsProbabilityMeasure F] {g : ℝ} (hbase : ∀ t, (Γ t).g = g)
    (hactive : ∀ᵐ v ∂F, g < v) (bid : ℕ → ℝ → ℝ) (hpos : ∀ t v, 0 ≤ bid t v)
    (hbest : ∀ t, ∀ᵐ v ∂F, ∀ i, (problem (Γ t) i).BestResponse v (safeFullBid n (bid t v)))
    (hbidzero : ∀ᵐ v ∂F, Tendsto (fun t => bid t v) atTop (𝓝 0)) :
    ∀ᵐ z ∂F.prod F, Tendsto (fun t => averageTypeSuccess (Γ t) (bid t) z.2 -
      averageTypeSuccess (Γ t) (bid t) z.1) atTop (𝓝 0) := by
  have hgood := hactive.and (hbidzero.and (ae_all_iff.mpr hbest))
  have hleft := (measurePreserving_fst (μ := F) (ν := F)).quasiMeasurePreserving.ae hgood
  have hright := (measurePreserving_snd (μ := F) (ν := F)).quasiMeasurePreserving.ae hgood
  have hgap {v w : ℝ} (hv : g < v)
      (hbestv : ∀ t i, (problem (Γ t) i).BestResponse v (safeFullBid n (bid t v)))
      (hbestw : ∀ t i, (problem (Γ t) i).BestResponse w (safeFullBid n (bid t w)))
      (hzero : Tendsto (fun t => bid t w) atTop (𝓝 0)) (hvw : v < w) :
      Tendsto (fun t => averageTypeSuccess (Γ t) (bid t) w -
        averageTypeSuccess (Γ t) (bid t) v) atTop (𝓝 0) := by
    have hb (t : ℕ) := averageTypeSuccess_gap_le (Γ t) (hm t) (hA t) (hG t)
      (bid t) (by rwa [hbase t]) hvw (hpos t w) (hbestv t) (hbestw t)
    apply squeeze_zero (fun t => (hb t).1)
      (fun t => by simpa only [hbase t] using (hb t).2)
    simpa using hzero.div_const (v-g)
  filter_upwards [hleft, hright] with z hz1 hz2
  rcases lt_trichotomy z.1 z.2 with h | h | h
  · exact hgap hz1.1 hz1.2.2 hz2.2.2 hz2.2.1 h
  · simp only [h, sub_self]
    exact tendsto_const_nhds
  · have hh := hgap hz2.1 hz2.2.2 hz1.2.2 hz1.2.1 h
    simpa only [neg_sub, neg_zero] using hh.neg

end FCAppendix.Bayes

namespace FCAppendix.PayOnce.VanishingBidIC
open MeasureTheory ProbabilityTheory Set Filter Topology

theorem tendsto_integral_pair_abs_gap_zero (F : Measure ℝ) [IsProbabilityMeasure F]
    (Q : ℕ → ℝ → ℝ) (hQ : ∀ t, Measurable (Q t))
    (hbound : ∀ t v, Q t v ∈ Icc (0 : ℝ) 1)
    (hpair : ∀ᵐ z ∂F.prod F, Tendsto (fun t => Q t z.2-Q t z.1) atTop (𝓝 0)) :
    Tendsto (fun t => ∫ z, |Q t z.2-Q t z.1| ∂F.prod F) atTop (𝓝 0) := by
  have hm (t : ℕ) : AEStronglyMeasurable (fun z : ℝ × ℝ => |Q t z.2-Q t z.1|) (F.prod F) :=
    (((hQ t).comp measurable_snd).sub ((hQ t).comp measurable_fst)).abs.aestronglyMeasurable
  have hb (t : ℕ) : ∀ᵐ z ∂F.prod F, ‖|Q t z.2-Q t z.1|‖ ≤ (1 : ℝ) := by
    apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs, abs_abs, abs_le]
    constructor <;> linarith [(hbound t z.1).1, (hbound t z.1).2,
      (hbound t z.2).1, (hbound t z.2).2]
  have hl : ∀ᵐ z ∂F.prod F, Tendsto (fun t => |Q t z.2-Q t z.1|) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hpair] with z hz
    simpa only [abs_zero] using hz.abs
  have hh := tendsto_integral_of_dominated_convergence (fun _ : ℝ × ℝ => (1 : ℝ))
    hm (integrable_const _) hb hl
  simpa only [integral_zero] using hh

end FCAppendix.PayOnce.VanishingBidIC
