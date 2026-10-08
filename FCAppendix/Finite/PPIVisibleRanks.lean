import FCAppendix.Finite.PPIRankTypes
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Filter Set Topology

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def visibleBidMeasure (Γ : FiniteGame m n c Seed) (j : Fin n) : Measure ℝ :=
  ((userLaw Γ).restrict {d | j ∈ firstK d.2 d.1.2.routeCount}).map (fun d => d.1.2.bid)

instance (Γ : FiniteGame m n c Seed) (j : Fin n) : IsFiniteMeasure (visibleBidMeasure Γ j) := by
  unfold visibleBidMeasure
  infer_instance

theorem visibleBidMeasure_tail (Γ : FiniteGame m n c Seed) (j : Fin n) (b : ℝ) :
    (visibleBidMeasure Γ j).real (Ioi b) = alphaGt Γ j b := by
  have hm : Measurable (fun d : UserDraw n => d.1.2.bid) := by
    simpa only [Function.comp_def] using (measurable_bid n).comp
      (measurable_snd.comp (measurable_fst : Measurable (Prod.fst : UserDraw n → ℝ × JointAction n)))
  unfold visibleBidMeasure alphaGt Measure.real
  rw [Measure.map_apply hm measurableSet_Ioi, Measure.restrict_apply (hm measurableSet_Ioi)]
  congr 2
  ext d
  simp only [mem_inter_iff, mem_preimage, mem_Ioi, mem_setOf_eq, aboveAt]
  exact and_comm

theorem visibleBidMeasure_singleton (Γ : FiniteGame m n c Seed)
    (hatom : PositiveVisibleAtomless Γ) (j : Fin n) (b : ℝ) (hb : 0 < b) :
    visibleBidMeasure Γ j {b} = 0 := by
  have hm : Measurable (fun d : UserDraw n => d.1.2.bid) := by
    simpa only [Function.comp_def] using (measurable_bid n).comp
      (measurable_snd.comp (measurable_fst : Measurable (Prod.fst : UserDraw n → ℝ × JointAction n)))
  unfold visibleBidMeasure
  rw [Measure.map_apply hm (measurableSet_singleton b),
    Measure.restrict_apply (hm (measurableSet_singleton b))]
  convert hatom j b hb using 2
  ext d
  simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_setOf_eq]
  exact and_comm

theorem continuousAt_real_tail_of_no_atom (μ : Measure ℝ) [IsFiniteMeasure μ]
    (b : ℝ) (hb : μ {b} = 0) : ContinuousAt (fun t => μ.real (Ioi t)) b := by
  have hint : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) μ (min b (b - 1)) (max b (b + 1)) :=
    intervalIntegrable_const
  have hc := (intervalIntegral.continuousWithinAt_primitive hb hint).continuousAt
    (Icc_mem_nhds (by linarith : b - 1 < b) (by linarith : b < b + 1))
  have he (t : ℝ) : μ.real (Ioi t) = μ.real (Ioi b) - ∫ _x in b..t, (1 : ℝ) ∂μ := by
    rcases le_total b t with hbt | htb
    · rw [intervalIntegral.integral_of_le hbt, setIntegral_const, smul_eq_mul, mul_one,
        ← Ioi_sdiff_Ioi, measureReal_sdiff (Ioi_subset_Ioi hbt) measurableSet_Ioi]
      ring
    · rw [intervalIntegral.integral_symm t b, intervalIntegral.integral_of_le htb,
        setIntegral_const, smul_eq_mul, mul_one, ← Ioi_sdiff_Ioi,
        measureReal_sdiff (Ioi_subset_Ioi htb) measurableSet_Ioi]
      ring
  exact (continuousAt_const.sub hc).congr_of_eventuallyEq (Eventually.of_forall he)

theorem alphaGt_continuousAt_pos (Γ : FiniteGame m n c Seed)
    (hatom : PositiveVisibleAtomless Γ) (j : Fin n) (b : ℝ) (hb : 0 < b) :
    ContinuousAt (alphaGt Γ j) b := by
  simpa only [visibleBidMeasure_tail] using continuousAt_real_tail_of_no_atom
    (visibleBidMeasure Γ j) b (visibleBidMeasure_singleton Γ hatom j b hb)

theorem alphaGt_continuousWithinAt_nonneg (Γ : FiniteGame m n c Seed) (j : Fin n) :
    ContinuousWithinAt (alphaGt Γ j) (Ici 0) 0 := by
  have hh := ((integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ))
    (visibleBidMeasure Γ j)).integrableOn (s := Ioi 0)).continuousWithinAt_Ici_primitive_Ioi
  simpa only [setIntegral_const, smul_eq_mul, mul_one, visibleBidMeasure_tail, id_eq] using hh

theorem alphaGt_tendsto_zero (Γ : FiniteGame m n c Seed) (j : Fin n) :
    Tendsto (alphaGt Γ j) atTop (𝓝 0) := by
  have hh := tendsto_integral_Ioi_zero (f := fun _ : ℝ => (1 : ℝ))
    (μ := visibleBidMeasure Γ j) tendsto_id
  simpa only [setIntegral_const, smul_eq_mul, mul_one, visibleBidMeasure_tail, id_eq] using hh

theorem exists_positive_bid_at_rank (Γ : FiniteGame m n c Seed)
    (hatom : PositiveVisibleAtomless Γ) (j : Fin n) (q : ℝ)
    (hq : 0 < q) (hqA : q < alphaGt Γ j 0) :
    ∃ b : ℝ, 0 < b ∧ alphaGt Γ j b = q := by
  obtain ⟨B, hB, htail⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    ((alphaGt_tendsto_zero Γ j).eventually (eventually_lt_nhds hq))).exists
  have hcont : ContinuousOn (alphaGt Γ j) (Icc 0 B) := by
    intro b hb
    rcases eq_or_lt_of_le hb.1 with he | hp
    · subst b
      exact (alphaGt_continuousWithinAt_nonneg Γ j).mono (fun x hx => hx.1)
    · exact (alphaGt_continuousAt_pos Γ hatom j b hp).continuousWithinAt
  obtain ⟨b, hb, heq⟩ := intermediate_value_Icc' hB.le hcont ⟨htail.le, hqA.le⟩
  have hb0 : b ≠ 0 := by
    intro he
    rw [he] at heq
    exact hqA.ne heq.symm
  exact ⟨b, lt_of_le_of_ne hb.1 hb0.symm, heq⟩

theorem exists_actual_draw_in_rank_band (Γ : FiniteGame m n c Seed)
    (hatom : PositiveVisibleAtomless Γ) (j : Fin n) (lo hi : ℝ)
    (hlo : 0 < lo) (hlt : lo < hi) (hhi : hi < alphaGt Γ j 0)
    (P : UserDraw n → Prop) (hP : ∀ᵐ d ∂userLaw Γ, P d) :
    ∃ d : UserDraw n, P d ∧ j ∈ firstK d.2 d.1.2.routeCount ∧ 0 < d.1.2.bid ∧
      lo ≤ alphaGt Γ j d.1.2.bid ∧ alphaGt Γ j d.1.2.bid ≤ hi := by
  obtain ⟨b, hb, hbrank⟩ := exists_positive_bid_at_rank Γ hatom j hi (hlo.trans hlt) hhi
  obtain ⟨t, _, htrank⟩ := exists_positive_bid_at_rank Γ hatom j lo hlo (hlt.trans hhi)
  have hbt : b < t := by
    by_contra hnot
    have hh := alphaGt_antitone Γ j (le_of_not_gt hnot)
    rw [hbrank, htrank] at hh
    exact hlt.not_ge hh
  have hsub : aboveAt j t ⊆ aboveAt j b := fun d hd => ⟨hd.1, hbt.trans hd.2⟩
  have hmass : 0 < (userLaw Γ).real (aboveAt j b \ aboveAt j t) := by
    rw [measureReal_sdiff hsub (measurableSet_aboveAt j t)]
    change 0 < alphaGt Γ j b - alphaGt Γ j t
    rw [hbrank, htrank]
    exact sub_pos.mpr hlt
  have hmass' : userLaw Γ (aboveAt j b \ aboveAt j t) ≠ 0 := by
    intro he
    rw [Measure.real, he, ENNReal.toReal_zero] at hmass
    exact (lt_irrefl _ hmass)
  obtain ⟨d, hd, hdP⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hmass' (ae_restrict_of_ae hP)
  have hdt : d.1.2.bid ≤ t := by
    by_contra hnot
    exact hd.2 ⟨hd.1.1, lt_of_not_ge hnot⟩
  refine ⟨d, hdP, hd.1.1, hb.trans hd.1.2, ?_, ?_⟩
  · rw [← htrank]
    exact alphaGt_antitone Γ j hdt
  · rw [← hbrank]
    exact alphaGt_antitone Γ j hd.1.2.le

theorem ppi_rank_le_value_tail_of_rare_response {N : ℕ}
    (Γ : FiniteGame (N + 1) n c Seed) [NullSingletonClass Γ.F]
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j) (hu : UsersOptimal Γ)
    (i : Fin (N + 1)) (j : Fin n) (V : Set ℝ) (hV : ∀ᵐ w ∂Γ.F, w ∈ V)
    (ε : ℝ)
    (hroute : ∀ w ∈ V, ∀ a : JointAction n, (problem Γ i).BestResponse w a →
      1 ≤ a.routeCount → ε ≤ binomBelow N (alphaGt Γ j a.bid) c → a.routeCount = 1)
    (b : ℝ) (hb : 0 < b) (hq : ε ≤ binomBelow N (alphaGt Γ j b) c)
    (v : ℝ) (a : JointAction n) (ha : (problem Γ i).BestResponse v a)
    (hra : ((problem Γ i).outcome a).success < ε) :
    alphaGt Γ j b ≤ Γ.F.real (Ioi v) / n := by
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  have hbr : ∀ᵐ d ∂userLaw Γ, (problem Γ i).BestResponse d.1.1 d.1.2 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_bestResponse_compProd Γ hu i)
  have hpres : MeasurePreserving (fun d : UserDraw n => d.1.1) (userLaw Γ) Γ.F :=
    ⟨measurable_fst.comp measurable_fst, userLaw_value_map Γ⟩
  have hvne : ∀ᵐ w ∂Γ.F, w ≠ v := by
    simpa only [mem_singleton_iff] using
      (measure_eq_zero_iff_ae_notMem.mp (measure_singleton v : Γ.F {v} = 0))
  have hvalues := hpres.quasiMeasurePreserving.ae (hV.and hvne)
  let E : Set (ℝ × JointAction n) := {x | v < x.1}
  let R : Set (Equiv.Perm (Fin n)) := {τ | j ∈ firstK τ 1}
  have hsub : aboveAt j b ≤ᵐ[userLaw Γ] E ×ˢ R := by
    filter_upwards [hbr, hvalues] with d hd hv hreach
    have hk : 1 ≤ d.1.2.routeCount := by
      have hcard := Finset.card_pos.mpr ⟨j, hreach.1⟩
      rwa [card_firstK _ _ d.1.2.routeCount_le] at hcard
    have hmono := rank_probability_monotone_bid Γ i j hreach.2.le
    simp only [Nat.add_sub_cancel] at hmono
    have hdq := hq.trans hmono
    have hroute1 := hroute d.1.1 hv.1 d.1.2 hd hk hdq
    have hsuccess : ε ≤ ((problem Γ i).outcome d.1.2).success := by
      rw [singleton_success Γ hn i d.1.2 hroute1,
        ppi_meanAcceptProb_eq_rank Γ hA hatom hj i j d.1.2.bid (hb.trans hreach.2)]
      exact hdq
    have hw : v < d.1.1 := by
      rcases lt_or_gt_of_ne hv.2 with hw | hw
      · have hh := (problem Γ i).success_order d.1.1 v hw d.1.2 a hd ha
        exact (hra.not_ge (hsuccess.trans hh)).elim
      · exact hw
    exact ⟨hw, by simpa only [R, mem_setOf_eq, ← hroute1] using hreach.1⟩
  have hE : (Γ.F ⊗ₘ Γ.σ) E = Γ.F (Ioi v) := by
    calc
      (Γ.F ⊗ₘ Γ.σ) E = (Γ.F ⊗ₘ Γ.σ).fst (Ioi v) := by
        rw [Measure.fst, Measure.map_apply measurable_fst measurableSet_Ioi]
        rfl
      _ = Γ.F (Ioi v) := by rw [Measure.fst_compProd]
  have hmass := ENNReal.toReal_mono (measure_ne_top (userLaw Γ) (E ×ˢ R)) (measure_mono_ae hsub)
  change alphaGt Γ j b ≤ (userLaw Γ).real (E ×ˢ R) at hmass
  rw [Measure.real, userLaw, Measure.prod_prod, ENNReal.toReal_mul, hE] at hmass
  change alphaGt Γ j b ≤ Γ.F.real (Ioi v) * (permLaw n).real R at hmass
  rw [permLaw_mem_firstK n 1 hn hn j, Nat.cast_one, mul_one_div] at hmass
  exact hmass

theorem ppi_success_ge_of_rank_mass {N : ℕ}
    (Γ : FiniteGame (N + 1) n c Seed) [NullSingletonClass Γ.F]
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j) (hu : UsersOptimal Γ)
    (i : Fin (N + 1)) (j : Fin n) (V : Set ℝ) (hV : ∀ᵐ w ∂Γ.F, w ∈ V)
    (ε : ℝ)
    (hroute : ∀ w ∈ V, ∀ a : JointAction n, (problem Γ i).BestResponse w a →
      1 ≤ a.routeCount → ε ≤ binomBelow N (alphaGt Γ j a.bid) c → a.routeCount = 1)
    (b : ℝ) (hb : 0 < b) (hq : ε ≤ binomBelow N (alphaGt Γ j b) c)
    (v : ℝ) (hmass : Γ.F.real (Ioi v) / n < alphaGt Γ j b)
    (a : JointAction n) (ha : (problem Γ i).BestResponse v a) :
    ε ≤ ((problem Γ i).outcome a).success := by
  by_contra hnot
  exact hmass.not_ge (ppi_rank_le_value_tail_of_rare_response Γ hA hatom hj hu i j V hV
    ε hroute b hb hq v a ha (lt_of_not_ge hnot))

end FCAppendix.Bayes
