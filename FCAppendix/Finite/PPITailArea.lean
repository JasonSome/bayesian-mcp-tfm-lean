import FCAppendix.Finite.PPIVisibleRanks

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Filter Set Topology
open scoped BigOperators
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem value_tail_le_rank_of_higher_bids (Γ : FiniteGame m n c Seed)
    (j : Fin n) (v b : ℝ)
    (hb : ∀ᵐ d ∂userLaw Γ, v < d.1.1 → b < d.1.2.bid ∧ 1 ≤ d.1.2.routeCount) :
    Γ.F.real (Ioi v) / n ≤ alphaGt Γ j b := by
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  let E : Set (ℝ × JointAction n) := {x | v < x.1}
  let R : Set (Equiv.Perm (Fin n)) := {τ | j ∈ firstK τ 1}
  have hsub : E ×ˢ R ≤ᵐ[userLaw Γ] aboveAt j b := by
    filter_upwards [hb] with d hd hmem
    obtain ⟨hbid, hroute⟩ := hd hmem.1
    exact ⟨firstK_mono d.2 hroute hmem.2, hbid⟩
  have hmass := ENNReal.toReal_mono (measure_ne_top (userLaw Γ) (aboveAt j b))
    (measure_mono_ae hsub)
  change (userLaw Γ).real (E ×ˢ R) ≤ alphaGt Γ j b at hmass
  have hE : (Γ.F ⊗ₘ Γ.σ) E = Γ.F (Ioi v) := by
    calc
      (Γ.F ⊗ₘ Γ.σ) E = (Γ.F ⊗ₘ Γ.σ).fst (Ioi v) := by
        rw [Measure.fst, Measure.map_apply measurable_fst measurableSet_Ioi]
        rfl
      _ = Γ.F (Ioi v) := by rw [Measure.fst_compProd]
  rw [Measure.real, userLaw, Measure.prod_prod, ENNReal.toReal_mul, hE] at hmass
  change Γ.F.real (Ioi v) * (permLaw n).real R ≤ alphaGt Γ j b at hmass
  rwa [permLaw_mem_firstK n 1 hn hn j, Nat.cast_one, mul_one_div] at hmass

theorem route_pos_of_success_pos (Γ : FiniteGame m n c Seed)
    (i : Fin m) (act : JointAction n) (hs : 0 < ((problem Γ i).outcome act).success) :
    1 ≤ act.routeCount := by
  by_contra hn
  have hz : act.routeCount = 0 := by omega
  have hh := load_le_routeCount_mul_success Γ i act
  have hh' := ((problem Γ i).outcome act).success_le_load
  simp only [hz, Nat.cast_zero, zero_mul] at hh
  linarith

theorem ppi_value_tail_le_rank_of_success_gap (Γ : FiniteGame m n c Seed)
    (hA : Γ.A = Schedule.ppi n) (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hu : UsersOptimal Γ) (i : Fin m) (j : Fin n) (v b : ℝ)
    (act : JointAction n) (ha : (problem Γ i).BestResponse v act)
    (hgap : (n : ℝ) * binomBelow (m - 1) (alphaGt Γ j b) c <
      ((problem Γ i).outcome act).success)
    (hs : 0 < ((problem Γ i).outcome act).success) :
    Γ.F.real (Ioi v) / n ≤ alphaGt Γ j b := by
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  have hbr : ∀ᵐ d ∂userLaw Γ, (problem Γ i).BestResponse d.1.1 d.1.2 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_bestResponse_compProd Γ hu i)
  apply value_tail_le_rank_of_higher_bids Γ j v b
  filter_upwards [hbr] with d hd hv
  have horder := (problem Γ i).success_order v d.1.1 hv act d.1.2 ha hd
  have hroute := route_pos_of_success_pos Γ i d.1.2 (hs.trans_le horder)
  refine ⟨?_, hroute⟩
  by_contra hnot
  have hb : d.1.2.bid ≤ b := le_of_not_gt hnot
  have hq := (ppi_meanAcceptProb_le_rank Γ hA hj i j d.1.2.bid d.1.2.bid_nonneg).trans
    (rank_probability_monotone_bid Γ i j hb)
  have hupper := (success_le_n_meanAcceptProb Γ hn i d.1.2).trans
    (mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg n))
  linarith

theorem continuous_binomBelow (N c : ℕ) : Continuous (fun p => binomBelow N p c) := by
  unfold binomBelow PiBinomial.pmf
  fun_prop

theorem ppi_success_le_value_tail_rank (Γ : FiniteGame m n c Seed)
    (hA : Γ.A = Schedule.ppi n) (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hatom : PositiveVisibleAtomless Γ) (hu : UsersOptimal Γ)
    (hpos : ∀ᵐ d ∂userLaw Γ, 1 ≤ d.1.2.routeCount → 0 < d.1.2.bid)
    (i : Fin m) (j : Fin n) (v : ℝ) (htail : 0 < Γ.F.real (Ioi v))
    (act : JointAction n) (ha : (problem Γ i).BestResponse v act) :
    ((problem Γ i).outcome act).success ≤
      (n : ℝ) * binomBelow (m - 1) (Γ.F.real (Ioi v) / n) c := by
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  let q := Γ.F.real (Ioi v) / n
  have hq0 : 0 < q := div_pos htail hnR
  have hq1 : q ≤ 1 := by
    apply (div_le_iff₀ hnR).mpr
    have hm : Γ.F.real (Ioi v) ≤ 1 := measureReal_le_one
    have hh : (1 : ℝ) ≤ n := by exact_mod_cast hn
    simpa only [one_mul] using hm.trans hh
  have hQ0 : 0 ≤ binomBelow (m - 1) q c := by
    unfold binomBelow PiBinomial.pmf
    apply Finset.sum_nonneg
    intro r _
    positivity
  by_contra hnot
  have hgap : (n : ℝ) * binomBelow (m - 1) q c <
      ((problem Γ i).outcome act).success := lt_of_not_ge hnot
  have hs : 0 < ((problem Γ i).outcome act).success :=
    (mul_nonneg hnR.le hQ0).trans_lt hgap
  have hbr : ∀ᵐ d ∂userLaw Γ, (problem Γ i).BestResponse d.1.1 d.1.2 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_bestResponse_compProd Γ hu i)
  have hqα : q ≤ alphaGt Γ j 0 := by
    apply value_tail_le_rank_of_higher_bids Γ j v 0
    filter_upwards [hbr, hpos] with d hd hp hv
    have horder := (problem Γ i).success_order v d.1.1 hv act d.1.2 ha hd
    have hroute := route_pos_of_success_pos Γ i d.1.2 (hs.trans_le horder)
    exact ⟨hp hroute, hroute⟩
  let r : ℕ → ℝ := fun k => q * (1 - 1 / ((k : ℝ) + 2))
  have hr0 (k : ℕ) : 0 < r k := by
    dsimp [r]
    apply mul_pos hq0
    have hk : (1 : ℝ) < (k : ℝ) + 2 := by have hh := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith
    have hh : (1 : ℝ) / ((k : ℝ) + 2) < 1 := (div_lt_one (by positivity)).mpr hk
    linarith
  have hrq (k : ℕ) : r k < q := by
    dsimp [r]
    have hp : 0 < (1 : ℝ) / ((k : ℝ) + 2) := by positivity
    nlinarith
  have hr : Tendsto r atTop (𝓝 q) := by
    have hh : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
    simpa only [r, sub_zero, mul_one] using (hh.const_sub 1).const_mul q
  have hlim := ((continuous_binomBelow (m - 1) c).continuousAt.tendsto.comp hr).const_mul (n : ℝ)
  obtain ⟨k, hk⟩ := ((tendsto_order.mp hlim).2 _ hgap).exists
  obtain ⟨b, hb, hbrank⟩ := exists_positive_bid_at_rank Γ hatom j (r k) (hr0 k)
    ((hrq k).trans_le hqα)
  have hm := ppi_value_tail_le_rank_of_success_gap Γ hA hj hu i j v b act ha
    (by simpa only [hbrank, Function.comp_def] using hk) hs
  change q ≤ alphaGt Γ j b at hm
  rw [hbrank] at hm
  exact (hrq k).not_ge hm

theorem routed_bids_pos_of_visible_zero_atomless (Γ : FiniteGame m n c Seed)
    (hz : ∀ j, visibleBidMeasure Γ j {0} = 0) :
    ∀ᵐ d ∂userLaw Γ, 1 ≤ d.1.2.routeCount → 0 < d.1.2.bid := by
  have ha (j : Fin n) : ∀ᵐ d ∂userLaw Γ,
      ¬ (j ∈ firstK d.2 d.1.2.routeCount ∧ d.1.2.bid = 0) := by
    have hm : Measurable (fun d : UserDraw n => d.1.2.bid) := by
      simpa only [Function.comp_def] using (measurable_bid n).comp
        (measurable_snd.comp (measurable_fst : Measurable (Prod.fst : UserDraw n → ℝ × JointAction n)))
    have hh := hz j
    unfold visibleBidMeasure at hh
    rw [Measure.map_apply hm (measurableSet_singleton 0),
      Measure.restrict_apply (hm (measurableSet_singleton 0))] at hh
    have hn := measure_eq_zero_iff_ae_notMem.mp hh
    filter_upwards [hn] with d hd hc
    exact hd ⟨hc.2, hc.1⟩
  filter_upwards [ae_all_iff.mpr ha] with d hd hk
  have hcard : 0 < (firstK d.2 d.1.2.routeCount).card := by
    rw [card_firstK _ _ d.1.2.routeCount_le]
    omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hcard
  exact lt_of_le_of_ne d.1.2.bid_nonneg (fun he => hd j ⟨hj, he.symm⟩)

theorem ppi_success_le_value_tail_gap (Γ : FiniteGame m n c Seed)
    (hc : c ≤ (m - 1) + 1)
    (hA : Γ.A = Schedule.ppi n) (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hatom : PositiveVisibleAtomless Γ) (hu : UsersOptimal Γ)
    (hzero : ∀ j, visibleBidMeasure Γ j {0} = 0)
    (i : Fin m) (j : Fin n) (v : ℝ) (htail : 0 < Γ.F.real (Ioi v))
    (act : JointAction n) (ha : (problem Γ i).BestResponse v act)
    (δ : ℝ) (hδ : 0 < δ)
    (hgap : δ ≤ (m - 1 : ℕ) * (Γ.F.real (Ioi v) / n) - (c : ℝ)) :
    ((problem Γ i).outcome act).success ≤ (n : ℝ) * ((m - 1 : ℕ) / (4 * δ ^ 2)) := by
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hq0 : 0 ≤ Γ.F.real (Ioi v) / n := by positivity
  have hq1 : Γ.F.real (Ioi v) / n ≤ 1 := by
    apply (div_le_iff₀ hnR).mpr
    have hm : Γ.F.real (Ioi v) ≤ 1 := measureReal_le_one
    have hh : (1 : ℝ) ≤ n := by exact_mod_cast hn
    simpa only [one_mul] using hm.trans hh
  exact (ppi_success_le_value_tail_rank Γ hA hj hatom hu
    (routed_bids_pos_of_visible_zero_atomless Γ hzero) i j v htail act ha).trans
    (mul_le_mul_of_nonneg_left (binomBelow_upper_of_gap (m - 1) c hc _ δ hq0 hq1 hδ hgap) hnR.le)

end FCAppendix.Bayes
