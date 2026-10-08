import FCAppendix.Finite.BinomialLogBounds

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Filter Set Topology
variable {N n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem ppi_rank_band_le_value_band
    (Γ : FiniteGame (N+1) n c Seed) [NullSingletonClass Γ.F]
    (hA : Γ.A = Schedule.ppi n) (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hatom : PositiveVisibleAtomless Γ) (hu : UsersOptimal Γ)
    (i : Fin (N+1)) (j : Fin n) (y v lo hi : ℝ)
    (hlo : 0 < lo) (hlh : lo ≤ hi)
    (ay av : JointAction n) (hy : (problem Γ i).BestResponse y ay)
    (hv : (problem Γ i).BestResponse v av)
    (hyl : ((problem Γ i).outcome ay).success < binomBelow N (alphaGt Γ j lo) c)
    (hvh : (n:ℝ)*binomBelow N (alphaGt Γ j hi) c < ((problem Γ i).outcome av).success) :
    alphaGt Γ j lo - alphaGt Γ j hi ≤ Γ.F.real (Ioo y v) := by
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  have hbr : ∀ᵐ d ∂userLaw Γ, (problem Γ i).BestResponse d.1.1 d.1.2 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_bestResponse_compProd Γ hu i)
  have hpres : MeasurePreserving (fun d : UserDraw n => d.1.1) (userLaw Γ) Γ.F :=
    ⟨measurable_fst.comp measurable_fst, userLaw_value_map Γ⟩
  have hne (w : ℝ) : ∀ᵐ d ∂userLaw Γ, d.1.1 ≠ w := by
    have hh : ∀ᵐ x ∂Γ.F, x ≠ w := by
      simpa only [mem_singleton_iff] using
        (measure_eq_zero_iff_ae_notMem.mp (measure_singleton w : Γ.F {w} = 0))
    exact hpres.quasiMeasurePreserving.ae hh
  have hsub : aboveAt j hi ⊆ aboveAt j lo := fun d hd => ⟨hd.1, hlh.trans_lt hd.2⟩
  have hs : aboveAt j lo \ aboveAt j hi ≤ᵐ[userLaw Γ] {d | d.1.1 ∈ Ioo y v} := by
    filter_upwards [hbr, hne y, hne v] with d hd hdy hdv hmem
    have hbid : lo < d.1.2.bid := hmem.1.2
    have hbid' : d.1.2.bid ≤ hi := by
      by_contra hh
      exact hmem.2 ⟨hmem.1.1, lt_of_not_ge hh⟩
    have hk : 1 ≤ d.1.2.routeCount := by
      have hh := Finset.card_pos.mpr ⟨j,hmem.1.1⟩
      rw [card_firstK _ _ d.1.2.routeCount_le] at hh
      omega
    have hml := rank_probability_monotone_bid Γ i j hbid.le
    have hmh := rank_probability_monotone_bid Γ i j hbid'
    simp only [Nat.add_sub_cancel] at hml hmh
    have hq := ppi_meanAcceptProb_eq_rank Γ hA hatom hj i j d.1.2.bid (hlo.trans hbid)
    have hloS := meanAcceptProb_le_success Γ hn i d.1.2 hk
    have hhiS := success_le_n_meanAcceptProb Γ hn i d.1.2
    rw [hq] at hloS hhiS
    have hys : ((problem Γ i).outcome ay).success < ((problem Γ i).outcome d.1.2).success :=
      hyl.trans_le (hml.trans hloS)
    have hvs : ((problem Γ i).outcome d.1.2).success < ((problem Γ i).outcome av).success :=
      (hhiS.trans (mul_le_mul_of_nonneg_left hmh (Nat.cast_nonneg n))).trans_lt hvh
    constructor
    · rcases lt_or_gt_of_ne hdy with hw | hw
      · exact (hys.not_ge ((problem Γ i).success_order d.1.1 y hw d.1.2 ay hd hy)).elim
      · exact hw
    · rcases lt_or_gt_of_ne hdv with hw | hw
      · exact hw
      · exact (hvs.not_ge ((problem Γ i).success_order v d.1.1 hw av d.1.2 hv hd)).elim
  have hh := ENNReal.toReal_mono (measure_ne_top (userLaw Γ) {d | d.1.1 ∈ Ioo y v})
    (measure_mono_ae hs)
  change (userLaw Γ).real (aboveAt j lo \ aboveAt j hi) ≤
    (userLaw Γ).real {d | d.1.1 ∈ Ioo y v} at hh
  rw [measureReal_sdiff hsub (measurableSet_aboveAt j hi)] at hh
  have he : (userLaw Γ).real {d | d.1.1 ∈ Ioo y v} = Γ.F.real (Ioo y v) := by
    rw [← userLaw_value_map Γ]
    simp only [Measure.real]
    rw [Measure.map_apply
      (show Measurable (fun d : UserDraw n => d.1.1) from
        measurable_fst.comp measurable_fst) measurableSet_Ioo]
    rfl
  rw [he] at hh
  exact hh

theorem binomBelow_zero_probability (N c : ℕ) (hc : 0 < c) : binomBelow N 0 c = 1 := by
  classical
  unfold binomBelow PiBinomial.pmf
  simp [zero_pow_eq, hc]

theorem binomBelow_pos_of_lt_one (N c : ℕ) (hc : 0 < c) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p < 1) : 0 < binomBelow N p c := by
  rcases eq_or_lt_of_le hp0 with he | he
  · subst p
    rw [binomBelow_zero_probability N c hc]
    norm_num
  · exact binomBelow_pos N c hc p ⟨he,hp1⟩

theorem exists_positive_bid_at_rank_success
    (Γ : FiniteGame (N+1) n c Seed) (hatom : PositiveVisibleAtomless Γ)
    (hc : 0 < c) (j : Fin n) (q : ℝ)
    (hq0 : binomBelow N (alphaGt Γ j 0) c < q) (hq1 : q < 1) :
    ∃ b : ℝ, 0 < b ∧ binomBelow N (alphaGt Γ j b) c = q := by
  have hlim : Tendsto (fun b => binomBelow N (alphaGt Γ j b) c) atTop (𝓝 1) := by
    simpa only [Function.comp_def,binomBelow_zero_probability N c hc] using
      (continuous_binomBelow N c).continuousAt.tendsto.comp (alphaGt_tendsto_zero Γ j)
  obtain ⟨B,hB,hQ⟩ := ((eventually_gt_atTop (0:ℝ)).and
    (hlim.eventually (eventually_gt_nhds hq1))).exists
  have hcont : ContinuousOn (fun b => binomBelow N (alphaGt Γ j b) c) (Icc 0 B) := by
    apply (continuous_binomBelow N c).comp_continuousOn
    intro b hb
    rcases eq_or_lt_of_le hb.1 with he | he
    · subst b
      exact (alphaGt_continuousWithinAt_nonneg Γ j).mono (fun x hx => hx.1)
    · exact (alphaGt_continuousAt_pos Γ hatom j b he).continuousWithinAt
  obtain ⟨b,hb,hq⟩ := intermediate_value_Icc hB.le hcont ⟨hq0.le,hQ.le⟩
  have hbne : b ≠ 0 := by
    intro he
    rw [he] at hq
    exact hq0.ne hq
  exact ⟨b,lt_of_le_of_ne hb.1 hbne.symm,hq⟩

theorem ppi_envelope_ge_zero_rank
    (Γ : FiniteGame (N+1) n c Seed)
    (hA : Γ.A = Schedule.ppi n) (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hatom : PositiveVisibleAtomless Γ) (i : Fin (N+1)) (j : Fin n) (v : ℝ) :
    v * binomBelow N (alphaGt Γ j 0) c ≤ (problem Γ i).envelope (Γ.g+v) := by
  have hlim : Tendsto (fun k : ℕ => (v-1/((k:ℝ)+1))*binomBelow N (alphaGt Γ j 0) c)
      atTop (𝓝 (v*binomBelow N (alphaGt Γ j 0) c)) := by
    simpa only [sub_zero] using (tendsto_one_div_add_atTop_nhds_zero_nat.const_sub v).mul_const
      (binomBelow N (alphaGt Γ j 0) c)
  apply le_of_tendsto hlim
  exact Eventually.of_forall fun k => rank_price_gap_mul_le_envelope Γ hA hatom hj i j
    0 (1/((k:ℝ)+1)) v (by positivity) (by positivity)

theorem ppi_success_ge_zero_rank
    (Γ : FiniteGame (N+1) n c Seed)
    (hA : Γ.A = Schedule.ppi n) (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hatom : PositiveVisibleAtomless Γ) (i : Fin (N+1)) (j : Fin n)
    (v : ℝ) (hv : 0 < v) (a : JointAction n)
    (ha : (problem Γ i).BestResponse (Γ.g+v) a) :
    binomBelow N (alphaGt Γ j 0) c ≤ ((problem Γ i).outcome a).success := by
  have hl := ppi_envelope_ge_zero_rank Γ hA hj hatom i j v
  have hu := CountLaw.utility_le_bid_net_success ((problem Γ i).outcome a)
    (Γ.g+v) a.bid Γ.g Γ.A Γ.G a.bid_nonneg Γ.g_nonneg
  change (problem Γ i).payoff (Γ.g+v) a ≤ _ at hu
  rw [(problem Γ i).bestResponse_iff_attains (Γ.g+v) a |>.mp ha] at hu
  have hn := mul_nonneg a.bid_nonneg ((problem Γ i).outcome a).success_nonneg
  nlinarith

end FCAppendix.Bayes
