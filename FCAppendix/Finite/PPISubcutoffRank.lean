import FCAppendix.Finite.PPISubcutoffDensity

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Filter Set Topology
open scoped BigOperators
variable {N n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem ppi_value_rank_gap (F : Measure ℝ) [IsProbabilityMeasure F]
    (vstar V : ℝ) (d : PPISubcutoffDensity F vstar V)
    (hn : 2 ≤ n) (ρ w : ℝ) (hw0 : 0 ≤ w) (hw : w < vstar)
    (hcut : F.real (Ioi vstar) = (n:ℝ)*ρ) :
    ρ < F.real (Ioi w)/(n:ℝ) ∧ F.real (Ioi w)/(n:ℝ) < 1 := by
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm := d.interval_mass_pos w vstar hw0 hw d.cutoff_mem.2.le
  have hh : F.real (Ioo w vstar) ≤ F.real (Ioc w vstar) :=
    measureReal_mono (fun _ hx => ⟨hx.1,hx.2.le⟩)
  have he : F.real (Ioc w vstar) = F.real (Ioi w)-F.real (Ioi vstar) := by
    rw [← Ioi_sdiff_Ioi,measureReal_sdiff (Ioi_subset_Ioi hw.le) measurableSet_Ioi]
  rw [he,hcut] at hh
  constructor
  · apply (lt_div_iff₀ hnR).mpr
    nlinarith
  · apply (div_lt_one hnR).mpr
    have h1 : F.real (Ioi w) ≤ 1 := measureReal_le_one
    have h2 : (2:ℝ) ≤ n := Nat.cast_le.mpr hn
    linarith

theorem binomBelow_antitone_above_capacity_ratio
    (N c : ℕ) (hc : 0 < c) (hcN : c ≤ N+1) (ρ a b : ℝ)
    (hcap : (c:ℝ) = ρ*((N:ℝ)+1)) (hρ : 0 < ρ)
    (hρa : ρ ≤ a) (hab : a ≤ b) (hb1 : b < 1) :
    binomBelow N b c ≤ binomBelow N a c := by
  have ha : 0 < a := hρ.trans_le hρa
  have hd : ((c-1:ℕ):ℝ) = ρ*((N:ℝ)+1)-1 := by
    rw [Nat.cast_sub hc,Nat.cast_one,hcap]
  have hgap : 0 ≤ (N:ℝ)*a-(c-1:ℕ) := by
    rw [hd]
    have hm := mul_nonneg (show 0 ≤ (N:ℝ)+1 by positivity) (sub_nonneg.mpr hρa)
    nlinarith [hab.trans_lt hb1]
  have h := binomBelow_le_exp_mul_of_rank_gap N c hc hcN a b ha hab hb1 hgap
  have he : Real.exp (-((N:ℝ)*a-(c-1:ℕ))*(b-a)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hgap) (sub_nonneg.mpr hab)
  have hQ := (binomBelow_pos_of_lt_one N c hc a ha.le (hab.trans_lt hb1)).le
  exact h.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right he hQ)

theorem binomBelow_subcutoff_relative
    (N c : ℕ) (hc : 0 < c) (hcN : c ≤ N+1) (ρ Δ : ℝ)
    (hcap : (c:ℝ) = ρ*((N:ℝ)+1)) (hρ : 0 < ρ)
    (hΔ : 0 < Δ) (h1 : ρ+2*Δ < 1) :
    binomBelow N (ρ+2*Δ) c ≤
      Real.exp (-Δ^2*((N:ℝ)+1))*binomBelow N (ρ+Δ) c := by
  have hd : ((c-1:ℕ):ℝ) = ρ*((N:ℝ)+1)-1 := by
    rw [Nat.cast_sub hc,Nat.cast_one,hcap]
  have hgap : ((N:ℝ)+1)*Δ ≤ (N:ℝ)*(ρ+Δ)-(c-1:ℕ) := by
    rw [hd]
    nlinarith
  have hgap0 : 0 ≤ (N:ℝ)*(ρ+Δ)-(c-1:ℕ) :=
    (by positivity : 0 ≤ ((N:ℝ)+1)*Δ).trans hgap
  have h := binomBelow_le_exp_mul_of_rank_gap N c hc hcN (ρ+Δ) (ρ+2*Δ)
    (by linarith) (by linarith) h1 hgap0
  have he : -((N:ℝ)*(ρ+Δ)-(c-1:ℕ))*((ρ+2*Δ)-(ρ+Δ)) ≤ -Δ^2*((N:ℝ)+1) := by
    nlinarith [mul_le_mul_of_nonneg_right hgap hΔ.le]
  have hQ := (binomBelow_pos_of_lt_one N c hc (ρ+Δ) (by linarith) (by linarith)).le
  exact h.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he) hQ)

theorem ppi_subcutoff_rank_separation
    (Γ : FiniteGame (N+1) n c Seed) (hn : 2 ≤ n)
    (hA : Γ.A = Schedule.ppi n) (hg : Γ.g = 0)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hatom : PositiveVisibleAtomless Γ) (hu : UsersOptimal Γ)
    (hzero : ∀ j, visibleBidMeasure Γ j {0} = 0)
    (hc : 0 < c) (hcN : c ≤ N+1) (ρ : ℝ) (hρ : 0 < ρ)
    (hcap : (c:ℝ) = ρ*((N:ℝ)+1))
    (vstar V : ℝ) (d : PPISubcutoffDensity Γ.F vstar V)
    (w : ℝ) (hw0 : 0 ≤ w) (hw : w < vstar)
    (hcut : Γ.F.real (Ioi vstar) = (n:ℝ)*ρ)
    (i : Fin (N+1)) (j : Fin n) (hslack : alphaGt Γ j 0 < 1)
    (hsize : (n:ℝ)*Real.exp (-((Γ.F.real (Ioi w)/(n:ℝ)-ρ)/2)^2*((N:ℝ)+1)) < 1)
    (v : ℝ) (hv : 0 < v) (hvw : v ≤ w)
    (act : JointAction n) (hact : (problem Γ i).BestResponse v act) :
    0 < act.bid ∧ ρ+(Γ.F.real (Ioi w)/(n:ℝ)-ρ)/2 ≤ alphaGt Γ j act.bid := by
  let astar := Γ.F.real (Ioi w)/(n:ℝ)
  let Δ := (astar-ρ)/2
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨hastar,hastar1⟩ := ppi_value_rank_gap Γ.F vstar V d hn ρ w hw0 hw hcut
  have hΔ : 0 < Δ := by dsimp [Δ,astar]; linarith
  have hastarEq : astar = ρ+2*Δ := by dsimp only [Δ]; ring
  have ha : 0 < ρ+Δ := by linarith
  have ha1 : ρ+Δ < 1 := by
    change astar < 1 at hastar1
    rw [hastarEq] at hastar1
    linarith
  have hvV : v ≤ V := hvw.trans (hw.le.trans d.cutoff_mem.2.le)
  have hband := d.interval_mass_pos (v/2) v (by positivity) (by linarith) hvV
  have hb := ppi_bestResponse_bid_pos_of_full_atomlessness Γ hA hg hj hatom hu hzero
    hc i j hslack v hv hband act hact
  refine ⟨hb,?_⟩
  have hpos := routed_bids_pos_of_visible_zero_atomless Γ hzero
  have hbr : ∀ᵐ x ∂userLaw Γ, (problem Γ i).BestResponse x.1.1 x.1.2 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_bestResponse_compProd Γ hu i)
  have hAstar : astar ≤ alphaGt Γ j 0 := by
    apply value_tail_le_rank_of_higher_bids Γ j w 0
    filter_upwards [hbr,hpos] with x hx hp hwx
    have hx0 : 0 < x.1.1 := lt_of_le_of_lt hw0 hwx
    obtain ⟨_,hk,_⟩ := ppi_positive_bestResponse_of_visible_slack Γ hA hg hj hatom
      hc i j hslack x.1.1 hx0 x.1.2 hx
    exact ⟨hp hk,hk⟩
  have hvtail : astar ≤ Γ.F.real (Ioi v)/(n:ℝ) := by
    apply div_le_div_of_nonneg_right _ hnR.le
    exact measureReal_mono (Ioi_subset_Ioi hvw)
  have hvtail0 : 0 < Γ.F.real (Ioi v) := by
    have hh : 0 < Γ.F.real (Ioi v)/(n:ℝ) := (hρ.trans hastar).trans_le hvtail
    simpa only [zero_mul] using (lt_div_iff₀ hnR).mp hh
  have hvtail1 : Γ.F.real (Ioi v)/(n:ℝ) < 1 := by
    apply (div_lt_one hnR).mpr
    have hh : Γ.F.real (Ioi v) ≤ 1 := measureReal_le_one
    have hn2 : (2:ℝ) ≤ n := Nat.cast_le.mpr hn
    linarith
  have hs := ppi_success_le_value_tail_rank Γ hA hj hatom hu hpos i j v hvtail0 act hact
  simp only [Nat.add_sub_cancel] at hs
  have hQmono := binomBelow_antitone_above_capacity_ratio N c hc hcN ρ astar
    (Γ.F.real (Ioi v)/(n:ℝ)) hcap hρ hastar.le hvtail hvtail1
  have hsstar : ((problem Γ i).outcome act).success ≤ (n:ℝ)*binomBelow N astar c :=
    hs.trans (mul_le_mul_of_nonneg_left hQmono hnR.le)
  have hrelative := binomBelow_subcutoff_relative N c hc hcN ρ Δ hcap hρ hΔ
    (by rwa [← hastarEq])
  rw [← hastarEq] at hrelative
  have hSrelative := hsstar.trans (mul_le_mul_of_nonneg_left hrelative hnR.le)
  by_contra hnot
  have hrank : alphaGt Γ j act.bid < ρ+Δ := lt_of_not_ge hnot
  obtain ⟨b,hb0,hbα⟩ := exists_positive_bid_at_rank Γ hatom j (ρ+Δ) ha
    (lt_of_lt_of_le (by rw [hastarEq]; linarith) hAstar)
  have hbact : b ≤ act.bid := by
    by_contra hh
    have hm := alphaGt_antitone Γ j (le_of_lt (lt_of_not_ge hh))
    rw [hbα] at hm
    exact hrank.not_ge hm
  have hm := rank_probability_monotone_bid Γ i j hbact
  simp only [Nat.add_sub_cancel,hbα] at hm
  have hk := route_pos_of_success_pos Γ i act
    (ppi_positive_bestResponse_of_visible_slack Γ hA hg hj hatom hc i j hslack v hv act hact).1
  have hmean := meanAcceptProb_le_success Γ (by omega) i act hk
  rw [ppi_meanAcceptProb_eq_rank Γ hA hatom hj i j act.bid hb] at hmean
  have hQS := hm.trans hmean
  have hQpos := binomBelow_pos_of_lt_one N c hc (ρ+Δ) ha.le ha1
  have hsize' : (n:ℝ)*Real.exp (-Δ^2*((N:ℝ)+1)) < 1 := hsize
  have hstrict := mul_lt_mul_of_pos_right hsize' hQpos
  nlinarith [hSrelative]

end FCAppendix.Bayes
