import FCAppendix.Finite.PPISubcutoffRank
import FCAppendix.Finite.PPISubcutoffNetRent

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Filter Set Topology
variable {N n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem ppi_subcutoff_net_rank_separation
    (Γ : FiniteGame (N+1) n c Seed) (hn : 2 ≤ n)
    (hA : Γ.A = Schedule.ppi n)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hatom : PositiveVisibleAtomless Γ) (hu : UsersOptimal Γ)
    (hzero : ∀ j, visibleBidMeasure Γ j {0} = 0)
    (hc : 0 < c) (hcN : c ≤ N+1) (ρ : ℝ) (hρ : 0 < ρ)
    (hcap : (c:ℝ) = ρ*((N:ℝ)+1))
    (vstar V : ℝ) (d : PPISubcutoffDensity Γ.F vstar V)
    (w : ℝ) (hgw : Γ.g ≤ w) (hw : w < vstar)
    (hcut : Γ.F.real (Ioi vstar) = (n:ℝ)*ρ)
    (i : Fin (N+1)) (j : Fin n) (hslack : alphaGt Γ j 0 < 1)
    (hsize : (n:ℝ)*Real.exp (-((Γ.F.real (Ioi w)/(n:ℝ)-ρ)/2)^2*((N:ℝ)+1)) < 1)
    (v : ℝ) (hv : Γ.g < v) (hvw : v ≤ w)
    (act : JointAction n) (hact : (problem Γ i).BestResponse v act) :
    ρ+(Γ.F.real (Ioi w)/(n:ℝ)-ρ)/2 ≤ alphaGt Γ j act.bid := by
  let astar := Γ.F.real (Ioi w)/(n:ℝ)
  let Δ := (astar-ρ)/2
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨hastar,hastar1⟩ := ppi_value_rank_gap Γ.F vstar V d hn ρ w (Γ.g_nonneg.trans hgw) hw hcut
  have hΔ : 0 < Δ := by dsimp [Δ,astar]; linarith
  have hastarEq : astar = ρ+2*Δ := by dsimp only [Δ]; ring
  have ha : 0 < ρ+Δ := by linarith
  have ha1 : ρ+Δ < 1 := by
    change astar < 1 at hastar1
    rw [hastarEq] at hastar1
    linarith
  have hpos := routed_bids_pos_of_visible_zero_atomless Γ hzero
  have hbr : ∀ᵐ x ∂userLaw Γ, (problem Γ i).BestResponse x.1.1 x.1.2 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_bestResponse_compProd Γ hu i)
  have hAstar : astar ≤ alphaGt Γ j 0 := by
    apply value_tail_le_rank_of_higher_bids Γ j w 0
    filter_upwards [hbr,hpos] with x hx hp hwx
    have hx0 : Γ.g < x.1.1 := lt_of_le_of_lt hgw hwx
    obtain ⟨_,hk,_⟩ := ppi_positive_net_bestResponse_of_visible_slack Γ hA hj hatom
      hc i j hslack x.1.1 hx0 x.1.2 hx
    exact ⟨hp hk,hk⟩
  have hzero_case : act.bid = 0 → ρ+Δ ≤ alphaGt Γ j act.bid := by
    intro hbzero
    rw [hbzero]
    have hlow : ρ+Δ ≤ astar := by linarith [hastarEq]
    exact hlow.trans hAstar
  by_cases hb : 0 < act.bid
  swap
  · exact hzero_case (le_antisymm (le_of_not_gt hb) act.bid_nonneg)
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
    (ppi_positive_net_bestResponse_of_visible_slack Γ hA hj hatom hc i j hslack v hv act hact).1
  have hmean := meanAcceptProb_le_success Γ (by omega) i act hk
  rw [ppi_meanAcceptProb_eq_rank Γ hA hatom hj i j act.bid hb] at hmean
  have hQS := hm.trans hmean
  have hQpos := binomBelow_pos_of_lt_one N c hc (ρ+Δ) ha.le ha1
  have hsize' : (n:ℝ)*Real.exp (-Δ^2*((N:ℝ)+1)) < 1 := hsize
  have hstrict := mul_lt_mul_of_pos_right hsize' hQpos
  nlinarith [hSrelative]

end FCAppendix.Bayes
