import FCAppendix.Finite.PPISubcutoffDensity

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Filter Set Topology
variable {N n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem ppi_positive_net_bestResponse_of_visible_slack
    (Γ : FiniteGame (N+1) n c Seed) (hA : Γ.A = Schedule.ppi n)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j) (hatom : PositiveVisibleAtomless Γ)
    (hc : 0 < c) (i : Fin (N+1)) (j : Fin n)
    (hslack : alphaGt Γ j 0 < 1) (v : ℝ) (hv : Γ.g < v)
    (act : JointAction n) (hact : (problem Γ i).BestResponse v act) :
    0 < ((problem Γ i).outcome act).success ∧ 1 ≤ act.routeCount ∧ act.bid < v-Γ.g := by
  have hQ := binomBelow_pos_of_lt_one N c hc _ measureReal_nonneg hslack
  have hS := ppi_success_ge_zero_rank Γ hA hj hatom i j (v-Γ.g) (sub_pos.mpr hv) act
    (by simpa only [add_sub_cancel] using hact)
  have hs := hQ.trans_le hS
  have hU := ppi_envelope_ge_zero_rank Γ hA hj hatom i j (v-Γ.g)
  simp only [add_sub_cancel] at hU
  have hUpos : 0 < (problem Γ i).envelope v := (mul_pos (sub_pos.mpr hv) hQ).trans_le hU
  have hu := CountLaw.utility_le_bid_net_success ((problem Γ i).outcome act)
    v act.bid Γ.g Γ.A Γ.G act.bid_nonneg Γ.g_nonneg
  change (problem Γ i).payoff v act ≤ _ at hu
  rw [(problem Γ i).bestResponse_iff_attains v act |>.mp hact] at hu
  have hmargin := pos_of_mul_pos_left (hUpos.trans_le hu) hs.le
  exact ⟨hs, route_pos_of_success_pos Γ i act hs, by linarith⟩

theorem ppi_net_rent_of_small_value_band
    (Γ : FiniteGame (N+1) n c Seed) [NullSingletonClass Γ.F]
    (hA : Γ.A = Schedule.ppi n)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hatom : PositiveVisibleAtomless Γ) (hu : UsersOptimal Γ)
    (hc : 0 < c) (hcN : c ≤ N+1) (i : Fin (N+1)) (j : Fin n)
    (δ : ℝ) (hδ : 0 < δ) (hslack : alphaGt Γ j 0 ≤ 1-δ)
    (y v : ℝ) (hy0 : Γ.g < y) (hyv : y < v)
    (ay av : JointAction n) (hy : (problem Γ i).BestResponse y ay)
    (hv : (problem Γ i).BestResponse v av)
    (hmass : (N:ℝ)/δ * Γ.F.real (Ioo y v) ≤ 1) :
    (v-y)/((n:ℝ)^2*Real.exp 1) ≤ v-Γ.g-av.bid := by
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hsuccess := ppi_success_comparison_of_small_value_band Γ hA hj hatom hu
    hc hcN i j δ hδ hslack y v hy0 ay av hy hv hmass
  have hsupp := (problem Γ i).supporting_line y ay hy v
  have henvy := (problem Γ i).envelope_nonneg y
  have hleft : (v-y)*((problem Γ i).outcome av).success/((n:ℝ)*Real.exp 1) ≤
      (problem Γ i).envelope v := by
    have hh := mul_le_mul_of_nonneg_left hsuccess (sub_pos.mpr hyv).le
    rw [← mul_div_assoc] at hh
    linarith
  have hpos := (ppi_positive_net_bestResponse_of_visible_slack Γ hA hj hatom hc i j
    (by linarith) v (hy0.trans hyv) av hv).1
  have hupper := CountLaw.utility_le_bid_net_success ((problem Γ i).outcome av)
    v av.bid Γ.g Γ.A Γ.G av.bid_nonneg Γ.g_nonneg
  change (problem Γ i).payoff v av ≤ _ at hupper
  rw [(problem Γ i).bestResponse_iff_attains v av |>.mp hv] at hupper
  have hmargin : (v-y)/((n:ℝ)*Real.exp 1) ≤ v-Γ.g-av.bid := by
    apply (mul_le_mul_iff_left₀ hpos).mp
    simpa only [div_mul_eq_mul_div] using hleft.trans hupper
  have hden : (n:ℝ)*Real.exp 1 ≤ (n:ℝ)^2*Real.exp 1 := by
    exact mul_le_mul_of_nonneg_right (by nlinarith : (n:ℝ) ≤ (n:ℝ)^2)
      (Real.exp_pos 1).le
  exact (div_le_div_of_nonneg_left (sub_nonneg.mpr hyv.le)
    (mul_pos hnR (Real.exp_pos 1)) hden).trans hmargin

theorem ppi_net_rent_uniform
    (Γ : FiniteGame (N+1) n c Seed) [NullSingletonClass Γ.F]
    (hA : Γ.A = Schedule.ppi n)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j) (hatom : PositiveVisibleAtomless Γ)
    (hu : UsersOptimal Γ) (hc : 0 < c) (hcN : c ≤ N+1)
    (i : Fin (N+1)) (j : Fin n) (vstar V : ℝ)
    (d : PPISubcutoffDensity Γ.F vstar V)
    (δ : ℝ) (hδ : 0 < δ) (hslack : alphaGt Γ j 0 ≤ 1-δ)
    (v : ℝ) (hv : Γ.g < v) (hvV : v ≤ V)
    (act : JointAction n) (hact : (problem Γ i).BestResponse v act) :
    ppiSubcutoffTheta δ d.upper V * (v-Γ.g) /
      (2*(n:ℝ)^2*Real.exp 1*((N:ℝ)+1)) ≤ v-Γ.g-act.bid := by
  let θ := ppiSubcutoffTheta δ d.upper V
  let h := θ*(v-Γ.g)/((N:ℝ)+1)
  have hnet : 0 < v-Γ.g := sub_pos.mpr hv
  have hnetV : v-Γ.g ≤ V := by linarith [Γ.g_nonneg]
  have hV : 0 < V := d.cutoff_mem.1.trans d.cutoff_mem.2
  have hupper : 0 < d.upper := d.upper_pos
  have hθ : 0 < θ := lt_min (by norm_num) (by positivity)
  have hθhalf : θ ≤ 1/2 := min_le_left _ _
  have hθmass : θ ≤ δ/(2*d.upper*V) := min_le_right _ _
  have hm : 0 < (N:ℝ)+1 := by positivity
  have hh : 0 < h := by dsimp [h]; positivity
  have hhv : h ≤ (v-Γ.g)/2 := by
    dsimp [h]
    apply (div_le_iff₀ hm).mpr
    have htv := mul_le_mul_of_nonneg_right hθhalf hnet.le
    have hNv := mul_nonneg (Nat.cast_nonneg N : (0:ℝ) ≤ N) hnet.le
    nlinarith
  have hl : Γ.g < v-h := by linarith
  have hl0 : 0 < v-h := Γ.g_nonneg.trans_lt hl
  have hband := d.interval_mass_pos (v-h) (v-h/2) hl0.le (by linarith) (by linarith)
  have hbr : ∀ᵐ x ∂userLaw Γ, (problem Γ i).BestResponse x.1.1 x.1.2 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_bestResponse_compProd Γ hu i)
  obtain ⟨x,hx,hxbr⟩ := exists_actual_draw_in_value_band Γ _ _ hband _ hbr
  have hy0 : Γ.g < x.1.1 := hl.trans hx.1
  have hyv : x.1.1 < v := by linarith [hx.2]
  have hmass := d.interval_mass_le x.1.1 v (Γ.g_nonneg.trans hy0.le) hyv.le hvV
  have hNv : (N:ℝ)/((N:ℝ)+1) ≤ 1 := (div_le_one hm).mpr (by linarith)
  have hθfv : θ*d.upper*(v-Γ.g) ≤ δ := by
    have hbound := (le_div_iff₀ (by positivity : 0 < 2*d.upper*V)).mp hθmass
    have hvbound := mul_le_mul_of_nonneg_left hnetV (mul_nonneg hθ.le d.upper_pos.le)
    nlinarith
  have hNh : (N:ℝ)*d.upper*h ≤ δ := by
    dsimp only [h]
    have hprod := mul_le_mul_of_nonneg_left hNv
      (mul_nonneg (mul_nonneg hθ.le d.upper_pos.le) hnet.le)
    have hid : θ*d.upper*(v-Γ.g)*((N:ℝ)/((N:ℝ)+1)) =
        (N:ℝ)*d.upper*(θ*(v-Γ.g)/((N:ℝ)+1)) := by ring
    rw [hid] at hprod
    linarith
  have hsmall : (N:ℝ)/δ*Γ.F.real (Ioo x.1.1 v) ≤ 1 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hδ).mpr
    have hM := mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg N)
    have hyh : v-x.1.1 ≤ h := by linarith [hx.1]
    have hM' := mul_le_mul_of_nonneg_left hyh
      (mul_nonneg (Nat.cast_nonneg N) d.upper_pos.le)
    have hh' : (N:ℝ)*Γ.F.real (Ioo x.1.1 v) ≤ δ := by nlinarith
    simpa only [one_mul] using hh'
  have hrent := ppi_net_rent_of_small_value_band Γ hA hj hatom hu hc hcN i j
    δ hδ hslack x.1.1 v hy0 hyv x.1.2 act hxbr hact hsmall
  have hden : 0 < (n:ℝ)^2*Real.exp 1 := by
    have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
    positivity
  have hcomp := div_le_div_of_nonneg_right
    (show h/2 ≤ v-x.1.1 by linarith [hx.2]) hden.le
  apply le_trans _ (hcomp.trans hrent)
  change θ*(v-Γ.g)/(2*(n:ℝ)^2*Real.exp 1*((N:ℝ)+1)) ≤ _
  dsimp only [h]
  apply le_of_eq
  field_simp [hm.ne',hden.ne']

end FCAppendix.Bayes
