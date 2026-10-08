import FCAppendix.Finite.PPIRankBands

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Filter Set Topology
variable {N n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem ppi_log_success_gap_le
    (Γ : FiniteGame (N+1) n c Seed) [NullSingletonClass Γ.F]
    (hA : Γ.A = Schedule.ppi n) (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hatom : PositiveVisibleAtomless Γ) (hu : UsersOptimal Γ)
    (hc : 0 < c) (hcN : c ≤ N+1) (i : Fin (N+1)) (j : Fin n)
    (δ : ℝ) (hδ : 0 < δ) (hAδ : alphaGt Γ j 0 ≤ 1-δ)
    (y v : ℝ) (hy0 : Γ.g < y)
    (ay av : JointAction n) (hy : (problem Γ i).BestResponse y ay)
    (hv : (problem Γ i).BestResponse v av)
    (hgap : ((problem Γ i).outcome ay).success < ((problem Γ i).outcome av).success / n) :
    Real.log (((problem Γ i).outcome av).success / n) -
      Real.log (((problem Γ i).outcome ay).success) ≤
      (N:ℝ)/δ * Γ.F.real (Ioo y v) := by
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  let s := ((problem Γ i).outcome ay).success
  let t := ((problem Γ i).outcome av).success / n
  have hA1 : alphaGt Γ j 0 < 1 := by linarith
  have hsA : binomBelow N (alphaGt Γ j 0) c ≤ s := by
    have hh := ppi_success_ge_zero_rank Γ hA hj hatom i j (y-Γ.g) (sub_pos.mpr hy0) ay
      (by simpa only [add_sub_cancel] using hy)
    exact hh
  have hs0 : 0 < s := (binomBelow_pos_of_lt_one N c hc _ measureReal_nonneg hA1).trans_le hsA
  have hst : s < t := hgap
  have ht1 : t ≤ 1 := by
    apply (div_le_iff₀ hnR).mpr
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
    simpa only [one_mul] using ((problem Γ i).outcome av).success_le_one.trans hn1
  let e : ℕ → ℝ := fun k => (t-s)/((k:ℝ)+3)
  have he0 (k : ℕ) : 0 < e k := by dsimp [e]; positivity
  have he2 (k : ℕ) : 2*e k < t-s := by
    dsimp only [e]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < (k:ℝ)+3)).mpr
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  have helim : Tendsto e atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop (3:ℝ) tendsto_natCast_atTop_atTop)
  have hbound (k : ℕ) : Real.log (t-e k)-Real.log (s+e k) ≤
      (N:ℝ)/δ * Γ.F.real (Ioo y v) := by
    have he := he0 k
    have he' := he2 k
    obtain ⟨lo,hlo,hloQ⟩ := exists_positive_bid_at_rank_success Γ hatom hc j (s+e k)
      (by linarith) (by linarith)
    obtain ⟨hi,hhi,hhiQ⟩ := exists_positive_bid_at_rank_success Γ hatom hc j (t-e k)
      (by linarith) (by linarith)
    have hlh : lo ≤ hi := by
      by_contra hh
      have hm := rank_probability_monotone_bid Γ i j (le_of_lt (lt_of_not_ge hh))
      simp only [Nat.add_sub_cancel,hloQ,hhiQ] at hm
      linarith
    have hband := ppi_rank_band_le_value_band Γ hA hj hatom hu i j y v lo hi hlo hlh ay av hy hv
      (by rw [hloQ]; change s < s+e k; linarith)
      (by rw [hhiQ]; dsimp only [t]; field_simp; nlinarith)
    have hα : alphaGt Γ j hi ≤ alphaGt Γ j lo := alphaGt_antitone Γ j hlh
    have hαA : alphaGt Γ j lo ≤ alphaGt Γ j 0 := alphaGt_antitone Γ j hlo.le
    have hα0 : 0 < alphaGt Γ j hi := by
      have hnon : 0 ≤ alphaGt Γ j hi := measureReal_nonneg
      apply lt_of_le_of_ne hnon
      intro hh
      have hh' : alphaGt Γ j hi = 0 := hh.symm
      rw [hh',binomBelow_zero_probability N c hc] at hhiQ
      linarith
    have hlog := log_binomBelow_sub_le N c hc hcN (alphaGt Γ j hi) (alphaGt Γ j lo)
      hα0 hα (hαA.trans_lt hA1)
    rw [hloQ,hhiQ] at hlog
    have hcoef : (N:ℝ)/(1-alphaGt Γ j lo) ≤ (N:ℝ)/δ :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg N) hδ (by linarith)
    exact hlog.trans ((mul_le_mul_of_nonneg_right hcoef (sub_nonneg.mpr hα)).trans
      (mul_le_mul_of_nonneg_left hband (by positivity)))
  have hlim : Tendsto (fun k => Real.log (t-e k)-Real.log (s+e k))
      atTop (𝓝 (Real.log t-Real.log s)) := by
    have htl : Tendsto (fun k => t-e k) atTop (𝓝 t) := by simpa using helim.const_sub t
    have hsl : Tendsto (fun k => s+e k) atTop (𝓝 s) := by simpa using helim.const_add s
    exact (Real.continuousAt_log (hs0.trans hst).ne').tendsto.comp htl |>.sub
      ((Real.continuousAt_log hs0.ne').tendsto.comp hsl)
  exact le_of_tendsto hlim (Eventually.of_forall hbound)

theorem ppi_success_comparison_of_small_value_band
    (Γ : FiniteGame (N+1) n c Seed) [NullSingletonClass Γ.F]
    (hA : Γ.A = Schedule.ppi n) (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hatom : PositiveVisibleAtomless Γ) (hu : UsersOptimal Γ)
    (hc : 0 < c) (hcN : c ≤ N+1) (i : Fin (N+1)) (j : Fin n)
    (δ : ℝ) (hδ : 0 < δ) (hAδ : alphaGt Γ j 0 ≤ 1-δ)
    (y v : ℝ) (hy0 : Γ.g < y)
    (ay av : JointAction n) (hy : (problem Γ i).BestResponse y ay)
    (hv : (problem Γ i).BestResponse v av)
    (hmass : (N:ℝ)/δ * Γ.F.real (Ioo y v) ≤ 1) :
    ((problem Γ i).outcome av).success / ((n:ℝ)*Real.exp 1) ≤
      ((problem Γ i).outcome ay).success := by
  have hn : (0:ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt j.isLt)
  have hs : 0 ≤ ((problem Γ i).outcome ay).success := CountLaw.success_nonneg _
  have hexp : 1 ≤ Real.exp 1 := by exact Real.one_le_exp (by norm_num)
  by_cases hgap : ((problem Γ i).outcome ay).success < ((problem Γ i).outcome av).success / n
  · have hlog := (ppi_log_success_gap_le Γ hA hj hatom hu hc hcN i j δ hδ hAδ y v hy0 ay av hy hv hgap).trans hmass
    have hsy : 0 < ((problem Γ i).outcome ay).success := by
      have hlo := ppi_success_ge_zero_rank Γ hA hj hatom i j (y-Γ.g) (sub_pos.mpr hy0) ay
        (by simpa only [add_sub_cancel] using hy)
      exact (binomBelow_pos_of_lt_one N c hc _ measureReal_nonneg (by change alphaGt Γ j 0 < 1; linarith)).trans_le hlo
    have hst : 0 < ((problem Γ i).outcome av).success/n := hsy.trans hgap
    have hh := Real.exp_le_exp.mpr (show Real.log (((problem Γ i).outcome av).success/n) ≤
        1+Real.log (((problem Γ i).outcome ay).success) by linarith)
    rw [Real.exp_add,Real.exp_log hst,Real.exp_log hsy] at hh
    apply (div_le_iff₀ (mul_pos hn (Real.exp_pos 1))).mpr
    have hm := (div_le_iff₀ hn).mp hh
    nlinarith
  · have hh := le_of_not_gt hgap
    have hm : ((problem Γ i).outcome ay).success ≤ Real.exp 1 * ((problem Γ i).outcome ay).success := by
      nlinarith
    apply (div_le_iff₀ (mul_pos hn (Real.exp_pos 1))).mpr
    have hb := (div_le_iff₀ hn).mp (hh.trans hm)
    nlinarith

theorem ppi_rent_of_small_value_band
    (Γ : FiniteGame (N+1) n c Seed) [NullSingletonClass Γ.F]
    (hA : Γ.A = Schedule.ppi n) (hg : Γ.g = 0)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hatom : PositiveVisibleAtomless Γ) (hu : UsersOptimal Γ)
    (hc : 0 < c) (hcN : c ≤ N+1) (i : Fin (N+1)) (j : Fin n)
    (δ : ℝ) (hδ : 0 < δ) (hAδ : alphaGt Γ j 0 ≤ 1-δ)
    (y v : ℝ) (hy0 : 0 < y) (hyv : y < v)
    (ay av : JointAction n) (hy : (problem Γ i).BestResponse y ay)
    (hv : (problem Γ i).BestResponse v av)
    (hmass : (N:ℝ)/δ * Γ.F.real (Ioo y v) ≤ 1) :
    (v-y)*((problem Γ i).outcome av).success/((n:ℝ)*Real.exp 1) ≤
      (problem Γ i).envelope v ∧
    (v-y)/((n:ℝ)^2*Real.exp 1) ≤ v-av.bid := by
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hsuccess := ppi_success_comparison_of_small_value_band Γ hA hj hatom hu hc hcN i j
    δ hδ hAδ y v (by simpa only [hg] using hy0) ay av hy hv hmass
  have hsupp := (problem Γ i).supporting_line y ay hy v
  have henvy := (problem Γ i).envelope_nonneg y
  have hleft : (v-y)*((problem Γ i).outcome av).success/((n:ℝ)*Real.exp 1) ≤
      (problem Γ i).envelope v := by
    have hh := mul_le_mul_of_nonneg_left hsuccess (sub_pos.mpr hyv).le
    rw [← mul_div_assoc] at hh
    linarith
  refine ⟨hleft,?_⟩
  have hpos : 0 < ((problem Γ i).outcome av).success := by
    have hh := ppi_success_ge_zero_rank Γ hA hj hatom i j v (hy0.trans hyv) av
      (by simpa only [hg,zero_add] using hv)
    exact (binomBelow_pos_of_lt_one N c hc _ measureReal_nonneg
      (by change alphaGt Γ j 0 < 1; linarith)).trans_le hh
  have hk := route_pos_of_success_pos Γ i av hpos
  have hq := meanAcceptProb_le_success Γ hn i av hk
  have hqpos : 0 < meanAcceptProb Γ i av.bid := by
    have hh := success_le_n_meanAcceptProb Γ hn i av
    nlinarith
  have hmul : (v-y)*meanAcceptProb Γ i av.bid/((n:ℝ)*Real.exp 1) ≤
      (problem Γ i).envelope v := by
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hq (sub_pos.mpr hyv).le) (by positivity)).trans hleft
  have hpay : (problem Γ i).envelope v = v*((problem Γ i).outcome av).success -
      av.bid*((problem Γ i).outcome av).load := by
    rw [← (problem Γ i).bestResponse_iff_attains v av |>.mp hv]
    change ((problem Γ i).outcome av).utility v av.bid Γ.g Γ.A Γ.G = _
    rw [CountLaw.utility_eq,hA,hg,CountLaw.charge_ppi]
    ring
  have hupper : (problem Γ i).envelope v ≤
      (v-av.bid)*(av.routeCount:ℝ)*meanAcceptProb Γ i av.bid := by
    rw [hpay]
    have hl := mul_le_mul_of_nonneg_left ((problem Γ i).outcome av).success_le_load (hy0.trans hyv).le
    rw [load_eq_mean Γ hn i av] at hl ⊢
    nlinarith
  have hdiff : 0 ≤ v-av.bid := by
    have hh : 0 < (v-y)*meanAcceptProb Γ i av.bid/((n:ℝ)*Real.exp 1) := by positivity
    have hkr : 0 < (av.routeCount:ℝ) := by exact_mod_cast hk
    have hm : 0 < (av.routeCount:ℝ)*meanAcceptProb Γ i av.bid := mul_pos hkr hqpos
    have hu' : (v-av.bid)*((av.routeCount:ℝ)*meanAcceptProb Γ i av.bid) > 0 := by
      nlinarith [hh.trans_le (hmul.trans hupper)]
    exact (pos_of_mul_pos_left hu' hm.le).le
  have hkn : (av.routeCount:ℝ) ≤ n := Nat.cast_le.mpr av.routeCount_le
  have hb := hmul.trans (hupper.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hkn hdiff) hqpos.le))
  have hb' : (v-y)/((n:ℝ)*Real.exp 1) ≤ (v-av.bid)*(n:ℝ) := by
    apply (mul_le_mul_iff_left₀ hqpos).mp
    simpa only [div_mul_eq_mul_div] using hb
  apply (div_le_iff₀ (by positivity : 0 < (n:ℝ)^2*Real.exp 1)).mpr
  have hh := (div_le_iff₀ (mul_pos hnR (Real.exp_pos 1))).mp hb'
  nlinarith

end FCAppendix.Bayes
