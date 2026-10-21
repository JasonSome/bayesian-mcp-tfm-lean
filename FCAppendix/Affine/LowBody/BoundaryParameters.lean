import FCAppendix.Affine.LowBody.BinomialBoundary
import FCAppendix.Affine.LowBody.Rows
import FCAppendix.Affine.LowBody.CategoricalRateGuards

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory Set Filter Topology Real

lemma log_pmf_eq (N K : ℕ) (p : ℝ) (hKN : K≤N) (hp0 : 0<p) (hp1 : p<1) :
    log (PiBinomial.pmf N p K)=log (N.choose K:ℝ)+(K:ℝ)*log p+
      ((N-K:ℕ):ℝ)*log (1-p) := by
  have hc : (N.choose K:ℝ)≠0 := (Nat.cast_pos.mpr (Nat.choose_pos hKN)).ne'
  unfold PiBinomial.pmf
  rw [log_mul (mul_ne_zero hc (pow_ne_zero _ hp0.ne'))
      (pow_ne_zero _ (sub_pos.mpr hp1).ne'),log_mul hc (pow_ne_zero _ hp0.ne')]
  simp only [log_pow]

lemma hasDerivAt_log_pmf (N K : ℕ) (p : ℝ) (hKN : K≤N) (hp0 : 0<p) (hp1 : p<1) :
    HasDerivAt (fun q=>log (PiBinomial.pmf N q K))
      ((K:ℝ)/p-((N-K:ℕ):ℝ)/(1-p)) p := by
  have he := ((hasDerivAt_const p (log (N.choose K:ℝ))).add
    (((hasDerivAt_id p).log hp0.ne').const_mul (K:ℝ))).add
    ((((hasDerivAt_const p (1:ℝ)).sub (hasDerivAt_id p)).log
      (sub_pos.mpr hp1).ne').const_mul ((N-K:ℕ):ℝ))
  have hh : HasDerivAt (fun q=>log (N.choose K:ℝ)+(K:ℝ)*log q+
      ((N-K:ℕ):ℝ)*log (1-q)) ((K:ℝ)/p-((N-K:ℕ):ℝ)/(1-p)) p := by
    convert he using 1 <;> first | rfl | (simp only [id_eq,Pi.sub_apply]; ring)
  apply hh.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hp0 hp1] with q hq
  exact log_pmf_eq N K q hKN hq.1 hq.2

theorem pmf_antitone_above_mode (N K : ℕ) (hKN : K≤N) (q₀ q₁ : ℝ)
    (hq0 : 0<q₀) (hq1 : q₁<1) (hmode : (K:ℝ)≤(N:ℝ)*q₀) :
    AntitoneOn (fun p=>PiBinomial.pmf N p K) (Icc q₀ q₁) := by
  have hlog : AntitoneOn (fun p=>log (PiBinomial.pmf N p K)) (Icc q₀ q₁) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · intro p hp
      exact (hasDerivAt_log_pmf N K p hKN (hq0.trans_le hp.1) (hp.2.trans_lt hq1)).continuousAt.continuousWithinAt
    · intro p hp
      have hp' := interior_subset hp
      exact (hasDerivAt_log_pmf N K p hKN (hq0.trans_le hp'.1) (hp'.2.trans_lt hq1)).differentiableAt.differentiableWithinAt
    · intro p hp
      have hp' := interior_subset hp
      have hp0 : 0<p := hq0.trans_le hp'.1
      have hp1 : p<1 := hp'.2.trans_lt hq1
      rw [(hasDerivAt_log_pmf N K p hKN hp0 hp1).deriv]
      apply sub_nonpos.mpr
      apply (div_le_div_iff₀ hp0 (sub_pos.mpr hp1)).2
      rw [Nat.cast_sub hKN]
      have hm := mul_le_mul_of_nonneg_left hp'.1 (Nat.cast_nonneg N)
      nlinarith
  intro p hp q hq hpq
  have hpp := pmf_pos N K p (hq0.trans_le hp.1) (hp.2.trans_lt hq1) hKN
  have hpq' := pmf_pos N K q (hq0.trans_le hq.1) (hq.2.trans_lt hq1) hKN
  exact (Real.log_le_log_iff hpq' hpp).mp (hlog hp hq hpq)

def higherBidProbability (s a h : ℝ) (G : Measure ℝ) (b : ℝ) : ℝ :=
  a+h/2+s*G.real (Ioi b)

theorem higherBidProbability_bounds (s a h : ℝ) (hs : 0 ≤ s)
    (hsum : s+a+h=1) (G : Measure ℝ) [IsProbabilityMeasure G] (b : ℝ) :
    higherBidProbability s a h G b∈Icc (a+h/2) (1-h/2) := by
  have h0 : 0≤G.real (Ioi b) := measureReal_nonneg
  have h1 : G.real (Ioi b)≤1 := measureReal_le_one
  unfold higherBidProbability
  constructor
  · nlinarith [mul_nonneg hs h0]
  · nlinarith [mul_le_mul_of_nonneg_left h1 hs]

theorem eventually_boundary_uniform (c : ℕ→ℕ) (ρ q₀ q₁ : ℝ) (hρ : 0<ρ)
    (hq : ρ<q₀) (hqq : q₀≤q₁) (hq1 : q₁<1)
    (hc : Tendsto (fun m=>(c m:ℝ)/(m:ℝ)) atTop (𝓝 ρ)) :
    ∀ᶠ m : ℕ in atTop,∀q∈Icc q₀ q₁,
      boundary c q₁ m≤PiBinomial.pmf (m-2) q (c m-1) := by
  have he := (tendsto_boundary_trials_fraction c ρ hρ hc 2).eventually_lt_const hq
  filter_upwards [he,eventually_gt_atTop (2:ℕ)] with m hm hm2
  have hN : (0:ℝ)<((m-2:ℕ):ℝ) := Nat.cast_pos.mpr (by omega)
  have hKN : c m-1 ≤ m-2 := by
    have hh : ((c m-1:ℕ):ℝ)/((m-2:ℕ):ℝ)<1 := hm.trans (hqq.trans_lt hq1)
    exact (Nat.cast_lt.mp ((div_lt_one hN).mp hh)).le
  have hmode : ((c m-1:ℕ):ℝ)≤((m-2:ℕ):ℝ)*q₀ := by
    have hh := (div_lt_iff₀ hN).mp hm
    simpa only [mul_comm q₀] using hh.le
  intro q hq'
  exact pmf_antitone_above_mode (m-2) (c m-1) hKN q₀ q₁ (hρ.trans hq) hq1 hmode
    hq' ⟨hqq,le_rfl⟩ hq'.2

end FCAppendix.Affine.LowBody
