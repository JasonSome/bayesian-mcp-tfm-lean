import FCAppendix.Existence.RankEnvelopeProbability
import FCAppendix.Finite.NonrareRanks

noncomputable section
namespace FCAppendix.Existence.RankEnvelope
open MeasureTheory Set Filter Topology

theorem capacity_rival_density (N C : ℕ → ℕ) (hN : Tendsto N atTop atTop) {rho : ℝ}
    (hDensity : Tendsto (fun t => (C t:ℝ)/((N t:ℝ)+1)) atTop (𝓝 rho)) :
    Tendsto (fun t => (C t:ℝ)/(N t:ℝ)) atTop (𝓝 rho) := by
  have hInv : Tendsto (fun t => 1/(N t:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hN)
  have hfactor : Tendsto (fun t => ((N t:ℝ)+1)/(N t:ℝ)) atTop (𝓝 1) := by
    have hh := (tendsto_const_nhds (x:=(1:ℝ))).add hInv
    rw [add_zero] at hh
    apply hh.congr'
    filter_upwards [hN.eventually_gt_atTop 0] with t ht
    have hNt : (N t:ℝ) ≠ 0 := by positivity
    field_simp
  have hh := hDensity.mul hfactor
  rw [mul_one] at hh
  convert hh using 1
  funext t
  have hden : (N t:ℝ)+1 ≠ 0 := by positivity
  field_simp

theorem ample_rank_zero_tendsto_one (mu : Measure ℝ) [IsFiniteMeasure mu]
    {n : ℕ} (hn : 2 ≤ n) (hmass : mu.real univ ≤ 1)
    (N C : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hC : ∀ t, C t ≤ N t+1)
    {rho : ℝ} (hDensity : Tendsto (fun t => (C t:ℝ)/((N t:ℝ)+1)) atTop (𝓝 rho))
    (hgap : contactTail mu n 0<rho) :
    Tendsto (fun t => rank mu (N t) (C t) n 0) atTop (𝓝 1) := by
  have hp := contactTail_bounds mu hn hmass 0
  have hq := Bayes.binomBelow_tendsto_one_of_subcritical N C (fun _ => contactTail mu n 0)
    hN hC (fun _ => hp.1) (fun _ => hp.2.le) tendsto_const_nhds
    (capacity_rival_density N C hN hDensity) hgap
  apply hq.congr'
  apply Eventually.of_forall
  intro t
  change Bayes.binomBelow (N t) (contactTail mu n 0) (C t)=rankSuccess (N t) (C t) (contactTail mu n 0)
  rw [rankSuccess_eq_prob _ _ ⟨hp.1,hp.2.le⟩,
    Bayes.binomBelow_eq_prob _ _ (hC t) _ hp.1 hp.2.le]

theorem eventually_costly_duplicate_gap {q0 : ℕ → ℝ} (hq0 : Tendsto q0 atTop (𝓝 1))
    {d H : ℝ} (hd : 0<d) : ∀ᶠ t in atTop, H*(1-q0 t)<d*(2*q0 t-1) := by
  have hh := (((hq0.const_mul 2).sub_const 1).const_mul d).sub
    (((tendsto_const_nhds (x:=(1:ℝ))).sub hq0).const_mul H)
  have hlim : Tendsto (fun t => d*(2*q0 t-1)-H*(1-q0 t)) atTop (𝓝 d) := by
    convert hh using 1
    norm_num
  filter_upwards [hlim.eventually (eventually_gt_nhds hd)] with t ht
  linarith

theorem uniform_bid_bound_tendsto_zero {q0 : ℕ → ℝ}
    (hq0 : Tendsto q0 atTop (𝓝 1)) (H : ℝ) :
    Tendsto (fun t => H*(1-q0 t)) atTop (𝓝 0) := by
  simpa only [sub_self,mul_zero] using ((tendsto_const_nhds (x:=(1:ℝ))).sub hq0).const_mul H

theorem integral_rank_bounds (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    (r c : ℕ) (hc : 1 ≤ c) (hcr : c ≤ r+1) {n : ℕ} (hn : 2 ≤ n) (hmass : mu.real univ ≤ 1)
    (hsupport : ∀ᵐ v ∂mu, 0 ≤ v) :
    mu.real univ*rank mu (r+1) c n 0 ≤ ∫ v, rank mu (r+1) c n v ∂mu ∧
      (∫ v, rank mu (r+1) c n v ∂mu) ≤ mu.real univ := by
  have hi : Integrable (rank mu (r+1) c n) mu :=
      Integrable.of_bound (continuous_rank mu _ _ _).aestronglyMeasurable 1
        (Eventually.of_forall fun v => by
          rw [Real.norm_eq_abs,abs_of_nonneg (rank_bounds mu _ _ hn hmass v).1]
          exact (rank_bounds mu _ _ hn hmass v).2)
  have hmono : Monotone (rank mu (r+1) c n) := rank_monotone mu hc hcr hn hmass
  constructor
  · have hh := integral_mono_ae (integrable_const (rank mu (r+1) c n 0)) hi
      (hsupport.mono fun v hv => hmono hv)
    simpa only [integral_const,smul_eq_mul] using hh
  · have hh := integral_mono_ae hi (integrable_const (1:ℝ))
      (Eventually.of_forall fun v => (rank_bounds mu _ _ hn hmass v).2)
    simpa only [integral_const,smul_eq_mul,mul_one] using hh

end FCAppendix.Existence.RankEnvelope
