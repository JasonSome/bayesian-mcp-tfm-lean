import FCAppendix.Affine.Hybrid.Multiple03.Rates

noncomputable section
namespace FCAppendix.Affine.Hybrid.Tail03
open Set Filter Topology
open FCAppendix.Affine.Hybrid.Multiple03

def lowerRateWitness (δ : ℝ) : ℝ :=
  witnessGap (1/100+δ) (8/25) (67/100-δ) (4/25)
def upperRateWitness (δ privateMass : ℝ) : ℝ :=
  witnessGap (1/100+δ) (67/100-δ-privateMass) (8/25+privateMass) (3/25)

theorem rational_log_witnesses_at_zero :
    (1397/10000:ℝ)< lowerRateWitness 0 ∧
    (1101/10000:ℝ)< upperRateWitness 0 0 := by
  constructor
  · simpa [lowerRateWitness,rateLowQ,rateActiveQ,rateUpperQ,tiltQ,certifiedGapQ]
      using rational_witness_gap RateCase.tailLower
  · simpa [upperRateWitness,rateLowQ,rateActiveQ,rateUpperQ,tiltQ,certifiedGapQ]
      using rational_witness_gap RateCase.tailUpper

theorem lowerRateWitness_continuous_zero : ContinuousAt lowerRateWitness 0 := by
  unfold lowerRateWitness witnessGap
  fun_prop (disch := norm_num)

theorem upperRateWitness_continuous_zero :
    ContinuousAt (fun x : ℝ×ℝ => upperRateWitness x.1 x.2) (0,0) := by
  unfold upperRateWitness witnessGap
  fun_prop (disch := norm_num)

theorem rate_witnesses_open_neighborhood :
    ∃ ε : ℝ,0< ε ∧ ε≤1/1000 ∧ ∀ δ privateMass : ℝ,
      |δ|< ε→|privateMass|< ε→
      (1397/10000:ℝ)< lowerRateWitness δ ∧
      (1101/10000:ℝ)< upperRateWitness δ privateMass := by
  have hl : ContinuousAt (fun x : ℝ×ℝ => lowerRateWitness x.1) (0,0) :=
    lowerRateWitness_continuous_zero.comp_of_eq continuous_fst.continuousAt rfl
  have hh := upperRateWitness_continuous_zero
  have hev : ∀ᶠ x : ℝ×ℝ in 𝓝 (0,0),
      (1397/10000:ℝ)< lowerRateWitness x.1 ∧
      (1101/10000:ℝ)< upperRateWitness x.1 x.2 :=
    (hl.tendsto.eventually (Ioi_mem_nhds rational_log_witnesses_at_zero.1)).and
      (hh.tendsto.eventually (Ioi_mem_nhds rational_log_witnesses_at_zero.2))
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min ε (1/1000),lt_min hε (by norm_num),min_le_right _ _,?_⟩
  intro δ p hδ hp
  apply hball (y := (δ,p))
  change max (dist δ 0) (dist p 0)< ε
  simp only [Real.dist_eq,sub_zero]
  exact max_lt (hδ.trans_le (min_le_left _ _)) (hp.trans_le (min_le_left _ _))

theorem perturbable_source_rate_guards :
    ∃ ε : ℝ,0< ε ∧ ε≤1/1000 ∧ ∀ δ p : ℝ,
      0≤ δ→ δ< ε→0≤ p→ p< ε→
      2*FCAppendix.Ample.binaryKL (99/200) (1-(67/100-δ)/2)+1397/10000<
        FCAppendix.Affine.LowBody.jointRate (1/100+δ) (8/25) (67/100-δ) (99/200) ∧
      2*FCAppendix.Ample.binaryKL (99/200) (1-(8/25+p)/2)+1101/10000<
        FCAppendix.Affine.LowBody.jointRate (1/100+δ) (67/100-δ-p) (8/25+p) (99/200) := by
  obtain ⟨ε,hε,heps,hneigh⟩ := rate_witnesses_open_neighborhood
  refine ⟨ε,hε,heps,?_⟩
  intro δ p hδ0 hδ hp0 hp
  have hh := hneigh δ p (by rwa [abs_of_nonneg hδ0]) (by rwa [abs_of_nonneg hp0])
  constructor
  · exact source_rate_gap_of_witness (by positivity) (by norm_num)
      (by linarith) (by norm_num) (by norm_num) hh.1
  · exact source_rate_gap_of_witness (by positivity) (by linarith)
      (by positivity) (by norm_num) (by norm_num) hh.2

theorem small_theta_rate_guards :
    ∃ ε : ℝ,0< ε ∧ ∀ᶠ θ : ℝ in 𝓝[>] (0:ℝ),
      θ^2< ε ∧ ∀ p : ℝ,0≤ p→ p< ε→
        (1397/10000:ℝ)< lowerRateWitness (θ^2) ∧
        (1101/10000:ℝ)< upperRateWitness (θ^2) p := by
  obtain ⟨ε,hε,_,hneigh⟩ := rate_witnesses_open_neighborhood
  have ht : Tendsto (fun θ : ℝ => θ^2) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) := by
    have hh : Tendsto (fun θ : ℝ => θ^2) (𝓝 (0:ℝ)) (𝓝 ((0:ℝ)^2)) :=
      (hasDerivAt_pow 2 (0:ℝ)).continuousAt.tendsto
    simpa only [zero_pow (by norm_num : (2:ℕ)≠0)] using hh.mono_left nhdsWithin_le_nhds
  refine ⟨ε,hε,?_⟩
  filter_upwards [ht.eventually (Iio_mem_nhds hε)] with θ hθ
  refine ⟨hθ,?_⟩
  intro p hp0 hp
  exact hneigh (θ^2) p (by rwa [abs_of_nonneg (sq_nonneg θ)])
    (by rwa [abs_of_nonneg hp0])

theorem eventual_vanishing_private_rate_guards
    (ε : ℝ) (hε : 0< ε) (δ : ℝ) (hδ0 : 0≤ δ) (hδ : δ< ε)
    (h : ∀ d p : ℝ,0≤ d→ d< ε→0≤ p→ p< ε→
      (1397/10000:ℝ)< lowerRateWitness d ∧
      (1101/10000:ℝ)< upperRateWitness d p)
    (p : ℕ→ℝ) (hp0 : ∀m,0≤ p m) (hp : Tendsto p atTop (𝓝 0)) :
    ∀ᶠ m in atTop,(1397/10000:ℝ)< lowerRateWitness δ ∧
      (1101/10000:ℝ)< upperRateWitness δ (p m) := by
  filter_upwards [hp.eventually (Iio_mem_nhds hε)] with m hm
  exact h δ (p m) hδ0 hδ (hp0 m) hm

end FCAppendix.Affine.Hybrid.Tail03
