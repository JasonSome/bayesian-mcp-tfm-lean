import FCAppendix.Affine.Uniform06.EntryLiteralResponseMoments

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryLiteralCanonicalTransfer

open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.LowBody
open FCAppendix.Affine.WeightedSampling
open LiteralExperiment LiteralKernelIdentity EntryRawCentral EntryEarlySourceLimits
open EntryLiteralResponseGeometry EntryLiteralResponseMoments EntrySamplingLaw
open EntryReciprocalLimit
open ActualEntryGoodGeometry
open scoped BigOperators

variable {N C : ℕ}

theorem conditional_canonical_moments_on_prefix
    (μ : Measure RowRival) (i : Row) (g : GuardData)
    {b₀ b A U ε c q lo γ w s : ℝ}
    (h : Inputs μ i g N C b₀ A U ε c q lo γ w s)
    (hb : b ≤ g.multiplier+g.radius)
    (r : Fin N → RowRival) (hno : ∀ j,(r j).1 ≠ 1)
    (hcap : ∀ j,(r j).1=0 → (r j).2 ≤ U)
    (hgood : r ∈ RivalGood.good μ (tests (xi i) g A U) N ε) :
    let T := patternTemplate C (fun j => (r j).1)
    let B := rowBids b r
    (∫ u : unitInterval, response μ i C g b A U ε (r,u))=
      (canonicalLaw (xi i) g T B).expect (fairMarginal 0) ∧
    (∫ u : unitInterval, (response μ i C g b A U ε (r,u))^2)=
      (canonicalLaw (xi i) g T B).expect (duplicate 0) := by
  have hξ1 : xi i < 1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  let T := patternTemplate C (fun j => (r j).1)
  let B := rowBids b r
  have hc := finite_counts μ i g h r hno hgood
  have hd : imbalance T=RawMixedSource.draws r :=
    RawDeficitGeometry.template_imbalance_eq_draws C r hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  have hw : weights (xi i) g T B = profile i g b r :=
    EntryLiteralCentral.weights_eq_profile i g h.requiredDemand_eq C b r
  have hαs := all_action_guard_and_strip μ g h.rivals_pos (xi_pos i) hξ1 h.epsilon_nonneg
    h.prefix.margin_pos h.prefix.population_pos h.prefix.lower_pos
    (by linarith [h.prefix.lower_pos,h.radius_pos]) h.prefix.rejectionScale_pos
    h.means h.floor_error h.residual_positive h.residual_room h.demand_margin
    h.weight_margin h.rejection_margin h.seed_margin h.strip_margin h.count_margin r hno hgood
  have hα : 0 < guardAlpha (xi i) g T B := by rw [hαs.2.1 b]; norm_num
  have hW : (imbalance T:ℝ)< totalWeight (weights (xi i) g T B) := by
    nlinarith [SourceGuardGeometry.positive_guard_weight g T B h.prefix.margin_pos
      h.prefix.population_pos hα,mul_pos h.prefix.margin_pos h.prefix.population_pos]
  have hw0 : (weights (xi i) g T B).val 0=0 := by
    unfold weights
    dsimp only
    split_ifs
    · exact h.prefix.zero_eligibility (xi_pos i) _ hb
    · rfl
  have haeq (k : ℕ) :
      (∫ u : unitInterval,(response μ i C g b A U ε (r,u))^k)=
        ∫ u : unitInterval,(complement i C g b (r,u))^k := by
    apply integral_congr_ae
    filter_upwards [EntryLiteralCentral.sampler_positive_mass_ae
      (RawMixedSource.draws r) (profile i g b r)] with u hu
    have hx : (r,u) ∈ usable μ i g b A U ε := ⟨hgood,hno,hcap,hu⟩
    simp only [response,if_pos hx]
  have hpath (k : ℕ) :
      (∫ u : unitInterval,(complement i C g b (r,u))^k)=
        (pathLaw (weights (xi i) g T B) (imbalance T) ∅).expect (fun p =>
          (complementMarginal (xi i) T B (finalSet (imbalance T) ∅ p) 0)^k) := by
    change (∫ u : unitInterval,(fun p : Path (Fin (N+1)) (RawMixedSource.draws r) =>
      (complementMarginal (xi i) T B (finalSet (RawMixedSource.draws r) ∅ p) 0)^k)
      (sampler (RawMixedSource.draws r) (profile i g b r) u))=_
    rw [← hw,← hd]
    exact integral_sampler_test (weights (xi i) g T B) (imbalance T)
      (fun p => (complementMarginal (xi i) T B (finalSet (imbalance T) ∅ p) 0)^k)
  constructor
  · have hh := (haeq 1).trans (hpath 1)
    simp only [pow_one] at hh
    rw [canonical_path_fair_marginal (xi_pos i) hξ1 g T B 0 hW hw0]
    exact hh
  · rw [canonical_path_duplicate (xi_pos i) hξ1]
    exact (haeq 2).trans (hpath 2)

theorem conditional_canonical_moments
    (μ : Measure RowRival) (i : Row) (g : GuardData)
    {b A U ε c q lo γ w s : ℝ} (h : Inputs μ i g N C b A U ε c q lo γ w s)
    (r : Fin N → RowRival) (hno : ∀ j,(r j).1 ≠ 1)
    (hcap : ∀ j,(r j).1=0 → (r j).2 ≤ U)
    (hgood : r ∈ RivalGood.good μ (tests (xi i) g A U) N ε) :
    let T := patternTemplate C (fun j => (r j).1)
    let B := rowBids b r
    (∫ u : unitInterval, response μ i C g b A U ε (r,u))=
      (canonicalLaw (xi i) g T B).expect (fairMarginal 0) ∧
    (∫ u : unitInterval, (response μ i C g b A U ε (r,u))^2)=
      (canonicalLaw (xi i) g T B).expect (duplicate 0) :=
  conditional_canonical_moments_on_prefix μ i g h h.bid_window.2 r hno hcap hgood

def canonicalGoodMarginal (i : Row) (G : Measure (ℝ × ℝ)) (C N : ℕ)
    (g : GuardData) (b A U ε : ℝ) : ℝ :=
  ∫ r in RivalGood.good (RawMixedSource.source i G) (tests (xi i) g A U) N ε,
    (canonicalLaw (xi i) g (patternTemplate C (fun j => (r j).1)) (rowBids b r)).expect (fairMarginal 0)
    ∂Measure.pi (fun _ : Fin N => RawMixedSource.source i G)

def canonicalGoodDuplicate (i : Row) (G : Measure (ℝ × ℝ)) (C N : ℕ)
    (g : GuardData) (b A U ε : ℝ) : ℝ :=
  ∫ r in RivalGood.good (RawMixedSource.source i G) (tests (xi i) g A U) N ε,
    (canonicalLaw (xi i) g (patternTemplate C (fun j => (r j).1)) (rowBids b r)).expect (duplicate 0)
    ∂Measure.pi (fun _ : Fin N => RawMixedSource.source i G)

theorem integrated_canonical_moments_on_prefix (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (g : GuardData) {b₀ b A U ε c q lo γ w s : ℝ}
    (h : Inputs (RawMixedSource.source i G) i g N C b₀ A U ε c q lo γ w s)
    (hb : b ≤ g.multiplier+g.radius)
    (hcap : ∀ᵐ p ∂G,p.2 ≤ U) :
    (∫ x, response (RawMixedSource.source i G) i C g b A U ε x
      ∂EntryIIDCentral.rowLaw (RawMixedSource.source i G) N)=
      canonicalGoodMarginal i G C N g b A U ε ∧
    (∫ x, (response (RawMixedSource.source i G) i C g b A U ε x)^2
      ∂EntryIIDCentral.rowLaw (RawMixedSource.source i G) N)=
      canonicalGoodDuplicate i G C N g b A U ε := by
  let ν := RawMixedSource.source i G
  let p : EntryIIDCentral.Row (Ω := RowRival) N → ℝ := response ν i C g b A U ε
  let E := RivalGood.good ν (tests (xi i) g A U) N ε
  have hE : MeasurableSet E :=
    RivalGood.measurable_good ν _ (RivalGood.statistics_measurable _ _ _ _ _ _ _ _ _) N ε
  have hpb x : p x ∈ Icc (0:ℝ) 1 := by
    dsimp [p,response]
    split_ifs
    · exact EntryLiteralResponseGeometry.complement_bounds i C g b x
    · norm_num
  have hpi : Integrable p (EntryIIDCentral.rowLaw ν N) :=
    Integrable.of_mem_Icc 0 1 (measurable_response _ i _ _ _ _ _ _).aemeasurable (ae_of_all _ hpb)
  have hpsqi : Integrable (fun x => (p x)^2) (EntryIIDCentral.rowLaw ν N) := by
    apply Integrable.of_mem_Icc 0 1 ((measurable_response _ i _ _ _ _ _ _).pow_const 2).aemeasurable
    exact ae_of_all _ fun x => ⟨sq_nonneg _,by nlinarith [(hpb x).1,(hpb x).2]⟩
  have hraw (j : Fin N) := (measurePreserving_eval (fun _ : Fin N => ν) j).quasiMeasurePreserving.ae ((raw_no_tag_one i G).and (raw_lower_cap i G hcap))
  have ha : ∀ᵐ r ∂Measure.pi (fun _ : Fin N => ν),
      (∀ j,(r j).1 ≠ 1) ∧ (∀ j,(r j).1=0 → (r j).2 ≤ U) := by
    filter_upwards [ae_all_iff.mpr hraw] with r hr
    exact ⟨fun j => (hr j).1,fun j => (hr j).2⟩
  have heq (r : Fin N → RowRival) (hr : r ∉ E) (u : unitInterval) : p (r,u)=0 := by
    have hx : (r,u) ∉ usable ν i g b A U ε := fun hx => hr hx.1
    simp [p,response,hx]
  constructor
  · rw [EntryIIDCentral.rowLaw,integral_prod _ hpi]
    unfold canonicalGoodMarginal
    rw [← integral_indicator hE]
    apply integral_congr_ae
    filter_upwards [ha] with r hr
    by_cases hg : r ∈ E
    · rw [Set.indicator_of_mem hg]
      exact (conditional_canonical_moments_on_prefix ν i g h hb r hr.1 hr.2 hg).1
    · rw [Set.indicator_of_notMem hg]
      simp only [heq r hg,integral_zero]
  · rw [EntryIIDCentral.rowLaw,integral_prod _ hpsqi]
    unfold canonicalGoodDuplicate
    rw [← integral_indicator hE]
    apply integral_congr_ae
    filter_upwards [ha] with r hr
    by_cases hg : r ∈ E
    · rw [Set.indicator_of_mem hg]
      exact (conditional_canonical_moments_on_prefix ν i g h hb r hr.1 hr.2 hg).2
    · rw [Set.indicator_of_notMem hg]
      simp only [heq r hg,zero_pow (by decide : (2:ℕ)≠0),integral_zero]

theorem integrated_canonical_moments (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (g : GuardData) {b A U ε c q lo γ w s : ℝ}
    (h : Inputs (RawMixedSource.source i G) i g N C b A U ε c q lo γ w s)
    (hcap : ∀ᵐ p ∂G,p.2 ≤ U) :
    (∫ x, response (RawMixedSource.source i G) i C g b A U ε x
      ∂EntryIIDCentral.rowLaw (RawMixedSource.source i G) N)=
      canonicalGoodMarginal i G C N g b A U ε ∧
    (∫ x, (response (RawMixedSource.source i G) i C g b A U ε x)^2
      ∂EntryIIDCentral.rowLaw (RawMixedSource.source i G) N)=
      canonicalGoodDuplicate i G C N g b A U ε :=
  integrated_canonical_moments_on_prefix i G g h h.bid_window.2 hcap

lemma normalized_ratio_eq {P A B R : ℝ} (hR : R ≠ 0) :
    (R*A)^2/(P*(R^2*B))=A^2/(P*B) := by
  rw [mul_pow,show P*(R^2*B)=R^2*(P*B) by ring,
    mul_div_mul_left _ _ (pow_ne_zero 2 hR)]

section OriginalCentral
variable {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem original_central_canonical_ratio
    (i : Row) (V : Ω → ℝ) (B : ℕ → Ω → ℝ)
    (hV : Measurable V) (hB : ∀ m, Measurable (B m))
    (hvalue : μ.map V=LowChernoff.conditionalValueLaw i)
    (hadmissible : ∀ m, ∀ᵐ ω ∂μ, B m ω ≤ V ω)
    (hactive : ∀ᵐ ω ∂μ, entry i < V ω → Tendsto (fun m => B m ω) atTop
      (𝓝 (ActiveGraphComponent.activeBid i (V ω))))
    (b : ℕ → ℝ) (hbt : ∀ m, b m ≤ cutoff i) (hb : Tendsto b atTop (𝓝 (entry i)))
    (g : ℕ → GuardData) (hl : Tendsto (fun m => (g m).multiplier) atTop (𝓝 (entry i)))
    (n : ℕ → ℕ) (hnp : ∀ m, 4 ≤ n m) (hn : Tendsto n atTop atTop)
    {ε q U lo : ℝ} (hε : 0 < ε) (hloLam : lo < entry i)
    (A γ w s : ℕ → ℝ)
    (hcap : ∀ m, ∀ᵐ p ∂joint μ V (B m),p.2 ≤ U)
    (hfinite : ∀ m, Inputs (RawMixedSource.source i (joint μ V (B m))) i (g m)
      (n m-1) (capacity (n m)) (b m) (A m) U ε (eligibleMass μ i V/2) q lo (γ m) (w m) (s m))
    {z : ℝ} (hcentral : Tendsto (fun m => center i (joint μ V (B m))
      (n m-1) (capacity (n m)) (b m)) atTop (𝓝 z)) :
    let G := fun m => joint μ V (B m)
    let P := fun m => EntryIIDCentral.rowLaw (RawMixedSource.source i (G m)) (n m-1)
    let p : (m : ℕ) → EntryIIDCentral.Row (Ω := RowRival) (n m-1) → ℝ := fun m => response (RawMixedSource.source i (G m)) i
      (capacity (n m)) (g m) (b m) (A m) U ε
    let p0 := fun m => (P m).real {x | 0 < p m x}
    let Q := fun m => canonicalGoodMarginal i (G m) (capacity (n m)) (n m-1) (g m) (b m) (A m) U ε
    let R2 := fun m => canonicalGoodDuplicate i (G m) (capacity (n m)) (n m-1) (g m) (b m) (A m) U ε
    (∀ᶠ m in atTop, 0 < p0 m ∧ 0 < Q m ∧ 0 < R2 m) ∧
      ∃ r ≥ (1/2:ℝ), Tendsto (fun m => (Q m)^2/(p0 m*R2 m)) atTop (𝓝 r) ∧
        Tendsto (fun m => Q m/p0 m) atTop (𝓝 0) := by
  let G := fun m => joint μ V (B m)
  letI (m : ℕ) : IsProbabilityMeasure (G m) :=
    Measure.isProbabilityMeasure_map (hV.prodMk (hB m)).aemeasurable
  let N := fun m => n m-1
  let P := fun m => EntryIIDCentral.rowLaw (RawMixedSource.source i (G m)) (N m)
  let p : (m : ℕ) → EntryIIDCentral.Row (Ω := RowRival) (N m) → ℝ := fun m => response (RawMixedSource.source i (G m)) i
    (capacity (n m)) (g m) (b m) (A m) U ε
  let p0 := fun m => (P m).real {x | 0 < p m x}
  let Q := fun m => canonicalGoodMarginal i (G m) (capacity (n m)) (N m) (g m) (b m) (A m) U ε
  let R2 := fun m => canonicalGoodDuplicate i (G m) (capacity (n m)) (N m) (g m) (b m) (A m) U ε
  let α := Real.sqrt (limitingVariance μ i V)
  let β := eligibleHMean μ i V*Real.sqrt (1-cutoff i)
  let κ := reciprocalMean μ i V
  have hm := original_central_response_moments μ i V B hV hB hvalue hadmissible hactive
    b hbt hb g hl n hnp hn hε hloLam A γ w s hcap hfinite hcentral
  change Tendsto p0 atTop (𝓝 (EntryCentralRatio.success α β z)) ∧
    Tendsto (fun m => ∫ x, Real.sqrt (N m:ℝ)*p m x ∂P m) atTop
      (𝓝 (EntryCentralRatio.firstMoment α β z/(entry i*κ))) ∧
    Tendsto (fun m => ∫ x, (Real.sqrt (N m:ℝ)*p m x)^2 ∂P m) atTop
      (𝓝 (EntryCentralRatio.secondMoment α β z/(entry i*κ)^2)) at hm
  have hbp (m) : 0 < b m := (hfinite m).lo_pos.trans_le
    ((hfinite m).lower_price.trans (hfinite m).bid_window.1)
  have hα : 0 < α := Real.sqrt_pos.mpr
    (limitingVariance_positive μ i V B hV hB hvalue hadmissible hactive b hbp hbt hb)
  have hβ : 0 ≤ β := mul_nonneg (eligibleHMean_positive μ i V hV hvalue).le (Real.sqrt_nonneg _)
  have hκ : 0 < κ := reciprocalMean_positive μ i V hV hvalue
  have hk : 0 < entry i*κ := mul_pos (EarlyMean.entry_pos i) hκ
  have hp0 := EntryCentralRatio.success_pos hα β z
  have hAB := EntryCentralRatio.first_second_moment_pos hα β z
  have he (m) := integrated_canonical_moments i (G m) (g m) (hfinite m) (hcap m)
  have hfirst (m) : (∫ x, Real.sqrt (N m:ℝ)*p m x ∂P m)=Real.sqrt (N m:ℝ)*Q m := by
    rw [integral_const_mul,(he m).1]
  have hsecond (m) : (∫ x, (Real.sqrt (N m:ℝ)*p m x)^2 ∂P m)=(N m:ℝ)*R2 m := by
    simp_rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg (N m))]
    rw [integral_const_mul,(he m).2]
  have hQ : Tendsto (fun m => Real.sqrt (N m:ℝ)*Q m) atTop
      (𝓝 (EntryCentralRatio.firstMoment α β z/(entry i*κ))) := by
    simpa only [hfirst] using hm.2.1
  have hR : Tendsto (fun m => (N m:ℝ)*R2 m) atTop
      (𝓝 (EntryCentralRatio.secondMoment α β z/(entry i*κ)^2)) := by
    simpa only [hsecond] using hm.2.2
  have hpos : ∀ᶠ m in atTop, 0 < p0 m ∧ 0 < Q m ∧ 0 < R2 m := by
    filter_upwards [hm.1.eventually_const_lt hp0,
      hQ.eventually_const_lt (div_pos hAB.1 hk),
      hR.eventually_const_lt (div_pos hAB.2 (sq_pos_of_pos hk))] with m hp hq hr
    have hNr : (0:ℝ)< N m := by exact_mod_cast (hfinite m).rivals_pos
    exact ⟨hp,(mul_pos_iff_of_pos_left (Real.sqrt_pos.mpr hNr)).mp hq,
      (mul_pos_iff_of_pos_left hNr).mp hr⟩
  have hlim := (hQ.pow 2).div (hm.1.mul hR)
    (mul_pos hp0 (div_pos hAB.2 (sq_pos_of_pos hk))).ne'
  have hvalue' : (EntryCentralRatio.firstMoment α β z/(entry i*κ))^2/
      (EntryCentralRatio.success α β z*(EntryCentralRatio.secondMoment α β z/(entry i*κ)^2))=
      (EntryCentralRatio.firstMoment α β z)^2/
        (EntryCentralRatio.success α β z*EntryCentralRatio.secondMoment α β z) := by
    field_simp [hk.ne',hp0.ne',hAB.2.ne',(EarlyMean.entry_pos i).ne',hκ.ne']
  rw [hvalue'] at hlim
  have hratio (m) : (Real.sqrt (N m:ℝ)*Q m)^2/(p0 m*((N m:ℝ)*R2 m))=
      (Q m)^2/(p0 m*R2 m) := by
    have hNr : (0:ℝ)< N m := by exact_mod_cast (hfinite m).rivals_pos
    have hh := normalized_ratio_eq (P := p0 m) (A := Q m) (B := R2 m)
      (Real.sqrt_pos.mpr hNr).ne'
    simpa only [Real.sq_sqrt hNr.le] using hh
  have hQzero : Tendsto Q atTop (𝓝 0) := by
    have hsN : Tendsto (fun m => Real.sqrt (N m:ℝ)) atTop atTop := by
      simpa only [N,Function.comp_def] using Real.tendsto_sqrt_atTop.comp
        (tendsto_natCast_atTop_atTop.comp (PhysicalRates.rivals_tendsto.comp hn))
    have hz := hQ.div_atTop hsN
    apply hz.congr
    intro m
    have hNr : (0:ℝ)< N m := by exact_mod_cast (hfinite m).rivals_pos
    change Real.sqrt (N m:ℝ)*Q m/Real.sqrt (N m:ℝ)=Q m
    field_simp [(Real.sqrt_pos.mpr hNr).ne']
  have hconditional : Tendsto (fun m => Q m/p0 m) atTop (𝓝 0) := by
    simpa using! hQzero.div hm.1 hp0.ne'
  refine ⟨hpos,_,EntryCentralRatio.actual_central_ratio_ge_half hα hβ z,?_,hconditional⟩
  change Tendsto (fun m => (Real.sqrt (N m:ℝ)*Q m)^2/(p0 m*((N m:ℝ)*R2 m))) atTop
    (𝓝 ((EntryCentralRatio.firstMoment α β z)^2/
      (EntryCentralRatio.success α β z*EntryCentralRatio.secondMoment α β z))) at hlim
  simpa only [hratio] using! hlim

end OriginalCentral

end FCAppendix.Affine.Uniform06.EntryLiteralCanonicalTransfer
