import FCAppendix.Affine.Uniform06.EntryProducedMoments

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryGoodKernelBounds

open MeasureTheory Set Filter Topology LowBody
open scoped BigOperators
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.ClippedResidual
open LiteralExperiment LiteralKernelDecomposition EntryLiteralResponseGeometry
open EntryLiteralCanonicalTransfer EntryLiteralResponseMoments EntryRawCentral
open ActualEntryGoodGeometry FixedPriceEntryIntegral EntryEarlySourceLimits

variable {N C : ℕ}

theorem Inputs.at_bid {μ : Measure RowRival} {i : Row} {g : GuardData}
    {b₀ b A U ε c q lo γ w s : ℝ}
    (h : Inputs μ i g N C b₀ A U ε c q lo γ w s)
    (hb : b∈Icc (g.multiplier-g.radius) (g.multiplier+g.radius))
    (hcap : b≤ U) (hhalf : (1-xi i/2)*U≤ b) :
    Inputs μ i g N C b A U ε c q lo γ w s :=
  {h with bid_window := hb,bid_cap := hcap,half_receipt := hhalf}

theorem good_alpha (μ : Measure RowRival) (i : Row) (g : GuardData)
    {b A U ε c q lo γ w s : ℝ} (h : Inputs μ i g N C b A U ε c q lo γ w s)
    (r : Fin N→ RowRival) (hno : ∀ j,(r j).1≠1)
    (hr : r∈RivalGood.good μ (tests (xi i) g A U) N ε) :
    ∀ a : ℝ,guardAlpha (xi i) g (patternTemplate C (fun j => (r j).1)) (rowBids a r)=1 := by
  have hξ1 : xi i<1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  exact (all_action_guard_and_strip μ g h.rivals_pos (xi_pos i) hξ1 h.epsilon_nonneg
    h.prefix.margin_pos h.prefix.population_pos h.prefix.lower_pos
    (by linarith [h.prefix.lower_pos,h.prefix.radius_nonneg]) h.prefix.rejectionScale_pos
    h.means h.floor_error h.residual_positive h.residual_room h.demand_margin h.weight_margin
    h.rejection_margin h.seed_margin h.strip_margin h.count_margin r hno hr).2.1

theorem original_below_lower_zero (i : Row) (G : Measure (ℝ×ℝ)) [IsProbabilityMeasure G]
    (g : GuardData) {b₀ b A U ε c q lo γ w s : ℝ}
    (h : Inputs (RawMixedSource.source i G) i g N C b₀ A U ε c q lo γ w s)
    (hb : b≤ g.multiplier-g.radius) :
    canonicalGoodMarginal i G C N g b A U ε=0 := by
  let ν := RawMixedSource.source i G
  let H := RivalGood.good ν (tests (xi i) g A U) N ε
  let P := Measure.pi (fun _ : Fin N => ν)
  have hH : MeasurableSet H := RivalGood.measurable_good ν _
    (RivalGood.statistics_measurable _ _ _ _ _ _ _ _ _) N ε
  have hno : ∀ᵐ r ∂P,∀ j,(r j).1≠1 := ae_all_iff.mpr fun j =>
    (measurePreserving_eval (fun _ : Fin N => ν) j).quasiMeasurePreserving.ae (raw_no_tag_one i G)
  change (∫ r, (canonicalLaw (xi i) g (patternTemplate C (fun j => (r j).1))
    (rowBids b r)).expect (fairMarginal 0) ∂P.restrict H)=0
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem hH,ae_restrict_of_ae hno] with r hr hn
  have hα := good_alpha ν i g h r hn hr b
  have hz := SourceGuardGeometry.canonical_low_focal_zero (xi_pos i)
    (by cases i <;> norm_num [xi,xiQ,etaQ]) g (patternTemplate C (fun j => (r j).1))
    (rowBids b r) h.prefix.margin_pos h.prefix.population_pos h.prefix.radius_nonneg
    h.prefix.requiredDemand_pos h.prefix.lower_pos (rowBids_outside C b r) 0 hb
  rw [hα,one_mul,one_mul] at hz
  have he := expect_first_add_duplicate (canonicalLaw (xi i) g
    (patternTemplate C (fun j => (r j).1)) (rowBids b r)) 0
  change (canonicalLaw (xi i) g (patternTemplate C (fun j => (r j).1))
    (rowBids b r)).expect (fairMarginal 0)=(0:ℝ)
  linarith [hz.1,hz.2]

theorem original_frozen_integral (i : Row) (G : Measure (ℝ×ℝ)) [IsProbabilityMeasure G]
    (g : GuardData) {b₀ b A U ε c q lo γ w s : ℝ}
    (h : Inputs (RawMixedSource.source i G) i g N C b₀ A U ε c q lo γ w s)
    (hcap : ∀ᵐ p ∂G,p.2≤ U) (hb : b≤ g.multiplier+g.radius) :
    canonicalGoodMarginal i G C N g b A U ε=
      ∫ x,frozen (RawMixedSource.source i G) i C g b₀ A U ε b x
        ∂EntryIIDCentral.rowLaw (RawMixedSource.source i G) N := by
  rw [← (integrated_canonical_moments_on_prefix i G g h hb hcap).1]
  apply integral_congr_ae
  exact ae_of_all _ fun x => response_eq_frozen _ i g h.requiredDemand_eq h.prefix hb h.bid_window.2 x

theorem original_good_lipschitz (i : Row) (G : Measure (ℝ×ℝ)) [IsProbabilityMeasure G]
    (hnon : ∀ᵐ p ∂G,0≤ p.2) (g : GuardData) {b₀ A U ε c q lo γ w s a : ℝ}
    (h : Inputs (RawMixedSource.source i G) i g N C b₀ A U ε c q lo γ w s)
    (hcap : ∀ᵐ p ∂G,p.2≤ U) (ha : 0< a) :
    LipschitzOnWith (Real.nnabs (1/(xi i*a)))
      (fun b => canonicalGoodMarginal i G C N g b A U ε) (Icc a (g.multiplier+g.radius)) := by
  let ν := RawMixedSource.source i G
  let P := EntryIIDCentral.rowLaw ν N
  let f := frozen (N:=N) ν i C g b₀ A U ε
  have hnon' : ∀ᵐ x ∂P,∀ j,(x.1 j).1=0 → 0≤(x.1 j).2 := ae_all_iff.mpr fun j =>
    (EntryIIDCentral.eval_preserving ν N j).quasiMeasurePreserving.ae
      (FixedPriceRawDerivative.raw_lower_nonnegative i G hnon)
  have hfi (b : ℝ) : Integrable (f b) P := Integrable.of_mem_Icc 0 1
    (measurable_frozen ν i C g b₀ A U ε b).aemeasurable
      (ae_of_all _ fun x => frozen_bounds _ _ _ _ _ _ _ _ _ x)
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [original_frozen_integral i G g h hcap hx.2,
    original_frozen_integral i G g h hcap hy.2,Real.dist_eq,Real.dist_eq]
  have hl : ∀ᵐ z ∂P,|f x z-f y z|≤(Real.nnabs (1/(xi i*a)):ℝ)*|x-y| := by
    filter_upwards [hnon'] with z hz
    have hh := (frozen_lipschitz ν i g h ha z hz).1.dist_le_mul x hx.1 y hy.1
    simpa only [Real.dist_eq] using hh
  calc
    |(∫ z,f x z ∂P)-(∫ z,f y z ∂P)|=|∫ z,f x z-f y z ∂P| := by
      rw [integral_sub (hfi x) (hfi y)]
    _ ≤ ∫ z,|f x z-f y z| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ _z,(Real.nnabs (1/(xi i*a)):ℝ)*|x-y| ∂P :=
      integral_mono_ae ((hfi x).sub (hfi y)).abs (integrable_const _) hl
    _ = _ := by simp

theorem original_good_monotone (i : Row) (G : Measure (ℝ×ℝ)) [IsProbabilityMeasure G]
    (hnon : ∀ᵐ p ∂G,0≤ p.2) (g : GuardData) {b₀ A U ε c q lo γ w s : ℝ}
    (h : Inputs (RawMixedSource.source i G) i g N C b₀ A U ε c q lo γ w s)
    (hcap : ∀ᵐ p ∂G,p.2≤ U) :
    MonotoneOn (fun b => canonicalGoodMarginal i G C N g b A U ε) (Icc 0 (g.multiplier+g.radius)) := by
  let ν := RawMixedSource.source i G
  let P := EntryIIDCentral.rowLaw ν N
  let f := frozen (N:=N) ν i C g b₀ A U ε
  have hnon' : ∀ᵐ x ∂P,∀ j,(x.1 j).1=0 → 0≤(x.1 j).2 := ae_all_iff.mpr fun j =>
    (EntryIIDCentral.eval_preserving ν N j).quasiMeasurePreserving.ae
      (FixedPriceRawDerivative.raw_lower_nonnegative i G hnon)
  have hfi (b : ℝ) : Integrable (f b) P := Integrable.of_mem_Icc 0 1
    (measurable_frozen ν i C g b₀ A U ε b).aemeasurable
      (ae_of_all _ fun x => frozen_bounds _ _ _ _ _ _ _ _ _ x)
  intro x hx y hy hxy
  change canonicalGoodMarginal i G C N g x A U ε≤canonicalGoodMarginal i G C N g y A U ε
  rw [original_frozen_integral i G g h hcap hx.2,original_frozen_integral i G g h hcap hy.2]
  apply integral_mono_ae (hfi x) (hfi y)
  filter_upwards [hnon'] with z hz
  by_cases hu : z∈usable ν i g b₀ A U ε
  · simp only [f,frozen,if_pos hu]
    have hh := GuardPrefix.complement_marginal_update_monotone (xi_pos i)
      (by cases i <;> norm_num [xi,xiQ,etaQ]) (patternTemplate C (fun j => (z.1 j).1))
      (rowBids 0 z.1) 0 (fun j _ => LowBody.rowBids_nonneg 0 z.1 le_rfl hz j)
      (sampleSet i g b₀ z) hx.1 hxy
    simpa only [LowBody.rowBids_update] using hh
  · simp only [f,frozen,if_neg hu,le_refl]

theorem original_good_lower_tail (i : Row) (G : Measure (ℝ×ℝ)) [IsProbabilityMeasure G]
    (g : GuardData) {b A U ε c q lo γ w s τ : ℝ}
    (h : Inputs (RawMixedSource.source i G) i g N C b A U ε c q lo γ w s)
    (hcap : ∀ᵐ p ∂G,p.2≤ U) (hτ : 0≤τ)
    (hmean : (C:ℝ)/(N:ℝ)+τ≤ RawMixedSource.mean i G b) :
    canonicalGoodMarginal i G C N g b A U ε≤ Real.exp (-2*(N:ℝ)*τ^2) := by
  let ν := RawMixedSource.source i G
  let P := EntryIIDCentral.rowLaw ν N
  let Q := Measure.pi (fun _ : Fin N => ν)
  let X := RawMixedSource.demand (xi i) b
  let E : Set (Fin N→ RowRival) := {r | (∑ j,X (r j))<(C:ℝ)}
  let f := response (N:=N) ν i C g b A U ε
  have hb : 0< b := h.lo_pos.trans_le (h.lower_price.trans h.bid_window.1)
  have hn : (0:ℝ)< N := Nat.cast_pos.mpr h.rivals_pos
  have hE : MeasurableSet E := by
    exact measurableSet_lt (Finset.measurable_sum _ fun j _ =>
      (RawMixedSource.measurable_demand _ _).comp (measurable_pi_apply j)) measurable_const
  have hfi : Integrable f P := Integrable.of_mem_Icc 0 1
    (measurable_response ν i C g b A U ε).aemeasurable
      (ae_of_all _ fun x => EntryLiteralModerate.response_bounds (N:=N) (C:=C) ν i g b A U ε x)
  have hI : Integrable (fun x : EntryIIDCentral.Row (Ω := RowRival) N => E.indicator (fun _ => (1:ℝ)) x.1) P :=
    Integrable.of_mem_Icc 0 1 ((measurable_const.indicator hE).comp measurable_fst).aemeasurable
      (ae_of_all _ fun x => by simp only [indicator_apply]; split_ifs <;> norm_num)
  have hpoint : ∀ x,f x≤ E.indicator (fun _ => (1:ℝ)) x.1 := by
    intro x
    by_cases hx : x.1∈E
    · rw [indicator_of_mem hx]
      exact (EntryLiteralModerate.response_bounds (N:=N) (C:=C) ν i g b A U ε x).2
    · rw [indicator_of_notMem hx]
      by_contra hp
      have hp' : 0< f x := lt_of_not_ge hp
      have hD := ((total_finite_geometry ν i g h 0 x).2.2.2.2.2.2.mp hp').2
      have hs := EntryRawGoodMoments.selected_nonneg i hb g.multiplier c (hstar := 0) le_rfl x
      unfold EntryRawCentral.deficit at hD
      have hh : (∑ j,X (x.1 j))<(C:ℝ) := by change _< _ at hD; linarith
      exact hx hh
  have hq := integral_mono hfi hI hpoint
  have hproj : MeasurePreserving Prod.fst P Q := measurePreserving_fst
  have hprojI : (∫ x : EntryIIDCentral.Row (Ω:=RowRival) N,
      E.indicator (fun _ => (1:ℝ)) x.1 ∂P)=∫ r,E.indicator (fun _ => (1:ℝ)) r ∂Q := by
    rw [← hproj.map_eq,integral_map measurable_fst.aemeasurable
      (measurable_const.indicator hE).aestronglyMeasurable]
  rw [(integrated_canonical_moments i G g h hcap).1,hprojI] at hq
  change canonicalGoodMarginal i G C N g b A U ε≤
    ∫ r,E.indicator (1 : (Fin N→RowRival)→ℝ) r ∂Q at hq
  rw [integral_indicator_one hE] at hq
  have hsub : E⊆{r | τ≤(∫ z,X z ∂ν)-(∑ j,X (r j))/(N:ℝ)} := by
    intro r hr
    have hs : (∑ j,X (r j))/(N:ℝ)<(C:ℝ)/(N:ℝ) :=
      (div_lt_div_iff_of_pos_right hn).mpr hr
    change (C:ℝ)/(N:ℝ)+τ≤∫ z,X z ∂ν at hmean
    change τ≤(∫ z,X z ∂ν)-(∑ j,X (r j))/(N:ℝ)
    linarith
  exact hq.trans ((measureReal_mono hsub).trans
    (FCAppendix.Probability.iid_empiricalMean_lower_tail_le ν
      (RawMixedSource.measurable_demand _ _).aemeasurable
      (ae_of_all _ (RawMixedSource.demand_bounds (xi_pos i) hb)) N h.rivals_pos hτ))

end FCAppendix.Affine.Uniform06.EntryGoodKernelBounds
