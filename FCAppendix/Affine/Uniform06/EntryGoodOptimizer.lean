import FCAppendix.Affine.Uniform06.EntrySubentryLocalization

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryGoodOptimizer

open MeasureTheory Set Filter Topology LowBody
open FCAppendix.Affine.Uniform07
open EntryConstructedSource EntryConstructedSource.EarlyArray EntryFiniteConstructor
open EntryProducedMoments EntryGoodKernelBounds EntrySubentryLocalization
open EntryLiteralCanonicalTransfer EntrySourceLower EntryOptimizer EntryMomentAlgebra

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {i : Row} (s : EarlyArray μ i)

def one (v : ℕ→ℝ) (m : ℕ) (b : ℝ) : ℝ := (v m-b)*first s m b
def two (v : ℕ→ℝ) (m : ℕ) (b : ℝ) : ℝ :=
  2*(v m-b)*first s m b-((v m-b)+eta i*b)*second s m b

def benchmark (v : ℕ→ℝ) (m : ℕ) : ℝ :=
  min (v m) (entry i)-1/(((s.population m-1:ℕ):ℝ)+1)

def optimal (v : ℕ→ℝ) (m : ℕ) (b : ℝ) : Prop :=
  b∈Icc (lowerPrice i) (v m) ∧ ∀ a∈Icc (lowerPrice i) (v m),one s v m a≤ one s v m b

def chosen (v : ℕ→ℝ) (m : ℕ) : ℝ := by
  classical
  exact if h : ∃ b,optimal s v m b then Classical.choose h else entry i

omit [IsProbabilityMeasure μ] in
theorem first_nonneg (m : ℕ) (b : ℝ) : 0≤ first s m b := by
  unfold first EntryLiteralCanonicalTransfer.canonicalGoodMarginal
  exact integral_nonneg fun r => (LiteralKernelDecomposition.expect_fair_bounds _ 0).1

omit [IsProbabilityMeasure μ] in
theorem benchmark_surplus (v : ℕ→ℝ) (m : ℕ) :
    1/(((s.population m-1:ℕ):ℝ)+1)≤ v m-benchmark s v m ∧ benchmark s v m< v m := by
  have hmin := min_le_left (v m) (entry i)
  have hd : 0<1/(((s.population m-1:ℕ):ℝ)+1) := by positivity
  unfold benchmark
  constructor <;> linarith

omit [IsProbabilityMeasure μ] in
theorem benchmark_tendsto (v : ℕ→ℝ) (hv : Tendsto v atTop (𝓝 (entry i))) :
    Tendsto (benchmark s v) atTop (𝓝 (entry i)) := by
  have hN : Tendsto (fun m => s.population m-1) atTop atTop := by
    simpa only [Function.comp_def] using PhysicalRates.rivals_tendsto.comp s.population_tendsto
  have hden : Tendsto (fun m => ((s.population m-1:ℕ):ℝ)+1) atTop atTop := by
    simpa only [Function.comp_def] using tendsto_atTop_add_const_right atTop 1
      (tendsto_natCast_atTop_atTop.comp hN)
  have hh := (hv.min (tendsto_const_nhds (x:=entry i))).sub (tendsto_inv_atTop_zero.comp hden)
  change Tendsto (fun m => benchmark s v m) atTop (𝓝 (entry i))
  simpa only [benchmark,one_div,min_self,sub_zero,Function.comp_def] using hh

lemma subexponential_divide (N : ℕ→ℕ) (hN : Tendsto N atTop atTop)
    (F H : ℕ→ℝ) (hF : SubexponentialLower N F) {c : ℝ} (hc : 0< c)
    (hH : ∀ᶠ m in atTop,c*F m/(N m:ℝ)≤ H m) : SubexponentialLower N H := by
  intro e he
  have hdecay : Tendsto (fun m => (N m:ℝ)*Real.exp (-(e/2)*(N m:ℝ))) atTop (𝓝 (0:ℝ)) := by
    have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) (e/2)
      (by positivity)).comp (tendsto_natCast_atTop_atTop.comp hN)
    simpa only [Real.rpow_one,Function.comp_def] using hh
  filter_upwards [hF (e/2) (by positivity),hH,hdecay.eventually_lt_const hc,
    hN.eventually_ge_atTop 1] with m hm hHm hcm hNm
  have hn : (0:ℝ)< N m := by exact_mod_cast (show 0< N m by omega)
  have hpoly : Real.exp (-(e/2)*(N m:ℝ))≤ c/(N m:ℝ) :=
    (le_div_iff₀ hn).mpr (by nlinarith)
  have hh := mul_le_mul hpoly hm (Real.exp_pos _).le (div_nonneg hc.le hn.le)
  have hex : Real.exp (-(e/2)*(N m:ℝ))*Real.exp (-(e/2)*(N m:ℝ))=
      Real.exp (-e*(N m:ℝ)) := by rw [← Real.exp_add]; congr 1; ring
  rw [hex] at hh
  exact hh.trans (by convert! hHm using 1; ring)

theorem benchmark_subexponential (v : ℕ→ℝ) (hv : Tendsto v atTop (𝓝 (entry i))) :
    SubexponentialLower (fun m => s.population m-1) (fun m => one s v m (benchmark s v m)) := by
  have hN : Tendsto (fun m => s.population m-1) atTop atTop := by
    simpa only [Function.comp_def] using PhysicalRates.rivals_tendsto.comp s.population_tendsto
  apply subexponential_divide _ hN _ _ (original_first_subexponential s _ (benchmark_tendsto s v hv))
    (c := 1/2) (by norm_num)
  filter_upwards [hN.eventually_ge_atTop 1] with m hm
  have hn : (1:ℝ)≤((s.population m-1:ℕ):ℝ) := by exact_mod_cast hm
  have hsur := (benchmark_surplus s v m).1
  have hq := first_nonneg s m (benchmark s v m)
  have hden : 1/(2*((s.population m-1:ℕ):ℝ))≤1/(((s.population m-1:ℕ):ℝ)+1) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hh := mul_le_mul_of_nonneg_right (hden.trans hsur) hq
  unfold one
  convert! hh using 1
  ring

theorem eventually_optimizer (v : ℕ→ℝ) (hv : Tendsto v atTop (𝓝 (entry i))) :
    ∀ᶠ m in atTop,optimal s v m (chosen s v m) ∧
      lowerPrice i< chosen s v m ∧ chosen s v m< v m ∧
      0< one s v m (chosen s v m) ∧
      ∀ a∈Icc (0:ℝ) (v m),one s v m a≤ one s v m (chosen s v m) := by
  have ht := cutoff_pos i
  have hlo : 0< lowerPrice i := by
    have hx : (7/10:ℝ)≤ x i := by cases i <;> norm_num [x,xQ]
    unfold lowerPrice entry
    nlinarith
  have hlowerEntry : lowerPrice i< entry i := by unfold lowerPrice; linarith
  have hbench := benchmark_tendsto s v hv
  have hbEntry : entry i∈band i := by
    unfold band SourcePrefixConstructor.radius
    constructor <;> linarith
  have hhi : ∀ᶠ m in atTop,v m≤(s.guards m).multiplier+(s.guards m).radius := by
    have hdiff : Tendsto (fun m => v m-(s.guards m).multiplier) atTop (𝓝 (0:ℝ)) := by
      simpa only [sub_self] using hv.sub s.multiplier_tendsto
    have ha : 0< SourcePrefixConstructor.radius i := by unfold SourcePrefixConstructor.radius; positivity
    filter_upwards [hdiff.eventually_lt_const ha] with m hm
    rw [(s.literal m).radius_eq]
    linarith
  filter_upwards [s.eventually_inputs,hbench.eventually_const_lt hlowerEntry,
    benchmark_subexponential s v hv 1 (by norm_num),hhi] with m hm hblo hpositive hvhi
  let g := normalizeCount (s.guards m)
  have h := hm.2 (entry i) hbEntry
  have hbv := (benchmark_surplus s v m).2
  have hcont : ContinuousOn (one s v m) (Icc (lowerPrice i) (v m)) := by
    have hc := (original_good_lipschitz i (s.jointLaw m) (s.joint_nonnegative m) g h (s.cap m) hlo).continuousOn
    have hc' : ContinuousOn (first s m) (Icc (lowerPrice i) (v m)) := by
      change ContinuousOn (fun b => first s m b) (Icc (lowerPrice i) (v m))
      simpa only [first,g,canonicalGoodMarginal_normalize] using hc.mono
        (show Icc (lowerPrice i) (v m)⊆Icc (lowerPrice i) (g.multiplier+g.radius) from
          fun _ ha => ⟨ha.1,ha.2.trans hvhi⟩)
    exact (continuous_const.sub continuous_id).continuousOn.mul hc'
  obtain ⟨a,ha,hmax⟩ := isCompact_Icc.exists_isMaxOn
    ⟨benchmark s v m,⟨hblo.le,hbv.le⟩⟩ hcont
  have hex : ∃ b,optimal s v m b := ⟨a,ha,hmax⟩
  have hspec : optimal s v m (chosen s v m) := by
    rw [chosen,dif_pos hex]
    exact Classical.choose_spec hex
  have hpos : 0< one s v m (chosen s v m) :=
    (Real.exp_pos _).trans_le (hpositive.trans (hspec.2 _ ⟨hblo.le,hbv.le⟩))
  have hleft : lowerPrice i< chosen s v m := by
    apply lt_of_le_of_ne hspec.1.1
    intro heq
    have hz := original_below_lower_zero i (s.jointLaw m) g h h.lower_price
    have hz' : first s m (lowerPrice i)=0 := by
      simpa only [first,g,canonicalGoodMarginal_normalize] using hz
    rw [← heq,one,hz',mul_zero] at hpos
    exact lt_irrefl _ hpos
  have hright : chosen s v m< v m := by
    apply lt_of_le_of_ne hspec.1.2
    intro heq
    rw [heq,one,sub_self,zero_mul] at hpos
    exact lt_irrefl _ hpos
  refine ⟨hspec,hleft,hright,hpos,?_⟩
  intro a ha
  by_cases hal : lowerPrice i≤ a
  · exact hspec.2 a ⟨hal,ha.2⟩
  · have hz := original_below_lower_zero i (s.jointLaw m) g h
      ((le_of_not_ge hal).trans h.lower_price)
    have hz' : first s m a=0 := by
      simpa only [first,g,canonicalGoodMarginal_normalize] using hz
    simp only [one,hz',mul_zero]
    exact hpos.le

theorem chosen_subexponential (v : ℕ→ℝ) (hv : Tendsto v atTop (𝓝 (entry i))) :
    SubexponentialLower (fun m => s.population m-1) (fun m => one s v m (chosen s v m)) := by
  intro e he
  have hlowerEntry : lowerPrice i< entry i := by unfold lowerPrice; have := cutoff_pos i; linarith
  filter_upwards [eventually_optimizer s v hv,benchmark_subexponential s v hv e he,
    (benchmark_tendsto s v hv).eventually_const_lt hlowerEntry] with m hm hb hblo
  exact hb.trans (hm.1.2 _ ⟨hblo.le,(benchmark_surplus s v m).2.le⟩)

theorem chosen_tendsto (v : ℕ→ℝ) (hv : Tendsto v atTop (𝓝 (entry i))) :
    Tendsto (chosen s v) atTop (𝓝 (entry i)) := by
  apply Metric.tendsto_atTop.mpr
  intro e he
  let z := max ((lowerPrice i+entry i)/2) (entry i-e)
  have ht := cutoff_pos i
  have hlowerEntry : lowerPrice i< entry i := by unfold lowerPrice; linarith
  have hz : z∈Ioo (lowerPrice i) (entry i) := by
    refine ⟨lt_of_lt_of_le (by linarith) (le_max_left _ _),?_⟩
    exact max_lt (by linarith) (by linarith)
  obtain ⟨κ,hκ,hsmall⟩ := all_bids_below_fixed_price s hz
  have hn : Tendsto (fun m => s.population m-1) atTop atTop := by
    simpa only [Function.comp_def] using PhysicalRates.rivals_tendsto.comp s.population_tendsto
  have hevent : ∀ᶠ m in atTop,dist (chosen s v m) (entry i)< e := by
    filter_upwards [eventually_optimizer s v hv,chosen_subexponential s v hv (κ/2) (by positivity),
      hsmall,hv.eventually_lt_const (show entry i< entry i+e by linarith),
      hv.eventually_lt_const (EarlyMean.entry_lt_cutoff i),hn.eventually_ge_atTop 1] with m hm hl hb hvu hvt hN
    have hn0 : (0:ℝ)<((s.population m-1:ℕ):ℝ) := by exact_mod_cast (show 0< s.population m-1 by omega)
    have hchosen0 : 0≤ chosen s v m := by
      have hx : (7/10:ℝ)≤ x i := by cases i <;> norm_num [x,xQ]
      have hh := hm.2.1
      unfold lowerPrice entry at hh
      nlinarith
    have hzlt : z< chosen s v m := by
      by_contra hnot
      have hq := hb (chosen s v m) ⟨hchosen0,le_of_not_gt hnot⟩
      have hq0 := first_nonneg s m (chosen s v m)
      have hu : one s v m (chosen s v m)≤ cutoff i*Real.exp (-κ*((s.population m-1:ℕ):ℝ)) := by
        unfold one
        apply (mul_le_mul_of_nonneg_right (show v m-chosen s v m≤ cutoff i by linarith) hq0).trans
        exact mul_le_mul_of_nonneg_left hq ht.le
      have he1 : cutoff i*Real.exp (-κ*((s.population m-1:ℕ):ℝ))≤ Real.exp (-κ*((s.population m-1:ℕ):ℝ)) :=
        mul_le_of_le_one_left (Real.exp_pos _).le (cutoff_lt_one i).le
      have he2 : Real.exp (-κ*((s.population m-1:ℕ):ℝ))< Real.exp (-(κ/2)*((s.population m-1:ℕ):ℝ)) :=
        Real.exp_lt_exp.mpr (by nlinarith)
      linarith
    have hzlower : entry i-e≤ z := le_max_right _ _
    rw [Real.dist_eq,abs_lt]
    constructor <;> linarith [hm.2.2.1]
  exact eventually_atTop.mp hevent

theorem actual_optimizer_advantage (v : ℕ→ℝ) (hv : Tendsto v atTop (𝓝 (entry i)))
    (hnull : ∀ m,∀ z : ℝ,((s.jointLaw m).map Prod.snd) {z}=0) :
    ∀ᶠ m in atTop,0< one s v m (chosen s v m) ∧
      (∀ a∈Icc (0:ℝ) (v m),one s v m a≤ one s v m (chosen s v m)) ∧
      ∃ dq : ℝ,HasDerivAt (first s m) dq (chosen s v m) ∧
        first s m (chosen s v m)=(v m-chosen s v m)*dq ∧
        (1+EntrySourceGap.margin i)*one s v m (chosen s v m)≤ two s v m (chosen s v m) := by
  have hgap := original_entry_gap s (chosen s v) (chosen_tendsto s v hv) hnull
  filter_upwards [eventually_optimizer s v hv,hgap] with m hm hg
  obtain ⟨dq,hd,hq,hr,hgap⟩ := hg
  have hmax : IsLocalMax (one s v m) (chosen s v m) := by
    filter_upwards [Ioo_mem_nhds hm.2.1 hm.2.2.1] with a ha
    exact hm.1.2 a ⟨ha.1.le,ha.2.le⟩
  have hFOC := singleton_FOC_of_localMax (first s m) (v m) (chosen s v m) dq hd hmax
  refine ⟨hm.2.2.2.1,hm.2.2.2.2,dq,hd,hFOC,?_⟩
  exact optimizer_twoRoute_margin hm.2.2.1.le hq hFOC hgap

end FCAppendix.Affine.Uniform06.EntryGoodOptimizer
