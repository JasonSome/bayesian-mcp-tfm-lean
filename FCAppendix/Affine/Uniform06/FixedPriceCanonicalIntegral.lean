import FCAppendix.Affine.Uniform06.FixedPriceCanonicalRows
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.FixedPriceCanonicalIntegral

open MeasureTheory ProbabilityTheory Set Filter Topology LowBody
open scoped BigOperators
open FCAppendix.Affine.ClippedResidual FCAppendix.Affine.WeightedSampling
open Uniform07 LiteralExperiment LiteralCoarsePath LiteralCoarseMeasurable
open LiteralKernelDecomposition LiteralPrefixStieltjes CanonicalPrefixLipschitz
open FixedPriceCanonicalRows

section Measurable
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
theorem measurable_guard_velocity (ξ : ℝ) (g : GuardData) (T : PureTemplate ι)
    (j : ι) (b : ℝ) :
    Measurable (fun B : ι → ℝ => GuardDerivative.velocity ξ g T B j b) := by
  have hs (k : Fin 5) : Measurable (fun B : ι → ℝ => GuardPrefix.rivalSlacks ξ g T B j k) := by
    have hd (z : ℝ) : Measurable (fun B : ι → ℝ =>
        ∑ k ∈ T.support.erase j,exposure ξ z (B k)) := by
      apply Finset.measurable_sum
      intro k _
      unfold exposure
      fun_prop
    have hw : Measurable (fun B : ι → ℝ =>
        ∑ k ∈ T.support.erase j,
          FiniteGuards.eligibility ξ g.multiplier g.requiredDemand (B k)) := by
      apply Finset.measurable_sum
      intro k _
      unfold FiniteGuards.eligibility FiniteGuards.clip01 exposure
      fun_prop
    have hp : Measurable (fun B : ι → ℝ =>
        ∑ k ∈ T.support.erase j,PrefixRoot.psi g.rejectionScale g.rejectionRoot (B k)) := by
      apply Finset.measurable_sum
      intro k _
      unfold PrefixRoot.psi
      fun_prop
    fin_cases k
    · exact ((hd _).sub_const _).sub_const _
    · exact measurable_const.sub (hd _)
    · exact hw.sub_const _
    · exact (hp.sub_const _).sub_const _
    · exact measurable_const
  have hseed : MeasurableSet {B : ι → ℝ | ∃ k ∈ T.support.erase j,B k≤ g.seedCutoff} := by
    have he : {B : ι → ℝ | ∃ k ∈ T.support.erase j,B k≤ g.seedCutoff}=
        ⋃ k : ι,{B | k ∈ T.support.erase j ∧ B k≤ g.seedCutoff} := by
      ext B
      simp only [mem_setOf_eq,mem_iUnion]
    rw [he]
    apply MeasurableSet.iUnion
    intro k
    by_cases hk : k ∈ T.support.erase j
    · simpa only [hk,true_and] using measurableSet_le (measurable_pi_apply k) measurable_const
    · simp only [hk,false_and,setOf_false]
      exact MeasurableSet.empty
  have hc : Measurable (fun B : ι → ℝ => GuardDerivative.fixedCoefficient ξ g T B j) := by
    unfold GuardDerivative.fixedCoefficient
    apply Measurable.ite hseed _ measurable_const
    apply Finset.measurable_prod
    intro k _
    unfold FiniteGuards.ramp FiniteGuards.clip01
    exact measurable_const.max
      (measurable_const.min (((hs k.succ).sub_const _).div_const _))
  have hr : Measurable (fun B : ι → ℝ => GuardDerivative.rampSlope (g.margin*g.population)
      (GuardPrefix.rivalSlacks ξ g T B j 0+exposure ξ (g.multiplier-g.radius) b)) := by
    unfold GuardDerivative.rampSlope
    exact Measurable.ite
      ((measurableSet_lt measurable_const ((hs 0).add_const _)).inter
        (measurableSet_lt ((hs 0).add_const _) measurable_const)) measurable_const measurable_const
  unfold GuardDerivative.velocity
  split_ifs
  · exact (((hc.mul hr).mul_const _).div_const _)
  · exact measurable_const

theorem measurable_weightedVelocity {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (g : GuardData) (T : PureTemplate ι) (j : ι) (q : ℕ) (b : ℝ) :
    Measurable (fun B : ι → ℝ => weightedVelocity ξ g T B j q b) := by
  have hu : Measurable (fun B : ι→ℝ=>Function.update B j b) := measurable_update_left
  have hmass (p : Path ι (imbalance T)) :
      Measurable (fun B : ι → ℝ => (pathLaw (weights ξ g T B) (imbalance T) ∅).mass p) :=
    measurable_path_mass (fun B => weights ξ g T B)
      (measurable_weights ξ g T id (fun k => measurable_pi_apply k)) _ _ p
  have hcomp (p : Path ι (imbalance T)) : Measurable (fun B : ι → ℝ =>
      complementMarginal ξ T (Function.update B j b) (finalSet (imbalance T) ∅ p) j) :=
    measurable_complement hξ hξ1 T (fun B => Function.update B j b)
      (fun k=>(measurable_pi_apply k).comp hu) _ j
  have hslope (p : Path ι (imbalance T)) : Measurable (fun B : ι → ℝ =>
      MaskedRootDerivative.slope ξ T B (finalSet (imbalance T) ∅ p) j b) := by
    convert! (MaskedRootDerivative.measurable_slope hξ hξ1 T
      (finalSet (imbalance T) ∅ p) j).comp
      (measurable_id.prodMk (measurable_const (a:=b))) using 1
  have hp : Measurable (fun B : ι → ℝ => pathMoment ξ g T B j q b) := by
    unfold pathMoment FCAppendix.FiniteLaw.expect
    exact Finset.measurable_sum _ (fun p _ => (hmass p).mul ((hcomp p).pow_const q))
  have hv : Measurable (fun B : ι → ℝ => pathVelocity ξ g T B j q b) := by
    unfold pathVelocity FCAppendix.FiniteLaw.expect
    exact Finset.measurable_sum _ (fun p _ => (hmass p).mul
      ((((hcomp p).pow_const (q-1)).const_mul (q:ℝ)).mul (hslope p)))
  have hα : Measurable (fun B : ι → ℝ => guardAlpha ξ g T (Function.update B j b)) :=
    measurable_guard ξ g T (fun B => Function.update B j b)
      (fun k=>(measurable_pi_apply k).comp hu)
  unfold weightedVelocity
  split_ifs
  · exact hv
  · exact (hα.mul hv).add ((measurable_guard_velocity ξ g T j b).mul hp)
  · exact measurable_const

end Measurable

variable {N : ℕ}

theorem measurable_rowVelocity {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (C : ℕ) (g : GuardData) (margin : (Fin N → Fin 4) → ℝ) (q : ℕ) (b : ℝ) :
    Measurable (rowVelocity ξ C g margin q b) := by
  unfold rowVelocity
  apply measurable_pattern_choice (fun kind r=>weightedVelocity ξ {g with countMargin:=margin kind}
    (patternTemplate C kind) (rowBids 0 r) 0 q b)
  intro kind
  exact (measurable_weightedVelocity hξ hξ1 {g with countMargin := margin kind}
    (patternTemplate C kind) 0 q b).comp
      (measurable_pi_lambda _ fun k => measurable_raw_rowBids N 0 k)

lemma lipschitz_of_ordered_increments (f : ℝ → ℝ) (S : Set ℝ) {K : ℝ} (hK : 0≤ K)
    (hf : ∀ x ∈ S,∀ y ∈ S,x≤ y → 0≤ f y-f x ∧ f y-f x≤ K*(y-x)) :
    LipschitzOnWith (Real.nnabs K) f S := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [Real.coe_nnabs,abs_of_nonneg hK,Real.dist_eq,Real.dist_eq]
  rcases le_total x y with hxy | hyx
  · have hh := hf x hx y hy hxy
    rw [abs_of_nonpos (by linarith : f x-f y≤0),abs_of_nonpos (sub_nonpos.mpr hxy)]
    simpa only [neg_sub] using hh.2
  · have hh := hf y hy x hx hyx
    rw [abs_of_nonneg hh.1,abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact hh.2

theorem original_rows_lipschitz {ξ H a : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (C : ℕ) (g : GuardData) (hg : PrefixConditions ξ g H)
    (hH : 0≤ H) (ha : 0< a) (margin : (Fin N → Fin 4) → ℝ)
    (r : Fin N → RowRival) (hr : ∀ j,(r j).1=0 → 0≤(r j).2) :
    LipschitzOnWith (Real.nnabs (canonicalConstant ξ g H/a))
      (fun b => originalRowMarginal ξ C g margin b r) (Icc a H) ∧
    LipschitzOnWith (Real.nnabs (canonicalConstant ξ g H/a))
      (fun b => originalRowDuplicate ξ C g margin b r) (Icc a H) := by
  have hK := (canonicalConstant_pos hξ hH hg).le
  have hmS := row_canonical_first_monotone hξ hξ1 C g hg margin r hr
  have hmR := row_canonical_duplicate_monotone hξ hξ1 C g hg margin r hr
  have hpair (x : ℝ) (hx : x ∈ Icc a H) (y : ℝ) (hy : y ∈ Icc a H) (hxy : x≤ y) :
      (0≤ originalRowMarginal ξ C g margin y r-originalRowMarginal ξ C g margin x r ∧
        originalRowMarginal ξ C g margin y r-originalRowMarginal ξ C g margin x r≤
          canonicalConstant ξ g H/a*(y-x)) ∧
      (0≤ originalRowDuplicate ξ C g margin y r-originalRowDuplicate ξ C g margin x r ∧
        originalRowDuplicate ξ C g margin y r-originalRowDuplicate ξ C g margin x r≤
          canonicalConstant ξ g H/a*(y-x)) := by
    have hx0 := ha.trans_le hx.1
    have hS := hmS ⟨hx0.le,hx.2⟩ ⟨(ha.trans_le hy.1).le,hy.2⟩ hxy
    have hR := hmR ⟨hx0.le,hx.2⟩ ⟨(ha.trans_le hy.1).le,hy.2⟩ hxy
    have hi := row_canonical_increments hξ hξ1 C g hg margin r hr hx0 hxy hy.2
    have hbound : canonicalConstant ξ g H*(y-x)/x≤ canonicalConstant ξ g H/a*(y-x) := by
      have hh := div_le_div_of_nonneg_left (mul_nonneg hK (sub_nonneg.mpr hxy)) ha hx.1
      convert! hh using 1
      ring
    have hSx := row_canonical_first_eq ξ C g margin x r
    have hSy := row_canonical_first_eq ξ C g margin y r
    change (0≤ rowCanonicalFair ξ C g margin y r-rowCanonicalFair ξ C g margin x r ∧
      rowCanonicalFair ξ C g margin y r-rowCanonicalFair ξ C g margin x r≤
        canonicalConstant ξ g H/a*(y-x)) ∧
      (0≤ rowCanonicalDuplicate ξ C g margin y r-rowCanonicalDuplicate ξ C g margin x r ∧
      rowCanonicalDuplicate ξ C g margin y r-rowCanonicalDuplicate ξ C g margin x r≤
        canonicalConstant ξ g H/a*(y-x))
    constructor <;> constructor <;> linarith [hi.1.trans hbound,hi.2.trans hbound]
  exact ⟨lipschitz_of_ordered_increments _ _ (div_nonneg hK ha.le)
      (fun x hx y hy hxy => (hpair x hx y hy hxy).1),
    lipschitz_of_ordered_increments _ _ (div_nonneg hK ha.le)
      (fun x hx y hy hxy => (hpair x hx y hy hxy).2)⟩

theorem original_expected_kernel_derivatives (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G] (hnull : ∀ a : ℝ,(G.map Prod.snd) {a}=0)
    (hnon : ∀ᵐ p ∂G,0≤ p.2) {U H b : ℝ} (hcap : ∀ᵐ p ∂G,p.2≤ U)
    (C : ℕ) (g : GuardData) (margin : (Fin N → Fin 4) → ℝ)
    (hg : PrefixConditions (xi i) g H) (ha : 0< g.radius)
    (hεM : 1< g.margin*g.population) (hb : 0< b) (hbH : b< H)
    (hbL : b< g.multiplier) (hbz : b< g.rejectionRoot) (hbU : b< U)
    (hclip : (1-xi i)*U≤ g.multiplier-g.radius) :
    HasDerivAt (fun a => ∫ r,originalRowMarginal (xi i) C g margin a r
      ∂Measure.pi (fun _ : Fin N => RawMixedSource.source i G))
      (∫ r,rowVelocity (xi i) C g margin 1 b r
        ∂Measure.pi (fun _ : Fin N => RawMixedSource.source i G)) b ∧
    HasDerivAt (fun a => ∫ r,originalRowDuplicate (xi i) C g margin a r
      ∂Measure.pi (fun _ : Fin N => RawMixedSource.source i G))
      (∫ r,rowVelocity (xi i) C g margin 2 b r
        ∂Measure.pi (fun _ : Fin N => RawMixedSource.source i G)) b := by
  let μ := Measure.pi (fun _ : Fin N => RawMixedSource.source i G)
  have hξ1 : xi i<1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  have hm (a : ℝ) := measurable_rowCanonical (xi i) C g margin a (xi_pos i) hξ1
  have hi := integrable_rowCanonical (xi_pos i) hξ1 C g margin b μ
  have hvel1 := measurable_rowVelocity (xi_pos i) hξ1 C g margin 1 b
  have hvel2 := measurable_rowVelocity (xi_pos i) hξ1 C g margin 2 b
  have hder := original_every_fixed_bid_row_derivative i G hnull hnon hcap g hg ha hεM
    hb hbL hbz hbU hclip (N:=N)
  have hd1 : ∀ᵐ r ∂μ,HasDerivAt (fun a => originalRowMarginal (xi i) C g margin a r)
      (rowVelocity (xi i) C g margin 1 b r) b := by
    filter_upwards [hder] with r hr
    apply (hr C margin 1 (by norm_num)).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hbL] with a haL
    exact (original_row_moment_identities (xi_pos i) hξ1 C g margin
      (by linarith [hg.lower_pos,hg.radius_nonneg]) hg.margin_pos hg.population_pos
        hg.requiredDemand_pos haL.le r).1
  have hd2 : ∀ᵐ r ∂μ,HasDerivAt (fun a => originalRowDuplicate (xi i) C g margin a r)
      (rowVelocity (xi i) C g margin 2 b r) b := by
    filter_upwards [hder] with r hr
    apply (hr C margin 2 (by norm_num)).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hbL] with a haL
    exact (original_row_moment_identities (xi_pos i) hξ1 C g margin
      (by linarith [hg.lower_pos,hg.radius_nonneg]) hg.margin_pos hg.population_pos
        hg.requiredDemand_pos haL.le r).2
  have hrnon : ∀ᵐ r ∂μ,∀ j,(r j).1=0 → 0≤(r j).2 :=
    ae_all_iff.mpr fun j => (measurePreserving_eval
      (fun _ : Fin N => RawMixedSource.source i G) j).quasiMeasurePreserving.ae
        (FixedPriceRawDerivative.raw_lower_nonnegative i G hnon)
  have hlip := hrnon.mono fun r hr => original_rows_lipschitz (xi_pos i) hξ1 C g hg
    (hb.trans hbH).le (half_pos hb) margin r hr
  have hs : Icc (b/2) H ∈ 𝓝 b := Icc_mem_nhds (by linarith) hbH
  have hfirst := hasDerivAt_integral_of_dominated_loc_of_lip hs
    (Eventually.of_forall fun a => (hm a).2.1.aestronglyMeasurable) hi.2.1
    hvel1.aestronglyMeasurable (hlip.mono fun _ h => h.1)
    (integrable_const (canonicalConstant (xi i) g H/(b/2))) hd1
  have hsecond := hasDerivAt_integral_of_dominated_loc_of_lip hs
    (Eventually.of_forall fun a => (hm a).2.2.aestronglyMeasurable) hi.2.2
    hvel2.aestronglyMeasurable (hlip.mono fun _ h => h.2)
    (integrable_const (canonicalConstant (xi i) g H/(b/2))) hd2
  exact ⟨hfirst.2,hsecond.2⟩

def Cprime (i : Row) (m : ℕ) (G : Measure (ℝ × ℝ)) (g : GuardData)
    (margin : (Fin (m-1) → Fin 4) → ℝ) (b : ℝ) : ℝ :=
  ∫ r,rowVelocity (xi i) (capacity m) g margin 1 b r
    ∂Measure.pi (fun _ : Fin (m-1) => RawMixedSource.source i G)

def Rprime (i : Row) (m : ℕ) (G : Measure (ℝ × ℝ)) (g : GuardData)
    (margin : (Fin (m-1) → Fin 4) → ℝ) (b : ℝ) : ℝ :=
  ∫ r,rowVelocity (xi i) (capacity m) g margin 2 b r
    ∂Measure.pi (fun _ : Fin (m-1) => RawMixedSource.source i G)

theorem source_canonical_derivatives (i : Row) (m : ℕ) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G] (hnull : ∀ a : ℝ,(G.map Prod.snd) {a}=0)
    (hnon : ∀ᵐ p ∂G,0≤ p.2) {U H b : ℝ} (hcap : ∀ᵐ p ∂G,p.2≤ U)
    (g : GuardData) (margin : (Fin (m-1) → Fin 4) → ℝ)
    (hg : PrefixConditions (xi i) g H) (ha : 0< g.radius)
    (hεM : 1< g.margin*g.population) (hb : 0< b) (hbH : b< H)
    (hbL : b< g.multiplier) (hbz : b< g.rejectionRoot) (hbU : b< U)
    (hclip : (1-xi i)*U≤ g.multiplier-g.radius) :
    HasDerivAt (sourceCanonicalMarginal i m G g margin) (Cprime i m G g margin b) b ∧
      HasDerivAt (sourceCanonicalDuplicate i m G g margin) (Rprime i m G g margin b) b := by
  convert! original_expected_kernel_derivatives i G hnull hnon hcap (capacity m) g margin
    hg ha hεM hb hbH hbL hbz hbU hclip (N:=m-1) using 1

end FCAppendix.Affine.Uniform06.FixedPriceCanonicalIntegral
