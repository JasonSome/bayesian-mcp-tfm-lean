import FCAppendix.Affine.Uniform06.FixedPriceEntryGeometry
import FCAppendix.Affine.Uniform06.EntryLiteralCanonicalTransfer

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.FixedPriceEntryIntegral

open MeasureTheory ProbabilityTheory Set Filter Topology LowBody
open scoped BigOperators
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.WeightedSampling
open LiteralExperiment LiteralKernelIdentity EntryLiteralResponseGeometry
open EntryLiteralResponseMoments EntryLiteralCanonicalTransfer
open FixedPriceRawDerivative FixedPriceEntryGeometry EntryRawCentral EntrySamplingLaw
open EntryProfileMean EntryReciprocalLimit
attribute [local instance] Classical.propDecidable
attribute [local irreducible] complementMarginal MaskedRootDerivative.slope

variable {N C : ℕ}

theorem profile_constant_on_prefix (i : Row) (g : GuardData)
    (hr : g.requiredDemand=PrefixRoot.requiredDemand i)
    (hg : LiteralPrefixStieltjes.PrefixConditions (xi i) g (g.multiplier+g.radius))
    {a b : ℝ} (ha : a ≤ g.multiplier+g.radius) (hb : b ≤ g.multiplier+g.radius)
    (r : Fin N → RowRival) : profile i g a r=profile i g b r := by
  have hzero {z : ℝ} (hz : z ≤ g.multiplier+g.radius) :
      focalWeight i z g.multiplier=0 := by
    unfold focalWeight
    rw [← hr]
    exact hg.zero_eligibility (xi_pos i) z hz
  apply Subtype.ext
  funext j
  refine Fin.cases ?_ (fun k => rfl) j
  simp only [profile,profileWeights,Fin.cons_zero,hzero ha,hzero hb]

theorem sampleSet_constant_on_prefix (i : Row) (g : GuardData)
    (hr : g.requiredDemand=PrefixRoot.requiredDemand i)
    (hg : LiteralPrefixStieltjes.PrefixConditions (xi i) g (g.multiplier+g.radius))
    {a b : ℝ} (ha : a ≤ g.multiplier+g.radius) (hb : b ≤ g.multiplier+g.radius)
    (x : EntryIIDCentral.Row (Ω := RowRival) N) : sampleSet i g a x=sampleSet i g b x := by
  unfold sampleSet removed
  rw [profile_constant_on_prefix i g hr hg ha hb x.1]

theorem usable_constant_on_prefix (μ : Measure RowRival) (i : Row) (g : GuardData)
    (hr : g.requiredDemand=PrefixRoot.requiredDemand i)
    (hg : LiteralPrefixStieltjes.PrefixConditions (xi i) g (g.multiplier+g.radius))
    {a b A U ε : ℝ} (ha : a ≤ g.multiplier+g.radius) (hb : b ≤ g.multiplier+g.radius) :
    usable (N := N) μ i g a A U ε=usable μ i g b A U ε := by
  ext x
  simp only [usable,Set.mem_inter_iff,Set.mem_preimage,rawConditions,Set.mem_setOf_eq,sampleMass,
    profile_constant_on_prefix i g hr hg ha hb x.1]

def frozen (μ : Measure RowRival) (i : Row) (C : ℕ) (g : GuardData)
    (b A U ε a : ℝ) (x : EntryIIDCentral.Row (Ω := RowRival) N) : ℝ :=
  if x ∈ usable μ i g b A U ε then
    complementMarginal (xi i) (patternTemplate C (fun j => (x.1 j).1))
      (rowBids a x.1) (sampleSet i g b x) 0 else 0

def velocity (μ : Measure RowRival) (i : Row) (C : ℕ) (g : GuardData)
    (b A U ε : ℝ) (x : EntryIIDCentral.Row (Ω := RowRival) N) : ℝ :=
  if x ∈ usable μ i g b A U ε then
    MaskedRootDerivative.slope (xi i) (patternTemplate C (fun j => (x.1 j).1))
      (rowBids 0 x.1) (sampleSet i g b x) 0 b else 0

lemma frozen_at_base (μ : Measure RowRival) (i : Row) (C : ℕ) (g : GuardData)
    (b A U ε : ℝ) (x : EntryIIDCentral.Row (Ω := RowRival) N) :
    frozen μ i C g b A U ε b x=response μ i C g b A U ε x := rfl

theorem response_eq_frozen (μ : Measure RowRival) (i : Row) (g : GuardData)
    (hr : g.requiredDemand=PrefixRoot.requiredDemand i)
    (hg : LiteralPrefixStieltjes.PrefixConditions (xi i) g (g.multiplier+g.radius))
    {a b A U ε : ℝ} (ha : a ≤ g.multiplier+g.radius) (hb : b ≤ g.multiplier+g.radius)
    (x : EntryIIDCentral.Row (Ω := RowRival) N) :
    response μ i C g a A U ε x=frozen μ i C g b A U ε a x := by
  unfold response complement frozen
  rw [usable_constant_on_prefix μ i g hr hg ha hb,
    sampleSet_constant_on_prefix i g hr hg ha hb x]

lemma measurable_frozen (μ : Measure RowRival) (i : Row) (C : ℕ) (g : GuardData)
    (b A U ε a : ℝ) : Measurable (frozen (N := N) μ i C g b A U ε a) := by
  have hξ1 : xi i < 1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  have ht : Measurable (fun x : EntryIIDCentral.Row (Ω := RowRival) N =>
      (fun j => (x.1 j).1,sampleSet i g b x)) :=
    (measurable_pi_lambda _ fun j => ((measurable_pi_apply j).comp measurable_fst).fst).prodMk
      (measurable_sampleSet i g b)
  have hm : Measurable (fun y : ((Fin N → Fin 4) × Finset (Fin (N+1))) × (Fin (N+1) → ℝ) =>
      complementMarginal (xi i) (patternTemplate C y.1.1) y.2 y.1.2 0) :=
    measurable_from_prod_countable_right fun p =>
      LiteralKernelMeasurable.measurable_complementMarginal (xi_pos i) hξ1
        (patternTemplate C p.1) p.2 0
  exact Measurable.ite (measurable_usable μ i g b A U ε)
    (hm.comp (ht.prodMk ((EntryDeletedReciprocal.measurable_listBids N a).comp measurable_fst)))
    measurable_const

lemma measurable_velocity (μ : Measure RowRival) (i : Row) (C : ℕ) (g : GuardData)
    (b A U ε : ℝ) : Measurable (velocity (N := N) μ i C g b A U ε) := by
  have hξ1 : xi i < 1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  have ht : Measurable (fun x : EntryIIDCentral.Row (Ω := RowRival) N =>
      (fun j => (x.1 j).1,sampleSet i g b x)) :=
    (measurable_pi_lambda _ fun j => ((measurable_pi_apply j).comp measurable_fst).fst).prodMk
      (measurable_sampleSet i g b)
  have hm : Measurable (fun y : ((Fin N → Fin 4) × Finset (Fin (N+1))) × (Fin (N+1) → ℝ) =>
      MaskedRootDerivative.slope (xi i) (patternTemplate C y.1.1) y.2 y.1.2 0 b) :=
    measurable_from_prod_countable_right fun p =>
      (MaskedRootDerivative.measurable_slope (xi_pos i) hξ1 (patternTemplate C p.1) p.2 0).comp
        (measurable_id.prodMk measurable_const)
  exact Measurable.ite (measurable_usable μ i g b A U ε)
    (hm.comp (ht.prodMk ((EntryDeletedReciprocal.measurable_listBids N 0).comp measurable_fst)))
    measurable_const

lemma frozen_bounds (μ : Measure RowRival) (i : Row) (C : ℕ) (g : GuardData)
    (b A U ε a : ℝ) (x : EntryIIDCentral.Row (Ω := RowRival) N) :
    frozen μ i C g b A U ε a x ∈ Icc (0:ℝ) 1 := by
  unfold frozen
  split_ifs
  · exact LiteralPrefixStieltjes.complement_bounds (xi_pos i)
      (by cases i <;> norm_num [xi,xiQ,etaQ]) _ _ _ _
  · norm_num

theorem frozen_lipschitz (μ : Measure RowRival) (i : Row) (g : GuardData)
    {b A U ε c q lo γ w s a : ℝ} (h : Inputs μ i g N C b A U ε c q lo γ w s)
    (ha : 0 < a) (x : EntryIIDCentral.Row (Ω := RowRival) N)
    (hx : ∀ j,(x.1 j).1=0 → 0 ≤ (x.1 j).2) :
    LipschitzOnWith (Real.nnabs (1/(xi i*a))) (fun z => frozen μ i C g b A U ε z x) (Ici a) ∧
      LipschitzOnWith (Real.nnabs (2/(xi i*a))) (fun z => (frozen μ i C g b A U ε z x)^2) (Ici a) := by
  have hξ1 : xi i < 1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  by_cases hu : x ∈ usable μ i g b A U ε
  · have hreg := usable_regularity μ i g h x hu
    have hB := masked_nonnegative C x.1 (sampleSet i g b x) hx
    simp only [frozen,if_pos hu,complement_eq_marginal i C x.1 (sampleSet i g b x) hreg.1]
    exact ⟨RootDerivativeIntegral.actual_lipschitz_on (xi_pos i) hξ1 _ _ 0
      (fun k _ => hB k) ha,RootDerivativeIntegral.actual_duplicate_lipschitz_on (xi_pos i) hξ1 _ _ 0
      (fun k _ => hB k) ha⟩
  · simp only [frozen,if_neg hu,zero_pow (by decide : (2:ℕ)≠0)]
    constructor <;> intro x hx y hy <;> simp

theorem original_canonical_good_derivatives (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G] (hnull : ∀ a : ℝ,(G.map Prod.snd) {a}=0)
    (hnon : ∀ᵐ p ∂G,0 ≤ p.2)
    (g : GuardData) {b A U ε c q lo γ w s : ℝ}
    (hcap : ∀ᵐ p ∂G,p.2 ≤ U)
    (h : Inputs (RawMixedSource.source i G) i g N C b A U ε c q lo γ w s)
    (hinterior : b < g.multiplier+g.radius) :
    let P := EntryIIDCentral.rowLaw (RawMixedSource.source i G) N
    let p := response (RawMixedSource.source i G) i C g b A U ε
    let v := velocity (RawMixedSource.source i G) i C g b A U ε
    HasDerivAt (fun a => canonicalGoodMarginal i G C N g a A U ε) (∫ x,v x ∂P) b ∧
      HasDerivAt (fun a => canonicalGoodDuplicate i G C N g a A U ε)
        (∫ x,2*p x*v x ∂P) b := by
  let μ := RawMixedSource.source i G
  let P := EntryIIDCentral.rowLaw μ N
  let f : ℝ → EntryIIDCentral.Row (Ω := RowRival) N → ℝ := frozen μ i C g b A U ε
  let v : EntryIIDCentral.Row (Ω := RowRival) N → ℝ := velocity μ i C g b A U ε
  have hb : 0 < b := h.lo_pos.trans_le (h.lower_price.trans h.bid_window.1)
  have hd : ∀ᵐ x ∂P,HasDerivAt (fun a => f a x) (v x) b := by
    filter_upwards [actual_fixed_bid_derivative i G hnull hnon g h] with x hx
    by_cases hu : x ∈ usable μ i g b A U ε
    · simpa only [f,v,frozen,velocity,if_pos hu] using hx hu
    · simp only [f,v,frozen,velocity,if_neg hu]
      exact hasDerivAt_const b 0
  have hnon' : ∀ᵐ x ∂P,∀ j,(x.1 j).1=0 → 0 ≤ (x.1 j).2 :=
    ae_all_iff.mpr fun j => (EntryIIDCentral.eval_preserving μ N j).quasiMeasurePreserving.ae
      (raw_lower_nonnegative i G hnon)
  have hfi : Integrable (f b) P := Integrable.of_mem_Icc 0 1
    (measurable_frozen μ i C g b A U ε b).aemeasurable (ae_of_all _ fun x => frozen_bounds _ _ _ _ _ _ _ _ _ x)
  have hfi2 : Integrable (fun x => (f b x)^2) P := Integrable.of_mem_Icc 0 1
    ((measurable_frozen μ i C g b A U ε b).pow_const 2).aemeasurable (ae_of_all _ fun x => by
      have hh := frozen_bounds μ i C g b A U ε b x
      exact ⟨sq_nonneg _,by nlinarith [hh.1,hh.2]⟩)
  have hs : Ici (b/2) ∈ 𝓝 b := Ici_mem_nhds (by linarith)
  have hl := hnon'.mono fun x hx => frozen_lipschitz μ i g h (show 0 < b/2 by positivity) x hx
  have hd1 := (hasDerivAt_integral_of_dominated_loc_of_lip hs
    (Eventually.of_forall fun a => (measurable_frozen μ i C g b A U ε a).aestronglyMeasurable)
    hfi (measurable_velocity μ i C g b A U ε).aestronglyMeasurable
    (hl.mono fun _ hx => hx.1) (integrable_const (1/(xi i*(b/2)))) hd).2
  have hd2 := (hasDerivAt_integral_of_dominated_loc_of_lip hs
    (Eventually.of_forall fun a => ((measurable_frozen μ i C g b A U ε a).pow_const 2).aestronglyMeasurable)
    hfi2 (((measurable_frozen μ i C g b A U ε b).const_mul 2).mul
      (measurable_velocity μ i C g b A U ε)).aestronglyMeasurable
    (hl.mono fun _ hx => hx.2) (integrable_const (2/(xi i*(b/2))))
    (hd.mono fun x hx => by simpa only [Nat.cast_ofNat,show (2:ℕ)-1=1 by decide,pow_one,Pi.pow_apply,Pi.mul_apply] using! hx.pow 2)).2
  have he : ∀ᶠ a in 𝓝 b,
      canonicalGoodMarginal i G C N g a A U ε=(∫ x,f a x ∂P) ∧
      canonicalGoodDuplicate i G C N g a A U ε=(∫ x,(f a x)^2 ∂P) := by
    filter_upwards [eventually_lt_nhds hinterior] with a ha
    have hc := integrated_canonical_moments_on_prefix i G g h ha.le hcap
    have hf (x : EntryIIDCentral.Row (Ω := RowRival) N) :
        response μ i C g a A U ε x=f a x :=
      response_eq_frozen μ i g h.requiredDemand_eq h.prefix ha.le h.bid_window.2 x
    change (∫ x,response μ i C g a A U ε x ∂P)=canonicalGoodMarginal i G C N g a A U ε ∧
      (∫ x,(response μ i C g a A U ε x)^2 ∂P)=canonicalGoodDuplicate i G C N g a A U ε at hc
    simp_rw [hf] at hc
    exact ⟨hc.1.symm,hc.2.symm⟩
  refine ⟨hd1.congr_of_eventuallyEq (he.mono fun _ hh => hh.1),?_⟩
  have hh := hd2.congr_of_eventuallyEq (he.mono fun _ hh => hh.2)
  simpa only [f,frozen_at_base,Pi.mul_apply] using! hh

end FCAppendix.Affine.Uniform06.FixedPriceEntryIntegral
