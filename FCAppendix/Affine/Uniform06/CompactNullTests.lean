import FCAppendix.Affine.LowBody.BoundedNullWeakIntegral
import FCAppendix.Existence.R01CompactProduct
import FCAppendix.Affine.Uniform06.EntryActiveLimit
import FCAppendix.Affine.Uniform06.EntryReciprocalLimit

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.CompactNullTests

open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.Existence.Distributional FCAppendix.Affine.LowBody
open FCAppendix.Affine.ClippedResidual ReciprocalSecantBounds

section Abstract

variable {P X : Type*} [MetricSpace P] [MeasurableSpace P] [BorelSpace P]
  [CompactSpace P] [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

theorem moving_parameter_integral
    (μ : ℕ → ProbabilityMeasure X) (μ0 : ProbabilityMeasure X)
    (hμ : Tendsto μ atTop (𝓝 μ0)) (p : ℕ → P) {p0 : P}
    (hp : Tendsto p atTop (𝓝 p0)) (f : P × X → ℝ) (hf : Measurable f)
    (S : Set (P × X)) (hS : IsClosed S)
    (hcont : ∀ q ∉ S, ContinuousAt f q) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ q, |f q| ≤ C)
    (hnull : ∀ᵐ x ∂(μ0:Measure X), (p0,x) ∉ S) :
    Tendsto (fun n => ∫ x, f (p n,x) ∂(μ n:Measure X)) atTop
      (𝓝 (∫ x, f (p0,x) ∂(μ0:Measure X))) := by
  let ν := fun n => productLaw (diracProba (p n)) (μ n)
  let ν0 := productLaw (diracProba p0) μ0
  have hν : Tendsto ν atTop (𝓝 ν0) :=
    continuous_productLaw.continuousAt.tendsto.comp
      ((continuous_diracProba.continuousAt.tendsto.comp hp).prodMk_nhds hμ)
  have hnull' : (ν0:Measure (P × X)) S=0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    change ∀ᵐ q ∂(Measure.dirac p0).prod (μ0:Measure X),q ∉ S
    apply (Measure.ae_prod_iff_ae_ae hS.measurableSet.compl).mpr
    simpa only [ae_dirac_eq,Filter.eventually_pure] using hnull
  have ht := tendsto_integral_of_closed_null_discontinuities f hf S hS
    hcont hC hbound ν ν0 hν hnull'
  have he (a : P) (M : ProbabilityMeasure X) :
      (∫ q, f q ∂(productLaw (diracProba a) M:Measure (P × X)))=
        ∫ x, f (a,x) ∂(M:Measure X) := by
    change (∫ q, f q ∂(Measure.dirac a).prod (M:Measure X))=_
    rw [Measure.dirac_prod,integral_map measurable_prodMk_left.aemeasurable
      hf.aestronglyMeasurable]
  simpa only [ν,ν0,he] using ht

end Abstract

abbrev Bid (U : ℝ) := Icc (0:ℝ) U
abbrev Parameters (lo hi Θ : ℝ) := Icc lo hi × Icc lo hi × Icc (-Θ) Θ
abbrev Sample (lo hi Θ U : ℝ) := Parameters lo hi Θ × Bid U

def clipBid (U : ℝ) (hU : 0 ≤ U) : C(ℝ × ℝ,Bid U) :=
  ⟨fun p => ⟨max 0 (min U p.2),⟨le_max_left _ _,max_le hU (min_le_left _ _)⟩⟩,
    (continuous_const.max (continuous_const.min continuous_snd)).subtype_mk _⟩

theorem clipBid_eq {U : ℝ} (hU : 0 ≤ U) {p : ℝ × ℝ}
    (hp : p.2 ∈ Icc (0:ℝ) U) : (clipBid U hU p:ℝ)=p.2 := by
  simp only [clipBid,ContinuousMap.coe_mk,min_eq_right hp.2,max_eq_right hp.1]

def clippedLaw (U : ℝ) (hU : 0 ≤ U) (G : ProbabilityMeasure (ℝ × ℝ)) :
    ProbabilityMeasure (Bid U) := G.map (clipBid U hU).continuous.measurable.aemeasurable

theorem clippedLaw_tendsto {U : ℝ} (hU : 0 ≤ U)
    (G : ℕ → ProbabilityMeasure (ℝ × ℝ)) (G0 : ProbabilityMeasure (ℝ × ℝ))
    (hG : Tendsto G atTop (𝓝 G0)) :
    Tendsto (fun n => clippedLaw U hU (G n)) atTop (𝓝 (clippedLaw U hU G0)) :=
  (ProbabilityMeasure.continuous_map (clipBid U hU).continuous).continuousAt.tendsto.comp hG

def likelihood {lo hi Θ U : ℝ} (ξ : ℝ) (p : Sample lo hi Θ U) : ℝ :=
  Real.exp (-(p.1.2.2:ℝ)*exposure ξ p.1.1 p.2)

theorem continuous_likelihood {lo hi Θ U ξ : ℝ} (hlo : 0 < lo) (hξ : 0 < ξ) :
    Continuous (@likelihood lo hi Θ U ξ) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have he : ContinuousAt (fun q : Sample lo hi Θ U => exposure ξ q.1.1 q.2) p :=
    (EntryActiveLimit.continuousAt_exposure_pair (z := (p.1.1:ℝ)) (b := (p.2:ℝ)) hξ
      (hlo.trans_le p.1.1.2.1)).comp (f := fun q : Sample lo hi Θ U => ((q.1.1:ℝ),(q.2:ℝ)))
      (show ContinuousAt (fun q : Sample lo hi Θ U => ((q.1.1:ℝ),(q.2:ℝ))) p by fun_prop)
  have harg : ContinuousAt (fun q : Sample lo hi Θ U => -(q.1.2.2:ℝ)*exposure ξ q.1.1 q.2) p :=
    (show ContinuousAt (fun q : Sample lo hi Θ U => -(q.1.2.2:ℝ)) p by fun_prop).mul he
  change ContinuousAt (fun q : Sample lo hi Θ U => Real.exp (-(q.1.2.2:ℝ)*exposure ξ q.1.1 q.2)) p
  exact Real.continuous_exp.continuousAt.comp harg

theorem likelihood_bounds {lo hi Θ U ξ : ℝ} (hlo : 0 < lo) (hξ : 0 < ξ)
    (p : Sample lo hi Θ U) : 0 < likelihood ξ p ∧ likelihood ξ p ≤ Real.exp Θ := by
  refine ⟨Real.exp_pos _,Real.exp_le_exp.mpr ?_⟩
  have hx0 := exposure_nonneg hξ (hlo.trans_le p.1.1.2.1) (b:=p.2)
  have hx1 := exposure_le_one ξ (p.1.1:ℝ) (p.2:ℝ)
  have hθ := p.1.2.2.2
  have hΘ : 0 ≤ Θ := by linarith [hθ.1,hθ.2]
  have hh := mul_le_mul_of_nonneg_right (show -(p.1.2.2:ℝ) ≤ Θ by linarith [hθ.1]) hx0
  exact hh.trans (by nlinarith)

def badSet (lo hi Θ U : ℝ) : Set (Sample lo hi Θ U) :=
  {p | (p.2:ℝ)=(p.1.2.1:ℝ) ∨ (p.2:ℝ)=(p.1.1:ℝ)}

theorem badSet_closed (lo hi Θ U : ℝ) : IsClosed (badSet lo hi Θ U) :=
  (isClosed_eq (by fun_prop) (by fun_prop)).union (isClosed_eq (by fun_prop) (by fun_prop))

def reciprocalTest {lo hi Θ U : ℝ} (ξ : ℝ) (p : Sample lo hi Θ U) : ℝ :=
  likelihood ξ p*reciprocalTerm p.2 p.1.2.1

def windowTest {lo hi Θ U : ℝ} (ξ : ℝ) (p : Sample lo hi Θ U) : ℝ :=
  likelihood ξ p*(if (p.1.2.1:ℝ)< p.2 ∧ (p.2:ℝ)≤ p.1.1 then 1 else 0)

theorem measurable_reciprocalTest {lo hi Θ U ξ : ℝ}
    (hlo : 0 < lo) (hξ : 0 < ξ) :
    Measurable (@reciprocalTest lo hi Θ U ξ) := by
  exact (continuous_likelihood hlo hξ).measurable.mul
    (Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop))
      (by fun_prop) measurable_const)

theorem measurable_windowTest {lo hi Θ U ξ : ℝ}
    (hlo : 0 < lo) (hξ : 0 < ξ) :
    Measurable (@windowTest lo hi Θ U ξ) := by
  exact (continuous_likelihood hlo hξ).measurable.mul
    (Measurable.ite ((measurableSet_lt
      (show Measurable (fun q : Sample lo hi Θ U => (q.1.2.1:ℝ)) by fun_prop)
      (show Measurable (fun q : Sample lo hi Θ U => (q.2:ℝ)) by fun_prop)).inter
      (measurableSet_le
        (show Measurable (fun q : Sample lo hi Θ U => (q.2:ℝ)) by fun_prop)
        (show Measurable (fun q : Sample lo hi Θ U => (q.1.1:ℝ)) by fun_prop)))
      measurable_const measurable_const)

theorem reciprocalTest_bound {lo hi Θ U ξ : ℝ} (hlo : 0 < lo) (hξ : 0 < ξ)
    (p : Sample lo hi Θ U) : |reciprocalTest ξ p| ≤ Real.exp Θ/lo := by
  rw [reciprocalTest,abs_mul,abs_of_pos (likelihood_bounds hlo hξ p).1]
  have hb := EntryReciprocalLimit.reciprocal_abs_bound (B:=(p.2:ℝ)) hlo p.1.2.1.2.1
  simpa only [div_eq_mul_inv] using mul_le_mul (likelihood_bounds hlo hξ p).2 hb
    (abs_nonneg _) (Real.exp_pos _).le

theorem windowTest_bound {lo hi Θ U ξ : ℝ} (hlo : 0 < lo) (hξ : 0 < ξ)
    (p : Sample lo hi Θ U) : |windowTest ξ p| ≤ Real.exp Θ := by
  unfold windowTest
  split_ifs
  · simpa only [mul_one,abs_of_pos (likelihood_bounds hlo hξ p).1] using
      (likelihood_bounds hlo hξ p).2
  · simp only [mul_zero,abs_zero]
    exact (Real.exp_pos _).le

theorem reciprocalTest_continuous_off {lo hi Θ U ξ : ℝ}
    (hlo : 0 < lo) (hξ : 0 < ξ) (p : Sample lo hi Θ U)
    (hp : p ∉ badSet lo hi Θ U) : ContinuousAt (reciprocalTest ξ) p := by
  unfold reciprocalTest
  apply (continuous_likelihood hlo hξ).continuousAt.mul
  have hne : (p.2:ℝ)≠(p.1.2.1:ℝ) := fun h => hp (Or.inl h)
  by_cases h : (p.1.2.1:ℝ)< p.2
  · have he : ∀ᶠ q : Sample lo hi Θ U in 𝓝 p,(q.1.2.1:ℝ)< q.2 :=
      (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds h
    have hc : ContinuousAt (fun q : Sample lo hi Θ U => (q.2:ℝ)⁻¹) p :=
      (show ContinuousAt (fun q : Sample lo hi Θ U => (q.2:ℝ)) p by fun_prop).inv₀
        (hlo.trans_le p.1.2.1.2.1 |>.trans h).ne'
    apply hc.congr_of_eventuallyEq
    filter_upwards [he] with q hq
    simp only [reciprocalTerm,if_pos hq]
  · have hlt : (p.2:ℝ)< p.1.2.1 := lt_of_le_of_ne (le_of_not_gt h) hne
    have he : ∀ᶠ q : Sample lo hi Θ U in 𝓝 p,(q.2:ℝ)< q.1.2.1 :=
      (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds hlt
    apply (continuousAt_const (y := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [he] with q hq
    simp only [reciprocalTerm,if_neg (not_lt.mpr hq.le)]

theorem windowTest_continuous_off {lo hi Θ U ξ : ℝ}
    (hlo : 0 < lo) (hξ : 0 < ξ) (p : Sample lo hi Θ U)
    (hp : p ∉ badSet lo hi Θ U) : ContinuousAt (windowTest ξ) p := by
  have hc : ContinuousAt (fun q : Sample lo hi Θ U =>
      if (q.1.2.1:ℝ)<q.2 ∧ (q.2:ℝ)≤q.1.1 then (1:ℝ) else 0) p := by
    have hn1 : (p.2:ℝ)≠(p.1.2.1:ℝ) := fun h => hp (Or.inl h)
    have hn2 : (p.2:ℝ)≠(p.1.1:ℝ) := fun h => hp (Or.inr h)
    by_cases h : (p.1.2.1:ℝ)< p.2 ∧ (p.2:ℝ)≤ p.1.1
    · have h2 : (p.2:ℝ)< p.1.1 := lt_of_le_of_ne h.2 hn2
      have he1 : ∀ᶠ q : Sample lo hi Θ U in 𝓝 p,(q.1.2.1:ℝ)< q.2 :=
        (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds h.1
      have he2 : ∀ᶠ q : Sample lo hi Θ U in 𝓝 p,(q.2:ℝ)< q.1.1 :=
        (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds h2
      apply (continuousAt_const (y:=(1:ℝ))).congr_of_eventuallyEq
      filter_upwards [he1,he2] with q hq1 hq2
      have hq : (q.1.2.1:ℝ)<q.2 ∧ (q.2:ℝ)≤q.1.1 := ⟨hq1,hq2.le⟩
      simp only [if_pos hq]
    · rcases not_and_or.mp h with h | h
      · have hlt : (p.2:ℝ)< p.1.2.1 := lt_of_le_of_ne (le_of_not_gt h) hn1
        have he : ∀ᶠ q : Sample lo hi Θ U in 𝓝 p,(q.2:ℝ)< q.1.2.1 :=
          (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds hlt
        apply (continuousAt_const (y:=(0:ℝ))).congr_of_eventuallyEq
        filter_upwards [he] with q hq
        have hnot : ¬((q.1.2.1:ℝ)<q.2 ∧ (q.2:ℝ)≤q.1.1) := fun h => (not_lt_of_ge hq.le) h.1
        simp only [if_neg hnot]
      · have hlt : (p.1.1:ℝ)< p.2 := lt_of_not_ge h
        have he : ∀ᶠ q : Sample lo hi Θ U in 𝓝 p,(q.1.1:ℝ)< q.2 :=
          (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds hlt
        apply (continuousAt_const (y:=(0:ℝ))).congr_of_eventuallyEq
        filter_upwards [he] with q hq
        have hnot : ¬((q.1.2.1:ℝ)<q.2 ∧ (q.2:ℝ)≤q.1.1) := fun h => (not_le_of_gt hq) h.2
        simp only [if_neg hnot]
  exact (continuous_likelihood hlo hξ).continuousAt.mul hc

theorem moving_reciprocal_and_window
    {ξ lo hi Θ U : ℝ} (hξ : 0 < ξ) (hlo : 0 < lo) (hU : 0 ≤ U)
    (G : ℕ → ProbabilityMeasure (ℝ × ℝ)) (G0 : ProbabilityMeasure (ℝ × ℝ))
    (hG : Tendsto G atTop (𝓝 G0))
    (hbox : ∀ n,∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),p.2 ∈ Icc (0:ℝ) U)
    (hbox0 : ∀ᵐ p ∂(G0:Measure (ℝ × ℝ)),p.2 ∈ Icc (0:ℝ) U)
    (b z θ : ℕ → ℝ) {b0 θ0 : ℝ}
    (hb : ∀ n,b n ∈ Icc lo hi) (hz : ∀ n,z n ∈ Icc lo hi)
    (hθ : ∀ n,θ n ∈ Icc (-Θ) Θ)
    (hblim : Tendsto b atTop (𝓝 b0)) (hzlim : Tendsto z atTop (𝓝 b0))
    (hθlim : Tendsto θ atTop (𝓝 θ0))
    (hnull : ((G0:Measure (ℝ × ℝ)).map Prod.snd) {b0}=0) :
    Tendsto (fun n => ∫ p, Real.exp (-θ n*exposure ξ (b n) p.2)*
      reciprocalTerm p.2 (z n) ∂(G n:Measure (ℝ × ℝ))) atTop
        (𝓝 (∫ p,Real.exp (-θ0*exposure ξ b0 p.2)*reciprocalTerm p.2 b0
          ∂(G0:Measure (ℝ × ℝ)))) ∧
    Tendsto (fun n => ∫ p,Real.exp (-θ n*exposure ξ (b n) p.2)*
      (if z n< p.2 ∧ p.2≤ b n then 1 else 0) ∂(G n:Measure (ℝ × ℝ)))
        atTop (𝓝 0) := by
  have hb0 := isClosed_Icc.mem_of_tendsto hblim (Eventually.of_forall hb)
  have hθ0 := isClosed_Icc.mem_of_tendsto hθlim (Eventually.of_forall hθ)
  let p : ℕ → Parameters lo hi Θ := fun n => (⟨b n,hb n⟩,⟨z n,hz n⟩,⟨θ n,hθ n⟩)
  let p0 : Parameters lo hi Θ := (⟨b0,hb0⟩,⟨b0,hb0⟩,⟨θ0,hθ0⟩)
  have hp : Tendsto p atTop (𝓝 p0) :=
    (tendsto_subtype_rng.mpr hblim).prodMk_nhds
      ((tendsto_subtype_rng.mpr hzlim).prodMk_nhds (tendsto_subtype_rng.mpr hθlim))
  have hne : ∀ᵐ q ∂(G0:Measure (ℝ × ℝ)),q.2≠b0 := by
    have hh := measure_eq_zero_iff_ae_notMem.mp hnull
    exact (ae_map_iff measurable_snd.aemeasurable (by measurability)).mp hh
  have hbad : ∀ᵐ B ∂(clippedLaw U hU G0:Measure (Bid U)),
      (p0,B) ∉ badSet lo hi Θ U := by
    apply (ae_map_iff (clipBid U hU).continuous.measurable.aemeasurable
      ((badSet_closed lo hi Θ U).measurableSet.compl.preimage
        (measurable_const.prodMk measurable_id))).mpr
    filter_upwards [hbox0,hne] with q hq hqn
    simpa only [badSet,mem_compl_iff,mem_setOf_eq,id_eq,p0,clipBid_eq hU hq,or_self] using hqn
  have hr := moving_parameter_integral (fun n => clippedLaw U hU (G n))
    (clippedLaw U hU G0) (clippedLaw_tendsto hU G G0 hG) p hp
    (reciprocalTest ξ) (measurable_reciprocalTest hlo hξ) (badSet lo hi Θ U)
    (badSet_closed _ _ _ _) (reciprocalTest_continuous_off hlo hξ)
    (by positivity : 0 ≤ Real.exp Θ/lo) (reciprocalTest_bound hlo hξ) hbad
  have hw := moving_parameter_integral (fun n => clippedLaw U hU (G n))
    (clippedLaw U hU G0) (clippedLaw_tendsto hU G G0 hG) p hp
    (windowTest ξ) (measurable_windowTest hlo hξ) (badSet lo hi Θ U)
    (badSet_closed _ _ _ _) (windowTest_continuous_off hlo hξ)
    (Real.exp_pos Θ).le (windowTest_bound hlo hξ) hbad
  have he (f : Sample lo hi Θ U → ℝ) (hf : Measurable f)
      (a : Parameters lo hi Θ) (M : ProbabilityMeasure (ℝ × ℝ)) :
      (∫ B,f (a,B) ∂(clippedLaw U hU M:Measure (Bid U)))=
        ∫ q,f (a,clipBid U hU q) ∂(M:Measure (ℝ × ℝ)) := by
    rw [clippedLaw,ProbabilityMeasure.toMeasure_map,
      integral_map (f := fun B : Bid U => f (a,B)) (clipBid U hU).continuous.measurable.aemeasurable
        (hf.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable]
  simp_rw [he _ (measurable_reciprocalTest hlo hξ)] at hr
  simp_rw [he _ (measurable_windowTest hlo hξ)] at hw
  have hrn (n : ℕ) : (∫ q,reciprocalTest ξ (p n,clipBid U hU q)
      ∂(G n:Measure (ℝ × ℝ)))=∫ q,Real.exp (-θ n*exposure ξ (b n) q.2)*
        reciprocalTerm q.2 (z n) ∂(G n:Measure (ℝ × ℝ)) := by
    apply integral_congr_ae
    exact (hbox n).mono fun q hq => by simp only [reciprocalTest,likelihood,p,clipBid_eq hU hq]
  have hr0 : (∫ q,reciprocalTest ξ (p0,clipBid U hU q) ∂(G0:Measure (ℝ × ℝ)))=
      ∫ q,Real.exp (-θ0*exposure ξ b0 q.2)*reciprocalTerm q.2 b0 ∂(G0:Measure (ℝ × ℝ)) := by
    apply integral_congr_ae
    exact hbox0.mono fun q hq => by simp only [reciprocalTest,likelihood,p0,clipBid_eq hU hq]
  have hwn (n : ℕ) : (∫ q,windowTest ξ (p n,clipBid U hU q)
      ∂(G n:Measure (ℝ × ℝ)))=∫ q,Real.exp (-θ n*exposure ξ (b n) q.2)*
        (if z n< q.2 ∧ q.2≤ b n then 1 else 0) ∂(G n:Measure (ℝ × ℝ)) := by
    apply integral_congr_ae
    exact (hbox n).mono fun q hq => by simp only [windowTest,likelihood,p,clipBid_eq hU hq]
  have hw0 : (∫ q,windowTest ξ (p0,clipBid U hU q) ∂(G0:Measure (ℝ × ℝ)))=0 := by
    have hf0 : ∀ q,windowTest ξ (p0,clipBid U hU q)=0 := by
      intro q
      have hn : ¬(b0 < (clipBid U hU q:ℝ) ∧ (clipBid U hU q:ℝ) ≤ b0) :=
        fun h => not_lt_of_ge h.2 h.1
      simp only [windowTest,p0,if_neg hn,mul_zero]
    simp_rw [hf0]
    exact integral_zero _ _
  exact ⟨by simpa only [hrn,hr0] using hr,by simpa only [hwn,hw0] using hw⟩

end FCAppendix.Affine.Uniform06.CompactNullTests
