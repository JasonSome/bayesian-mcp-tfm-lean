import FCAppendix.Affine.Tail04.MovingGuardVariation
import FCAppendix.Affine.Hybrid.FavoredUniformContinuity

noncomputable section
namespace FCAppendix.Affine.Tail04.CompactPromotionErrors
open MeasureTheory Set Filter Topology Classical
open TypicalFinitePromotion ActualFallbackPromotion UniformFallbackVariation
open TypicalGuardStatistics MovingGuardVariation EqualPrivateSignal
open scoped BigOperators

def finiteVariation {J X : Type*} [Fintype J] (f : X → J → ℝ) (x y : X) : ℝ :=
  ∑ j,|f x j-f y j|

theorem exists_finite_modulus {J X : Type*} [Fintype J]
    [PseudoMetricSpace X] [CompactSpace X] (f : X → J → ℝ)
    (hf : Continuous f) {e : ℝ} (he : 0< e) :
    ∃ δ : ℝ,0< δ ∧ ∀ x y,dist x y< δ → finiteVariation f x y< e := by
  let a : ℝ := e/((Fintype.card J:ℝ)+1)
  have hden : 0<(Fintype.card J:ℝ)+1 := by positivity
  have ha : 0< a := div_pos he hden
  obtain ⟨δ,hδ,hmod⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hf) a ha
  refine ⟨δ,hδ,?_⟩
  intro x y hxy
  have hh (j : J) : |f x j-f y j|≤ a := by
    have hj : |f x j-f y j|<a := by
      simpa only [Real.dist_eq] using (dist_pi_lt_iff ha).mp (hmod hxy) j
    exact hj.le
  have hs := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset J)) => hh j)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
  change finiteVariation f x y≤(Fintype.card J:ℝ)*a at hs
  apply hs.trans_lt
  calc
    _ < ((Fintype.card J:ℝ)+1)*a :=
      mul_lt_mul_of_pos_right (by linarith) ha
    _ = e := by dsimp [a];field_simp

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

abbrev BoxInput (ι : Type*) (BL BU PL PU vlo vhi C : ℝ) :=
  (Icc BL BU×Icc PL PU)×(Icc vlo vhi×(ι → Icc (1:ℝ) C))

def boxUtility (N H0 H1 c : ℕ) (ξ R width e0 F eta : ℝ)
    (he0 : 0≤ eta) (he1 : eta≤1) (reg lowPresent : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (i : ι)
    {BL BU PL PU vlo vhi C : ℝ} (x : BoxInput ι BL BU PL PU vlo vhi C)
    (j : Fin 3×ι) : ℝ :=
  conditionalUtility (NativeTypicalCount.countParameters N H0 H1 c ξ reg ν0 ν1)
    (effectivePhi lowPresent (phi N H0 H1 c ξ x.1.1 R x.1.2 width reg ν0 ν1))
    e0 F eta x.2.1 he0 he1 i (FiniteLaw.dirac j.1) (fun k => (x.2.2 k:ℝ)) j.2

omit [Nonempty ι] in
theorem continuous_boxUtility (N H0 H1 c : ℕ) (ξ R width e0 F eta : ℝ)
    (he0 : 0≤ eta) (he1 : eta≤1) (reg lowPresent : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (i : ι)
    {BL BU PL PU vlo vhi C : ℝ} :
    Continuous (boxUtility N H0 H1 c ξ R width e0 F eta he0 he1 reg lowPresent ν0 ν1 i
      (BL:=BL) (BU:=BU) (PL:=PL) (PU:=PU) (vlo:=vlo) (vhi:=vhi) (C:=C)) := by
  apply continuous_pi
  intro j
  apply continuous_iff_continuousAt.mpr
  intro x
  have hB : Continuous (fun y : BoxInput ι BL BU PL PU vlo vhi C=>(y.1.1:ℝ)) :=
    continuous_fst.fst.subtype_val
  have hRp : Continuous (fun y : BoxInput ι BL BU PL PU vlo vhi C=>(y.1.2:ℝ)) :=
    continuous_fst.snd.subtype_val
  have hv : Continuous (fun y : BoxInput ι BL BU PL PU vlo vhi C=>(y.2.1:ℝ)) :=
    continuous_snd.fst.subtype_val
  have hb : Continuous (fun y : BoxInput ι BL BU PL PU vlo vhi C=>fun k=>(y.2.2 k:ℝ)) :=
    continuous_pi (fun k=>((continuous_apply k).comp continuous_snd.snd).subtype_val)
  exact continuousAt_conditionalUtility_moving N H0 H1 c ξ R width e0 F eta he0 he1
    reg lowPresent ν0 ν1
    (fun y : BoxInput ι BL BU PL PU vlo vhi C=>(y.1.1:ℝ))
    (fun y : BoxInput ι BL BU PL PU vlo vhi C=>(y.1.2:ℝ))
    (fun y : BoxInput ι BL BU PL PU vlo vhi C=>(y.2.1:ℝ))
    (fun y : BoxInput ι BL BU PL PU vlo vhi C=>fun k=>(y.2.2 k:ℝ)) x
    hB.continuousAt hRp.continuousAt hv.continuousAt hb.continuousAt
    (fun k=>lt_of_lt_of_le (by norm_num) (x.2.2 k).2.1) i j.2 (FiniteLaw.dirac j.1)

omit [Nonempty ι] in

theorem exists_actual_variation_modulus (N H0 H1 c : ℕ)
    (ξ R width e0 F eta : ℝ) (he0 : 0≤ eta) (he1 : eta≤1) (reg lowPresent : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (i : ι)
    (BL BU PL PU vlo vhi C : ℝ) {e : ℝ} (he : 0< e) :
    ∃ δ : ℝ,0< δ ∧ ∀ B : Icc BL BU,∀ Rp : Icc PL PU,∀ v : Icc vlo vhi,
      ∀ b d : ι → Icc (1:ℝ) C,dist b d< δ → ∀ K : CountLaw 2,
      variation (conditionalUtility (NativeTypicalCount.countParameters N H0 H1 c ξ reg ν0 ν1)
        (effectivePhi lowPresent (phi N H0 H1 c ξ B R Rp width reg ν0 ν1))
        e0 F eta v he0 he1 i K) (fun k => (b k:ℝ)) (fun k => (d k:ℝ))< e := by
  obtain ⟨δ,hδ,hmod⟩ := exists_finite_modulus
    (boxUtility N H0 H1 c ξ R width e0 F eta he0 he1 reg lowPresent ν0 ν1 i
      (BL:=BL) (BU:=BU) (PL:=PL) (PU:=PU) (vlo:=vlo) (vhi:=vhi) (C:=C))
      (continuous_boxUtility N H0 H1 c ξ R width e0 F eta he0 he1 reg lowPresent ν0 ν1 i) he
  refine ⟨δ,hδ,?_⟩
  intro B Rp v b d hbd K
  have hh := hmod ((B,Rp),(v,b)) ((B,Rp),(v,d)) (by simpa [Prod.dist_eq] using hbd)
  have heq : finiteVariation
      (boxUtility N H0 H1 c ξ R width e0 F eta he0 he1 reg lowPresent ν0 ν1 i)
      ((B,Rp),(v,b)) ((B,Rp),(v,d))=
      uniformVariation (NativeTypicalCount.countParameters N H0 H1 c ξ reg ν0 ν1)
        (effectivePhi lowPresent (phi N H0 H1 c ξ B R Rp width reg ν0 ν1))
        e0 F eta v he0 he1 i (fun k => (b k:ℝ)) (fun k => (d k:ℝ)) := by
    simp only [finiteVariation,Fintype.sum_prod_type,boxUtility,uniformVariation,variation]
  rw [heq] at hh
  exact (variation_le_uniformVariation _ _ e0 F eta v he0 he1 i K _ _).trans_lt hh

def flagVariation (e0 F : ℝ) (b d : ι → ℝ) : ℝ :=
  ∑ z : ι → Bool,
    |(independentFlagLaw (sourceFlagProb e0 F b) (sourceFlagProb_nonneg e0 F b)
      (sourceFlagProb_le_one e0 F b)).mass z-
     (independentFlagLaw (sourceFlagProb e0 F d) (sourceFlagProb_nonneg e0 F d)
      (sourceFlagProb_le_one e0 F d)).mass z|

omit [Nonempty ι] in
lemma flagVariation_nonneg (e0 F : ℝ) (b d : ι → ℝ) : 0≤ flagVariation e0 F b d :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

omit [Nonempty ι] in

theorem flag_probability_difference (e0 F : ℝ) (b d : ι → ℝ) (E : (ι → Bool) → Prop) :
    |(independentFlagLaw (sourceFlagProb e0 F b) (sourceFlagProb_nonneg e0 F b)
        (sourceFlagProb_le_one e0 F b)).prob E-
      (independentFlagLaw (sourceFlagProb e0 F d) (sourceFlagProb_nonneg e0 F d)
        (sourceFlagProb_le_one e0 F d)).prob E|≤ flagVariation e0 F b d := by
  simp only [FiniteLaw.prob,FiniteLaw.expect,←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro z _
  by_cases hz : E z
  · simp only [if_pos hz,mul_one]
    exact le_rfl
  · simp only [if_neg hz,mul_zero,sub_self,abs_zero]
    exact abs_nonneg _

omit [Nonempty ι] in
theorem exists_flagVariation_modulus (e0 F C : ℝ) {e : ℝ} (he : 0< e) :
    ∃ δ : ℝ,0< δ ∧ ∀ b d : ι → Icc (1:ℝ) C,dist b d< δ →
      flagVariation e0 F (fun k => (b k:ℝ)) (fun k => (d k:ℝ))< e := by
  let f : (ι → Icc (1:ℝ) C) → (ι → Bool) → ℝ := fun b z =>
    (independentFlagLaw (sourceFlagProb e0 F (fun k => (b k:ℝ)))
      (sourceFlagProb_nonneg e0 F (fun k => (b k:ℝ)))
      (sourceFlagProb_le_one e0 F (fun k => (b k:ℝ)))).mass z
  have hf : Continuous f := by
    apply continuous_pi
    intro z
    apply continuous_iff_continuousAt.mpr
    intro b
    let g : (ι→ℝ)→ℝ := fun a=>
      (independentFlagLaw (sourceFlagProb e0 F a) (sourceFlagProb_nonneg e0 F a)
        (sourceFlagProb_le_one e0 F a)).mass z
    have hg : ContinuousAt g (fun k=>(b k:ℝ)) :=
      continuousAt_sourceFlagLaw_mass e0 F (fun k=>(b k:ℝ)) z
    have hcoe : Continuous (fun a : ι→Icc (1:ℝ) C=>fun k=>(a k:ℝ)) :=
      continuous_pi (fun k=>(continuous_apply k).subtype_val)
    change ContinuousAt (fun a : ι→Icc (1:ℝ) C=>g (fun k=>(a k:ℝ))) b
    exact ContinuousAt.comp' (f:=fun a : ι→Icc (1:ℝ) C=>fun k=>(a k:ℝ))
      (g:=g) (x:=b) hg hcoe.continuousAt
  exact exists_finite_modulus f hf he

theorem integral_variation_small {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (err : Ω → ℝ) (herr : Integrable err μ) {e : ℝ}
    (he : ∀ᵐ ω ∂μ,err ω≤ e) : ∫ ω,err ω ∂μ≤ e := by
  have h := integral_mono_ae herr (integrable_const e) he
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using h

end FCAppendix.Affine.Tail04.CompactPromotionErrors
