import FCAppendix.Affine.LowBody.NoisyExpectedSurplus
import FCAppendix.Affine.LowBody.NoisyCompactLimit

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Classical Filter Topology
open Existence.Distributional
variable {N : ℕ}

theorem noisy_joint_supported_surplus (d : ℝ) {ξ ε : ℝ}
    (hξ : 0<ξ) (hξh : ξ≤1/2) (hε : 0<ε) (hsmall : ε≤1/4)
    (c : ℕ) (categories : FiniteLaw (Fin 4))
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=unitInterval) mu) (sigma : Kernel (LowValue d) unitInterval)
    [IsMarkovKernel sigma]
    (hdis : mu⊗ₘsigma=(pi.1 : Measure (LowValue d×unitInterval)))
    (hopt : ∀ᵐw ∂mu,∀ᵐq ∂sigma w,∀q' : unitInterval,
      noisyExpectedUtility (N:=N) d ξ ε hε (by linarith) c categories mu (pi,(w,q'))≤
        noisyExpectedUtility (N:=N) d ξ ε hε (by linarith) c categories mu (pi,(w,q)))
    (hjoint : (CommonList.iid categories N).prob (BothUnderflow c)≤
      (CommonList.iid categories N).prob (LocalUnderflow c 0)/4) :
    ∀ᵐx ∂(pi.1 : Measure (LowValue d×unitInterval)),
      x.1.1*(CommonList.iid categories N).prob (LocalUnderflow c 0)/4≤
        x.1.1-x.1.1*bidRatio ε x.2 := by
  rw [←hdis]
  apply Measure.ae_compProd_of_ae_ae
  · apply measurableSet_le
    · fun_prop
    · unfold bidRatio
      fun_prop
  · filter_upwards [hopt] with w hw
    filter_upwards [hw] with q hq
    by_cases hw0 : 0<w.1
    · exact noisy_supported_surplus d hξ hξh hε hsmall c categories mu pi w hw0 q
        (hq quarterChoice) hjoint
    · have hz : w.1=0:=le_antisymm (le_of_not_gt hw0) w.property.1
      simp only [hz,zero_mul,zero_div,sub_zero,le_refl]

theorem lowNoisyLaw_supported_surplus {d ε g : ℝ} (hε : 0<ε) (hsmall : ε≤1/2)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=unitInterval) mu)
    (hs : ∀ᵐx ∂(pi.1 : Measure (LowValue d×unitInterval)),
      x.1.1*g≤x.1.1-x.1.1*bidRatio ε x.2) :
    ∀ᵐx ∂((lowNoisyLaw d ε hε hsmall mu pi).1 : Measure (LowValue d×LowValue d)),
      x.1.1*g-ε*x.1.1≤x.1.1-x.2.1 := by
  let psi : (LowValue d×unitInterval)×unitInterval→LowValue d×LowValue d :=
    fun x=>(x.1.1,noisyBid d ε hε hsmall x)
  have hm : Measurable psi:=(measurable_fst.comp measurable_fst).prodMk
    (continuous_noisyBid d ε hε hsmall).measurable
  have hS : MeasurableSet {x : LowValue d×LowValue d | x.1.1*g-ε*x.1.1≤x.1.1-x.2.1} := by
    apply measurableSet_le <;> fun_prop
  change ∀ᵐx ∂(((pi.1 : Measure (LowValue d×unitInterval)).prod
    (volume : Measure unitInterval)).map psi),x.1.1*g-ε*x.1.1≤x.1.1-x.2.1
  apply (ae_map_iff hm.aemeasurable hS).mpr
  apply (Measure.ae_prod_iff_ae_ae (hS.preimage hm)).mpr
  filter_upwards [hs] with x hx
  exact ae_of_all _ (fun z=>by
    have hb:=noisyBid_bounds hε hsmall x.1 x.2 (0:unitInterval)
    have hb0 : 0≤x.1.1*bidRatio ε x.2:=by simpa using hb.1
    have hb1 : x.1.1*bidRatio ε x.2≤x.1.1:=by simpa using hb.2
    have hc : x.1.1*bidRatio ε x.2*ε*z.1≤ε*x.1.1 := by
      calc
        _≤x.1.1*bidRatio ε x.2*ε*1:=
          mul_le_mul_of_nonneg_left z.property.2 (mul_nonneg hb0 hε.le)
        _=ε*(x.1.1*bidRatio ε x.2):=by ring
        _≤ε*x.1.1:=mul_le_mul_of_nonneg_left hb1 hε.le
    change x.1.1*g-ε*x.1.1≤x.1.1-x.1.1*bidRatio ε x.2*(1+ε*z.1)
    nlinarith)

theorem limit_supported_surplus {d g : ℝ}
    (pi : ℕ→ProbabilityMeasure (LowValue d×LowValue d))
    (pi₀ : ProbabilityMeasure (LowValue d×LowValue d))
    (eps : ℕ→ℝ) (heps : ∀j,0≤eps j) (heps0 : Tendsto eps atTop (𝓝 0))
    (ht : Tendsto pi atTop (𝓝 pi₀))
    (hs : ∀j,∀ᵐx ∂(pi j : Measure (LowValue d×LowValue d)),
      x.1.1*g-eps j*x.1.1≤x.1.1-x.2.1) :
    ∀ᵐx ∂(pi₀ : Measure (LowValue d×LowValue d)),x.1.1*g≤x.1.1-x.2.1 := by
  let f : C(LowValue d×LowValue d,ℝ):=⟨fun x=>max 0 (x.1.1*g-(x.1.1-x.2.1)),by fun_prop⟩
  have hfi (ν : ProbabilityMeasure (LowValue d×LowValue d)) :
      Integrable f (ν : Measure _):=(ContinuousMap.equivBoundedOfCompact _ _ f).integrable _
  have hint : ∀j,∫x,f x ∂(pi j : Measure _)≤eps j*d := by
    intro j
    have hh:=integral_mono_ae (hfi (pi j)) (integrable_const (eps j*d)) (show
      ∀ᵐx ∂(pi j : Measure (LowValue d×LowValue d)),f x≤eps j*d from ?_)
    · simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using hh
    · filter_upwards [hs j] with x hx
      have hd : 0≤d:=x.1.property.1.trans x.1.property.2
      change max 0 _≤eps j*d
      apply max_le (mul_nonneg (heps j) hd)
      have hmul:=mul_le_mul_of_nonneg_left x.1.property.2 (heps j)
      linarith
  have hf0 := (ProbabilityMeasure.continuous_integral_continuousMap f).continuousAt.tendsto.comp ht
  have he0 : Tendsto (fun j=>eps j*d) atTop (𝓝 0):=by simpa using heps0.mul_const d
  have hle : ∫x,f x ∂(pi₀ : Measure _)≤0:=le_of_tendsto_of_tendsto hf0 he0
    (Eventually.of_forall hint)
  have hnon : ∀x,f x≥0:=fun _=>le_max_left _ _
  have hz : ∫x,f x ∂(pi₀ : Measure _)=0:=le_antisymm hle (integral_nonneg hnon)
  have hae:=(integral_eq_zero_iff_of_nonneg hnon (hfi pi₀)).mp hz
  filter_upwards [hae] with x hx
  have hh : x.1.1*g-(x.1.1-x.2.1)≤f x:=le_max_right _ _
  change f x=0 at hx
  linarith

theorem exists_actual_supported_low_limit {N : ℕ} (d : ℝ)
    {ξ : ℝ} (hξ : 0<ξ) (hξh : ξ≤1/2) (c : ℕ) (categories : FiniteLaw (Fin 4))
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (hjoint : (CommonList.iid categories N).prob (BothUnderflow c)≤
      (CommonList.iid categories N).prob (LocalUnderflow c 0)/4) :
    ∃pi₀ : Law (A:=LowValue d) mu,
      (∀ᵐx ∂(pi₀.1 : Measure (LowValue d×LowValue d)),x.2.1≤x.1.1) ∧
      (∀ᵐx ∂(pi₀.1 : Measure (LowValue d×LowValue d)),
        x.1.1*(CommonList.iid categories N).prob (LocalUnderflow c 0)/4≤x.1.1-x.2.1) ∧
      (∀ᵐx ∂(pi₀.1 : Measure (LowValue d×LowValue d)),
        x.2.1*(CommonList.iid categories N).prob (LocalUnderflow c 0)/4≤x.1.1-x.2.1) ∧
      ∃(eps : ℕ→ℝ)(heps : ∀j,0<eps j)(hsmall : ∀j,eps j≤1/2)
        (pi : ℕ→Law (A:=unitInterval) mu),
        (∀j,eps j≤1/4) ∧ Tendsto eps atTop (𝓝 0) ∧
        (∀j,∃sigma : Kernel (LowValue d) unitInterval,
          IsMarkovKernel sigma ∧ mu⊗ₘsigma=((pi j).1 : Measure (LowValue d×unitInterval)) ∧
          (∀ᵐw ∂mu,∀ᵐq ∂sigma w,∀q' : unitInterval,
            noisyExpectedUtility (N:=N) d ξ (eps j) (heps j) (hsmall j) c categories mu (pi j,(w,q'))≤
              noisyExpectedUtility (N:=N) d ξ (eps j) (heps j) (hsmall j) c categories mu (pi j,(w,q)))) ∧
        Tendsto (fun j=>(lowNoisyLaw d (eps j) (heps j) (hsmall j) mu (pi j)).1)
          atTop (𝓝 pi₀.1) := by
  obtain ⟨eps,heps,hsmall,pi,pi₀,hquarter,heps0,hIC,hlim,hle⟩:=
    exists_actual_noisy_low_limit (N:=N) d hξ (by linarith) c categories mu
  let g : ℝ:=(CommonList.iid categories N).prob (LocalUnderflow c 0)/4
  have hgap : ∀j,∀ᵐx ∂((lowNoisyLaw d (eps j) (heps j) (hsmall j) mu (pi j)).1 :
      Measure (LowValue d×LowValue d)),x.1.1*g-eps j*x.1.1≤x.1.1-x.2.1 := by
    intro j
    obtain ⟨sigma,hmark,hdis,hopt⟩:=hIC j
    letI:=hmark
    have hh:=noisy_joint_supported_surplus (N:=N) d hξ hξh (heps j) (hquarter j)
      c categories mu (pi j) sigma hdis hopt hjoint
    exact lowNoisyLaw_supported_surplus (heps j) (hsmall j) mu (pi j)
      (by simpa only [g,mul_div_assoc] using hh)
  have hlimGap:=limit_supported_surplus
    (fun j=>(lowNoisyLaw d (eps j) (heps j) (hsmall j) mu (pi j)).1) pi₀.1
      eps (fun j=>(heps j).le) heps0 hlim hgap
  have hlimGap' : ∀ᵐx ∂(pi₀.1 : Measure (LowValue d×LowValue d)),
      x.1.1*(CommonList.iid categories N).prob (LocalUnderflow c 0)/4≤x.1.1-x.2.1 := by
    simpa only [g,mul_div_assoc] using hlimGap
  refine ⟨pi₀,hle,hlimGap',?_,eps,heps,hsmall,pi,hquarter,heps0,hIC,hlim⟩
  filter_upwards [hle,hlimGap'] with x hx hg
  have hm:=mul_le_mul_of_nonneg_right hx
    ((CommonList.iid categories N).prob_nonneg (LocalUnderflow c 0))
  linarith

end FCAppendix.Affine.LowBody
