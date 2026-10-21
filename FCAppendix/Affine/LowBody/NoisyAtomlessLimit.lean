import FCAppendix.Affine.LowBody.NoisySupportedLimit
import FCAppendix.Affine.LowBody.NoisyPositiveLimit
import FCAppendix.Affine.LowBody.NoisyZeroLimit
import FCAppendix.Affine.LowBody.LimitBidLaw
import FCAppendix.Affine.LowBody.SourcePrimitiveGuards

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Existence.Distributional

structure ActualAtomlessLowLimit (N : ℕ) (d ξ : ℝ) (c : ℕ)
    (categories : FiniteLaw (Fin 4)) (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] where
  joint : Law (A:=LowValue d) mu
  bid_le_value : ∀ᵐx ∂(joint.1 : Measure (LowValue d×LowValue d)),x.2.1≤x.1.1
  value_surplus_gap : ∀ᵐx ∂(joint.1 : Measure (LowValue d×LowValue d)),
    x.1.1*(CommonList.iid categories N).prob (LocalUnderflow c 0)/4≤x.1.1-x.2.1
  bid_surplus_gap : ∀ᵐx ∂(joint.1 : Measure (LowValue d×LowValue d)),
    x.2.1*(CommonList.iid categories N).prob (LocalUnderflow c 0)/4≤x.1.1-x.2.1
  value_positive : ∀ᵐx ∂(joint.1 : Measure (LowValue d×LowValue d)),0<x.1.1
  bid_positive : ∀ᵐx ∂(joint.1 : Measure (LowValue d×LowValue d)),0<x.2.1
  real_atomless : NullSingletonClass (realLowBidLaw joint.1 : Measure ℝ)
  compact_atomless : NullSingletonClass
    (joint.1.map measurable_snd.aemeasurable : Measure (LowValue d))
  eps : ℕ→ℝ
  eps_pos : ∀j,0<eps j
  eps_small : ∀j,eps j≤1/2
  noisy : ℕ→Law (A:=unitInterval) mu
  eps_quarter : ∀j,eps j≤1/4
  eps_tendsto : Tendsto eps atTop (𝓝 0)
  noisy_IC : ∀j,∃sigma : Kernel (LowValue d) unitInterval,
    IsMarkovKernel sigma ∧ mu⊗ₘsigma=((noisy j).1 : Measure (LowValue d×unitInterval)) ∧
    ∀ᵐw ∂mu,∀ᵐq ∂sigma w,∀q' : unitInterval,
      noisyExpectedUtility (N:=N) d ξ (eps j) (eps_pos j) (eps_small j) c categories mu
        (noisy j,(w,q'))≤
      noisyExpectedUtility (N:=N) d ξ (eps j) (eps_pos j) (eps_small j) c categories mu
        (noisy j,(w,q))
  physical_tendsto : Tendsto
    (fun j=>(lowNoisyLaw d (eps j) (eps_pos j) (eps_small j) mu (noisy j)).1)
    atTop (𝓝 joint.1)

theorem exists_actual_atomless_low_limit {N : ℕ} {d ξ ell H : ℝ} (hd : 0≤d)
    (hξ : 0<ξ) (hξh : ξ≤1/2) (c : ℕ) (hc : 0<c)
    (s a h : ℝ) (hs : 0<s) (ha : 0≤a) (hh : 0≤h) (hsum : s+a+h=1)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (hell : 0<ell)
    (hellDef : ell=(CommonList.iid (categoryLaw s a h hs.le ha hh hsum Gref) (N+1)).prob
      (LocalUnderflow c 0))
    (hjoint : (CommonList.iid (categoryLaw s a h hs.le ha hh hsum Gref) (N+1)).prob
      (BothUnderflow c)≤ell/4)
    (hHe : (CommonList.iid (categoryLaw s a h hs.le ha hh hsum Gref) N).prob
      (BothUnderflow c)<H)
    (hboundary : ∀(G : Measure ℝ)(_hG : IsProbabilityMeasure G)(u : ℝ),
      H≤PiBinomial.pmf N (higherBidProbability s a h G u) (c-1))
    (hcoefficient : 8*(1-2*ξ)*(N+1:ℕ)*
      (CommonList.iid (categoryLaw s a h hs.le ha hh hsum Gref) N).prob (BothUnderflow c)/
      (ell*(H-(CommonList.iid (categoryLaw s a h hs.le ha hh hsum Gref) N).prob
        (BothUnderflow c)))<1/2)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] (hmu : ∀ᵐw ∂mu,0<w.1) :
    Nonempty (ActualAtomlessLowLimit (N+1) d ξ c
      (categoryLaw s a h hs.le ha hh hsum Gref) mu) := by
  let Cref:=categoryLaw s a h hs.le ha hh hsum Gref
  obtain ⟨pi0,hle,hvg,hbg,eps,heps,hsmall,pi,hquarter,heps0,hIC,hlim⟩:=
    exists_actual_supported_low_limit (N:=N+1) d hξ hξh c Cref mu
      (by simpa only [Cref,hellDef] using hjoint)
  have hpositive:=noisy_limit_no_positive_atoms hd hξ hξh c hc s a h hs ha hh hsum
    Gref hell hellDef hjoint hHe hboundary hcoefficient mu hmu eps heps hsmall pi pi0
    heps0 hlim hIC
  let e:=(CommonList.iid Cref N).prob (BothUnderflow c)
  have hbzero : ∀(G : Measure ℝ)(_hG : IsProbabilityMeasure G)(u : ℝ),
      H-e≤(Measure.pi (fun _ : Fin N=>rivalLaw s a h G)).real (firstCopyBoundary c u) := by
    intro G hG u
    letI:=hG
    have hb:=firstCopyBoundary_probability_lower s a h hs.le ha hh hsum G N c u
    rw [categoryLaw_eq_low_law s a h hs.le ha hh hsum G Gref] at hb
    exact (sub_le_sub_right (hboundary G hG u) e).trans hb
  have hzero:=noisy_limit_no_zero_atom hξ hξh c hc s a h hs ha hh hsum
    (sub_pos.mpr hHe) hbzero Gref mu hmu eps heps hsmall pi pi0 heps0 hlim hIC
  have hr:=realLowBidLaw_atomless_of_nonnegative_atoms pi0.1 hzero hpositive
  letI:=hr
  exact ⟨{
    joint:=pi0
    bid_le_value:=hle
    value_surplus_gap:=hvg
    bid_surplus_gap:=hbg
    value_positive:=law_value_positive mu pi0 hmu
    bid_positive:=joint_bid_positive_of_real_zero_atom pi0.1 hzero
    real_atomless:=hr
    compact_atomless:=compactBidLaw_atomless_of_real pi0.1
    eps:=eps
    eps_pos:=heps
    eps_small:=hsmall
    noisy:=pi
    eps_quarter:=hquarter
    eps_tendsto:=heps0
    noisy_IC:=hIC
    physical_tendsto:=hlim }⟩

theorem eventually_exists_actual_atomless_low_limit {d ξ : ℝ} (hd : 0≤d)
    (hξ : 0<ξ) (hξh : ξ≤1/2)
    (s a h : ℝ) (hs : 0<s) (ha : 0≤a) (hh : 0<h) (hsum : s+a+h=1)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (c : ℕ→ℕ) (ρ : ℝ) (hρ : 0<ρ) (hrank : ρ<a+h/2)
    (hc : Tendsto (fun m=>(c m:ℝ)/(m:ℝ)) atTop (𝓝 ρ))
    (hgap : 2*Ample.binaryKL ρ (1-h/2)<jointRate s a h ρ)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] (hmu : ∀ᵐw ∂mu,0<w.1) :
    ∀ᶠm : ℕ in atTop,Nonempty (ActualAtomlessLowLimit (m-1) d ξ (c m)
      (categoryLaw s a h hs.le ha hh.le hsum Gref) mu) := by
  have hg:=eventually_primitive_source_guards s a h hs ha hh hsum Gref c ρ (1-2*ξ)
    hρ hrank (by linarith) hc hgap
  filter_upwards [hg] with m hm
  obtain ⟨hm2,hcm,hL,hE,hD,hcoef,huniform⟩:=hm
  have hmN : m-2+1=m-1:=by omega
  have hf:=exists_actual_atomless_low_limit (N:=m-2) hd hξ hξh (c m) hcm
    s a h hs ha hh.le hsum Gref hL (by rw [hmN]) (by rw [hmN]; exact hD)
    hE (fun G hG u=>(huniform G hG u).1) (by rw [hmN]; exact hcoef) mu hmu
  simpa only [hmN] using hf

end FCAppendix.Affine.LowBody
