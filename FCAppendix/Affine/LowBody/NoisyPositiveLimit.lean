import FCAppendix.Affine.LowBody.NoisyPositiveClusterEstimate
import FCAppendix.Affine.LowBody.PositiveClusterLimit

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Existence.Distributional
variable {N : ℕ}

theorem noisy_limit_no_positive_atoms {d ξ ell H : ℝ} (hd : 0≤d)
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
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] (hmu : ∀ᵐw ∂mu,0<w.1)
    (eps : ℕ→ℝ) (heps : ∀j,0<eps j) (hsmall : ∀j,eps j≤1/2)
    (pi : ℕ→Law (A:=unitInterval) mu) (pi0 : Law (A:=LowValue d) mu)
    (heps0 : Tendsto eps atTop (𝓝 0))
    (hlim : Tendsto (fun j=>(lowNoisyLaw d (eps j) (heps j) (hsmall j) mu (pi j)).1)
      atTop (𝓝 pi0.1))
    (hIC : ∀j,∃sigma : Kernel (LowValue d) unitInterval,
      IsMarkovKernel sigma ∧ mu⊗ₘsigma=((pi j).1 : Measure (LowValue d×unitInterval)) ∧
      ∀ᵐw ∂mu,∀ᵐq ∂sigma w,∀q' : unitInterval,
        noisyExpectedUtility (N:=N+1) d ξ (eps j) (heps j) (hsmall j) c
          (categoryLaw s a h hs.le ha hh hsum Gref) mu (pi j,(w,q'))≤
        noisyExpectedUtility (N:=N+1) d ξ (eps j) (heps j) (hsmall j) c
          (categoryLaw s a h hs.le ha hh hsum Gref) mu (pi j,(w,q))) :
    ∀b : ℝ,0<b→(realLowBidLaw pi0.1 : Measure ℝ) {b}=0 := by
  let e:=(CommonList.iid (categoryLaw s a h hs.le ha hh hsum Gref) N).prob (BothUnderflow c)
  let A:=s*ell*(H-e)/8
  let D:=(1-2*ξ)*(N+1:ℕ)*s*e
  let C:=4+8*(1-ξ)
  let L:=d*s*(H-e)/2
  let Gj : ℕ→ProbabilityMeasure ℝ:=fun j=>realLowBidLaw
    (lowNoisyLaw d (eps j) (heps j) (hsmall j) mu (pi j)).1
  let Hj : ℕ→ProbabilityMeasure ℝ:=fun j=>baseBidLaw d (eps j) (heps j) (hsmall j) mu (pi j)
  have he : 0≤e:=(CommonList.iid (categoryLaw s a h hs.le ha hh hsum Gref) N).prob_nonneg _
  have hdiff : 0<H-e:=sub_pos.mpr hHe
  have hA : 0<A:=by dsimp [A]; positivity
  have hD : 0≤D:=by
    have hη : 0≤1-2*ξ:=by linarith
    dsimp [D]
    positivity
  have hC : 0≤C:=by dsimp [C]; linarith
  have hsmallC : D/A<1/2 := by
    have heq : D/A=8*(1-2*ξ)*(N+1:ℕ)*e/(ell*(H-e)) := by
      dsimp [D,A]
      field_simp
    rw [heq]
    exact hcoefficient
  have hHj : Tendsto Hj atTop (𝓝 (realLowBidLaw pi0.1)):=
    baseBidLaw_tendsto mu eps heps hsmall pi pi0 heps0 hlim
  have hGj : Tendsto Gj atTop (𝓝 (realLowBidLaw pi0.1)):=
    (continuous_realLowBidLaw d).continuousAt.tendsto.comp hlim
  apply no_positive_atoms_of_actual_cluster_estimates (κ:=1-ξ) (A:=A) (D:=D) (C:=C) (L:=L)
    Hj Gj (realLowBidLaw pi0.1)
    hHj hGj (show 0<1-ξ by linarith) hA hD hC hsmallC eps heps0
  intro b hb err herr
  obtain ⟨R,hR,hfinite⟩:=noisy_positive_cluster_quadratic_uniform (N:=N) d hd hξ hξh b hb err herr
  let cap:=b*ell/(8*(ell+12))
  have hcap : 0<cap:=by dsimp [cap]; positivity
  refine ⟨min R cap,lt_min hR hcap,?_⟩
  intro δ hδ hδb hδmax
  have hδR : δ<R:=hδmax.trans_le (min_le_left _ _)
  have hδcap : δ<cap:=hδmax.trans_le (min_le_right _ _)
  have hmargin : 0<(b-δ)*ell/4-3*δ := by
    have hm:=(lt_div_iff₀ (by positivity : 0<8*(ell+12))).mp hδcap
    have hmul:=mul_pos hδ hell
    nlinarith
  have hquarter : ∀ᶠj : ℕ in atTop,eps j≤1/4:=
    (heps0.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1/4))).mono (fun _ hj=>hj.le)
  have hcost : Tendsto (fun j=>eps j*d) atTop (𝓝 0):=by simpa using heps0.mul_const d
  filter_upwards [hquarter,hcost.eventually (Iio_mem_nhds hδ),
    hcost.eventually (Iio_mem_nhds hmargin)] with j hj hn hm
  obtain ⟨sigma,hsigma,hdis,hopt⟩:=hIC j
  letI:=hsigma
  have hf:=hfinite δ hδ hδb hδR (eps j) (heps j) hj hn ell hell.le
    (by linarith) c hc s a h hs.le ha hh hsum Gref inferInstance mu inferInstance
    (pi j) hmu sigma inferInstance hdis hopt hellDef hjoint H
    (hboundary (Gj j : Measure ℝ) inferInstance (b+δ+eps j*d))
  dsimp only at hf
  rw [baseClusterSet_mass] at hf
  convert hf using 1 <;> dsimp only [Hj,Gj,A,D,C,L,e] <;> first | rfl | ring

end FCAppendix.Affine.LowBody
