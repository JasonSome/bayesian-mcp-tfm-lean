import FCAppendix.Affine.LowBody.NoisyZeroClusterEstimate
import FCAppendix.Affine.LowBody.ZeroClusterLimit

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Existence.Distributional
variable {N : ℕ}

theorem noisy_limit_no_zero_atom {d ξ H : ℝ} (hξ : 0<ξ) (hξh : ξ≤1/2)
    (c : ℕ) (hc : 0<c) (s a h : ℝ) (hs : 0<s) (ha : 0≤a) (hh : 0≤h) (hsum : s+a+h=1)
    (hH : 0<H)
    (hboundary : ∀(G : Measure ℝ)(_hG : IsProbabilityMeasure G)(u : ℝ),
      H≤(Measure.pi (fun _ : Fin N=>rivalLaw s a h G)).real (firstCopyBoundary c u))
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
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
    (realLowBidLaw pi0.1 : Measure ℝ) {0}=0 := by
  apply no_zero_atom_of_actual_cluster_estimates mu hmu
    (show 0<s*H/2 by positivity) (show (0:ℝ)≤8 by norm_num)
    eps heps hsmall pi pi0 heps0 hlim
  intro tau htau δ hδ hroom
  have hquarter : ∀ᶠj : ℕ in atTop,eps j≤1/4:=
    (heps0.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1/4))).mono (fun _ hj=>hj.le)
  have hcost : Tendsto (fun j=>eps j*d) atTop (𝓝 0):=by simpa using heps0.mul_const d
  have hnoise : ∀ᶠj : ℕ in atTop,eps j*d≤δ:=
    (hcost.eventually (Iio_mem_nhds hδ)).mono (fun _ hj=>hj.le)
  filter_upwards [hquarter,hnoise] with j hj hn
  obtain ⟨sigma,hsigma,hdis,hopt⟩:=hIC j
  letI:=hsigma
  have hfinite:=noisy_zero_cluster_quadratic (N:=N) (heps j) hj hδ hroom hn hξ hξh
    c hc s a h hs.le ha hh hsum Gref mu (pi j) hmu sigma hdis hopt
  let E:=zeroBaseClusterSet (d:=d) (heps j) (hsmall j) tau δ
  let p:=((pi j).1 : Measure (LowValue d×unitInterval)).real E
  let G:=(realLowBidLaw (lowNoisyLaw d (eps j) (heps j) (hsmall j) mu (pi j)).1 : Measure ℝ)
  let ν:=Measure.pi (fun _ : Fin N=>rivalLaw s a h G)
  change (tau-2*δ)*s*p^2*ν.real (firstCopyBoundary c (2*δ))/2≤8*δ*p at hfinite
  change p^2*((tau-2*δ)*(s*H/2))≤p*(8*δ)
  have hb:=hboundary G inferInstance (2*δ)
  have hcoef : 0≤(tau-2*δ)*s*p^2/2:=by
    have ht : 0≤tau-2*δ:=by linarith
    positivity
  calc
    _=((tau-2*δ)*s*p^2/2)*H:=by ring
    _≤((tau-2*δ)*s*p^2/2)*ν.real (firstCopyBoundary c (2*δ)):=
      mul_le_mul_of_nonneg_left hb hcoef
    _=(tau-2*δ)*s*p^2*ν.real (firstCopyBoundary c (2*δ))/2:=by ring
    _≤8*δ*p:=hfinite
    _=p*(8*δ):=by ring

end FCAppendix.Affine.LowBody
