import FCAppendix.Affine.LowBody.NoisyLimitIC
import FCAppendix.Affine.LowBody.NoisyAtomlessLimit

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Filter Topology
open Existence.Distributional

namespace ActualAtomlessLowLimit

theorem all_bid_IC {N : ℕ} {d ξ : ℝ} {c : ℕ} {categories : FiniteLaw (Fin 4)}
    {mu : Measure (LowValue d)} [IsProbabilityMeasure mu]
    (L : ActualAtomlessLowLimit N d ξ c categories mu) (hξ : 0<ξ) (hξh : ξ≤1/2) :
    ∀ᵐx ∂(L.joint.1 : Measure (LowValue d×LowValue d)),∀b : ℝ,0≤b→
      exactExpectedPayoff N d ξ c categories (L.joint.1.map measurable_snd.aemeasurable) (x.1.1,b)≤
        exactExpectedPayoff N d ξ c categories (L.joint.1.map measurable_snd.aemeasurable) (x.1.1,x.2.1) := by
  letI:=L.compact_atomless
  exact actual_noisy_limit_all_bid_IC hξ hξh c categories mu L.eps L.eps_pos L.eps_small
    L.eps_quarter L.eps_tendsto L.noisy L.joint L.noisy_IC L.physical_tendsto L.value_positive L.bid_positive

end ActualAtomlessLowLimit

theorem eventually_exists_actual_low_bid_equilibrium {d ξ : ℝ} (hd : 0≤d)
    (hξ : 0<ξ) (hξh : ξ≤1/2)
    (s a h : ℝ) (hs : 0<s) (ha : 0≤a) (hh : 0<h) (hsum : s+a+h=1)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (c : ℕ→ℕ) (rho : ℝ) (hrho : 0<rho) (hrank : rho<a+h/2)
    (hc : Tendsto (fun m=>(c m:ℝ)/(m:ℝ)) atTop (𝓝 rho))
    (hgap : 2*Ample.binaryKL rho (1-h/2)<jointRate s a h rho)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] (hmu : ∀ᵐw ∂mu,0<w.1) :
    ∀ᶠm : ℕ in atTop,
      ∃L : ActualAtomlessLowLimit (m-1) d ξ (c m)
          (categoryLaw s a h hs.le ha hh.le hsum Gref) mu,
        ∀ᵐx ∂(L.joint.1 : Measure (LowValue d×LowValue d)),∀b : ℝ,0≤b→
          exactExpectedPayoff (m-1) d ξ (c m) (categoryLaw s a h hs.le ha hh.le hsum Gref)
            (L.joint.1.map measurable_snd.aemeasurable) (x.1.1,b)≤
          exactExpectedPayoff (m-1) d ξ (c m) (categoryLaw s a h hs.le ha hh.le hsum Gref)
            (L.joint.1.map measurable_snd.aemeasurable) (x.1.1,x.2.1) := by
  filter_upwards [eventually_exists_actual_atomless_low_limit hd hξ hξh s a h hs ha hh hsum
    Gref c rho hrho hrank hc hgap mu hmu] with m hm
  obtain ⟨L⟩:=hm
  exact ⟨L,L.all_bid_IC hξ hξh⟩

end FCAppendix.Affine.LowBody
