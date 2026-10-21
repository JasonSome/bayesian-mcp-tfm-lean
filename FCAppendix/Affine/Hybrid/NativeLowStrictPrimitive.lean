import FCAppendix.Affine.Hybrid.NativeLowStrict

set_option maxHeartbeats 2200000
noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Set Game Bayes LowBody Filter Topology Classical
open Existence.Distributional

theorem eventually_exists_native_low_population_strict (d U η : ℝ) (hd:0 ≤ d) (hdU:d ≤ U)
    (hη0:0 ≤ η) (hη1:η<1)
    (s a h : ℝ) (hs:0<s) (ha:0 ≤ a) (hh:0<h) (hsum:s+a+h=1)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (c : ℕ→ℕ) (rho : ℝ) (hrho:0<rho) (hrank:rho<a+h/2)
    (hc:Tendsto (fun m=>(c m:ℝ)/(m:ℝ)) atTop (𝓝 rho))
    (hgap:2*Ample.binaryKL rho (1-h/2)<jointRate s a h rho)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] (hmu:∀ᵐw ∂mu,0<w.1)
    (PA PH : ProbabilityMeasure (ℝ×JointAction 2))
    (hactive:∀ᵐx ∂(PA : Measure (ℝ×JointAction 2)),d<((1+η)/2)*x.2.bid ∧
      x.2.bid ≤ U ∧ x.2.routeCount=2)
    (hupper:∀ᵐx ∂(PH : Measure (ℝ×JointAction 2)),U<x.2.bid ∧ x.2.routeCount=1) :
    ∀ᶠm : ℕ in atTop,
      ∃L : ActualAtomlessLowLimit (m-1) d ((1-η)/2) (c m)
          (categoryLaw s a h hs.le ha hh.le hsum Gref) mu,
        let P:=populationLaw s a h hs.le ha hh.le hsum (lowJoint mu L.joint) PA PH
        let Gamma:=PopulationGame.game m (c m) P η hη0 hη1 U
        2 < m ∧
          Gamma.F⊗ₘGamma.σ=populationJoint s a h (lowJoint mu L.joint) PA PH ∧
          (∀ᵐx ∂(L.joint.1 : Measure (LowValue d×LowValue d)),0<x.2.1 ∧ x.2.1 ≤ x.1.1) ∧
          (∀b : ℝ,(realLowBidLaw L.joint.1 : Measure ℝ) {b}=0) ∧
          ∀i : Fin m,∀ᵐx ∂(lowJoint mu L.joint : Measure (ℝ×JointAction 2)),
            (problem Gamma i).BestResponse x.1 x.2 ∧
              ∀act : JointAction 2,act.routeCount=1 →
                (problem Gamma i).payoff x.1 act<(problem Gamma i).payoff x.1 x.2:=by
  have hbase:=eventually_exists_native_low_population d U η hd hdU hη0 hη1 s a h hs ha hh hsum
    Gref c rho hrho hrank hc hgap mu hmu PA PH hactive hupper
  have hguards:=eventually_primitive_source_guards s a h hs ha hh hsum Gref c rho η hrho hrank hη0 hc hgap
  filter_upwards [hbase,hguards] with m hmBase hmG
  obtain ⟨L,hm2,hjoint,_⟩:=hmBase
  rcases hmG with ⟨_,_,hell,_,hsmall,_,_⟩
  obtain ⟨k,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : m≠0)
  refine ⟨L,hm2,hjoint,?_,?_,?_⟩
  · filter_upwards [L.bid_positive,L.bid_le_value] with x hp hle
    exact ⟨hp,hle⟩
  · letI:=L.real_atomless
    intro b
    exact measure_singleton b
  · intro i
    exact population_low_actual_strict_one_route hd hdU s a h hs.le ha hh.le hsum Gref mu hη0 hη1
      L PA PH hactive hupper hell hsmall i

end FCAppendix.Affine.Hybrid
