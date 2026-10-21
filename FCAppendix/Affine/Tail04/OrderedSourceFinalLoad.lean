import FCAppendix.Affine.Tail04.OrderedSourceAnalyticAdapter
import FCAppendix.Affine.Tail04.OrderedSourceFinalCountFamily
import FCAppendix.Affine.Tail04.OrderedOriginalNativeUnderfill

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourceFinalLoad
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation
open SourceAnalyticContract SourceMovingScalarGuards SourceTailNoisyFixedPoint
open OrderedSourceActiveCountData OrderedSourceFinalCountFamily SourceMenuPopulation

section Fixed

variable (S : SourceAnalyticContract.Parameters) {N : ℕ}
  (E : OrderedSourceAnalyticAdapter.Parameters.Envelope S N)

lemma capacity_eq : (E.market.D).c=Markets.capacity (N+1) := by
  change MenuError.iidCapacity (99/200) N=Markets.capacity (N+1)
  simp only [MenuError.iidCapacity,Markets.capacity,Nat.cast_add,Nat.cast_one]

lemma capacity_le_half : ((E.market.D).c:ℝ)≤((N+1:ℕ):ℝ)/2 := by
  rw [capacity_eq S E]
  exact Markets.capacity_le_half (N+1)

include E in
lemma actual_upper_mass_le : activeMass S.P.theta*S.P.zeta*powerTail S.P.M 10 (cutoff N)≤1/10 := by
  have hh:=(E.market).point.range.upper_mass_guard
  have hs : S.P.theta^2≤1/100 := by nlinarith [S.P.theta_pos,S.P.theta_small]
  dsimp [upperMass,Central.mixedR,Central.h] at hh
  nlinarith

theorem native_unused (j : Fin 2) :
    (∫ω,unusedCapacity (E.market.native S.low_gap) j ω ∂backgroundLaw (E.market.native S.low_gap))≤
      ((E.market.D).c:ℝ)*Real.exp (-((N+1:ℕ):ℝ)/50) := by
  exact OrderedOriginalNativeUnderfill.normalized_source_unused (OrderedNativeZeroNoiseSource.regions E.market.D S.P (E.market.forget.low_gap S.low_gap) E.market.H E.market.upper_gap) S.P rfl (cutoff N) (E.market.point.range.cutoff_gt_M).le
    (E.market).point.low.joint (OrderedNativeZeroNoiseSource.partialLaw (E.market.D) S.P (cutoff N) (E.market.point.range.cutoff_gt_M) (E.market).sequence.limit)
    (OrderedNativeZeroNoiseSource.active (E.market.D) S.P (cutoff N) (E.market.point.range.cutoff_gt_M) (E.market).sequence.limit)
    (E.market).upperBid (E.market).upperBid_measurable (E.market).upper_floor (N+1) (E.market.D).c
    (E.market.D).ξ (E.market.D).width (E.market.D).regimeShare (E.market.D).eA (E.market.D).eR (E.market.D).F (E.market.D).hξ (E.market.D).hξ1 (E.market.D).hw
    (E.market.D).regimeShare.2.1 (E.market.D).regimeShare.2.2 (by simpa only [Nat.cast_add,Nat.cast_one] using! E.market.forget.rare)
    (OrderedNativeZeroNoiseSource.base_duplicate_gap (E.market.D)) (E.market.D).eta (E.market.D).heta0 (E.market.D).heta1
    (by change (1-(1-2*S.ξ))/2=S.ξ;ring) S.low_gap
    (capacity_le_half S E) (actual_upper_mass_le S E) j

lemma fullySpecified_background : backgroundLaw E.fullySpecified=backgroundLaw (E.market.native S.low_gap) := by
  simp only [backgroundLaw,OrderedSourceUpperSpecified.userLaw_eq (E.market) S.low_gap S.width_small]
  rfl

lemma fullySpecified_unused_eq (j : Fin 2) (ω : Background (N+1) 2 NativeLocalPolicy.Seed) :
    unusedCapacity E.fullySpecified j ω=unusedCapacity (E.market.native S.low_gap) j ω := rfl

theorem fullySpecified_unused (j : Fin 2) :
    (∫ω,unusedCapacity E.fullySpecified j ω ∂backgroundLaw E.fullySpecified)≤
      ((E.market.D).c:ℝ)*Real.exp (-((N+1:ℕ):ℝ)/50) := by
  simp only [fullySpecified_background S E,fullySpecified_unused_eq S E]
  exact native_unused S E j

end Fixed

section Family

variable (S : SourceAnalyticContract.Parameters) (N : ℕ→ℕ) (hN : Tendsto N atTop atTop)
  (E : ∀j,OrderedSourceAnalyticAdapter.Parameters.Envelope S (N j))

include hN in
theorem load_tendsto :
    Tendsto (fun j=> finiteLoad (E j).fullySpecified) atTop (𝓝 (99/100:ℝ)) := by
  apply Markets.source_load_tendsto (fun j=> N j+1) (fun j=>(E j).market.D.c)
    (fun _=> NativeLocalPolicy.Seed) (fun j=>(E j).fullySpecified)
    (fun j=> Nat.succ_pos (N j))
    ((tendsto_add_atTop_nat 1).comp hN)
    (fun j=> capacity_le_half S (E j))
    (fun j p=> fullySpecified_unused S (E j) p)
    (fun j=> capacity_eq S (E j))

include hN in
theorem limit_load (lam : ℝ×ℝ) (hlam : lam∈S.Λ)
    (hls : Tendsto (fun j=> lambda (E j).market S.low_gap) atTop (𝓝 lam)) :
    (∫v,(OrderedSourceOriginalCountFamily.limitLaw S.P S.ξ S.ξ_pos lam v).load ∂valueLaw S.P)=99/100 := by
  have hc:=(OrderedSourceFinalCountFamily.aggregates S.P S.ξ S.Up S.u S.k S.width
    S.ξ_pos S.ξ_half S.u_pos.le S.partial_floor_lt S.partial_cap_lt_one S.width_pos
    S.low_gap S.width_small N hN E S.κ_pos
    (OrderedSourceAnalyticAdapter.Parameters.bulkDerivativeBound S)
    (OrderedSourceAnalyticAdapter.Parameters.derivativeGeometry S) lam hlam hls).2.1
  exact tendsto_nhds_unique hc (load_tendsto S N hN E)

end Family
end FCAppendix.Affine.Tail04.OrderedSourceFinalLoad
