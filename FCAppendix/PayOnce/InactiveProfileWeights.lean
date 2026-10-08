import FCAppendix.PayOnce.DummyJointDerivative
import FCAppendix.PayOnce.DummyProfileWeights
import FCAppendix.PayOnce.EffectiveFocalTransport

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Filter Topology Set Game
open PayOnce PayOnce.DummyKernel PayOnce.RareSuccessSlope PayOnce.OwnImpact PayOnce.CompactifiedBidLaws
open scoped ProbabilityTheory BigOperators
variable {m n c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def dummyProfileMarginal (_Γ : FiniteGame m n c Seed) (hn : 2 ≤ n)
    (d : UserProfile m n) (i : Fin m) : ℝ :=
  profileMarginal n c hn (fun j => effectiveBid (d j).1.2) i

theorem measurable_dummyProfileMarginal (Γ : FiniteGame m n c Seed) (hn : 2 ≤ n) (i : Fin m) :
    Measurable (fun d => dummyProfileMarginal Γ hn d i) :=
  (measurable_allocation_joint hn).comp (effectiveFocalBid_rivals_measurePreserving Γ i).measurable

theorem dummyProfileMarginal_bounds (Γ : FiniteGame m n c Seed) (hn : 2 ≤ n)
    (d : UserProfile m n) (i : Fin m) : dummyProfileMarginal Γ hn d i ∈ Icc (0:ℝ) 1 :=
  profileMarginal_bounds hn _ i

theorem exists_dummy_profile_weights (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hatom : ∀ b : ℝ, 0 < b → (BidScaling.realBidLaw Γ : Measure ℝ) {b} = 0) :
    let hn : 2 ≤ k+1 := by omega
    let p := dummyProfileMarginal Γ hn
    ∃ weight : (i : Fin m) → ℝ × (Rival i → ℝ) → ℝ,
      (∀ i, Measurable (weight i)) ∧
      (∀ i z, weight i z ∈ Icc (0:ℝ) 1) ∧
      (∀ i z, 1/(((k+1:ℕ):ℝ)^3+1) ≤ 1-weight i z) ∧
      (∀ i, ∀ᵐ b ∂(BidScaling.realBidLaw Γ : Measure ℝ), 0 < b →
        HasDerivAt (coverage (k+1) c hn
          (Measure.pi fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ)))
          ((∫ r, weightedSlope (k+1) (allocation (k+1) c hn r b)
            (weight i (b,r)) ∂Measure.pi (fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ)))/b) b) ∧
      (∀ᵐ d ∂userProfileLaw Γ, ∀ i, 0 < effectiveBid (d i).1.2 →
        effectiveBid (d i).1.2*deriv (fun x => success (k+1)
          (allocation (k+1) c hn (effectiveRivalBids i d) x)) (effectiveBid (d i).1.2) =
          weightedSlope (k+1) (p d i) (weight i (effectiveBid (d i).1.2,effectiveRivalBids i d))) ∧
      (∀ᵐ d ∂userProfileLaw Γ,
        ∑ i ∈ interiorSet (p d), weight i (effectiveBid (d i).1.2,effectiveRivalBids i d) ≤ 1) := by
  classical
  dsimp only
  let hn : 2 ≤ k+1 := by omega
  let p := dummyProfileMarginal Γ hn
  choose weight hw hwb hwgap he hd using fun i : Fin m =>
    exists_joint_measurable_weight (ι := Rival i) (c := c) (BidScaling.realBidLaw Γ : Measure ℝ) hatom hn
  have hnorm : ∀ᵐ d ∂userProfileLaw Γ, ∀ i, 0 < effectiveBid (d i).1.2 →
      effectiveBid (d i).1.2*deriv (fun x => success (k+1)
        (allocation (k+1) c hn (effectiveRivalBids i d) x)) (effectiveBid (d i).1.2) =
        weightedSlope (k+1) (p d i) (weight i (effectiveBid (d i).1.2,effectiveRivalBids i d)) := by
    apply ae_all_iff.mpr
    intro i
    exact (effectiveFocalBid_rivals_measurePreserving Γ i).quasiMeasurePreserving.ae (he i)
  refine ⟨weight,hw,hwb,hwgap,hd,hnorm,?_⟩
  have hreg := (effectiveBid_profile_measurePreserving Γ).quasiMeasurePreserving.ae
    (DummyNullClipping.ae_regularRoot (ι := Fin m) (c := c) (BidScaling.realBidLaw Γ : Measure ℝ) hatom hn)
  filter_upwards [hnorm,hreg] with d hnorm hdreg
  obtain ⟨L,hL,hcap,hclip0,hclip1⟩ := hdreg
  let bids := fun i : Fin m => effectiveBid (d i).1.2
  have hp (i : Fin m) : p d i = CommonList.kernel (k+1) (bids i) L :=
    profileMarginal_eq_kernel hn bids hL hcap i
  have hpeq : p d = fun i => CommonList.kernel (k+1) (bids i) L := funext hp
  have hsum : (∑ i ∈ interiorSet (p d), weight i (effectiveBid (d i).1.2,effectiveRivalBids i d)) =
      ∑ i ∈ interiorSet (p d), impactWeight (k+1) bids (p d) i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hip : CommonList.kernel (k+1) (bids i) L ∈ Ioo (0:ℝ) 1 := by
      simpa only [interiorSet,Finset.mem_filter,Finset.mem_univ,true_and,hp i,mem_Ioo] using hi
    have hbi : 0 < bids i := by
      by_contra hh
      have hz := CommonList.kernel_of_le (k+1) ((le_of_not_gt hh).trans hL.le)
      linarith [hip.1]
    rw [hpeq]
    apply DummyKernel.weight_eq_impactWeight_of_derivative hn bids hL hcap i hip hclip0 hclip1
    rw [← hp i]
    exact hnorm i hbi
  rw [hsum]
  exact sum_impactWeight_le_one (k+1) bids (p d)

end FCAppendix.Bayes
