import FCAppendix.Affine.Tail04.OrderedNativePosteriorMeans
import FCAppendix.Finite.NoOverbidAE

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedNativeBayesianReceipts
open MeasureTheory ProbabilityTheory Set Classical Filter Game Bayes
open LocalCoordinates SortedCoordinates NativeLocalPolicy NativeObservationPair
open OrderedNativePosteriorMeans OriginalValues OriginalPopulation OriginalPrivateSource
open Existence.Distributional Hybrid

variable {m c : ℕ} (D : Data m c) (P : ValueParameters) (hd : D.E.d=P.d0)
    (t : ℝ) (ht : P.M≤ t)
local instance : IsProbabilityMeasure (P.originalMovingActiveLaw t ht) :=
  P.originalMovingActiveLaw_probability t ht
variable (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
    (πP : Law (A:=Icc D.E.R D.E.Rp) P.originalPartialLaw)
    (πA : Law (A:=Icc (1:ℝ) D.E.U) (P.originalMovingActiveLaw t ht))
    (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)
    (hfloor : ∀ v,t< v → D.E.H≤ upperBid v)
    (hrows : ∀ H : Fin (m+1),D.originalPrivateRow H=
      originalPrivateRow D.E P hd t ht πL πP πA upperBid hupperBid hfloor H.val)
    (Γ : FiniteGame m 2 c Seed)
    (hjoint : Γ.F ⊗ₘ Γ.σ=(originalJoint P t ht D.E.R D.E.Rp D.E.U
      (D.E.d_nonneg.trans D.E.d_lt_R.le) πL πP πA upperBid hupperBid : Measure _))
    (hseed : Γ.seedLaw=seedLaw)
    (hpolicy : ∀ j,Γ.policy j=OrderedNativePolicy.policy D j)
    (B : PosteriorSystem Γ)
    (η : ℝ) (hη0 : 0≤ η) (hη1 : η≤1)
    (hA : Γ.A=Schedule.affine 2 η hη0 hη1) (hξ : (1-η)/2=D.ξ)

lemma opposite_low_acceptance_label_independent (j k : Fin 2) (L : LocalList m) (i : Fin m) :
    NativeExactLow.acceptance D.ξ D.xi_pos D.xi_lt_one c (otherProposer j)
      (D.E.lowContext j L) i =
    NativeExactLow.acceptance D.ξ D.xi_pos D.xi_lt_one c (otherProposer k)
      (D.E.lowContext k L) i := by
  have hs (u : unitInterval) :
      NativeExactLow.select D.ξ D.xi_pos D.xi_lt_one c (otherProposer j) (D.E.lowContext j L) u =
      NativeExactLow.select D.ξ D.xi_pos D.xi_lt_one c (otherProposer k) (D.E.lowContext k L) u := by
    have hj : j = 0 ∨ j = 1 := by omega
    have hk : k = 0 ∨ k = 1 := by omega
    rcases hj with rfl | rfl <;> rcases hk with rfl | rfl <;>
      simp [NativeExactLow.select,NativeContinuation.residual,
        Observable.Regions.lowContext,Observable.Regions.context,contextUpper,otherProposer]
  unfold NativeExactLow.acceptance
  simp_rw [hs]

include P hd t ht πL πP πA upperBid hupperBid hfloor hrows hjoint hseed hpolicy η hη0 hη1 hA hξ in
theorem original_receipt_vector (j : Fin 2) :
    ∀ᵐ L ∂observedListLaw Γ j,
      NonnegativeList L ∧ D.offCommon L=∅ ∧
      beliefReceipts Γ.A (posteriorCountBelief Γ B j L) L=D.completedNumericalReceipt (OrderedNativePolicy.role D.E j L) L := by
  filter_upwards [original_means D P hd t ht πL πP πA upperBid hupperBid hfloor
    hrows Γ hjoint hseed hpolicy B j] with L hL
  refine ⟨hL.1,hL.2.1,?_⟩
  rw [D.completedNumericalReceipt_on_menu (OrderedNativePolicy.role D.E j L) L hL.2.1]
  funext i
  cases he : L i with
  | none => simp [beliefReceipts,he,D.numericalReceipt_absent (OrderedNativePolicy.role D.E j L) L i he]
  | some b =>
    have ha := posterior_affine_receipt Γ B η hη0 hη1 hA j L i b
    rw [hξ] at ha
    simp only [beliefReceipts,he]
    rw [ha]
    generalize hh : D.E.localTag (L i)=k
    have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk with rfl | rfl | rfl | rfl
    · rw [hL.2.2.2.1 i hh,
        opposite_low_acceptance_label_independent D j (OrderedNativePolicy.role D.E j L) L i]
      simpa only [he,entryBid] using (D.numericalReceipt_low_formula (OrderedNativePolicy.role D.E j L) L i hh).symm
    · have hi : i∈ids D.E 1 L := by simp [ids,hh]
      have hb := (D.offCommon_eq_empty_iff L).mp hL.2.1 i hh
      rw [hL.2.2.2.2 i hi]
      simpa only [he,entryBid] using (D.numericalReceipt_active (OrderedNativePolicy.role D.E j L) L i hi hb).symm
    · have hi : i∈ids D.E 2 L := by simp [ids,hh]
      rw [hL.2.2.1 i hh]
      simpa only [he,entryBid,mul_zero,sub_zero,mul_one] using
        (D.numericalReceipt_private (OrderedNativePolicy.role D.E j L) L i hi).symm
    · have hn := (D.E.localTag_absent (L i)).mp hh
      simp [he] at hn

include P hd t ht πL πP πA upperBid hupperBid hfloor hrows hjoint hseed hpolicy η hη0 hη1 hA hξ in
theorem original_proposer_onPath (hlow : D.E.d<1-D.ξ) (j : Fin 2) :
    ∀ᵐ L ∂observedListLaw Γ j,∀ u : Seed,
      Finite.Optimal c (beliefReceipts Γ.A (posteriorCountBelief Γ B j L) L)
        ((Γ.policy j L u).val) := by
  filter_upwards [original_receipt_vector D P hd t ht πL πP πA upperBid hupperBid hfloor
    hrows Γ hjoint hseed hpolicy B η hη0 hη1 hA hξ j] with L hL
  intro u
  rw [hL.2.2,hpolicy j]
  exact OrderedNativePolicy.numerical_optimal D hlow j L hL.1 u

include P hd t ht πL πP πA upperBid hupperBid hfloor hrows hjoint hseed hpolicy B η hη0 hη1 hA hξ in
theorem original_rationalOnPath (hlow : D.E.d<1-D.ξ) (j : Fin 2) :
    ProposerRationalOnPath Γ j := by
  refine ⟨posteriorCountBelief Γ B j,?_⟩
  filter_upwards [original_proposer_onPath D P hd t ht πL πP πA upperBid hupperBid hfloor
    hrows Γ hjoint hseed hpolicy B η hη0 hη1 hA hξ hlow j] with L hL
  exact ae_of_all _ hL

end FCAppendix.Affine.Tail04.OrderedNativeBayesianReceipts
