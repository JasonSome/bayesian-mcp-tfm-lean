import FCAppendix.AppendixRepair.GeneralLow.Implementation

noncomputable section
namespace FCAppendix.Appendix08.GeneralLow.LowReceipts
open MeasureTheory ProbabilityTheory Game Bayes Set Filter
open HigherPosterior HigherPolicy HigherReceipts
open FCAppendix.AppendixRepair.GeneralLow
open scoped BigOperators

variable {m c : ℕ}

def LowFactors (Γ : FiniteGame m 2 c unitInterval) (C : Information.Classifier)
    (d ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1) : Prop :=
  ∀ j L, CompatibleList C d (1-ξ) L → ∀ z i, Information.tag C (L i) = 0 →
    (i ∈ (Γ.policy j L z).val ↔ i ∈ DirectGame.lowSelect C ξ hξ hξ1 c L z)

theorem low_mean (Γ : FiniteGame m 2 c unitInterval) (B : PosteriorSystem Γ)
    (hseed : Γ.seedLaw = volume) (C : Information.Classifier) (d ξ : ℝ)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hfactor : LowFactors Γ C d ξ hξ hξ1)
    (j : Fin 2) (L : LocalList m)
    (hsupport : ∀ᵐ x ∂B.posterior j L,
      observe (drawsRealization x) j = L ∧ x ∈ profiles C d (1-ξ))
    (i : Fin m) (b : ℝ) (hi : L i = some b) (hb : C.label b = 0) :
    Affine.Hybrid.posteriorOtherMean Γ B j L i =
      ExactLow.acceptance ξ hξ hξ1 (Information.part C 0 L)
        (Information.otherResidual C c L) (Information.ownResidual C c L) i := by
  classical
  rw [Affine.Hybrid.posteriorOtherMean_eq_profile_integral]
  have hstat : ∀ᵐ x ∂B.posterior j L,
      (∫ z : Fin 2 → unitInterval, ((otherInclusionCount Γ j i (x,z)).val : ℝ)
        ∂Measure.pi (fun _ : Fin 2 => Γ.seedLaw)) =
      ExactLow.acceptance ξ hξ hξ1 (Information.part C 0 L)
        (Information.otherResidual C c L) (Information.ownResidual C c L) i := by
    filter_upwards [hsupport] with x hx
    have ho : observe (drawsRealization x) j i = some b := by rw [hx.1, hi]
    have hbid := listed_bid x j i b ho
    have hr : (x i).1.2.routeCount = 2 := by
      simpa only [hbid, hb, show (0 : Fin 3) ≠ 2 by decide, if_false] using (hx.2 i).2
    have hv : observe (drawsRealization x) (Affine.Hybrid.otherProposer j) i = some b := by
      simp [observe, drawsRealization, hr, Affine.Hybrid.firstK_full_two, hbid]
    have ht : Information.tag C (observe (drawsRealization x)
        (Affine.Hybrid.otherProposer j) i) = 0 := by
      simp [hv, Information.tag, hb]
    obtain ⟨hlow, hown, hother⟩ := decoded_low_opposite C c d (1-ξ) x hx.2 j
    rw [hx.1] at hlow hown hother
    have heq (z : Fin 2 → unitInterval) : ((otherInclusionCount Γ j i (x,z)).val : ℝ) =
        if i ∈ ExactLow.select ξ hξ hξ1 (Information.part C 0 L)
          (Information.otherResidual C c L) (Information.ownResidual C c L)
          (z (Affine.Hybrid.otherProposer j)) then 1 else 0 := by
      have hf := hfactor (Affine.Hybrid.otherProposer j)
        (observe (drawsRealization x) (Affine.Hybrid.otherProposer j))
        (observe_compatible C d (1-ξ) x hx.2 _) (z (Affine.Hybrid.otherProposer j)) i ht
      simp only [DirectGame.lowSelect, hlow, hown, hother] at hf
      rw [Affine.Hybrid.otherInclusionCount_two]
      simp only [allocation, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, hf]
    rw [integral_congr_ae (Eventually.of_forall heq)]
    let f : unitInterval → ℝ := fun z =>
      if i ∈ ExactLow.select ξ hξ hξ1 (Information.part C 0 L)
        (Information.otherResidual C c L) (Information.ownResidual C c L) z
      then 1 else 0
    have hm : Measurable f := Measurable.ite
      ((ExactLow.measurable_select ξ hξ hξ1
        (fun _ : unitInterval => Information.part C 0 L) measurable_const
        (fun _ => Information.otherResidual C c L)
        (fun _ => Information.ownResidual C c L) measurable_const measurable_const
        id measurable_id) (MeasurableSet.of_discrete :
          MeasurableSet {S : Finset (Fin m) | i ∈ S})) measurable_const measurable_const
    have hp := measurePreserving_eval (fun _ : Fin 2 => Γ.seedLaw)
      (Affine.Hybrid.otherProposer j)
    change (∫ z : Fin 2 → unitInterval, f (z (Affine.Hybrid.otherProposer j))
      ∂Measure.pi (fun _ : Fin 2 => Γ.seedLaw)) = ∫ z, f z
    calc
      _ = ∫ z, f z ∂(Measure.pi (fun _ : Fin 2 => Γ.seedLaw)).map
          (fun z => z (Affine.Hybrid.otherProposer j)) :=
        (integral_map hp.measurable.aemeasurable hm.aestronglyMeasurable).symm
      _ = ∫ z, f z ∂Γ.seedLaw := by rw [hp.map_eq]
      _ = _ := by rw [hseed]
  rw [integral_congr_ae hstat]
  simp

theorem low_receipt (Γ : FiniteGame m 2 c unitInterval) (B : PosteriorSystem Γ)
    (hseed : Γ.seedLaw = volume) (C : Information.Classifier) (d ξ η : ℝ)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hA : Γ.A = Schedule.affine 2 η hη0 hη1) (hξeq : ξ = (1-η)/2)
    (hfactor : LowFactors Γ C d ξ hξ hξ1) (j : Fin 2) (L : LocalList m)
    (hsupport : ∀ᵐ x ∂B.posterior j L,
      observe (drawsRealization x) j = L ∧ x ∈ profiles C d (1-ξ))
    (i : Fin m) (b : ℝ) (hi : L i = some b) (hb : C.label b = 0) :
    Finite.conditionalReceipt Γ.A (posteriorCountBelief Γ B j L i) b =
      ExactLow.receipt ξ hξ hξ1 (Information.part C 0 L)
        (Information.ownResidual C c L) (Information.otherResidual C c L) i := by
  rw [Affine.Hybrid.posterior_affine_receipt Γ B η hη0 hη1 hA,
    low_mean Γ B hseed C d ξ hξ hξ1 hfactor j L hsupport i b hi hb, ← hξeq]
  simp [ExactLow.receipt, Information.part, hi, Information.tag, hb,
    Existence.PayOnceBounded.listBids]

theorem implementation_low_factors (Γ : FiniteGame m 2 c unitInterval)
    (C : Information.Classifier) (d ξ R : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d (1-ξ))
    (H : Continuation.HC Γ C d (1-ξ) R hfull) :
    LowFactors (Implementation.game Γ C d ξ R hξ hξ1 hfull H) C d ξ hξ hξ1 := by
  intro j L hL z i hi
  exact Implementation.policy_low_membership Γ C d ξ R hξ hξ1 hfull H j L z i hL hi

end FCAppendix.Appendix08.GeneralLow.LowReceipts
