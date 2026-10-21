import FCAppendix.AppendixRepair.GeneralLow.Implementation

noncomputable section
namespace FCAppendix.Appendix08.GeneralLow.SaturatedReceipts
open MeasureTheory ProbabilityTheory Game Bayes Set Filter
open HigherPolicy HigherPosterior HigherReceipts Continuation

variable {m c : ℕ}

theorem bothSaturated_other (C : Information.Classifier) (d κ : ℝ)
    (x : UserProfile m 2) (hx : x ∈ profiles C d κ) (j : Fin 2)
    (hs : BothSaturated C c (observe (drawsRealization x) j)) :
    BothSaturated C c (observe (drawsRealization x) (Affine.Hybrid.otherProposer j)) := by
  constructor
  · rw [opposite_high_card C d κ x hx j]
    exact hs.2
  · have he := opposite_high_card C d κ x hx (Affine.Hybrid.otherProposer j)
    rw [Affine.Hybrid.otherProposer_other] at he
    rw [← he]
    exact hs.1

theorem other_visible_high (C : Information.Classifier) (x : UserProfile m 2)
    (j : Fin 2) (L : LocalList m) (hx : observe (drawsRealization x) j = L)
    (i : Fin m) (hi : i ∈ highSet C L)
    (hp : observe (drawsRealization x) (Affine.Hybrid.otherProposer j) i ≠ none) :
    i ∈ highSet C (observe (drawsRealization x) (Affine.Hybrid.otherProposer j)) := by
  have ho : L i ≠ none := highSet_present C L i hi
  have hj : j ∈ (drawsRealization x).recipients i := by
    by_contra hn
    exact ho (by rw [← hx]; simp [observe, hn])
  have hk : Affine.Hybrid.otherProposer j ∈ (drawsRealization x).recipients i := by
    by_contra hn
    exact hp (by simp [observe, hn])
  have he : observe (drawsRealization x) (Affine.Hybrid.otherProposer j) i = L i := by
    rw [← hx]
    simp only [observe, if_pos hk, if_pos hj]
  apply (mem_highSet C _ i).mpr
  rw [he]
  exact (mem_highSet C L i).mp hi

theorem mean_eq_on_core (Γ : FiniteGame m 2 c unitInterval) (C : Information.Classifier)
    (d ξ R : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hR : 0 ≤ R) (hRC : C.label R = 2) (hdR : d < R)
    (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d (1-ξ))
    (H : HC Γ C d (1-ξ) R hfull) (j : Fin 2) (L : LocalList m)
    (hL : FeasibleObservedList j L) (hcomp : CompatibleList C d (1-ξ) L)
    (hcore : L ∈ Continuation.core Γ C d (1-ξ) R hfull H.selector j)
    (hsat : BothSaturated C c L) (i : Fin m) (hi : i ∈ highSet C L) :
    Affine.Hybrid.posteriorOtherMean
      (Implementation.game Γ C d ξ R hξ hξ1 hfull H)
      (Implementation.belief Γ C d ξ R hξ hξ1 hfull H) j L i =
    Affine.Hybrid.posteriorOtherMean (higherGame Γ C H.selector)
      (higherPosterior Γ C d (1-ξ) R hfull H.selector) j L i := by
  classical
  let Δ := Implementation.game Γ C d ξ R hξ hξ1 hfull H
  let Θ := higherGame Γ C H.selector
  let N := NormalizedContinuation.selector Γ C d (1-ξ) R hfull H.selector
  have hnot : L ∉ NormalizedContinuation.bad Γ C d (1-ξ) R hfull H.selector j :=
    fun h => h.2 hcore
  rw [Affine.Hybrid.posteriorOtherMean_eq_profile_integral,
    Affine.Hybrid.posteriorOtherMean_eq_profile_integral,
    Implementation.belief_eq_original Γ C d ξ R hξ hξ1 hfull H j L hnot]
  change (∫ x, ∫ z : Fin 2 → unitInterval, ((otherInclusionCount Δ j i (x,z)).val : ℝ)
      ∂Measure.pi (fun _ : Fin 2 => Γ.seedLaw)
      ∂(HigherPosterior.posterior Γ C d (1-ξ) R hfull).posterior j L) =
    ∫ x, ∫ z : Fin 2 → unitInterval, ((otherInclusionCount Θ j i (x,z)).val : ℝ)
      ∂Measure.pi (fun _ : Fin 2 => Γ.seedLaw)
      ∂(HigherPosterior.posterior Γ C d (1-ξ) R hfull).posterior j L
  apply integral_congr_ae
  filter_upwards [posterior_support Γ C d (1-ξ) R hR hRC hdR hfull j L hL hcomp,
    Continuation.core_posterior Γ C d (1-ξ) R hfull H.selector j L hcore] with x hx hgood
  let L' := observe (drawsRealization x) (Affine.Hybrid.otherProposer j)
  have hs' : BothSaturated C c L' := by
    apply bothSaturated_other C d (1-ξ) x hx.2 j
    simpa only [hx.1] using hsat
  have hg' : L' ∈ Continuation.core Γ C d (1-ξ) R hfull H.selector
      (Affine.Hybrid.otherProposer j) := hgood _
  have hc' : CompatibleList C d (1-ξ) L' := observe_compatible C d (1-ξ) x hx.2 _
  have hseed := NormalizedContinuation.select_ae_eq Γ C d (1-ξ) R hfull H.selector
    (Affine.Hybrid.otherProposer j) L' hg'
  have heval := (measurePreserving_eval (fun _ : Fin 2 => Γ.seedLaw)
    (Affine.Hybrid.otherProposer j)).quasiMeasurePreserving.ae hseed
  apply integral_congr_ae
  filter_upwards [heval] with z hz
  have he : (i ∈ allocation (drawsRealization x) Δ.policy z (Affine.Hybrid.otherProposer j)) ↔
      i ∈ allocation (drawsRealization x) Θ.policy z (Affine.Hybrid.otherProposer j) := by
    by_cases hp : L' i = none
    · have hnΔ : i ∉ allocation (drawsRealization x) Δ.policy z
          (Affine.Hybrid.otherProposer j) := by
        intro hin
        exact ((Δ.policy (Affine.Hybrid.otherProposer j) L'
          (z (Affine.Hybrid.otherProposer j))).property.2 i hin) hp
      have hnΘ : i ∉ allocation (drawsRealization x) Θ.policy z
          (Affine.Hybrid.otherProposer j) := by
        intro hin
        exact ((Θ.policy (Affine.Hybrid.otherProposer j) L'
          (z (Affine.Hybrid.otherProposer j))).property.2 i hin) hp
      simp only [hnΔ, hnΘ]
    · have hh := other_visible_high C x j L hx.1 i hi hp
      have hf := Implementation.policy_high_factors Γ C d ξ R hξ hξ1 hfull H
        (Affine.Hybrid.otherProposer j) L' hc' (z (Affine.Hybrid.otherProposer j)) i hh
      rw [highSelection_eq_HC C (1-ξ) c N _ _ _ hs'.1 hs'.2] at hf
      change (i ∈ (Δ.policy (Affine.Hybrid.otherProposer j) L'
        (z (Affine.Hybrid.otherProposer j))).val ↔
        i ∈ H.selector.select (Affine.Hybrid.otherProposer j) L'
          (z (Affine.Hybrid.otherProposer j)))
      change (i ∈ (Δ.policy (Affine.Hybrid.otherProposer j) L'
        (z (Affine.Hybrid.otherProposer j))).val ↔
        i ∈ NormalizedContinuation.select Γ C d (1-ξ) R hfull H.selector
          (Affine.Hybrid.otherProposer j) L' (z (Affine.Hybrid.otherProposer j))) at hf
      rwa [hz] at hf
  rw [Affine.Hybrid.otherInclusionCount_two, Affine.Hybrid.otherInclusionCount_two]
  simp only [he]

theorem high_receipt_eq_on_core (Γ : FiniteGame m 2 c unitInterval)
    (C : Information.Classifier) (d ξ R η : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hA : Γ.A = Schedule.affine 2 η hη0 hη1)
    (hR : 0 ≤ R) (hRC : C.label R = 2) (hdR : d < R)
    (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d (1-ξ))
    (H : HC Γ C d (1-ξ) R hfull) (j : Fin 2) (L : LocalList m)
    (hL : FeasibleObservedList j L) (hcomp : CompatibleList C d (1-ξ) L)
    (hcore : L ∈ Continuation.core Γ C d (1-ξ) R hfull H.selector j)
    (hsat : BothSaturated C c L) :
    (fun i => if i ∈ highSet C L then
      beliefReceipts Γ.A
        (posteriorCountBelief (Implementation.game Γ C d ξ R hξ hξ1 hfull H)
          (Implementation.belief Γ C d ξ R hξ hξ1 hfull H) j L) L i else 0) =
      highReceipt Γ C d (1-ξ) R hfull H.selector j L := by
  classical
  funext i
  by_cases hi : i ∈ highSet C L
  · simp only [highReceipt, if_pos hi]
    cases hb : L i with
    | none => simp only [beliefReceipts, hb]
    | some b =>
        simp only [beliefReceipts, hb]
        change Finite.conditionalReceipt
          (Implementation.game Γ C d ξ R hξ hξ1 hfull H).A
          (posteriorCountBelief (Implementation.game Γ C d ξ R hξ hξ1 hfull H)
            (Implementation.belief Γ C d ξ R hξ hξ1 hfull H) j L i) b =
          Finite.conditionalReceipt (higherGame Γ C H.selector).A
            (posteriorCountBelief (higherGame Γ C H.selector)
              (higherPosterior Γ C d (1-ξ) R hfull H.selector) j L i) b
        rw [Affine.Hybrid.posterior_affine_receipt
          (Implementation.game Γ C d ξ R hξ hξ1 hfull H)
          (Implementation.belief Γ C d ξ R hξ hξ1 hfull H) η hη0 hη1 hA j L i b,
          Affine.Hybrid.posterior_affine_receipt (higherGame Γ C H.selector)
            (higherPosterior Γ C d (1-ξ) R hfull H.selector) η hη0 hη1 hA j L i b,
          mean_eq_on_core Γ C d ξ R hξ hξ1 hR hRC hdR hfull H j L hL hcomp hcore hsat i hi]
  · simp only [highReceipt, if_neg hi]

end FCAppendix.Appendix08.GeneralLow.SaturatedReceipts
