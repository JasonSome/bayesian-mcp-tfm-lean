import FCAppendix.AppendixRepair.GeneralLow.DirectGame
import FCAppendix.AppendixRepair.GeneralLow.Population

noncomputable section
namespace FCAppendix.Appendix08.GeneralLow
open MeasureTheory ProbabilityTheory Set Game Bayes
open Affine Affine.LowBody Affine.Hybrid Existence.Distributional
open HigherPolicy HigherPosterior

variable {d κ : ℝ}

theorem lowJoint_actionCompatible (B : BidClasses d)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A := LowValue d) mu) :
    ∀ᵐ x ∂(lowJoint mu pi : Measure (ℝ × JointAction 2)),
      ActionCompatible B.classifier d κ x.2 := by
  change ∀ᵐ x ∂(pi.1 : Measure (LowValue d × LowValue d)).map
    (fun x => (x.1.1, lowBroadcast x.2)), _
  apply (measurableEmbedding_lowJointPoint d).ae_map_iff.mpr
  apply ae_of_all
  intro x
  have hl := B.classifier_low_bid x.2.property.1 x.2.property.2
  simp [ActionCompatible, BidCompatible, lowBroadcast, hl, x.2.property.2]

theorem population_actionCompatible (B : BidClasses d) (H : HigherLaws B)
    (hA : ∀ b ∈ B.activeSet, d < κ * b)
    (hP : ∀ b ∈ B.privateSet, d < b)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s + a + h = 1)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A := LowValue d) mu) :
    ∀ᵐ x ∂(populationLaw s a h hs ha hh hsum (lowJoint mu pi)
      H.active H.privateLaw : Measure (ℝ × JointAction 2)),
      ActionCompatible B.classifier d κ x.2 := by
  have hl := lowJoint_actionCompatible (κ := κ) B mu pi
  have hac : ∀ᵐ x ∂(H.active : Measure (ℝ × JointAction 2)),
      ActionCompatible B.classifier d κ x.2 := by
    filter_upwards [H.active_support] with x hx
    have hc := B.classifier_active hx.1
    have hf := hA x.2.bid hx.1
    simp [ActionCompatible, BidCompatible, hc, hf, hx.2]
  have hpr : ∀ᵐ x ∂(H.privateLaw : Measure (ℝ × JointAction 2)),
      ActionCompatible B.classifier d κ x.2 := by
    filter_upwards [H.private_support] with x hx
    have hc := B.classifier_private hx.1
    have hf := hP x.2.bid hx.1
    simp [ActionCompatible, BidCompatible, hc, hf, hx.2]
  change ∀ᵐ x ∂populationJoint s a h (lowJoint mu pi) H.active H.privateLaw, _
  exact ae_add_measure_iff.mpr ⟨ae_add_measure_iff.mpr
    ⟨Measure.ae_smul_measure hl (ENNReal.ofReal s),
      Measure.ae_smul_measure hac (ENNReal.ofReal a)⟩,
    Measure.ae_smul_measure hpr (ENNReal.ofReal h)⟩

theorem population_bidCompatible (B : BidClasses d) (H : HigherLaws B)
    (hA : ∀ b ∈ B.activeSet, d < κ * b)
    (hP : ∀ b ∈ B.privateSet, d < b)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s + a + h = 1)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A := LowValue d) mu) :
    ∀ᵐ x ∂(populationLaw s a h hs ha hh hsum (lowJoint mu pi)
      H.active H.privateLaw : Measure (ℝ × JointAction 2)),
      BidCompatible B.classifier d κ x.2.bid :=
  (population_actionCompatible B H hA hP s a h hs ha hh hsum mu pi).mono
    (fun _ hx => hx.1)

theorem original_profile_support {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Gamma : FiniteGame m 2 c Seed) (C : Information.Classifier) (d κ : ℝ)
    (hpop : ∀ᵐ x ∂Gamma.F ⊗ₘ Gamma.σ, ActionCompatible C d κ x.2) :
    ∀ᵐ x ∂userProfileLaw Gamma, x ∈ profiles C d κ := by
  have hu : ∀ᵐ u ∂userLaw Gamma, ActionCompatible C d κ u.1.2 :=
    (measurePreserving_fst (μ := Gamma.F ⊗ₘ Gamma.σ) (ν := permLaw 2)).quasiMeasurePreserving.ae hpop
  exact ae_all_iff.mpr (fun i =>
    (measurePreserving_eval (fun _ : Fin m => userLaw Gamma) i).quasiMeasurePreserving.ae hu)

end FCAppendix.Appendix08.GeneralLow
