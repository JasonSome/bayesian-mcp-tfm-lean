import FCAppendix.AppendixRepair.GeneralLow.DirectCopy
import FCAppendix.AppendixRepair.GeneralLow.SourceSupport
import FCAppendix.AppendixRepair.GeneralLow.ReferenceContext

noncomputable section
namespace FCAppendix.Appendix08.GeneralLow
open MeasureTheory ProbabilityTheory Set Game Bayes
open Affine Affine.LowBody Affine.Hybrid Existence.Distributional
open HigherPolicy HigherPosterior

variable {m c : ℕ} {d η : ℝ}

def sourceAllocationCopy (B : BidClasses d) (hd : 0 ≤ d) (H : HigherLaws B)
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hA : ∀ b ∈ B.activeSet, d < ((1 + η) / 2) * b)
    (hP : ∀ b ∈ B.privateSet, d < b)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s + a + h = 1)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A := LowValue d) mu)
    (HC : HigherSelector (m := m) B.classifier c unitInterval) :
    LowAllocationReproduction
      (DirectGame.game m c
        (populationLaw s a h hs ha hh hsum (lowJoint mu pi) H.active H.privateLaw)
        η hη0 hη1 B.classifier d HC)
      (DirectGame.game m c
        (populationLaw s a h hs ha hh hsum (lowJoint mu pi)
          (H.referenceActive hd) (H.referencePrivate hd))
        η hη0 hη1 (ReferenceContext.classifier d (Tail.referenceActiveBid d)) d
          (DirectGame.emptyHigher (ReferenceContext.classifier d (Tail.referenceActiveBid d)) c)) d := by
  let P := populationLaw s a h hs ha hh hsum (lowJoint mu pi) H.active H.privateLaw
  have hA' : ∀ b ∈ B.activeSet, d < (1 - (1 - η) / 2) * b := by
    intro b hb
    convert hA b hb using 1
    ring
  have hp : ∀ᵐ x ∂(P : Measure (ℝ × JointAction 2)),
      BidCompatible B.classifier d (1 - (1 - η) / 2) x.2.bid :=
    population_bidCompatible B H hA' hP s a h hs ha hh hsum mu pi
  have hpop : DirectCopy.referencePopulation B.classifier d hd P =
      populationLaw s a h hs ha hh hsum (lowJoint mu pi)
        (H.referenceActive hd) (H.referencePrivate hd) := by
    apply Subtype.ext
    exact recode_population B hd H s a h hs ha hh hsum mu pi
  have copy := DirectCopy.allocationReproduction P η hη0 hη1 B.classifier d hd HC
    (fun b hb0 hbd => B.classifier_low_bid hb0 hbd) hp
  simpa only [DirectCopy.referenceGame, hpop, DirectCopy.referenceClassifier,
    ReferenceContext.classifier] using copy

theorem source_copy_common_conull (B : BidClasses d) (hd : 0 ≤ d) (H : HigherLaws B)
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hA : ∀ b ∈ B.activeSet, d < ((1 + η) / 2) * b)
    (hP : ∀ b ∈ B.privateSet, d < b)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s + a + h = 1)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A := LowValue d) mu)
    (HC : HigherSelector (m := m) B.classifier c unitInterval) :
    let P := populationLaw s a h hs ha hh hsum (lowJoint mu pi) H.active H.privateLaw
    let Gamma := DirectGame.game m c P η hη0 hη1 B.classifier d HC
    let Reference := DirectGame.game m c
      (populationLaw s a h hs ha hh hsum (lowJoint mu pi)
        (H.referenceActive hd) (H.referencePrivate hd))
      η hη0 hη1 (ReferenceContext.classifier d (Tail.referenceActiveBid d)) d
        (DirectGame.emptyHigher (ReferenceContext.classifier d (Tail.referenceActiveBid d)) c)
    let copy := sourceAllocationCopy B hd H hη0 hη1 hA hP s a h hs ha hh hsum mu pi HC
    ∀ᵐ ω ∂sampleLaw Gamma, ∀ i : Fin m, ∀ act : JointAction 2, act.bid ≤ d →
      ∀ j : Fin 2,
      (i ∈ allocation (deviated i act ω) Gamma.policy ω.1.2 j) ↔
      (i ∈ allocation (deviated i act (copy.relabel ω)) Reference.policy
        (copy.relabel ω).1.2 j) := by
  dsimp only
  exact ae_all_iff.mpr
    (sourceAllocationCopy B hd H hη0 hη1 hA hP s a h hs ha hh hsum mu pi HC).membership

end FCAppendix.Appendix08.GeneralLow
