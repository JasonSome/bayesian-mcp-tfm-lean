import FCAppendix.AppendixRepair.GeneralLow.ProposerOptimality
import FCAppendix.AppendixRepair.GeneralLow.SourceSupport

noncomputable section
namespace FCAppendix.Appendix08.GeneralLow.Market
open MeasureTheory ProbabilityTheory Set Game Bayes
open Affine Affine.LowBody Affine.Hybrid Existence.Distributional
open HigherPosterior

variable {d η : ℝ}

def privateAnchor {B : BidClasses d} (H : HigherLaws B) : ℝ :=
  (Classical.choose H.private_support.exists).2.bid

theorem privateAnchor_mem {B : BidClasses d} (H : HigherLaws B) :
    privateAnchor H ∈ B.privateSet :=
  (Classical.choose_spec H.private_support.exists).1

theorem privateAnchor_nonneg {B : BidClasses d} (H : HigherLaws B) :
    0 ≤ privateAnchor H :=
  (Classical.choose H.private_support.exists).2.bid_nonneg

theorem privateAnchor_label {B : BidClasses d} (H : HigherLaws B) :
    B.classifier.label (privateAnchor H) = 2 := B.classifier_private (privateAnchor_mem H)

theorem privateAnchor_gt {B : BidClasses d} (H : HigherLaws B)
    (hP : ∀ b ∈ B.privateSet, d < b) : d < privateAnchor H :=
  hP _ (privateAnchor_mem H)

def base (m c : ℕ) (B : BidClasses d) (H : HigherLaws B)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s + a + h = 1)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A := LowValue d) mu) : FiniteGame m 2 c unitInterval :=
  PopulationGame.game m c
    (populationLaw s a h hs ha hh hsum (lowJoint mu pi) H.active H.privateLaw)
    η hη0 hη1 d

theorem profile_support (m c : ℕ) (B : BidClasses d) (H : HigherLaws B)
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hA : ∀ b ∈ B.activeSet, d < ((1 + η) / 2) * b)
    (hP : ∀ b ∈ B.privateSet, d < b)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s + a + h = 1)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A := LowValue d) mu) :
    ∀ᵐ z ∂userProfileLaw (base m c B H η hη0 hη1 s a h hs ha hh hsum mu pi),
      z ∈ profiles B.classifier d (1 - (1 - η) / 2) := by
  apply original_profile_support
  rw [show (base m c B H η hη0 hη1 s a h hs ha hh hsum mu pi).F ⊗ₘ
      (base m c B H η hη0 hη1 s a h hs ha hh hsum mu pi).σ =
      (populationLaw s a h hs ha hh hsum (lowJoint mu pi) H.active H.privateLaw :
        Measure (ℝ × JointAction 2)) from PopulationGame.joint_law _ _ _ _ _ _ _]
  apply population_actionCompatible B H _ hP s a h hs ha hh hsum mu pi
  intro b hb
  convert hA b hb using 1
  ring

abbrev SourceHC (m c : ℕ) (B : BidClasses d) (H : HigherLaws B)
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hA : ∀ b ∈ B.activeSet, d < ((1 + η) / 2) * b)
    (hP : ∀ b ∈ B.privateSet, d < b)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s + a + h = 1)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A := LowValue d) mu) :=
  Continuation.HC (base m c B H η hη0 hη1 s a h hs ha hh hsum mu pi)
    B.classifier d (1 - (1 - η) / 2) (privateAnchor H)
    (profile_support m c B H hη0 hη1 hA hP s a h hs ha hh hsum mu pi)

def game (m c : ℕ) (B : BidClasses d) (H : HigherLaws B)
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hA : ∀ b ∈ B.activeSet, d < ((1 + η) / 2) * b)
    (hP : ∀ b ∈ B.privateSet, d < b)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s + a + h = 1)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A := LowValue d) mu)
    (HC : SourceHC m c B H hη0 hη1 hA hP s a h hs ha hh hsum mu pi) :
    FiniteGame m 2 c unitInterval :=
  Implementation.game (base m c B H η hη0 hη1 s a h hs ha hh hsum mu pi)
    B.classifier d ((1 - η) / 2) (privateAnchor H) (by linarith) (by linarith)
    (profile_support m c B H hη0 hη1 hA hP s a h hs ha hh hsum mu pi) HC

def selector (m c : ℕ) (B : BidClasses d) (H : HigherLaws B)
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hA : ∀ b ∈ B.activeSet, d < ((1 + η) / 2) * b)
    (hP : ∀ b ∈ B.privateSet, d < b)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s + a + h = 1)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A := LowValue d) mu)
    (HC : SourceHC m c B H hη0 hη1 hA hP s a h hs ha hh hsum mu pi) :
    HigherPolicy.HigherSelector (m := m) B.classifier c unitInterval :=
  NormalizedContinuation.selector (base m c B H η hη0 hη1 s a h hs ha hh hsum mu pi)
    B.classifier d (1 - (1 - η) / 2) (privateAnchor H)
    (profile_support m c B H hη0 hη1 hA hP s a h hs ha hh hsum mu pi) HC.selector

theorem game_eq_direct (m c : ℕ) (B : BidClasses d) (H : HigherLaws B)
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hA : ∀ b ∈ B.activeSet, d < ((1 + η) / 2) * b)
    (hP : ∀ b ∈ B.privateSet, d < b)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s + a + h = 1)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A := LowValue d) mu)
    (HC : SourceHC m c B H hη0 hη1 hA hP s a h hs ha hh hsum mu pi) :
    game m c B H hη0 hη1 hA hP s a h hs ha hh hsum mu pi HC =
      DirectGame.game m c
        (populationLaw s a h hs ha hh hsum (lowJoint mu pi) H.active H.privateLaw)
        η hη0 hη1 B.classifier d
        (selector m c B H hη0 hη1 hA hP s a h hs ha hh hsum mu pi HC) := rfl

def belief (m c : ℕ) (B : BidClasses d) (H : HigherLaws B)
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hA : ∀ b ∈ B.activeSet, d < ((1 + η) / 2) * b)
    (hP : ∀ b ∈ B.privateSet, d < b)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s + a + h = 1)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A := LowValue d) mu)
    (HC : SourceHC m c B H hη0 hη1 hA hP s a h hs ha hh hsum mu pi) :
    PosteriorSystem (game m c B H hη0 hη1 hA hP s a h hs ha hh hsum mu pi HC) :=
  Implementation.belief (base m c B H η hη0 hη1 s a h hs ha hh hsum mu pi)
    B.classifier d ((1 - η) / 2) (privateAnchor H) (by linarith) (by linarith)
    (profile_support m c B H hη0 hη1 hA hP s a h hs ha hh hsum mu pi) HC

theorem joint_law (m c : ℕ) (B : BidClasses d) (H : HigherLaws B)
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hA : ∀ b ∈ B.activeSet, d < ((1 + η) / 2) * b)
    (hP : ∀ b ∈ B.privateSet, d < b)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s + a + h = 1)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A := LowValue d) mu)
    (HC : SourceHC m c B H hη0 hη1 hA hP s a h hs ha hh hsum mu pi) :
    let Gamma := game m c B H hη0 hη1 hA hP s a h hs ha hh hsum mu pi HC
    Gamma.F ⊗ₘ Gamma.σ = populationJoint s a h (lowJoint mu pi) H.active H.privateLaw :=
  PopulationGame.joint_law m c _ η hη0 hη1 d

theorem proposer_optimal (m c : ℕ) (B : BidClasses d) (hd : 0 ≤ d) (H : HigherLaws B)
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hA : ∀ b ∈ B.activeSet, d < ((1 + η) / 2) * b)
    (hP : ∀ b ∈ B.privateSet, d < b)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s + a + h = 1)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A := LowValue d) mu)
    (HC : SourceHC m c B H hη0 hη1 hA hP s a h hs ha hh hsum mu pi) :
    PosteriorProposerOptimal
      (game m c B H hη0 hη1 hA hP s a h hs ha hh hsum mu pi HC)
      (belief m c B H hη0 hη1 hA hP s a h hs ha hh hsum mu pi HC) :=
  ProposerOptimality.proposer_optimal
    (base m c B H η hη0 hη1 s a h hs ha hh hsum mu pi)
    B.classifier d ((1 - η) / 2) (privateAnchor H) (by linarith) (by linarith)
    (profile_support m c B H hη0 hη1 hA hP s a h hs ha hh hsum mu pi) HC
    hd η hη0 hη1.le rfl rfl rfl
    (privateAnchor_nonneg H) (privateAnchor_label H) (privateAnchor_gt H hP)

end FCAppendix.Appendix08.GeneralLow.Market
