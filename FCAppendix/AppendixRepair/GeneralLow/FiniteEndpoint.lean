import FCAppendix.AppendixRepair.GeneralLow.Market
import FCAppendix.AppendixRepair.GeneralLow.LowIncentives

noncomputable section
namespace FCAppendix.Appendix08.GeneralLow
open MeasureTheory ProbabilityTheory Set Game Bayes
open Affine Affine.LowBody Affine.Hybrid Existence.Distributional
open Affine.AppendixRepair.TriangularLow

variable {m c N : ℕ} {d η : ℝ}

structure Conclusions (Gamma Reference : FiniteGame m 2 c unitInterval)
    (belief : PosteriorSystem Gamma) (low : ProbabilityMeasure (ℝ × JointAction 2))
    (categories : FiniteLaw (Fin 4)) (d : ℝ) : Prop where
  proposer_optimal : PosteriorProposerOptimal Gamma belief
  low_optimal : ∀ᵐ x ∂(low : Measure (ℝ × JointAction 2)), ∀ i : Fin m,
    (problem Gamma i).BestResponse x.1 x.2 ∧
    ∀ act : JointAction 2, act.routeCount = 1 →
      (problem Gamma i).payoff x.1 act < (problem Gamma i).payoff x.1 x.2
  strict_every_value : ∀ i : Fin m, ∀ v : ℝ, 0 < v → v ≤ d →
    ∀ act : JointAction 2, act.routeCount = 1 →
      ∃ raised : JointAction 2, raised.routeCount = 2 ∧ raised.bid ≤ d ∧
        (problem Gamma i).payoff v act < (problem Gamma i).payoff v raised
  count_bound : ∀ i : Fin m, ∀ act : JointAction 2, act.bid ≤ d →
    ((problem Gamma i).outcome act).success ≤
      (CommonList.iid categories (m - 1)).prob (HigherUnderflow c)
  duplicate_bound : ∀ i : Fin m, ∀ act : JointAction 2, act.bid ≤ d →
    ((problem Gamma i).outcome act).duplicates ≤
      (CommonList.iid categories (m - 1)).prob (BothUnderflow c)
  allocation_copy : Nonempty (LowAllocationReproduction Gamma Reference d)

def referenceMarket (m c : ℕ) (B : BidClasses d) (hd : 0 ≤ d) (H : HigherLaws B)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s + a + h = 1)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A := LowValue d) mu) : FiniteGame m 2 c unitInterval :=
  DirectGame.game m c
    (populationLaw s a h hs ha hh hsum (lowJoint mu pi)
      (H.referenceActive hd) (H.referencePrivate hd))
    η hη0 hη1 (ReferenceContext.classifier d (Tail.referenceActiveBid d)) d
      (DirectGame.emptyHigher (ReferenceContext.classifier d (Tail.referenceActiveBid d)) c)

theorem finite_implementation (B : BidClasses d) (hd : 0 ≤ d) (H : HigherLaws B)
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hA : ∀ b ∈ B.activeSet, d < ((1 + η) / 2) * b)
    (hP : ∀ b ∈ B.privateSet, d < b)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s + a + h = 1)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (L : ActualAtomlessLowLimit N d ((1 - η) / 2) c
      (categoryLaw s a h hs ha hh hsum Gref) mu)
    (HC : Market.SourceHC (N + 1) c B H hη0 hη1 hA hP
      s a h hs ha hh hsum mu L.joint)
    (hell : 0 < (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob
      (LocalUnderflow c 0))
    (hsmall : (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob
      (BothUnderflow c) ≤
      (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob (LocalUnderflow c 0) / 4) :
    Conclusions
      (Market.game (N + 1) c B H hη0 hη1 hA hP s a h hs ha hh hsum mu L.joint HC)
      (referenceMarket (N + 1) c B hd H η hη0 hη1 s a h hs ha hh hsum mu L.joint)
      (Market.belief (N + 1) c B H hη0 hη1 hA hP s a h hs ha hh hsum mu L.joint HC)
      (lowJoint mu L.joint) (categoryLaw s a h hs ha hh hsum Gref) d := by
  let high := Market.selector (N + 1) c B H hη0 hη1 hA hP
    s a h hs ha hh hsum mu L.joint HC
  letI := L.compact_atomless
  refine ⟨Market.proposer_optimal (N + 1) c B hd H hη0 hη1 hA hP
    s a h hs ha hh hsum mu L.joint HC, ?_, ?_, ?_, ?_, ?_⟩
  · exact source_low_actual_best_response B hd H hη0 hη1 hA hP
      s a h hs ha hh hsum Gref mu L high hell hsmall
  · intro i v hv hvd
    exact source_every_positive_low_value B hd H hη0 hη1 hA hP
      s a h hs ha hh hsum Gref mu L.joint high hell hsmall i v hv hvd
  · intro i act hbd
    exact (DirectBounds.source_counts_bound B hd H hη0 hη1 hA hP
      s a h hs ha hh hsum Gref mu L.joint high i act hbd).1
  · intro i act hbd
    exact (DirectBounds.source_counts_bound B hd H hη0 hη1 hA hP
      s a h hs ha hh hsum Gref mu L.joint high i act hbd).2
  · exact ⟨sourceAllocationCopy B hd H hη0 hη1 hA hP
      s a h hs ha hh hsum mu L.joint high⟩

end FCAppendix.Appendix08.GeneralLow
