import FCAppendix.AppendixRepair.GeneralLow.BorelClasses
import FCAppendix.AppendixRepair.TailApplication

noncomputable section
namespace FCAppendix.Appendix08.GeneralLow
open MeasureTheory ProbabilityTheory Set Game Bayes
open Affine Affine.LowBody Affine.Hybrid
open Existence.Distributional

variable {d : ℝ}

structure HigherLaws (B : BidClasses d) where
  active : ProbabilityMeasure (ℝ × JointAction 2)
  privateLaw : ProbabilityMeasure (ℝ × JointAction 2)
  active_support : ∀ᵐ x ∂(active : Measure (ℝ × JointAction 2)),
    x.2.bid ∈ B.activeSet ∧ x.2.routeCount = 2
  private_support : ∀ᵐ x ∂(privateLaw : Measure (ℝ × JointAction 2)),
    x.2.bid ∈ B.privateSet ∧ x.2.routeCount = 1

namespace HigherLaws
variable {B : BidClasses d} (H : HigherLaws B)

theorem active_labels : ∀ᵐ x ∂(H.active : Measure (ℝ × JointAction 2)),
    B.classifier.label x.2.bid = 1 ∧ x.2.routeCount = 2 := by
  filter_upwards [H.active_support] with x hx
  exact ⟨B.classifier_active hx.1, hx.2⟩

theorem private_labels : ∀ᵐ x ∂(H.privateLaw : Measure (ℝ × JointAction 2)),
    B.classifier.label x.2.bid = 2 ∧ x.2.routeCount = 1 := by
  filter_upwards [H.private_support] with x hx
  exact ⟨B.classifier_private hx.1, hx.2⟩

def referenceActive (hd : 0 ≤ d) : ProbabilityMeasure (ℝ × JointAction 2) :=
  Tail.recodePopulation B.classifier (Tail.referenceActiveBid d) (Tail.referencePrivateBid d)
    (Tail.referenceActiveBid_nonneg hd) (Tail.referencePrivateBid_nonneg hd) H.active

def referencePrivate (hd : 0 ≤ d) : ProbabilityMeasure (ℝ × JointAction 2) :=
  Tail.recodePopulation B.classifier (Tail.referenceActiveBid d) (Tail.referencePrivateBid d)
    (Tail.referenceActiveBid_nonneg hd) (Tail.referencePrivateBid_nonneg hd) H.privateLaw

theorem referenceActive_support (hd : 0 ≤ d) {η : ℝ} (hη : 0 ≤ η) :
    ∀ᵐ x ∂(H.referenceActive hd : Measure (ℝ × JointAction 2)),
      d < ((1 + η) / 2) * x.2.bid ∧
        x.2.bid ≤ Tail.referenceActiveBid d ∧ x.2.routeCount = 2 :=
  Tail.recoded_active_support B.classifier d η hd hη H.active H.active_labels

theorem referencePrivate_support (hd : 0 ≤ d) :
    ∀ᵐ x ∂(H.referencePrivate hd : Measure (ℝ × JointAction 2)),
      Tail.referenceActiveBid d < x.2.bid ∧ x.2.routeCount = 1 :=
  Tail.recoded_private_support B.classifier d hd H.privateLaw H.private_labels

end HigherLaws

theorem lowJoint_label (B : BidClasses d)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A := LowValue d) mu) :
    ∀ᵐ x ∂(lowJoint mu pi : Measure (ℝ × JointAction 2)),
      B.classifier.label x.2.bid = 0 := by
  change ∀ᵐ x ∂(pi.1 : Measure (LowValue d × LowValue d)).map
    (fun x => (x.1.1, lowBroadcast x.2)), _
  apply (measurableEmbedding_lowJointPoint d).ae_map_iff.mpr
  exact ae_of_all _ (fun x => B.classifier_low_bid x.2.property.1 x.2.property.2)

theorem recode_population (B : BidClasses d) (hd : 0 ≤ d) (H : HigherLaws B)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s + a + h = 1)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A := LowValue d) mu) :
    (populationLaw s a h hs ha hh hsum (lowJoint mu pi) H.active H.privateLaw :
      Measure (ℝ × JointAction 2)).map
      (Tail.recodeJoint B.classifier (Tail.referenceActiveBid d) (Tail.referencePrivateBid d)
        (Tail.referenceActiveBid_nonneg hd) (Tail.referencePrivateBid_nonneg hd)) =
      (populationLaw s a h hs ha hh hsum (lowJoint mu pi)
        (H.referenceActive hd) (H.referencePrivate hd) : Measure (ℝ × JointAction 2)) :=
  Tail.recode_populationJoint B.classifier (Tail.referenceActiveBid d)
    (Tail.referencePrivateBid d) (Tail.referenceActiveBid_nonneg hd)
    (Tail.referencePrivateBid_nonneg hd) s a h (lowJoint mu pi)
    H.active H.privateLaw (lowJoint_label B mu pi)

theorem recodeJoint_value_marginal (B : BidClasses d) (hd : 0 ≤ d)
    (P : ProbabilityMeasure (ℝ × JointAction 2)) :
    ((Tail.recodePopulation B.classifier (Tail.referenceActiveBid d)
      (Tail.referencePrivateBid d) (Tail.referenceActiveBid_nonneg hd)
      (Tail.referencePrivateBid_nonneg hd) P : Measure (ℝ × JointAction 2)).map Prod.fst) =
        (P : Measure (ℝ × JointAction 2)).map Prod.fst := by
  change ((P : Measure (ℝ × JointAction 2)).map
    (Tail.recodeJoint B.classifier (Tail.referenceActiveBid d) (Tail.referencePrivateBid d)
      (Tail.referenceActiveBid_nonneg hd) (Tail.referencePrivateBid_nonneg hd))).map Prod.fst = _
  rw [Measure.map_map measurable_fst (Tail.measurable_recodeJoint _ _ _ _ _)]
  rfl

end FCAppendix.Appendix08.GeneralLow
