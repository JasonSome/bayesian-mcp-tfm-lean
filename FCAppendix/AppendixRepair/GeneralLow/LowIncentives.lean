import FCAppendix.AppendixRepair.GeneralLow.SourceCopy
import FCAppendix.AppendixRepair.GeneralLow.DirectPositive
import FCAppendix.AppendixRepair.GeneralLow.DirectZeroEnvelope
import FCAppendix.AppendixRepair.GeneralLow.DirectBounds

set_option maxHeartbeats 2400000
noncomputable section
namespace FCAppendix.Appendix08.GeneralLow
open MeasureTheory ProbabilityTheory Set Game Bayes
open Affine Affine.LowBody Affine.Hybrid Existence.Distributional
open HigherPolicy HigherPosterior

variable {N c : ℕ} {d η : ℝ}

theorem source_positive_broadcast_payoff (B : BidClasses d) (hd : 0 ≤ d) (H : HigherLaws B)
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hA : ∀ b ∈ B.activeSet, d < ((1 + η) / 2) * b)
    (hP : ∀ b ∈ B.privateSet, d < b)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s + a + h = 1)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A := LowValue d) mu)
    [NullSingletonClass
      ((pi.1.map measurable_snd.aemeasurable : ProbabilityMeasure (LowValue d)) :
        Measure (LowValue d))]
    (HC : HigherSelector (m := N + 1) B.classifier c unitInterval)
    (i : Fin (N + 1)) (w : ℝ) (act : JointAction 2)
    (hk : act.routeCount = 2) (hb : 0 < act.bid) (hbd : act.bid ≤ d) :
    let P := populationLaw s a h hs ha hh hsum (lowJoint mu pi) H.active H.privateLaw
    let Gamma := DirectGame.game (N + 1) c P η hη0 hη1 B.classifier d HC
    (problem Gamma i).payoff w act =
      exactExpectedPayoff N d ((1 - η) / 2) c (categoryLaw s a h hs ha hh hsum Gref)
        (pi.1.map measurable_snd.aemeasurable) (w, act.bid) := by
  dsimp only
  let copy := (sourceAllocationCopy B hd H hη0 hη1 hA hP
    s a h hs ha hh hsum mu pi HC).toCounts
  rw [copy.payoff_eq rfl rfl rfl i w act hbd]
  exact direct_population_positive_broadcast_payoff hd (Tail.reference_bid_guards hd hη0).1
    s a h hs ha hh hsum Gref mu pi (H.referenceActive hd) (H.referencePrivate hd)
    hη0 hη1 (DirectGame.emptyHigher _ c) (H.referenceActive_support hd hη0)
    (H.referencePrivate_support hd) i w act hk hb hbd

theorem source_zero_envelope (B : BidClasses d) (hd : 0 ≤ d) (H : HigherLaws B)
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hA : ∀ b ∈ B.activeSet, d < ((1 + η) / 2) * b)
    (hP : ∀ b ∈ B.privateSet, d < b)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s + a + h = 1)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A := LowValue d) mu)
    (HC : HigherSelector (m := N + 1) B.classifier c unitInterval)
    (i : Fin (N + 1)) (w : ℝ) (hw : 0 ≤ w) (act : JointAction 2)
    (hk : act.routeCount = 2) (hzero : act.bid = 0)
    (y : ℝ) (hy : 0 < y) (hyd : y ≤ d) :
    let P := populationLaw s a h hs ha hh hsum (lowJoint mu pi) H.active H.privateLaw
    let Gamma := DirectGame.game (N + 1) c P η hη0 hη1 B.classifier d HC
    (problem Gamma i).payoff w act ≤
      (problem Gamma i).payoff w (NativeLowIncentives.broadcast y hy.le) + 2 * y := by
  dsimp only
  let copy := (sourceAllocationCopy B hd H hη0 hη1 hA hP
    s a h hs ha hh hsum mu pi HC).toCounts
  have h0d : act.bid ≤ d := by rw [hzero]; exact hd
  rw [copy.payoff_eq rfl rfl rfl i w act h0d,
    copy.payoff_eq rfl rfl rfl i w (NativeLowIncentives.broadcast y hy.le) hyd]
  let U := Tail.referenceActiveBid d
  let PA := H.referenceActive hd
  let PH := H.referencePrivate hd
  let P := populationLaw s a h hs ha hh hsum (lowJoint mu pi) PA PH
  have hdU : d ≤ U := (Tail.reference_bid_guards hd hη0).1
  have hκ : ((1 + η) / 2) ≤ 1 := by linarith
  have hac : ∀ᵐ x ∂(PA : Measure (ℝ × JointAction 2)),
      d < ((1 + η) / 2) * x.2.bid ∧ d < x.2.bid ∧ x.2.bid ≤ U ∧ x.2.routeCount = 2 := by
    filter_upwards [H.referenceActive_support hd hη0] with x hx
    exact ⟨hx.1, hx.1.trans_le (by
      nlinarith [mul_nonneg (sub_nonneg.mpr hκ) x.2.bid_nonneg]), hx.2⟩
  have hp : ∀ᵐ x ∂(P : Measure (ℝ × JointAction 2)),
      lowActionGuard d U ((1 + η) / 2) x.2 :=
    population_lowActionGuard hdU s a h mu pi PA PH hac (H.referencePrivate_support hd)
  have hprofiles := profile_lowActionGuard (N := N) (c := c) P hη0 hη1 hp
  exact DirectZeroEnvelope.zero_envelope_of_guard P hη0 hη1 hdU
    (DirectGame.emptyHigher (ReferenceContext.classifier d U) c)
    hprofiles i w hw act hk hzero y hy hyd

theorem source_every_positive_low_value (B : BidClasses d) (hd : 0 ≤ d) (H : HigherLaws B)
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hA : ∀ b ∈ B.activeSet, d < ((1 + η) / 2) * b)
    (hP : ∀ b ∈ B.privateSet, d < b)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s + a + h = 1)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A := LowValue d) mu)
    [NullSingletonClass
      ((pi.1.map measurable_snd.aemeasurable : ProbabilityMeasure (LowValue d)) :
        Measure (LowValue d))]
    (HC : HigherSelector (m := N + 1) B.classifier c unitInterval)
    (hell : 0 < (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob
      (LocalUnderflow c 0))
    (hsmall : (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob
      (BothUnderflow c) ≤
      (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob (LocalUnderflow c 0) / 4)
    (i : Fin (N + 1)) (v : ℝ) (hv : 0 < v) (hvd : v ≤ d) :
    let P := populationLaw s a h hs ha hh hsum (lowJoint mu pi) H.active H.privateLaw
    let Gamma := DirectGame.game (N + 1) c P η hη0 hη1 B.classifier d HC
    ∀ act : JointAction 2, act.routeCount = 1 →
      ∃ raised : JointAction 2, raised.routeCount = 2 ∧ raised.bid ≤ d ∧
        (problem Gamma i).payoff v act < (problem Gamma i).payoff v raised := by
  dsimp only
  let Gamma := DirectGame.game (N + 1) c
    (populationLaw s a h hs ha hh hsum (lowJoint mu pi) H.active H.privateLaw)
    η hη0 hη1 B.classifier d HC
  let ξ := (1 - η) / 2
  have hξ : 0 < ξ := by dsimp [ξ]; linarith
  have hξh : ξ ≤ 1 / 2 := by dsimp [ξ]; linarith
  let ell := (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob (LocalUnderflow c 0)
  let delta := (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob (BothUnderflow c)
  have hdelt : 0 ≤ delta := (CommonList.iid _ _).prob_nonneg _
  let ref := NativeLowIncentives.broadcast (v / 2) (by linarith : 0 ≤ v / 2)
  have hrefd : ref.bid ≤ d := by dsimp [ref, NativeLowIncentives.broadcast]; linarith
  have href : (problem Gamma i).payoff v ref =
      exactExpectedPayoff N d ξ c (categoryLaw s a h hs ha hh hsum Gref)
        (pi.1.map measurable_snd.aemeasurable) (v, v / 2) :=
    source_positive_broadcast_payoff B hd H hη0 hη1 hA hP s a h hs ha hh hsum
      Gref mu pi HC i v ref rfl (by dsimp [ref, NativeLowIncentives.broadcast]; linarith) hrefd
  have hcompare : v * (ell - delta) / 2 ≤ (problem Gamma i).payoff v ref := by
    rw [href]
    simpa only [ell, delta, div_mul_eq_mul_div] using
      exactExpectedPayoff_half_bid_lower (N := N) hξ hξh hv c
        (categoryLaw s a h hs ha hh hsum Gref) (pi.1.map measurable_snd.aemeasurable)
  have hgap : v * delta < (problem Gamma i).payoff v ref := by
    have hpos : 0 < v * (ell - 3 * delta) := mul_pos hv (by dsimp [ell, delta]; linarith)
    nlinarith
  intro act hk
  by_cases hbid : act.bid ≤ v
  · by_cases hu : (problem Gamma i).payoff v act ≤ v * delta
    · exact ⟨ref, rfl, hrefd, hu.trans_lt hgap⟩
    · have hdup : ((problem Gamma i).outcome (addSecondRoute act)).duplicates ≤ delta :=
        (DirectBounds.source_counts_bound B hd H hη0 hη1 hA hP
          s a h hs ha hh hsum Gref mu pi HC i (addSecondRoute act) (hbid.trans hvd)).2
      have hgain := native_second_route_utility_lower Gamma hη0 hη1.le rfl rfl i act hk hbid hdup
      refine ⟨addSecondRoute act, rfl, hbid.trans hvd, ?_⟩
      linarith
  · have hnp := NativeLowIncentives.payoff_nonpos_of_value_le_bid Gamma rfl i v act
      (le_of_lt (lt_of_not_ge hbid))
    exact ⟨ref, rfl, hrefd, hnp.trans_lt ((mul_nonneg hv.le hdelt).trans_lt hgap)⟩

theorem source_low_joint_best_response (B : BidClasses d) (hd : 0 ≤ d) (H : HigherLaws B)
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hA : ∀ b ∈ B.activeSet, d < ((1 + η) / 2) * b)
    (hP : ∀ b ∈ B.privateSet, d < b)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s + a + h = 1)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (L : ActualAtomlessLowLimit N d ((1 - η) / 2) c
      (categoryLaw s a h hs ha hh hsum Gref) mu)
    (HC : HigherSelector (m := N + 1) B.classifier c unitInterval)
    (hell : 0 < (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob
      (LocalUnderflow c 0))
    (hsmall : (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob
      (BothUnderflow c) ≤
      (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob (LocalUnderflow c 0) / 4) :
    let P := populationLaw s a h hs ha hh hsum (lowJoint mu L.joint) H.active H.privateLaw
    let Gamma := DirectGame.game (N + 1) c P η hη0 hη1 B.classifier d HC
    ∀ᵐ x ∂(L.joint.1 : Measure (LowValue d × LowValue d)), ∀ i : Fin (N + 1),
      (problem Gamma i).BestResponse x.1.1 (lowBroadcast x.2) ∧
      ∀ act : JointAction 2, act.routeCount = 1 →
        (problem Gamma i).payoff x.1.1 act <
          (problem Gamma i).payoff x.1.1 (lowBroadcast x.2) := by
  dsimp only
  let ξ := (1 - η) / 2
  have hξ : 0 < ξ := by dsimp [ξ]; linarith
  have hξh : ξ ≤ 1 / 2 := by dsimp [ξ]; linarith
  letI := L.compact_atomless
  let Gamma := DirectGame.game (N + 1) c
    (populationLaw s a h hs ha hh hsum (lowJoint mu L.joint) H.active H.privateLaw)
    η hη0 hη1 B.classifier d HC
  filter_upwards [L.all_bid_IC hξ hξh, L.value_positive, L.bid_positive] with x hIC hw hb
  intro i
  have hbest : (problem Gamma i).BestResponse x.1.1 (lowBroadcast x.2) := by
    apply NativeLowIncentives.best_response Gamma i hξ hξh hη0 hη1.le rfl rfl
      (categoryLaw s a h hs ha hh hsum Gref) (L.joint.1.map measurable_snd.aemeasurable)
      x.1 x.2 hw hb hIC
    · intro act hk hpos hbd
      exact source_positive_broadcast_payoff B hd H hη0 hη1 hA hP
        s a h hs ha hh hsum Gref mu L.joint HC i x.1.1 act hk hpos hbd
    · intro act hk hz y hy hyd
      exact source_zero_envelope B hd H hη0 hη1 hA hP
        s a h hs ha hh hsum mu L.joint HC i x.1.1 x.1.property.1 act hk hz y hy hyd
    · exact hell
    · exact hsmall
    · intro act _hk hbval
      exact (DirectBounds.source_counts_bound B hd H hη0 hη1 hA hP
        s a h hs ha hh hsum Gref mu L.joint HC i act (hbval.trans x.1.property.2)).2
  refine ⟨hbest, ?_⟩
  intro act hk
  obtain ⟨raised, _hr, _hd, hstrict⟩ := source_every_positive_low_value B hd H hη0 hη1 hA hP
    s a h hs ha hh hsum Gref mu L.joint HC hell hsmall i x.1.1 hw x.1.property.2 act hk
  exact hstrict.trans_le (hbest raised)

theorem source_low_actual_best_response (B : BidClasses d) (hd : 0 ≤ d) (H : HigherLaws B)
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hA : ∀ b ∈ B.activeSet, d < ((1 + η) / 2) * b)
    (hP : ∀ b ∈ B.privateSet, d < b)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s + a + h = 1)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (L : ActualAtomlessLowLimit N d ((1 - η) / 2) c
      (categoryLaw s a h hs ha hh hsum Gref) mu)
    (HC : HigherSelector (m := N + 1) B.classifier c unitInterval)
    (hell : 0 < (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob
      (LocalUnderflow c 0))
    (hsmall : (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob
      (BothUnderflow c) ≤
      (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob (LocalUnderflow c 0) / 4) :
    let P := populationLaw s a h hs ha hh hsum (lowJoint mu L.joint) H.active H.privateLaw
    let Gamma := DirectGame.game (N + 1) c P η hη0 hη1 B.classifier d HC
    ∀ᵐ x ∂(lowJoint mu L.joint : Measure (ℝ × JointAction 2)), ∀ i : Fin (N + 1),
      (problem Gamma i).BestResponse x.1 x.2 ∧
      ∀ act : JointAction 2, act.routeCount = 1 →
        (problem Gamma i).payoff x.1 act < (problem Gamma i).payoff x.1 x.2 := by
  dsimp only
  change ∀ᵐ x ∂(L.joint.1 : Measure (LowValue d × LowValue d)).map
    (fun x => (x.1.1, lowBroadcast x.2)), _
  apply (measurableEmbedding_lowJointPoint d).ae_map_iff.mpr
  exact source_low_joint_best_response B hd H hη0 hη1 hA hP
    s a h hs ha hh hsum Gref mu L HC hell hsmall

end FCAppendix.Appendix08.GeneralLow
