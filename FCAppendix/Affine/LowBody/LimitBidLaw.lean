import FCAppendix.Affine.LowBody.ZeroClusterLimit

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set

theorem realLowBidLaw_nonnegative {d : ℝ}
    (pi : ProbabilityMeasure (LowValue d×LowValue d)) :
    ∀ᵐb ∂(realLowBidLaw pi : Measure ℝ),0≤b := by
  change ∀ᵐb ∂(pi : Measure (LowValue d×LowValue d)).map (fun x=>x.2.1),0≤b
  apply (ae_map_iff measurable_snd.subtype_val.aemeasurable
    (measurableSet_le measurable_const measurable_id)).mpr
  exact ae_of_all _ (fun x=>x.2.property.1)

theorem realLowBidLaw_atomless_of_nonnegative_atoms {d : ℝ}
    (pi : ProbabilityMeasure (LowValue d×LowValue d))
    (hzero : (realLowBidLaw pi : Measure ℝ) {0}=0)
    (hpositive : ∀b : ℝ,0<b→(realLowBidLaw pi : Measure ℝ) {b}=0) :
    NullSingletonClass (realLowBidLaw pi : Measure ℝ) := by
  constructor
  intro b
  rcases lt_trichotomy b 0 with hb|hb|hb
  · have hn:=realLowBidLaw_nonnegative pi
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hn] with x hx hxb
    have he : x=b:=mem_singleton_iff.mp hxb
    linarith
  · simpa only [hb] using hzero
  · exact hpositive b hb

theorem compactBidLaw_singleton_eq {d : ℝ}
    (pi : ProbabilityMeasure (LowValue d×LowValue d)) (b : LowValue d) :
    (pi.map measurable_snd.aemeasurable : Measure (LowValue d)) {b}=
      (realLowBidLaw pi : Measure ℝ) {b.1} := by
  change ((pi : Measure (LowValue d×LowValue d)).map Prod.snd) {b}=
    ((pi : Measure (LowValue d×LowValue d)).map (fun x=>x.2.1)) {b.1}
  rw [Measure.map_apply measurable_snd (measurableSet_singleton b),
    Measure.map_apply measurable_snd.subtype_val (measurableSet_singleton b.1)]
  congr 1
  ext x
  simp only [mem_preimage,mem_singleton_iff,Subtype.ext_iff]

theorem compactBidLaw_atomless_of_real {d : ℝ}
    (pi : ProbabilityMeasure (LowValue d×LowValue d))
    [NullSingletonClass (realLowBidLaw pi : Measure ℝ)] :
    NullSingletonClass (pi.map measurable_snd.aemeasurable : Measure (LowValue d)) := by
  constructor
  intro b
  rw [compactBidLaw_singleton_eq,measure_singleton]

theorem joint_bid_positive_of_real_zero_atom {d : ℝ}
    (pi : ProbabilityMeasure (LowValue d×LowValue d))
    (hzero : (realLowBidLaw pi : Measure ℝ) {0}=0) :
    ∀ᵐx ∂(pi : Measure (LowValue d×LowValue d)),0<x.2.1 := by
  have hz : ∀ᵐb ∂(realLowBidLaw pi : Measure ℝ),b≠0:=
    measure_eq_zero_iff_ae_notMem.mp hzero
  have hj : ∀ᵐx ∂(pi : Measure (LowValue d×LowValue d)),x.2.1≠0 :=
    (ae_map_iff measurable_snd.subtype_val.aemeasurable
      (measurableSet_eq_fun measurable_id measurable_const).compl).mp hz
  filter_upwards [hj] with x hx
  exact lt_of_le_of_ne x.2.property.1 (Ne.symm hx)

end FCAppendix.Affine.LowBody
