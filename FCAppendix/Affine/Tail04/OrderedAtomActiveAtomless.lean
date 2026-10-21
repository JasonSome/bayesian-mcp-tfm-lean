import FCAppendix.Affine.Tail04.OrderedAtomContraction
import FCAppendix.Affine.Tail04.OrderedAtomPartialAtomless

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomActiveAtomless
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Existence.Distributional OriginalValues FiniteTailNoisyGame SourceTailNoisyFixedPoint
open OrderedOriginalNoisySequence OrderedAtomClusterLaws OrderedAtomContraction
open OrderedAtomPartialAtomless LatentSpeciesCalculus

variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)

lemma common_support (π : JointProfile D P t ht) :
    ∀ᵐ b ∂(baseRealLaw D P t ht π : Measure ℝ),b∈Icc (1:ℝ) D.U := by
  apply (ae_map_iff measurable_subtype_coe.aemeasurable measurableSet_Icc).mpr
  exact ae_of_all _ fun b => b.property

theorem band_strip_limit (N : ℕ) (S : Sequence D P t ht N) (k : Fin 3)
    (cut b : ℝ) (hcb : cut< b)
    (hstrip : ∀ᶠ j in atTop,(ProbabilityMeasure.toMeasure (S.law j k).1) {x | cut<(x.2:ℝ)}=0) :
    (Sequence.realBaseLaw k S.limit : Measure ℝ) {b}=0 := by
  have hz : ∀ᶠ j in atTop,(Sequence.realBaseLaw k (S.law j) : Measure ℝ) (Ioi cut)=0 := by
    filter_upwards [hstrip] with j hj
    change (((ProbabilityMeasure.toMeasure (S.law j k).1).map (fun x => (x.2:ℝ))) (Ioi cut))=0
    rw [Measure.map_apply measurable_snd.subtype_val measurableSet_Ioi]
    exact hj
  have hl := open_null_of_eventually_null
    (fun j => Sequence.realBaseLaw k (S.law j)) (Sequence.realBaseLaw k S.limit)
    (S.realBaseLaw_tendsto k) (Ioi cut) isOpen_Ioi hz
  exact measure_mono_null (by simpa only [singleton_subset_iff,mem_Ioi] using hcb) hl

theorem common_top_atom_zero (N : ℕ) (S : Sequence D P t ht N)
    (bulkCut tailCut : ℝ) (hbulk : bulkCut<1+D.u) (htail : tailCut< D.U)
    (hB : ∀ᶠ j in atTop,(ProbabilityMeasure.toMeasure (S.law j 0).1) {x | bulkCut<(x.2:ℝ)}=0)
    (hT : ∀ᶠ j in atTop,(ProbabilityMeasure.toMeasure (S.law j 1).1) {x | tailCut<(x.2:ℝ)}=0) :
    (baseRealLaw D P t ht S.limit : Measure ℝ) {D.U}=0 := by
  have hb := band_strip_limit D P t ht N S 0 bulkCut D.U (hbulk.trans_le D.huU) hB
  have ht' := band_strip_limit D P t ht N S 1 tailCut D.U htail hT
  have hbR : (ProbabilityMeasure.toMeasure (S.limit 0).1).real (typedCluster D P t 0 {D.U})=0 := by
    rw [←OrderedAtomPartialLimit.realBaseLaw_cluster D P t ht S.limit 0 _ (measurableSet_singleton _)]
    exact congrArg ENNReal.toReal hb
  have htR : (ProbabilityMeasure.toMeasure (S.limit 1).1).real (typedCluster D P t 1 {D.U})=0 := by
    rw [←OrderedAtomPartialLimit.realBaseLaw_cluster D P t ht S.limit 1 _ (measurableSet_singleton _)]
    exact congrArg ENNReal.toReal ht'
  have hz : (baseRealLaw D P t ht S.limit : Measure ℝ).real {D.U}=0 := by
    rw [baseRealLaw_formula D P t ht S.limit _ (measurableSet_singleton _),hbR,htR]
    ring
  exact ((ENNReal.toReal_eq_zero_iff _).mp hz).resolve_right (measure_ne_top _ _)

variable (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H) (N : ℕ)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀ v,t< v→ H≤ upperBid v)
  (S : Sequence D P t ht (N+1))

include hfloor in
theorem common_atomless (hN : 0< N) {C Q bulkCut tailCut : ℝ}
    (hξh : D.ξ<1/2) (hη : D.eta=1-2*D.ξ) (heps : D.eps≤1)
    (hC : 1≤ C) (hBC : D.B≤ C) (hCF : C< D.F) (hFtwo : D.F≤2)
    (hrare : (1-D.ξ)*D.B+D.ξ*D.B*((N+2:ℕ)*
      (tailMass P t/(partialMass+tailMass P t)))≤ D.R)
    (hQ : 0≤ Q)
    (hstrict : 2*(t+2*C+1)*Q<
      ActiveGainUniformModulus.populationCoefficient (N+2) D.ξ D.width
        (OrderedAtomFiniteGain.minFlag D) D.F C*(1/2-(75/4:ℝ)/Real.sqrt N))
    (hbeta : ConditionalBetaControl D P t ht hdR H hBH N πL upperBid hupperBid S Q)
    (hbulk : bulkCut<1+D.u) (htail : tailCut< D.U)
    (hB : ∀ j,(ProbabilityMeasure.toMeasure (S.law j 0).1) {x | bulkCut<(x.2:ℝ)}=0)
    (hT : ∀ᶠ j in atTop,(ProbabilityMeasure.toMeasure (S.law j 1).1) {x | tailCut<(x.2:ℝ)}=0) :
    NullSingletonClass (baseRealLaw D P t ht S.limit : Measure ℝ) := by
  constructor
  intro b
  by_cases hb : b∈Icc (1:ℝ) D.U
  · rcases lt_or_eq_of_le hb.2 with hbU | rfl
    · exact active_atom_zero D P t ht hdR H hBH N πL upperBid hupperBid hfloor S
        hN hξh hη heps hC hBC hCF hFtwo hrare hQ hstrict hbeta hbulk hB b hb.1 hbU
    · exact common_top_atom_zero D P t ht (N+1) S bulkCut tailCut hbulk htail
        (Eventually.of_forall hB) hT
  · apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [common_support D P t ht S.limit] with x hx hxb
    exact hb (by simpa only [mem_singleton_iff.mp hxb] using hx)

end FCAppendix.Affine.Tail04.OrderedAtomActiveAtomless

namespace FCAppendix.Affine.Tail04.OrderedAtomActiveAtomless
open MeasureTheory ProbabilityTheory Set Classical
open Existence.Distributional OriginalValues FiniteTailNoisyGame SourceTailNoisyFixedPoint
open OrderedOriginalNoisySequence OrderedAtomClusterLaws LatentSpeciesCalculus

variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)

theorem component_atomless (π : JointProfile D P t ht)
    (hcommon : NullSingletonClass (baseRealLaw D P t ht π : Measure ℝ)) :
    NullSingletonClass (Sequence.realBaseLaw 0 π : Measure ℝ) ∧
      NullSingletonClass (Sequence.realBaseLaw 1 π : Measure ℝ) := by
  have ha := activeWeight_pos P t ht
  have hs0 : 0<(originalBulkShare P t ht:ℝ) := div_pos P.bulkWeight_pos ha
  change 0<P.bulkWeight+P.truncatedTailWeight t at ha
  have hs1 : 0<1-(originalBulkShare P t ht:ℝ) := by
    have hh : P.bulkWeight/(P.bulkWeight+P.truncatedTailWeight t)<1 :=
      (div_lt_one ha).mpr (by linarith [P.truncatedTailWeight_pos t ht])
    exact sub_pos.mpr hh
  have hzero (b : ℝ) :
      (ProbabilityMeasure.toMeasure (π 0).1).real (typedCluster D P t 0 {b})=0 ∧
        (ProbabilityMeasure.toMeasure (π 1).1).real (typedCluster D P t 1 {b})=0 := by
    have hmass : (baseRealLaw D P t ht π : Measure ℝ).real {b}=0 := by
      letI := hcommon
      simp only [measureReal_def,measure_singleton,ENNReal.toReal_zero]
    rw [baseRealLaw_formula D P t ht π {b} (measurableSet_singleton _)] at hmass
    have h0 : 0≤(ProbabilityMeasure.toMeasure (π 0).1).real (typedCluster D P t 0 {b}) := measureReal_nonneg
    have h1 : 0≤(ProbabilityMeasure.toMeasure (π 1).1).real (typedCluster D P t 1 {b}) := measureReal_nonneg
    constructor <;> nlinarith [mul_nonneg hs0.le h0,mul_nonneg hs1.le h1]
  constructor
  · constructor
    intro b
    have hz := (hzero b).1
    rw [←OrderedAtomPartialLimit.realBaseLaw_cluster D P t ht π 0 {b} (measurableSet_singleton _)] at hz
    exact ((ENNReal.toReal_eq_zero_iff _).mp hz).resolve_right (measure_ne_top _ _)
  · constructor
    intro b
    have hz := (hzero b).2
    rw [←OrderedAtomPartialLimit.realBaseLaw_cluster D P t ht π 1 {b} (measurableSet_singleton _)] at hz
    exact ((ENNReal.toReal_eq_zero_iff _).mp hz).resolve_right (measure_ne_top _ _)

end FCAppendix.Affine.Tail04.OrderedAtomActiveAtomless
