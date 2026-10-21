import FCAppendix.Affine.Tail04.OriginalPrivateSignalLaw
import FCAppendix.Affine.Tail04.NativeSourcePolicy

noncomputable section
namespace FCAppendix.Affine.Tail04.OriginalPrivatePositiveLevels
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation
open OriginalPrivateSource OriginalPrivateSignalLaw EqualPrivateSignal EqualPrivateUpper
open CompactSourceBidLaws NoisyPrivateLaws

def PositiveLevelNull {H : ℕ} {R Rp : ℝ} (μ : Measure (Signal H R Rp)) : Prop :=
  ∀ a : ℝ,0< a→∀ᵐ s ∂μ,∀ j : Fin H,partialBid (s j)≠a

lemma measurableSet_avoid {H : ℕ} {R Rp : ℝ} (a : ℝ) :
    MeasurableSet {s : Signal H R Rp | ∀ j : Fin H,partialBid (s j)≠a} :=
  by
    convert! MeasurableSet.iInter (fun j : Fin H=>
      (measurableSet_eq_fun
        (continuous_partialBid.measurable.comp (measurable_pi_apply j))
        (measurable_const : Measurable (fun _ : Signal H R Rp=>a))).compl) using 1
    ext x
    simp only [Set.mem_setOf_eq,Set.mem_iInter,Set.mem_compl_iff,Function.comp_apply]

lemma entry_avoids {R Rp : ℝ} (p : unitInterval) (μP : ProbabilityMeasure (Icc R Rp))
    [NullSingletonClass ((μP : Measure (Icc R Rp)).map Subtype.val)] (a : ℝ) (ha : 0< a) :
    ∀ᵐ z ∂(residualEntryLaw p μP : Measure (Unit⊕Icc R Rp)),partialBid z≠a := by
  have hb : ∀ᵐ b : Icc R Rp ∂(μP : Measure (Icc R Rp)),(b:ℝ)≠a := by
    apply (ae_map_iff (μ:=(μP : Measure (Icc R Rp))) (f:=(Subtype.val : Icc R Rp→ℝ))
      (p:=fun b : ℝ=>b≠a) measurable_subtype_coe.aemeasurable
      (measurableSet_singleton a).compl).mp
    exact ((μP : Measure (Icc R Rp)).map (Subtype.val : Icc R Rp→ℝ)).ae_ne a
  have hh : ∀ᵐ z ∂(Measure.dirac (Sum.inl () : Unit⊕Icc R Rp)),partialBid z≠a := by
    simp only [ae_dirac_eq,partialBid]
    exact ha.ne
  have hp : ∀ᵐ z ∂((μP : Measure (Icc R Rp)).map Sum.inr),partialBid z≠a := by
    apply (ae_map_iff measurable_inr.aemeasurable
      (measurableSet_eq_fun continuous_partialBid.measurable measurable_const).compl).mpr
    exact hb
  change ∀ᵐ z ∂(ENNReal.ofReal (p:ℝ) • Measure.dirac (Sum.inl ())+
    ENNReal.ofReal (1-(p:ℝ)) • (μP : Measure (Icc R Rp)).map Sum.inr),partialBid z≠a
  exact ae_add_measure_iff.mpr ⟨Measure.ae_smul_measure hh _,Measure.ae_smul_measure hp _⟩

theorem raw_row (H : ℕ) {R Rp : ℝ} (p : unitInterval)
    (μP : ProbabilityMeasure (Icc R Rp))
    [NullSingletonClass ((μP : Measure (Icc R Rp)).map Subtype.val)] :
    PositiveLevelNull (rowLaw H (residualEntryLaw p μP) : Measure (Signal H R Rp)) := by
  intro a ha
  rw [rowLaw_eq_pi]
  apply ae_all_iff.mpr
  intro j
  exact (measurePreserving_eval (fun _ : Fin H=>(residualEntryLaw p μP : Measure (Unit⊕Icc R Rp))) j).quasiMeasurePreserving.ae (entry_avoids p μP a ha)

theorem sorted_row (E : Observable.Regions) (H : ℕ) (p : unitInterval)
    (μP : ProbabilityMeasure (Icc E.R E.Rp))
    [NullSingletonClass ((μP : Measure (Icc E.R E.Rp)).map Subtype.val)] :
    PositiveLevelNull ((rowLaw H (residualEntryLaw p μP) : Measure (Signal H E.R E.Rp)).map
      (PrivateRowSorting.sortSignal E H)) := by
  intro a ha
  apply (ae_map_iff (PrivateRowSorting.continuous_sortSignal E H).measurable.aemeasurable
    (measurableSet_avoid a)).mpr
  filter_upwards [raw_row H p μP a ha] with s hs
  intro j
  exact hs (PrivateRowSorting.permutation (fun k=> LocalCoordinates.signalKey E (s k)) j)

variable (E : Observable.Regions) (P : ValueParameters) (hd : E.d=P.d0)
  (t : ℝ) (ht : P.M≤ t)
local instance : IsProbabilityMeasure (P.originalMovingActiveLaw t ht) :=
  P.originalMovingActiveLaw_probability t ht
variable (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (πP : Law (A:=Icc E.R E.Rp) P.originalPartialLaw)
  (πA : Law (A:=Icc (1:ℝ) E.U) (P.originalMovingActiveLaw t ht))
  (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀ v,t< v→ E.H≤ upperBid v)

theorem original_sorted_row (H : ℕ)
    [NullSingletonClass ((πP.1 : Measure (Icc (2-P.w) (2+P.w)×Icc E.R E.Rp)).map (fun x=>(x.2:ℝ)))] :
    PositiveLevelNull ((originalPrivateRow E P hd t ht πL πP πA upperBid hupperBid hfloor H
      : Measure (Row H E.R E.Rp E.H)).map signal) := by
  have he : ((bidMarginal πP.1 : ProbabilityMeasure (Icc E.R E.Rp)) : Measure (Icc E.R E.Rp)).map Subtype.val=
      (πP.1 : Measure (Icc (2-P.w) (2+P.w)×Icc E.R E.Rp)).map (fun x=>(x.2:ℝ)) := by
    change ((πP.1 : Measure (Icc (2-P.w) (2+P.w)×Icc E.R E.Rp)).map Prod.snd).map Subtype.val=_
    rw [Measure.map_map measurable_subtype_coe measurable_snd]
    rfl
  letI : NullSingletonClass
      (((bidMarginal πP.1 : ProbabilityMeasure (Icc E.R E.Rp)) : Measure (Icc E.R E.Rp)).map Subtype.val) := by
    rw [he]
    infer_instance
  rw [original_sortedRow_signal_law E P hd t ht πL πP πA upperBid hupperBid hfloor H]
  exact sorted_row E H (privateShare P t ht) (bidMarginal πP.1)

theorem native_signal (m c : ℕ) (ξ width θ eA eR B0 : ℝ)
    (hξ0 : 0< ξ) (hξ1 : ξ<1) (hwidth : 0< width) (hθ0 : 0≤ θ) (hθ1 : θ≤1)
    (hrare : (1-ξ)*E.U+ξ*E.U*((m:ℝ)*
      (activeMass P.theta*P.zeta*powerTail P.M 10 t/
        (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t)))≤ E.R)
    (hdup : (1-ξ)*E.U<1) (H : Fin (m+1))
    [NullSingletonClass ((πP.1 : Measure (Icc (2-P.w) (2+P.w)×Icc E.R E.Rp)).map (fun x=>(x.2:ℝ)))] :
    PositiveLevelNull (WeakProbability.toMeasure
      ((NativeSourcePolicy.data E P hd t ht πL πP πA upperBid hupperBid hfloor
        m c ξ width θ eA eR B0 hξ0 hξ1 hwidth hθ0 hθ1 hrare hdup).signalLaw H)) :=
  original_sorted_row E P hd t ht πL πP πA upperBid hupperBid hfloor H.val

end FCAppendix.Affine.Tail04.OriginalPrivatePositiveLevels
