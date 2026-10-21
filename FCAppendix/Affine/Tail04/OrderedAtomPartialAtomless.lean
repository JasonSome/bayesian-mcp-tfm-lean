import FCAppendix.Affine.Tail04.OrderedAtomPartialLimit
import FCAppendix.Affine.Tail04.NoisyLocalization

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomPartialAtomless
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Game Bayes Hybrid
open Existence.Distributional OriginalValues OriginalPopulation
open SourceTailNoisyFixedPoint OrderedNativeNoisySource OrderedOriginalNoisySequence
open LatentSpeciesCalculus OrderedNativeBandCarrierIC OrderedAtomPartialLimit

section WeakEndpoint
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem open_null_of_eventually_null
    (μ : ℕ→ ProbabilityMeasure X) (μ₀ : ProbabilityMeasure X)
    (hμ : Tendsto μ atTop (𝓝 μ₀)) (G : Set X) (hG : IsOpen G)
    (hzero : ∀ᶠ j in atTop,(μ j : Measure X) G=0) :
    (μ₀ : Measure X) G=0 := by
  have h := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμ hG
  have he : liminf (fun j=>(μ j : Measure X) G) atTop=0 := by
    rw [liminf_congr hzero,liminf_const]
  rw [he] at h
  exact le_antisymm h bot_le

end WeakEndpoint

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)

theorem base_law_support (π : JointProfile D P t ht) (k : Fin 3) :
    ∀ᵐ b ∂(Sequence.realBaseLaw k π : Measure ℝ),b∈Icc (bidLo D k) (bidHi D k) := by
  apply (ae_map_iff measurable_snd.subtype_val.aemeasurable measurableSet_Icc).mpr
  exact ae_of_all _ (fun x=> x.2.property)

theorem partial_top_strip_limit (N : ℕ) (S : Sequence D P t ht N)
    (cut : ℝ) (hcut : cut< D.Up)
    (hstrip : ∀ᶠ j in atTop,
      (ProbabilityMeasure.toMeasure (S.law j 2).1) {x | cut<(x.2:ℝ)}=0) :
    (Sequence.realBaseLaw 2 S.limit : Measure ℝ) (Ioi cut)=0 ∧
      (Sequence.realBaseLaw 2 S.limit : Measure ℝ) {D.Up}=0 := by
  have hzero : ∀ᶠ j in atTop,
      (Sequence.realBaseLaw 2 (S.law j) : Measure ℝ) (Ioi cut)=0 := by
    filter_upwards [hstrip] with j hj
    change (((ProbabilityMeasure.toMeasure (S.law j 2).1).map (fun x=>(x.2:ℝ))) (Ioi cut))=0
    rw [Measure.map_apply measurable_snd.subtype_val measurableSet_Ioi]
    exact hj
  have hz := open_null_of_eventually_null
    (fun j=> Sequence.realBaseLaw 2 (S.law j)) (Sequence.realBaseLaw 2 S.limit)
    (S.realBaseLaw_tendsto 2) (Ioi cut) isOpen_Ioi hzero
  exact ⟨hz,measure_mono_null (by simpa only [singleton_subset_iff,mem_Ioi] using hcut) hz⟩

variable (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
    (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
    (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H) (hfloor : ∀ v,t< v→ H≤ upperBid v)
    (N : ℕ)
    (hrare : (1-D.ξ)*D.B+D.ξ*D.B*((N+1:ℕ)*
      (tailMass P t/(partialMass+tailMass P t)))≤ D.R)
    (S : Sequence D P t ht N)

theorem partial_atomless
    (hbudget : D.eps≤1) (hlow : P.d0<1-D.ξ)
    (hc : 0< D.c) (hcm : D.c< N+1) (hvalue : D.V<2-P.w)
    (hidentity : ∀ (j : ℕ) (i : Fin (N+1)) x,
      (∫ u,(problem (gameAt D P t ht πL upperBid hupperBid hdR H hBH hfloor N hrare S j) i).payoff
        (x.1:ℝ) (physicalBandAction (S.data j) P t 2 x u)
          ∂(volume : Measure unitInterval))=
        SourceOrderedNoisyFixedPoint.payoff (S.data j) P t ht N 2 (S.law j,x))
    (cut : ℝ) (hcut : cut< D.Up)
    (hstrip : ∀ᶠ j in atTop,
      (ProbabilityMeasure.toMeasure (S.law j 2).1) {x | cut<(x.2:ℝ)}=0) :
    NullSingletonClass (Sequence.realBaseLaw 2 S.limit : Measure ℝ) := by
  constructor
  intro β
  by_cases hβ : β∈Icc D.R D.Up
  · rcases lt_or_eq_of_le hβ.2 with hb | rfl
    · exact partial_interior_atom_zero D P t ht πL upperBid hupperBid hdR H hBH hfloor
        N hrare S hbudget hlow hc hcm hvalue hidentity β hβ.1 hb
    · exact (partial_top_strip_limit D P t ht N S cut hcut hstrip).2
  · apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [base_law_support D P t ht S.limit 2] with b hb hbe
    have hEq : b=β := mem_singleton_iff.mp hbe
    apply hβ
    simpa [hEq,bidLo,bidHi] using hb

end FCAppendix.Affine.Tail04.OrderedAtomPartialAtomless
