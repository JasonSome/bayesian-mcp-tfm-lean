import FCAppendix.Affine.Tail04.AmbientSignalSort
import FCAppendix.Affine.Tail04.CompactSourceBidLaws
import FCAppendix.Affine.Tail04.NoisyPrivateLaws
import FCAppendix.Existence.R01PayOnceZeroPayoff

noncomputable section
namespace FCAppendix.Affine.Tail04.FixedAmbientNoise
open TopologicalSpace
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Existence.Distributional EqualPrivateSignal CompactSourceBidLaws

section ParametricMap
variable {P X Y : Type*} [TopologicalSpace P]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [MetrizableSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [CompactSpace Y] [MetrizableSpace Y]

def push (f : P×X→ Y) (hf : Continuous f) (p : P) (μ : ProbabilityMeasure X) :
    ProbabilityMeasure Y :=
  μ.map (f := fun x => f (p,x))
    ((hf.comp (continuous_const.prodMk continuous_id)).measurable.aemeasurable)

omit [MetrizableSpace X] [MetrizableSpace Y] in
lemma continuous_push (f : P×X→ Y) (hf : Continuous f) :
    Continuous (fun z : P×ProbabilityMeasure X=> push f hf z.1 z.2) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral.mpr
  intro g
  have hc := continuous_law_integral (fun z : P×X=> g (f z)) (g.continuous.comp hf)
  convert! hc using 1
  funext z
  exact integral_map (μ := (z.2 : Measure X)) (φ := fun x => f (z.1,x))
    ((hf.comp (continuous_const.prodMk continuous_id)).measurable.aemeasurable)
    g.continuous.aestronglyMeasurable

end ParametricMap

abbrev Noise (E : ℝ) := Icc (0:ℝ) E

def zero (E : ℝ) (hE : 0≤ E) : Noise E := ⟨0,le_rfl,hE⟩

lemma upper_mono {L U E : ℝ} (hL : 0< L) (hLU : L≤ U) (e : Noise E) :
    U*(1+(e:ℝ))≤ U*(1+E) :=
  mul_le_mul_of_nonneg_left (add_le_add le_rfl e.2.2) (hL.le.trans hLU)

lemma base_le_upper {L U E : ℝ} (hL : 0< L) (hLU : L≤ U) (hE : 0≤ E) :
    U≤ U*(1+E) := by nlinarith [mul_nonneg (hL.le.trans hLU) hE]

def physical {L U E : ℝ} (hL : 0< L) (hLU : L≤ U)
    (p : Noise E×(Icc L U×unitInterval)) : Icc L (U*(1+E)) :=
  EqualPrivateAmbient.widen (upper_mono hL hLU p.1) (noisyBid hL p.1.2.1 p.2)

lemma continuous_physical {L U E : ℝ} (hL : 0< L) (hLU : L≤ U) :
    Continuous (physical (E:=E) hL hLU) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : Noise E×(Icc L U×unitInterval)=>
    (p.2.1:ℝ)*(1+(p.1:ℝ)*(p.2.2:ℝ)))
  fun_prop

@[simp] lemma physical_value {L U E : ℝ} (hL : 0< L) (hLU : L≤ U)
    (e : Noise E) (b : Icc L U) (u : unitInterval) :
    (physical hL hLU (e,b,u):ℝ)=(b:ℝ)*(1+(e:ℝ)*(u:ℝ)) := rfl

@[simp] lemma physical_zero {L U E : ℝ} (hL : 0< L) (hLU : L≤ U)
    (hE : 0≤ E) (b : Icc L U) (u : unitInterval) :
    physical hL hLU (zero E hE,b,u)=EqualPrivateAmbient.widen (base_le_upper hL hLU hE) b := by
  apply Subtype.ext
  simp only [physical_value,zero,zero_mul,add_zero,mul_one,EqualPrivateAmbient.widen]

def bidLaw {L U E : ℝ} (hL : 0< L) (hLU : L≤ U)
    (e : Noise E) (μ : ProbabilityMeasure (Icc L U)) : ProbabilityMeasure (Icc L (U*(1+E))) :=
  push (physical hL hLU) (continuous_physical hL hLU) e (productLaw μ uniformLaw)

lemma continuous_bidLaw {L U E : ℝ} (hL : 0< L) (hLU : L≤ U) :
    Continuous (fun p : Noise E×ProbabilityMeasure (Icc L U)=> bidLaw hL hLU p.1 p.2) :=
  (continuous_push (physical hL hLU) (continuous_physical hL hLU)).comp
    (continuous_fst.prodMk (continuous_productLaw.comp (continuous_snd.prodMk continuous_const)))

theorem bidLaw_eq {L U E : ℝ} (hL : 0< L) (hLU : L≤ U)
    (e : Noise E) (μ : ProbabilityMeasure (Icc L U)) :
    bidLaw hL hLU e μ=(noisyBidLaw hL e.2.1 μ).map
      (EqualPrivateAmbient.continuous_widen (upper_mono hL hLU e)).measurable.aemeasurable := by
  apply Subtype.ext
  change ((μ : Measure (Icc L U)).prod (volume : Measure unitInterval)).map
      (fun z=> physical hL hLU (e,z))=
    (((μ : Measure (Icc L U)).prod (volume : Measure unitInterval)).map (noisyBid hL e.2.1)).map _
  rw [Measure.map_map (EqualPrivateAmbient.continuous_widen _).measurable
    (continuous_noisyBid hL e.2.1).measurable]
  rfl

theorem bidLaw_zero {L U E : ℝ} (hL : 0< L) (hLU : L≤ U)
    (hE : 0≤ E) (μ : ProbabilityMeasure (Icc L U)) :
    bidLaw hL hLU (zero E hE) μ=μ.map
      (EqualPrivateAmbient.continuous_widen (base_le_upper hL hLU hE)).measurable.aemeasurable := by
  apply Subtype.ext
  change ((μ : Measure (Icc L U)).prod (volume : Measure unitInterval)).map
    (fun z=> physical hL hLU (zero E hE,z))=(μ : Measure (Icc L U)).map _
  have he : (fun z : Icc L U×unitInterval=> physical hL hLU (zero E hE,z))=
      EqualPrivateAmbient.widen (base_le_upper hL hLU hE) ∘ Prod.fst := by
    funext z
    exact physical_zero hL hLU hE z.1 z.2
  rw [he,←Measure.map_map (EqualPrivateAmbient.continuous_widen _).measurable measurable_fst,
    (measurePreserving_fst (μ:=(μ : Measure (Icc L U))) (ν:=(volume : Measure unitInterval))).map_eq]

def entryLaw {R Up E : ℝ} (hR : 0< R) (hRUp : R≤ Up) (p : unitInterval)
    (e : Noise E) (μ : ProbabilityMeasure (Icc R Up)) :
    ProbabilityMeasure (Unit⊕Icc R (Up*(1+E))) :=
  NoisyPrivateLaws.residualEntryLaw p (bidLaw hR hRUp e μ)

lemma continuous_entryLaw {R Up E : ℝ} (hR : 0< R) (hRUp : R≤ Up) (p : unitInterval) :
    Continuous (fun z : Noise E×ProbabilityMeasure (Icc R Up)=> entryLaw hR hRUp p z.1 z.2) :=
  (continuous_mixture p).comp (continuous_const.prodMk
    ((ProbabilityMeasure.continuous_map continuous_inr).comp (continuous_bidLaw hR hRUp)))

def privateRow {R Up E : ℝ} (hR : 0< R) (hRUp : R≤ Up) (p : unitInterval)
    (H : ℕ) (e : Noise E) (μ : ProbabilityMeasure (Icc R Up)) :
    ProbabilityMeasure (Signal H R (Up*(1+E))) := rowLaw H (entryLaw hR hRUp p e μ)

lemma continuous_privateRow {R Up E : ℝ} (hR : 0< R) (hRUp : R≤ Up)
    (p : unitInterval) (H : ℕ) :
    Continuous (fun z : Noise E×ProbabilityMeasure (Icc R Up)=> privateRow hR hRUp p H z.1 z.2) :=
  (continuous_rowLaw H).comp (continuous_entryLaw hR hRUp p)

theorem entryLaw_eq {R Up E : ℝ} (hR : 0< R) (hRUp : R≤ Up)
    (p : unitInterval) (e : Noise E) (μ : ProbabilityMeasure (Icc R Up)) :
    (entryLaw hR hRUp p e μ : Measure _)=
      (CompactSourceBidLaws.privateEntryLaw hR e.2.1 p μ : Measure (Unit⊕Icc R (Up*(1+(e:ℝ))))).map
        (EqualPrivateAmbient.entry (upper_mono hR hRUp e)) := by
  change ENNReal.ofReal (p:ℝ) • Measure.dirac (Sum.inl ()) +
      ENNReal.ofReal (1-(p:ℝ)) •
        (bidLaw hR hRUp e μ : Measure (Icc R (Up*(1+E)))).map Sum.inr =
    (ENNReal.ofReal (p:ℝ) • Measure.dirac (Sum.inl ()) +
      ENNReal.ofReal (1-(p:ℝ)) •
        (noisyBidLaw hR e.2.1 μ : Measure (Icc R (Up*(1+(e:ℝ))))).map Sum.inr).map
          (EqualPrivateAmbient.entry (upper_mono hR hRUp e))
  rw [Measure.map_add _ _ (EqualPrivateAmbient.continuous_entry _).measurable,
    Measure.map_smul,Measure.map_smul,
    Measure.map_dirac' (EqualPrivateAmbient.continuous_entry _).measurable,bidLaw_eq]
  congr 1
  congr 1
  change (((noisyBidLaw hR e.2.1 μ : Measure (Icc R (Up*(1+(e:ℝ))))).map (EqualPrivateAmbient.widen (upper_mono hR hRUp e))).map
    (Sum.inr : Icc R (Up*(1+E)) → Unit⊕Icc R (Up*(1+E))))=
    (((noisyBidLaw hR e.2.1 μ : Measure (Icc R (Up*(1+(e:ℝ))))).map (Sum.inr : Icc R (Up*(1+(e:ℝ))) → Unit⊕Icc R (Up*(1+(e:ℝ))))).map
      (EqualPrivateAmbient.entry (upper_mono hR hRUp e)))
  rw [Measure.map_map measurable_inr (EqualPrivateAmbient.continuous_widen _).measurable,
    Measure.map_map (EqualPrivateAmbient.continuous_entry _).measurable measurable_inr]
  rfl

theorem privateRow_eq {R Up E : ℝ} (hR : 0< R) (hRUp : R≤ Up)
    (p : unitInterval) (H : ℕ) (e : Noise E) (μ : ProbabilityMeasure (Icc R Up)) :
    (privateRow hR hRUp p H e μ : Measure _)=
      (rawPrivateRow hR e.2.1 p H μ : Measure (Signal H R (Up*(1+(e:ℝ))))).map
        (EqualPrivateAmbient.signal (upper_mono hR hRUp e)) := by
  have he : entryLaw hR hRUp p e μ=(CompactSourceBidLaws.privateEntryLaw hR e.2.1 p μ).map
      (EqualPrivateAmbient.continuous_entry (upper_mono hR hRUp e)).measurable.aemeasurable :=
    Subtype.ext (entryLaw_eq hR hRUp p e μ)
  rw [privateRow,he]
  exact Existence.PayOnceBounded.rowLaw_map H _ _ (EqualPrivateAmbient.continuous_entry _).measurable

def privateBayes (F : Observable.Regions) {Up E : ℝ}
    (hR : 0< F.R) (hRUp : F.R≤ Up) (hV : F.Rp=Up*(1+E))
    (p : unitInterval) (H : ℕ) (e : Noise E) (μ : ProbabilityMeasure (Icc F.R Up)) :
    ProbabilityMeasure (Signal H F.R F.Rp) :=
  (privateRow hR hRUp p H e μ).map
    ((PrivateRowSorting.continuous_sortSignal F H).comp
      (continuous_rowCast hV H)).measurable.aemeasurable

lemma continuous_privateBayes (F : Observable.Regions) {Up E : ℝ}
    (hR : 0< F.R) (hRUp : F.R≤ Up) (hV : F.Rp=Up*(1+E))
    (p : unitInterval) (H : ℕ) :
    Continuous (fun z : Noise E×ProbabilityMeasure (Icc F.R Up)=>
      privateBayes F hR hRUp hV p H z.1 z.2) :=
  (ProbabilityMeasure.continuous_map ((PrivateRowSorting.continuous_sortSignal F H).comp
    (continuous_rowCast hV H))).comp (continuous_privateRow hR hRUp p H)

end FCAppendix.Affine.Tail04.FixedAmbientNoise
