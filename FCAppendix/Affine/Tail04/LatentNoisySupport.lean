import FCAppendix.Affine.Tail04.LatentSpeciesCalculus
import FCAppendix.Affine.Tail04.NativeNoisyBindings

noncomputable section
namespace FCAppendix.Affine.Tail04.LatentNoisySupport
open MeasureTheory ProbabilityTheory Set Classical Game Bayes Hybrid
open Existence.Distributional OriginalValues OriginalPopulation
open SourceTailNoisyFixedPoint NativeNoisySource LatentNoisyPopulation
open LatentSpeciesCalculus OriginalFiniteFibers

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht) (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)

def bandRecord (k : Fin 3) (z : Draw) : Prop :=
  value z∈Icc (valueLo P k) (valueHi P t k) ∧
    baseBid z∈Icc (bidLo D k) (bidHi D k) ∧ z.1.1.2.2.routeCount=bandRoutes k

lemma measurableSet_bandRecord (k : Fin 3) : MeasurableSet {z | bandRecord D P t k z} :=
  (measurableSet_Icc.preimage measurable_value).inter
    ((measurableSet_Icc.preimage measurable_baseBid).inter
      (measurableSet_eq_fun ((measurable_routeCount 2).comp measurable_fst.fst.snd.snd) measurable_const))

lemma bandRecord_bandDraw (k : Fin 3) (z : BandDraw D P t k) :
    bandRecord D P t k (bandDraw D P t k z) := by
  exact ⟨z.1.1.1.2,z.1.1.2.2,rfl⟩

theorem original_band_record (k : Fin 3) :
    ∀ᵐ z ∂drawLaw D P t ht πL π upperBid hupperBid,
      label z=bandSpecies k → bandRecord D P t k z := by
  have hlabel : MeasurableSet {z : Draw | label z=bandSpecies k} :=
    measurableSet_eq_fun measurable_label measurable_const
  apply (ae_restrict_iff' hlabel).mp
  rw [drawLaw_restrict_label,component_band]
  apply Measure.ae_smul_measure
  apply (ae_map_iff (measurable_bandDraw D P t k).aemeasurable
    (measurableSet_bandRecord D P t k)).mpr
  exact ae_of_all _ (bandRecord_bandDraw D P t k)

variable (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H) (hfloor : ∀ v,t< v → H≤ upperBid v)
  (N : ℕ)
  (hrare : (1-D.ξ)*D.B+D.ξ*D.B*((N+1:ℕ)*
    (tailMass P t/(partialMass+tailMass P t)))≤ D.R)

local notation "Γ" => NativeNoisySource.game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) hrare
local notation "E" => regions D P hdR H hBH
local notation "μ" => drawLaw D P t ht πL π upperBid hupperBid

def commonSupport (z : Draw) : Prop :=
  sourceBands P E t (realize D z).1 ∧
    ∀ k : Fin 3,label z=bandSpecies k → bandRecord D P t k z

lemma measurableSet_commonSupport : MeasurableSet
    {z | commonSupport D P t hdR H hBH z} := by
  apply MeasurableSet.inter
  · exact (measurableSet_sourceBands P E t).preimage
      (measurable_fst.comp (measurable_realize D))
  · convert MeasurableSet.iInter (fun k : Fin 3 =>
      (show MeasurableSet {z : Draw | label z=bandSpecies k} from
        measurableSet_eq_fun measurable_label measurable_const).compl.union
        (measurableSet_bandRecord D P t k)) using 1
    ext z
    simp only [mem_setOf_eq,mem_iInter,mem_union,mem_compl_iff,imp_iff_not_or]
    rfl

include ht πL π upperBid hupperBid hfloor N hrare in
theorem original_common_support : ∀ᵐ z ∂μ,commonSupport D P t hdR H hBH z := by
  have hb : ∀ᵐ z ∂μ,sourceBands P E t (realize D z).1 := by
    apply (ae_map_iff (measurable_realize D).aemeasurable
      ((measurableSet_sourceBands P E t).preimage measurable_fst)).mp
    rw [realize_original_user D P t ht πL π upperBid hupperBid hdR H hBH hfloor (N+1) hrare]
    exact NativeNoisyBindings.source_user_bands D P t ht hdR H hBH πL π upperBid hupperBid hfloor N
      (by simpa only [tailMass,Nat.cast_add,Nat.cast_one] using hrare)
  have hr : ∀ᵐ z ∂μ,∀ k : Fin 3,label z=bandSpecies k → bandRecord D P t k z :=
    (ae_all_iff).mpr (original_band_record D P t ht πL π upperBid hupperBid)
  exact hb.and hr

theorem original_iid_common_support :
    ∀ᵐ z ∂(Measure.pi (fun _ : Fin (N+1) => μ)).prod
      (Measure.pi (fun _ : Fin 2 => (Γ).seedLaw)),
        ∀ i,commonSupport D P t hdR H hBH (z.1 i) := by
  have hrow : ∀ᵐ row ∂Measure.pi (fun _ : Fin (N+1) => μ),
      ∀ i,commonSupport D P t hdR H hBH (row i) := by
    apply (ae_all_iff).mpr
    intro i
    exact (measurePreserving_eval (fun _ : Fin (N+1) => μ) i).quasiMeasurePreserving.ae
      (original_common_support D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare)
  exact (measurePreserving_fst
    (ν:=Measure.pi (fun _ : Fin 2 => (Γ).seedLaw))).quasiMeasurePreserving.ae hrow

end FCAppendix.Affine.Tail04.LatentNoisySupport
