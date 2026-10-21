import FCAppendix.Affine.Tail04.AmbientFiniteGame
import FCAppendix.Affine.Tail04.OriginalNoiseProduct

noncomputable section
namespace FCAppendix.Affine.Tail04.SourceNoiseIntegration
open MeasureTheory ProbabilityTheory Set Classical
open Existence.Distributional CompactSourceBidLaws OriginalNoiseProduct

theorem common (A : ℕ) {L U eps : ℝ} (hL : 0< L) (heps : 0≤ eps)
    (μ : ProbabilityMeasure (Icc L U)) (f : (Fin A→ Icc L (U*(1+eps)))→ℝ)
    (hf : Measurable f) {C : ℝ} (hC : ∀b,|f b|≤ C) :
    (∫b,f b ∂(rowLaw A (noisyBidLaw hL heps μ) : Measure _))=
      ∫base,∫z : Fin A→ unitInterval,f (physicalRow hL heps A (base,z))
        ∂Measure.pi (fun _ : Fin A=>(volume : Measure unitInterval))
        ∂(rowLaw A μ : Measure _) := by
  have hp:=physicalRow_preserves hL heps A μ
  rw [rowLaw_eq_pi,←hp.map_eq,integral_map hp.measurable.aemeasurable hf.aestronglyMeasurable]
  rw [rowLaw_eq_pi]
  exact BoundedProbabilityIntegral.prod _ _ (fun x=>f (physicalRow hL heps A x))
    (hf.comp hp.measurable) (fun x=>hC _)

theorem focal (A : ℕ) {L U eps : ℝ} (hL : 0< L) (heps : 0≤ eps)
    (μ : ProbabilityMeasure (Icc L U)) (price : Icc L U)
    (f : (Fin (A+1)→ Icc L (U*(1+eps)))→ℝ)
    (hf : Measurable f) {C : ℝ} (hC : ∀b,|f b|≤ C) :
    (∫b,∫u : unitInterval,f (Fin.cons (noisyBid hL heps (price,u)) b)
      ∂(volume : Measure unitInterval) ∂(rowLaw A (noisyBidLaw hL heps μ) : Measure _))=
      ∫base,∫z : Fin (A+1)→ unitInterval,f (physicalRow hL heps (A+1) (Fin.cons price base,z))
        ∂Measure.pi (fun _ : Fin (A+1)=>(volume : Measure unitInterval))
        ∂(rowLaw A μ : Measure _) := by
  let g : unitInterval×(Fin A→ Icc L (U*(1+eps)))→ℝ:=
    fun p=> f (Fin.cons (noisyBid hL heps (price,p.1)) p.2)
  have hg : Measurable g := hf.comp (measurable_pi_lambda _ fun i=> by
    refine Fin.cases ?_ (fun j=>(measurable_pi_apply j).comp measurable_snd) i
    exact (continuous_noisyBid hL heps).measurable.comp (measurable_const.prodMk measurable_fst))
  have hp:=splitFocalNoise_preserves hL heps A μ
  calc
    _=∫u : unitInterval,∫b,g (u,b) ∂(rowLaw A (noisyBidLaw hL heps μ) : Measure _)
        ∂(volume : Measure unitInterval) :=
      (BoundedProbabilityIntegral.swap _ _ g hg (fun p=> hC _)).symm
    _=∫p,g p ∂((volume : Measure unitInterval).prod
        (Measure.pi (fun _ : Fin A=>(noisyBidLaw hL heps μ : Measure _)))) := by
      rw [rowLaw_eq_pi]
      exact (BoundedProbabilityIntegral.prod _ _ g hg (fun p=> hC _)).symm
    _=∫p,g (splitFocalNoise hL heps A p)
        ∂(Measure.pi (fun _ : Fin A=>(μ : Measure _))).prod
          (Measure.pi (fun _ : Fin (A+1)=>(volume : Measure unitInterval))) := by
      rw [←hp.map_eq,integral_map hp.measurable.aemeasurable hg.aestronglyMeasurable]
    _=_ := by
      rw [BoundedProbabilityIntegral.prod _ _ (fun p=>g (splitFocalNoise hL heps A p))
        (hg.comp hp.measurable) (fun p=>hC _),rowLaw_eq_pi]
      simp_rw [g,←physical_cons_eq hL heps A price]

theorem widen_row (A : ℕ) {L U V : ℝ} (h : U≤ V)
    (μ : ProbabilityMeasure (Icc L U)) (f : (Fin A→ Icc L V)→ℝ) (hf : Measurable f) :
    (∫b,f b ∂(rowLaw A (μ.map (EqualPrivateAmbient.continuous_widen h).measurable.aemeasurable) : Measure _))=
      ∫b : Fin A→ Icc L U,f (fun i=> EqualPrivateAmbient.widen h (b i))
        ∂(rowLaw A μ : Measure (Fin A→ Icc L U)) := by
  rw [Existence.PayOnceBounded.rowLaw_map A μ _ (EqualPrivateAmbient.continuous_widen h).measurable]
  exact integral_map (measurable_pi_lambda _ fun i=>
    (EqualPrivateAmbient.continuous_widen h).measurable.comp
      (measurable_pi_apply i)).aemeasurable hf.aestronglyMeasurable

end FCAppendix.Affine.Tail04.SourceNoiseIntegration
