import FCAppendix.Affine.Hybrid.Seed
import FCAppendix.Game.PosteriorBeliefs

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

variable {ι X K : Type*} [Fintype ι] [MeasurableSpace X]
  [MeasurableSpace K] [MeasurableSingletonClass K]

def categoryFiber (tag : X → K) (k : ι → K) : Set (ι → X) :=
  Set.univ.pi (fun i => tag ⁻¹' {k i})

lemma measurableSet_categoryFiber (tag : X → K) (htag : Measurable tag) (k : ι → K) :
    MeasurableSet (categoryFiber tag k) :=
  MeasurableSet.univ_pi (fun i => htag (measurableSet_singleton (k i)))

theorem conditional_categoryFiber (μ : Measure X) [IsProbabilityMeasure μ]
    (tag : X → K) (htag : Measurable tag) (k : ι → K) :
    cond (Measure.pi (fun _ : ι => μ)) (categoryFiber tag k) =
      Measure.pi (fun i : ι => cond μ (tag ⁻¹' {k i})) := by
  symm
  apply Measure.pi_eq
  intro t ht
  rw [cond_apply (measurableSet_categoryFiber tag htag k)]
  have hinter : categoryFiber tag k ∩ Set.univ.pi t =
      Set.univ.pi (fun i => (tag ⁻¹' {k i}) ∩ t i) := by
    exact Set.pi_inter_distrib.symm
  rw [hinter,categoryFiber,Measure.pi_pi,Measure.pi_pi]
  simp_rw [cond_apply (htag (measurableSet_singleton _))]
  rw [ENNReal.prod_inv_distrib (by
    intro i _ j _ _
    exact Or.inr (measure_ne_top μ _)),←Finset.prod_mul_distrib]

omit [MeasurableSpace K] [MeasurableSingletonClass K] in

lemma categoryFiber_mass (μ : Measure X) [IsProbabilityMeasure μ]
    (tag : X → K) (k : ι → K) :
    (Measure.pi (fun _ : ι => μ)) (categoryFiber tag k) =
      ∏ i, μ (tag ⁻¹' {k i}) := by
  exact Measure.pi_pi _ _

theorem native_conditional_categoryFiber {m n c : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (Γ : Bayes.FiniteGame m n c Seed)
    (tag : Bayes.UserDraw n → K) (htag : Measurable tag) (k : Fin m → K) :
    cond (Bayes.userProfileLaw Γ) (categoryFiber tag k) =
      Measure.pi (fun i : Fin m => cond (Bayes.userLaw Γ) (tag ⁻¹' {k i})) :=
  conditional_categoryFiber (Bayes.userLaw Γ) tag htag k

end FCAppendix.Affine.Hybrid
