import FCAppendix.Affine.Hybrid.FiniteSelector
import FCAppendix.Affine.Hybrid.SupportSampler
import Mathlib

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace GuardedData

def observable (G : GuardedData ι) :
    ℝ × (ι → ℝ) × Finset ι × Finset ι × ℕ :=
  (G.xi, G.bid, G.owner₁, G.owner₂, G.residual)

instance : MeasurableSpace (GuardedData ι) :=
  MeasurableSpace.comap observable inferInstance

lemma measurable_observable : Measurable (observable (ι := ι)) := comap_measurable observable
lemma measurable_xi : Measurable (fun G : GuardedData ι => G.xi) :=
  measurable_fst.comp measurable_observable
lemma measurable_bid : Measurable (fun G : GuardedData ι => G.bid) :=
  measurable_fst.comp (measurable_snd.comp measurable_observable)
lemma measurable_owner₁ : Measurable (fun G : GuardedData ι => G.owner₁) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_observable))
lemma measurable_owner₂ : Measurable (fun G : GuardedData ι => G.owner₂) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp measurable_observable)))
lemma measurable_residual : Measurable (fun G : GuardedData ι => G.residual) :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp measurable_observable)))
lemma measurable_mixed : Measurable (fun G : GuardedData ι => G.mixed) := by
  exact (measurable_of_countable (fun x : Finset ι × Finset ι =>
    Finset.univ \ (x.1 ∪ x.2))).comp (measurable_owner₁.prodMk measurable_owner₂)

lemma measurableSet_mem_mixed (i : ι) :
    MeasurableSet {G : GuardedData ι | i ∈ G.mixed} :=
  ((measurable_of_countable (fun S : Finset ι => i ∈ S)).comp measurable_mixed).setOf
lemma measurableSet_mem_owner₁ (i : ι) :
    MeasurableSet {G : GuardedData ι | i ∈ G.owner₁} :=
  ((measurable_of_countable (fun S : Finset ι => i ∈ S)).comp measurable_owner₁).setOf
lemma measurableSet_mem_owner₂ (i : ι) :
    MeasurableSet {G : GuardedData ι | i ∈ G.owner₂} :=
  ((measurable_of_countable (fun S : Finset ι => i ∈ S)).comp measurable_owner₂).setOf

lemma measurable_multiplier : Measurable (fun G : GuardedData ι => G.multiplier) := by
  have hsum : Measurable (fun G : GuardedData ι => ∑ i ∈ G.mixed, (G.bid i)⁻¹) := by
    have he : (fun G : GuardedData ι => ∑ i ∈ G.mixed, (G.bid i)⁻¹) =
        fun G => ∑ i, if i ∈ G.mixed then (G.bid i)⁻¹ else 0 := by
      funext G
      simp
    rw [he]
    apply Finset.measurable_sum
    intro i _
    exact Measurable.ite (measurableSet_mem_mixed i)
      (((measurable_pi_apply i).comp measurable_bid).inv) measurable_const
  have hc : Measurable (fun G : GuardedData ι => (G.mixed.card : ℝ)) :=
    (measurable_of_countable (fun S : Finset ι => (S.card : ℝ))).comp measurable_mixed
  have hr : Measurable (fun G : GuardedData ι => (G.residual : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp measurable_residual
  exact (hc.sub (measurable_xi.mul hr)).div hsum

lemma measurable_exposure (i : ι) :
    Measurable (fun G : GuardedData ι => exposure G.xi G.multiplier (G.bid i)) :=
  (measurable_const.sub (measurable_multiplier.div
    ((measurable_pi_apply i).comp measurable_bid))).div measurable_xi

lemma measurable_p₁ : Measurable (fun G : GuardedData ι => G.p₁) := by
  apply measurable_pi_lambda
  intro i
  exact Measurable.ite (measurableSet_mem_owner₁ i) measurable_const
    (Measurable.ite (measurableSet_mem_mixed i) (measurable_exposure i) measurable_const)
lemma measurable_p₂ : Measurable (fun G : GuardedData ι => G.p₂) := by
  apply measurable_pi_lambda
  intro i
  exact Measurable.ite (measurableSet_mem_owner₂ i) measurable_const
    (Measurable.ite (measurableSet_mem_mixed i) (measurable_exposure i) measurable_const)

lemma measurable_law₁_mass (S : Finset ι) :
    Measurable (fun G : GuardedData ι => G.law₁.mass S) :=
  (ExactCapacity.measurable_symmetricLottery_mass S).comp measurable_p₁
lemma measurable_law₂_mass (S : Finset ι) :
    Measurable (fun G : GuardedData ι => G.law₂.mass S) :=
  (ExactCapacity.measurable_symmetricLottery_mass S).comp measurable_p₂

theorem exists_private_samplers :
    ∃ f₁ f₂ : GuardedData ι → unitInterval → Finset ι,
      Measurable (Function.uncurry f₁) ∧ Measurable (Function.uncurry f₂) ∧
      (∀ (G : GuardedData ι) u, 0 < G.law₁.mass (f₁ G u)) ∧
      (∀ (G : GuardedData ι) u, 0 < G.law₂.mass (f₂ G u)) ∧
      (∀ (G : GuardedData ι), volume.map (f₁ G) = FiniteLaw.probabilityMeasure G.law₁) ∧
      (∀ (G : GuardedData ι), volume.map (f₂ G) = FiniteLaw.probabilityMeasure G.law₂) ∧
      ∀ G,
        ((volume : Measure unitInterval).prod volume).map
          (fun u => (f₁ G u.1, f₂ G u.2)) =
        (FiniteLaw.probabilityMeasure G.law₁).prod (FiniteLaw.probabilityMeasure G.law₂) := by
  obtain ⟨f₁,hf₁,hpos₁,hlaw₁⟩ := exists_support_sampler
    (fun G : GuardedData ι => G.law₁) measurable_law₁_mass
  obtain ⟨f₂,hf₂,hpos₂,hlaw₂⟩ := exists_support_sampler
    (fun G : GuardedData ι => G.law₂) measurable_law₂_mass
  refine ⟨f₁,f₂,hf₁,hf₂,hpos₁,hpos₂,hlaw₁,hlaw₂,?_⟩
  intro G
  have h₁ : Measurable (f₁ G) := hf₁.comp (measurable_const.prodMk measurable_id)
  have h₂ : Measurable (f₂ G) := hf₂.comp (measurable_const.prodMk measurable_id)
  calc
    _ = ((volume : Measure unitInterval).map (f₁ G)).prod (volume.map (f₂ G)) :=
      (Measure.map_prod_map _ _ h₁ h₂).symm
    _ = _ := by rw [hlaw₁ G,hlaw₂ G]

end GuardedData

lemma product_duplicate_probability
    (μ ν : FiniteLaw (Finset ι)) (i : ι) :
    (μ.prod ν).prob (fun ST => i ∈ ST.1 ∧ i ∈ ST.2) =
      μ.prob (fun S => i ∈ S) * ν.prob (fun T => i ∈ T) := by
  classical
  rw [FiniteLaw.prob_eq_expect, FiniteLaw.prob_eq_expect, FiniteLaw.prob_eq_expect]
  have hp (ST : Finset ι × Finset ι) :
      (if i ∈ ST.1 ∧ i ∈ ST.2 then (1 : ℝ) else 0) =
      (if i ∈ ST.1 then (1 : ℝ) else 0)*(if i ∈ ST.2 then (1 : ℝ) else 0) := by
    split_ifs <;> simp_all
  simp_rw [hp]
  exact FiniteLaw.expect_prod_mul μ ν (fun S => if i ∈ S then (1 : ℝ) else 0)
    (fun T => if i ∈ T then (1 : ℝ) else 0)

lemma guarded_duplicate_probability (G : GuardedData ι) (i : ι) :
    G.jointLaw.prob (fun ST => i ∈ ST.1 ∧ i ∈ ST.2) = G.p₁ i*G.p₂ i := by
  rw [GuardedData.jointLaw, product_duplicate_probability,
    G.law₁_implements.2, G.law₂_implements.2]

end FCAppendix.Affine.Hybrid
