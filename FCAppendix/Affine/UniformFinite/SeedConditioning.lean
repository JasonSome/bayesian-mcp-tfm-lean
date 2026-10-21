import FCAppendix.Affine.Hybrid.ObservedSeed
import FCAppendix.Affine.Hybrid.SupportSampler
import FCAppendix.Affine.UniformFinite.GuardMixture

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open MeasureTheory ProbabilityTheory Set Filter Topology Game
open scoped BigOperators

namespace Literal

def bidKind (zs U b : ℝ) : Fin 3 :=
  if b ≤ zs then 0 else if b ≤ U then 1 else 2

theorem measurable_bidKind (zs U : ℝ) : Measurable (bidKind zs U) := by
  unfold bidKind
  exact Measurable.ite measurableSet_Iic measurable_const
    (Measurable.ite measurableSet_Iic measurable_const measurable_const)

theorem bidKind_boxes {m : ℕ} (zs U : ℝ) (x : Realization m 2) :
    TaggedLocal.BidBoxes (fun i => bidKind zs U (x.action i).bid) x zs U := by
  intro i
  by_cases hs : (x.action i).bid ≤ zs
  · simp [bidKind, hs]
  · by_cases hU : (x.action i).bid ≤ U
    · simp [bidKind, hs, hU, lt_of_not_ge hs]
    · simp [bidKind, hs, hU, lt_of_not_ge hU]

theorem bidKind_routes {m : ℕ} {zs U : ℝ} (hzU : zs ≤ U) (x : Realization m 2)
    (hcast : ∀ i, (x.action i).bid ≤ U → x.recipients i = Finset.univ)
    (hsingle : ∀ i, U < (x.action i).bid → (x.recipients i).card = 1) :
    TaggedLocal.ClassRoutes (fun i => bidKind zs U (x.action i).bid) x := by
  constructor
  · intro i hi
    apply hcast i
    by_cases hs : (x.action i).bid ≤ zs
    · exact hs.trans hzU
    · by_cases hU : (x.action i).bid ≤ U
      · exact hU
      · exact False.elim (hi (by simp [bidKind, hs, hU]))
  · intro i hi
    apply hsingle i
    by_cases hs : (x.action i).bid ≤ zs
    · simp [bidKind, hs] at hi
    · by_cases hU : (x.action i).bid ≤ U
      · simp [bidKind, hs, hU] at hi
      · exact lt_of_not_ge hU

theorem observed_minimum_from_bid_classes {m n : ℕ} {zs U : ℝ}
    (hzU : zs ≤ U) (μB : Measure ℝ) (x : Realization m 2)
    (hcast : ∀ i, (x.action i).bid ≤ U → x.recipients i = Finset.univ)
    (hsingle : ∀ i, U < (x.action i).bid → (x.recipients i).card = 1)
    (e : Fin (n + 1) ≃ {i : Fin m // bidKind zs U (x.action i).bid = 0})
    (j : Fin 2) :
    Hybrid.observedLowSeed zs U μB (observe x j) =
      some (Hybrid.conditionalMinimumSeed μB n (fun k => (x.action (e k)).bid)) := by
  exact Hybrid.observedLowSeed_actual μB
    (fun i => bidKind zs U (x.action i).bid) x hzU (bidKind_boxes zs U x)
    (bidKind_routes hzU x hcast hsingle) e j

theorem conditional_seed_singletons {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Set X) (hS : MeasurableSet S)
    (bid : X → ℝ) (hb : Measurable bid)
    (hnull : ∀ b : ℝ, μ (S ∩ bid ⁻¹' {b}) = 0) :
    ∀ b : ℝ, ((cond μ S).map bid) {b} = 0 := by
  intro b
  rw [Measure.map_apply hb (measurableSet_singleton b), cond_apply hS, hnull b]
  simp

theorem heterogeneous_minimum_seed_joint
    {ι X Y : Type*} [Fintype ι] [MeasurableSpace X] [MeasurableSpace Y]
    (ν : ι → Measure X) [∀ i, IsProbabilityMeasure (ν i)]
    (p : ι → Prop) [DecidablePred p] (n : ℕ) (e : Fin (n + 1) ≃ Subtype p)
    (bid : X → ℝ) (hb : Measurable bid)
    (μB : Measure ℝ) [IsProbabilityMeasure μB]
    (hbid : ∀ j, (ν (e j)).map bid = μB)
    (hnoatoms : ∀ b : ℝ, μB {b} = 0)
    (ω : Measure Y) [IsProbabilityMeasure ω] :
    ((Measure.pi ν).prod ω).map
      (fun x => (Hybrid.conditionalMinimumSeed μB n (fun j => bid (x.1 (e j))),
        ((fun i : {i : ι // ¬ p i} => x.1 i), x.2))) =
      (volume : Measure unitInterval).prod
        ((Measure.pi (fun i : {i : ι // ¬ p i} => ν i)).prod ω) := by
  let rest := Measure.pi (fun i : {i : ι // ¬ p i} => ν i)
  let split : (ι → X) × Y →
      (Fin (n + 1) → ℝ) × (({i : ι // ¬ p i} → X) × Y) :=
    fun x => ((Hybrid.bidBlockSplit p n e bid x.1).1,
      ((Hybrid.bidBlockSplit p n e bid x.1).2, x.2))
  have hsplitM : Measurable split :=
    (((Hybrid.measurable_bidBlockSplit p n e bid hb).comp measurable_fst).fst).prodMk
      ((((Hybrid.measurable_bidBlockSplit p n e bid hb).comp measurable_fst).snd).prodMk
        measurable_snd)
  have hsplit : ((Measure.pi ν).prod ω).map split =
      (Hybrid.lowVectorLaw μB n).prod (rest.prod ω) := by
    have hblock := Hybrid.bidBlockSplit_law ν p n e bid hb μB hbid
    have hassoc := (measurePreserving_prodAssoc (Hybrid.lowVectorLaw μB n) rest ω).map_eq
    calc
      _ = (((Measure.pi ν).prod ω).map
          (Prod.map (Hybrid.bidBlockSplit p n e bid) id)).map MeasurableEquiv.prodAssoc := by
        rw [Measure.map_map MeasurableEquiv.prodAssoc.measurable
          ((Hybrid.measurable_bidBlockSplit p n e bid hb).prodMap measurable_id)]
        rfl
      _ = _ := by
        rw [← Measure.map_prod_map _ _ (Hybrid.measurable_bidBlockSplit p n e bid hb)
          measurable_id, hblock, Measure.map_id]
        exact hassoc
  change ((Measure.pi ν).prod ω).map
    ((Prod.map (Hybrid.conditionalMinimumSeed μB n) id) ∘ split) = _
  calc
    _ = (((Measure.pi ν).prod ω).map split).map
        (Prod.map (Hybrid.conditionalMinimumSeed μB n) id) :=
      (Measure.map_map ((Hybrid.measurable_conditionalMinimumSeed μB n).prodMap measurable_id)
        hsplitM).symm
    _ = _ := by
      rw [hsplit]
      exact Hybrid.conditionalMinimumSeed_joint μB hnoatoms n (rest.prod ω)

theorem integral_finiteLaw {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (P : FiniteLaw Ω) (g : Ω → ℝ) :
    (∫ x, g x ∂FiniteLaw.probabilityMeasure P) = P.expect g := by
  have he : FiniteLaw.ofMeasure (FiniteLaw.probabilityMeasure P) id measurable_id = P :=
    FiniteLaw.ofMeasure_eq_of_map_eq_probabilityMeasure _ id measurable_id P Measure.map_id
  calc
    _ = (FiniteLaw.ofMeasure (FiniteLaw.probabilityMeasure P) id measurable_id).expect g :=
      (FiniteLaw.expect_ofMeasure _ id measurable_id g).symm
    _ = P.expect g := by rw [he]

theorem exists_seed_sampler {X Ω : Type*} [MeasurableSpace X]
    [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] [StandardBorelSpace Ω]
    (P : X → FiniteLaw Ω) (hP : ∀ a, Measurable (fun x => (P x).mass a)) :
    ∃ f : X → unitInterval → Ω,
      Measurable (Function.uncurry f) ∧
      (∀ x u, 0 < (P x).mass (f x u)) ∧
      ∀ x, volume.map (f x) = FiniteLaw.probabilityMeasure (P x) :=
  Hybrid.exists_support_sampler P hP

theorem integrated_seed_kernel {R X Ω : Type*} [MeasurableSpace R]
    [MeasurableSpace X] [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure R) (ν : Measure X) [IsProbabilityMeasure ν]
    (T : R → X × unitInterval) (hT : Measurable T)
    (hTlaw : μ.map T = ν.prod (volume : Measure unitInterval))
    (P : X → FiniteLaw Ω) (f : X → unitInterval → Ω)
    (hf : Measurable (Function.uncurry f))
    (hflaw : ∀ x, volume.map (f x) = FiniteLaw.probabilityMeasure (P x))
    (g : X → Ω → ℝ) (hg : Measurable (Function.uncurry g))
    (C : ℝ) (hbound : ∀ x a, |g x a| ≤ C) :
    (∫ r, g (T r).1 (f (T r).1 (T r).2) ∂μ) =
      ∫ x, (P x).expect (g x) ∂ν := by
  let F : X × unitInterval → ℝ := fun x => g x.1 (f x.1 x.2)
  have hF : Measurable F := hg.comp (measurable_fst.prodMk hf)
  have hi : Integrable F (ν.prod (volume : Measure unitInterval)) :=
    Integrable.of_bound hF.aestronglyMeasurable C
      (Eventually.of_forall (fun x => hbound x.1 (f x.1 x.2)))
  calc
    _ = ∫ x, F x ∂(μ.map T) := (integral_map hT.aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ x, ∫ u, F (x,u) ∂(volume : Measure unitInterval) ∂ν := by
      rw [hTlaw, integral_prod _ hi]
    _ = ∫ x, (P x).expect (g x) ∂ν := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by
        have hfx : Measurable (f x) := hf.comp (measurable_const.prodMk measurable_id)
        have hgx : Measurable (g x) := hg.comp (measurable_const.prodMk measurable_id)
        change (∫ u, g x (f x u) ∂(volume : Measure unitInterval)) = _
        rw [← integral_map hfx.aemeasurable hgx.aestronglyMeasurable, hflaw x,
          integral_finiteLaw])

theorem integrated_seed_limit {R Ω : Type*} [MeasurableSpace R]
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : ℕ → Measure R) (T : ℕ → R → unitInterval)
    (hT : ∀ n, Measurable (T n))
    (hTlaw : ∀ n, (μ n).map (T n) = (volume : Measure unitInterval))
    (f : ℕ → unitInterval → Ω) (hf : ∀ n, Measurable (f n))
    (P : ℕ → FiniteLaw Ω) (P₀ : FiniteLaw Ω)
    (hflaw : ∀ n, volume.map (f n) = FiniteLaw.probabilityMeasure (P n))
    (g : ℕ → Ω → ℝ) (g₀ : Ω → ℝ)
    (hP : ∀ a, Tendsto (fun n => (P n).mass a) atTop (𝓝 (P₀.mass a)))
    (hg : ∀ a, Tendsto (fun n => g n a) atTop (𝓝 (g₀ a))) :
    Tendsto (fun n => ∫ r, g n (f n (T n r)) ∂μ n) atTop (𝓝 (P₀.expect g₀)) := by
  have he (n : ℕ) : (∫ r, g n (f n (T n r)) ∂μ n) = (P n).expect (g n) := by
    have hcomp : (μ n).map (fun r => f n (T n r)) = FiniteLaw.probabilityMeasure (P n) := by
      change (μ n).map (f n ∘ T n) = _
      rw [← Measure.map_map (hf n) (hT n), hTlaw n, hflaw n]
    change (μ n).map (f n ∘ T n) = _ at hcomp
    change (∫ r, g n ((f n ∘ T n) r) ∂μ n) = _
    rw [← integral_map ((hf n).comp (hT n)).aemeasurable
      (measurable_of_countable (g n)).aestronglyMeasurable, hcomp, integral_finiteLaw]
  simp_rw [he, FiniteLaw.expect]
  exact tendsto_finsetSum _ (fun a _ => (hP a).mul (hg a))

end Literal
end FCAppendix.Affine.UniformFinite
