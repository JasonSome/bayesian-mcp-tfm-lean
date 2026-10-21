import FCAppendix.Affine.Hybrid.SupportSampler
import FCAppendix.Proposer.LotterySupport

noncomputable section
namespace FCAppendix.Affine.Tail04.HierarchicalFiniteSampler
open MeasureTheory ProbabilityTheory Set Classical
open scoped BigOperators

section Integral
variable {X A : Type*} [MeasurableSpace X] [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A]

lemma integrable_finite_comp (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → A) (hf : Measurable f) (g : A → ℝ) : Integrable (fun x => g (f x)) μ := by
  apply Integrable.of_bound ((measurable_of_countable g).comp hf).aestronglyMeasurable
    (∑ a,|g a|)
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (fun a _ => abs_nonneg (g a)) (Finset.mem_univ (f x))
end Integral

section Law
variable {I A : Type*} [Fintype I] [Fintype A]
    [MeasurableSpace I] [MeasurableSpace A]
    [MeasurableSingletonClass I] [MeasurableSingletonClass A]
variable (w : FiniteLaw I) (μ : I → FiniteLaw A)
    (first : unitInterval → I) (hfirst : Measurable first)
    (hfirstLaw : volume.map first=FiniteLaw.probabilityMeasure w)
    (next : I → unitInterval → A) (hnext : Measurable (Function.uncurry next))
    (hnextLaw : ∀ i,volume.map (next i)=FiniteLaw.probabilityMeasure (μ i))

include hfirst hfirstLaw hnext hnextLaw in
theorem product_law :
    ((volume : Measure unitInterval).prod volume).map
      (fun z => next (first z.1) z.2)=
      FiniteLaw.probabilityMeasure (FiniteLaw.finiteMix w μ) := by
  let f : unitInterval×unitInterval → A := fun z => next (first z.1) z.2
  have hf : Measurable f := hnext.comp ((hfirst.comp measurable_fst).prodMk measurable_snd)
  have h0 : FiniteLaw.ofMeasure volume first hfirst=w :=
    FiniteLaw.ofMeasure_eq_of_map_eq_probabilityMeasure volume first hfirst w hfirstLaw
  have h1 (i : I) : FiniteLaw.ofMeasure volume (next i)
      (hnext.comp (measurable_const.prodMk measurable_id))=μ i :=
    FiniteLaw.ofMeasure_eq_of_map_eq_probabilityMeasure volume _ _ _ (hnextLaw i)
  have hfinite : FiniteLaw.ofMeasure ((volume : Measure unitInterval).prod volume) f hf=
      FiniteLaw.finiteMix w μ := by
    apply FiniteLaw.ext_expect
    intro g
    rw [FiniteLaw.expect_ofMeasure,integral_prod _ (integrable_finite_comp _ f hf g)]
    have hin (u : unitInterval) : (∫ v : unitInterval,g (f (u,v)))=(μ (first u)).expect g := by
      rw [←h1 (first u),FiniteLaw.expect_ofMeasure]
    simp_rw [hin]
    rw [←FiniteLaw.expect_ofMeasure volume first hfirst
      (fun i => (μ i).expect g),h0,FiniteLaw.expect_finiteMix]
  rw [←hfinite]
  exact (FiniteLaw.probabilityMeasure_ofMeasure _ f hf).symm

end Law

section Support
variable {I A : Type*} [Fintype I] [Fintype A]

lemma mass_le_map (μ : FiniteLaw I) (f : I → A) (i : I) :
    μ.mass i≤(μ.map f).mass (f i) := by
  classical
  have h := Finset.single_le_sum
    (f:=fun j : I => if f j=f i then μ.mass j else 0)
    (fun j _ => by split <;> first | exact μ.nonneg j | exact le_rfl)
    (Finset.mem_univ i)
  simpa [FiniteLaw.map] using h

lemma mass_mul_le_finiteMix (w : FiniteLaw I) (μ : I → FiniteLaw A) (i : I) (a : A) :
    w.mass i*(μ i).mass a≤(FiniteLaw.finiteMix w μ).mass a :=
  Finset.single_le_sum (fun j _ => mul_nonneg (w.nonneg j) ((μ j).nonneg a))
    (Finset.mem_univ i)

lemma map_support {f : I → A} (μ : FiniteLaw I) (a : A)
    (ha : 0<(μ.map f).mass a) : ∃ i,f i=a ∧ 0< μ.mass i := by
  classical
  by_contra hn
  have hz : (μ.map f).mass a=0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : f i=a
    · have hm : μ.mass i=0 := le_antisymm
        (le_of_not_gt (fun hp => hn ⟨i,hi,hp⟩)) (μ.nonneg i)
      simp only [if_pos hi,hm]
    · simp only [if_neg hi]
  linarith

end Support
end FCAppendix.Affine.Tail04.HierarchicalFiniteSampler
