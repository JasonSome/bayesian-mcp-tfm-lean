import FCAppendix.Affine.Tail04.NativeZeroNoiseSource
import FCAppendix.Affine.Tail04.NoisyCommonRowLaw

noncomputable section
namespace FCAppendix.Affine.Tail04.ZeroCommonRowLaw
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues CompactSourceBidLaws
open SourceTailNoisyFixedPoint NativeZeroNoiseSource ActiveJointMerge
open scoped BigOperators

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (π : JointProfile D P t ht)

theorem original_common_base_law :
    bidMarginal (active D P t ht π).1=
      (installOriginal D P t ht).commonLaw (bidLaws D P t ht π) := by
  apply ProbabilityMeasure.toMeasure_injective
  change (ProbabilityMeasure.toMeasure (mergedActiveJoint P t ht D.u D.U D.huU (π 0) (π 1))).map Prod.snd=_
  rw [mergedActiveJoint,NoisyCommonRowLaw.normalizedTwo_eq_mixture]
  rw [NoisyPrivateLaws.map_mixture _ _ _ Prod.snd measurable_snd]
  congr 1
  · congr 1
    change ((ProbabilityMeasure.toMeasure (π 0).1).map
      (bulkEmbedding P t ht D.u D.U D.huU)).map Prod.snd=_
    erw [Measure.map_map measurable_snd
      (continuous_bulkEmbedding P t ht D.u D.U D.huU).measurable]
    change (ProbabilityMeasure.toMeasure (π 0).1).map ((extendBid D.huU)∘Prod.snd)=_
    exact (Measure.map_map (continuous_extendBid _).measurable measurable_snd).symm
  · congr 1
    change ((ProbabilityMeasure.toMeasure (π 1).1).map (tailEmbedding P t D.U)).map Prod.snd=_
    erw [Measure.map_map measurable_snd (continuous_tailEmbedding P t D.U).measurable]
    rfl

theorem original_common_atomless
    [NullSingletonClass
      (((installOriginal D P t ht).commonLaw (bidLaws D P t ht π)).map
        measurable_subtype_coe.aemeasurable : Measure ℝ)] :
    NullSingletonClass (bidMarginal (active D P t ht π).1 : Measure (Icc (1:ℝ) D.U)) := by
  rw [original_common_base_law D P t ht π]
  constructor
  intro x
  have hh := measure_singleton (μ:=
    (((installOriginal D P t ht).commonLaw (bidLaws D P t ht π)).map
      measurable_subtype_coe.aemeasurable : Measure ℝ)) (x:ℝ)
  change ((ProbabilityMeasure.toMeasure ((installOriginal D P t ht).commonLaw (bidLaws D P t ht π))).map
    (Subtype.val : Icc (1:ℝ) D.U→ℝ)) {(x:ℝ)}=0 at hh
  erw [Measure.map_apply measurable_subtype_coe (measurableSet_singleton _)] at hh
  have he : (Subtype.val : Icc (1:ℝ) D.U→ℝ) ⁻¹' {(x:ℝ)}={x} := by
    ext y
    exact Subtype.val_injective.eq_iff
  rwa [he] at hh

section Rows
variable {L U : ℝ} (μ : ProbabilityMeasure (Icc L U))
  [NullSingletonClass (μ : Measure (Icc L U))]

lemma ae_ne_fixed (b : Icc L U) : ∀ᵐ(x : Icc L U) ∂(ProbabilityMeasure.toMeasure μ),(x:ℝ)≠(b:ℝ) := by
  have hh : ∀ᵐ(x : Icc L U) ∂(ProbabilityMeasure.toMeasure μ),x≠b := by
    rw [ae_iff]
    simpa only [not_not,Set.setOf_eq_eq_singleton] using (measure_singleton (μ:=(ProbabilityMeasure.toMeasure μ)) b)
  exact hh.mono (fun x hx he=> hx (Subtype.ext he))

theorem ae_cons_injective (A : ℕ) (b : Icc L U) :
    ∀ᵐ(row : Fin A→Icc L U) ∂Measure.pi (fun _ : Fin A=>(ProbabilityMeasure.toMeasure μ)),
      Function.Injective (fun j=>((Fin.cons b row : Fin (A+1)→Icc L U) j:ℝ)) := by
  have hf : ∀ᵐ(row : Fin A→Icc L U) ∂Measure.pi (fun _ : Fin A=>(ProbabilityMeasure.toMeasure μ)),
      ∀j,(row j:ℝ)≠(b:ℝ) :=
    ae_all_iff.mpr (fun j=>(measurePreserving_eval
      (fun _ : Fin A=>(ProbabilityMeasure.toMeasure μ)) j).quasiMeasurePreserving.ae (ae_ne_fixed μ b))
  have hp : ∀ᵐ(row : Fin A→Icc L U) ∂Measure.pi (fun _ : Fin A=>(ProbabilityMeasure.toMeasure μ)),
      ∀i j,i≠j→(row i:ℝ)≠(row j:ℝ) := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    by_cases hij : i=j
    · subst j
      exact ae_of_all _ (fun _ h=>(h rfl).elim)
    · have hd : ∀ᵐp ∂(ProbabilityMeasure.toMeasure μ).prod (ProbabilityMeasure.toMeasure μ),(p.1:ℝ)≠(p.2:ℝ) := by
        apply (Measure.ae_prod_iff_ae_ae
          (measurableSet_eq_fun measurable_fst.subtype_val measurable_snd.subtype_val).compl).mpr
        exact ae_of_all _ (fun x=>(ae_ne_fixed μ x).mono (fun y hy=> hy.symm))
      have hind := (iIndepFun_pi (μ:=fun _ : Fin A=>(ProbabilityMeasure.toMeasure μ))
        (X:=fun _=> id) (fun _=> measurable_id.aemeasurable)).indepFun hij
      have hm := hind.map_prod_eq_prod_map_map
        (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
      rw [(measurePreserving_eval (fun _ : Fin A=>(ProbabilityMeasure.toMeasure μ)) i).map_eq,
        (measurePreserving_eval (fun _ : Fin A=>(ProbabilityMeasure.toMeasure μ)) j).map_eq] at hm
      have hmap : MeasurePreserving (fun row : Fin A→ Icc L U=>(row i,row j))
          (Measure.pi (fun _ : Fin A=>(ProbabilityMeasure.toMeasure μ))) ((ProbabilityMeasure.toMeasure μ).prod (ProbabilityMeasure.toMeasure μ)) :=
        ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j),hm⟩
      exact (hmap.quasiMeasurePreserving.ae hd).mono (fun row hrow _=> hrow)
  filter_upwards [hf,hp] with row hf hp
  have hd : ∀i j : Fin (A+1),i≠j→((Fin.cons b row : Fin (A+1)→Icc L U) i:ℝ)≠((Fin.cons b row : Fin (A+1)→Icc L U) j:ℝ) := by
    intro i
    refine Fin.cases ?_ (fun i=>?_) i
    · intro j
      refine Fin.cases ?_ (fun j=>?_) j
      · intro hne
        exact (hne rfl).elim
      · intro _
        simpa only [Fin.cons_zero,Fin.cons_succ] using (hf j).symm
    · intro j
      refine Fin.cases ?_ (fun j=>?_) j
      · intro _
        simpa only [Fin.cons_zero,Fin.cons_succ] using hf i
      · intro hne
        exact hp i j (fun h=> hne (congrArg Fin.succ h))
  intro i j hij
  by_contra hne
  exact hd i j hne hij

end Rows
end FCAppendix.Affine.Tail04.ZeroCommonRowLaw
