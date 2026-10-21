import FCAppendix.Affine.Tail04.OrderedNativeNoisySource
import FCAppendix.Affine.Tail04.NoisyCommonRowLaw
import FCAppendix.Affine.Tail04.NativeCountGuards
import FCAppendix.Affine.Tail04.NativeDeletedCounts

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedNoisyNativeCategories
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation CompactSourceBidLaws
open SourceTailNoisyFixedPoint OrderedNativeNoisySource OriginalFiniteFibers NativeDeletedCounts
open scoped BigOperators

section FiniteMixture
variable {I A : Type*} [Fintype I] [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

lemma probabilityMeasure_finiteMix (w : FiniteLaw I) (μ : I → FiniteLaw A) :
    FiniteLaw.probabilityMeasure (FiniteLaw.finiteMix w μ)=
      ∑ i,ENNReal.ofReal (w.mass i) • FiniteLaw.probabilityMeasure (μ i) := by
  apply Measure.ext_of_singleton
  intro a
  rw [FiniteLaw.probabilityMeasure_singleton]
  simp only [Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul,
    FiniteLaw.probabilityMeasure_singleton]
  change ENNReal.ofReal (∑ i,w.mass i*(μ i).mass a)=_
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (w.nonneg i) ((μ i).nonneg a))]
  apply Finset.sum_congr rfl
  intro i _
  exact ENNReal.ofReal_mul (w.nonneg i)
end FiniteMixture

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M<t)
    (hdR : P.d0<D.R) (H : ℝ) (hBH : D.B<H)
    (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
    (π : JointProfile D P t ht)
    (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)
    (hfloor : ∀ v,t<v → H≤upperBid v)

lemma source_category_positive (k : Fin 4) : 0<(originalCategories P t ht).mass k := by
  fin_cases k
  · exact P.low_mass_pos
  · exact add_pos P.bulkWeight_pos (P.truncatedTailWeight_pos t ht)
  · change 0<(partialMass+(activeMass P.theta*P.zeta*powerTail P.M 10 t))/2
    exact div_pos (add_pos_of_pos_of_nonneg (by norm_num [partialMass]) (P.tailMass_nonneg t ht.le)) (by norm_num)
  · change 0<(partialMass+(activeMass P.theta*P.zeta*powerTail P.M 10 t))/2
    exact div_pos (add_pos_of_pos_of_nonneg (by norm_num [partialMass]) (P.tailMass_nonneg t ht.le)) (by norm_num)

section GivenGame
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (hjoint : Γ.F ⊗ₘ Γ.σ=((joint D P t ht πL π upperBid hupperBid) : Measure (ℝ×JointAction 2)))

include πL π upperBid hupperBid hfloor hjoint in
theorem native_source_category_law :
    FiniteLaw.ofMeasure (userLaw Γ) (regions D P hdR H hBH).coarseTag (regions D P hdR H hBH).measurable_coarseTag=(originalCategories P t ht) := by
  have hsum : lowMass P.theta+(activeMass P.theta-(activeMass P.theta*P.zeta*powerTail P.M 10 t))+(partialMass+(activeMass P.theta*P.zeta*powerTail P.M 10 t))=1 := by
    linarith [mass_sum P.theta]
  have hh : 0≤partialMass+(activeMass P.theta*P.zeta*powerTail P.M 10 t) := add_nonneg (by norm_num [partialMass]) (P.tailMass_nonneg t ht.le)
  have hr := native_original_exact_low_row (regions D P hdR H hBH) P rfl t ht.le πL
    (partialPhysical D P t ht π) (activePhysical D P t ht π) upperBid hupperBid hfloor Γ hjoint
  rw [NativeCountGuards.one_native_category_law Γ (regions D P hdR H hBH) (lowMass P.theta) (activeMass P.theta-(activeMass P.theta*P.zeta*powerTail P.M 10 t))
    (partialMass+(activeMass P.theta*P.zeta*powerTail P.M 10 t)) P.low_mass_pos.le (P.movingActiveMass_positive t ht.le).le hh hsum
    (LowBody.realLowBidLaw πL.1 : Measure ℝ) hr]
  apply FiniteLaw.ext
  intro k
  rw [LowBody.categoryLaw_mass]
  simp only [originalCategories,←P.component_weight_sum t,tailMass]

include πL π upperBid hupperBid hfloor hjoint in
theorem native_source_category_mass (k : Fin 4) :
    (userLaw Γ) ((regions D P hdR H hBH).coarseTag ⁻¹' {k})=ENNReal.ofReal ((originalCategories P t ht).mass k) := by
  have h := congrArg (fun ν : FiniteLaw (Fin 4) => ν.mass k)
    (native_source_category_law D P t ht hdR H hBH πL π upperBid hupperBid hfloor Γ hjoint)
  rw [FiniteLaw.ofMeasure_mass] at h
  have he : {x : UserDraw 2 | (regions D P hdR H hBH).coarseTag x=k}=(regions D P hdR H hBH).coarseTag ⁻¹' {k} := rfl
  rw [he] at h
  rw [←h,ENNReal.ofReal_toReal (measure_ne_top _ _)]

include t ht πL π upperBid hupperBid hfloor hjoint in
theorem native_source_category_ne_zero (k : Fin 4) :
    (userLaw Γ) ((regions D P hdR H hBH).coarseTag ⁻¹' {k})≠0 := by
  rw [native_source_category_mass D P t ht hdR H hBH πL π upperBid hupperBid hfloor Γ hjoint]
  exact (ENNReal.ofReal_pos.mpr (source_category_positive P t ht k)).ne'

include πL π upperBid hupperBid hfloor hjoint in
theorem native_pattern_weight {N : ℕ} (kind : Fin N → Fin 4) :
    (∏ i,userLaw Γ ((regions D P hdR H hBH).coarseTag ⁻¹' {kind i}))=
      ENNReal.ofReal ((CommonList.iid (originalCategories P t ht) N).mass kind) := by
  simp_rw [native_source_category_mass D P t ht hdR H hBH πL π upperBid hupperBid hfloor Γ hjoint]
  change (∏ i,ENNReal.ofReal ((originalCategories P t ht).mass (kind i)))=ENNReal.ofReal (∏ i,(originalCategories P t ht).mass (kind i))
  exact (ENNReal.ofReal_prod_of_nonneg (fun i _ => (originalCategories P t ht).nonneg (kind i))).symm

end GivenGame

section Focal
variable (N : ℕ)
variable (hrare : (1-D.ξ)*D.B+D.ξ*D.B*(((N+1):ℝ)*((activeMass P.theta*P.zeta*powerTail P.M 10 t)/(partialMass+(activeMass P.theta*P.zeta*powerTail P.M 10 t))))≤D.R)

def fiberMeasure (kind : Fin N → Fin 4) : Measure (DeletedSample N NativeLocalPolicy.Seed) :=
  ((Measure.pi (fun j => cond (userLaw (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare))) ((regions D P hdR H hBH).coarseTag ⁻¹' {kind j}))).prod
    (Measure.pi (fun _ : Fin 2 => (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare)).seedLaw))).prod (permLaw 2)

instance fiberMeasure_probability (kind : Fin N → Fin 4) :
    IsProbabilityMeasure (fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind) := by
  haveI (j : Fin N) : IsProbabilityMeasure (cond (userLaw (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare))) ((regions D P hdR H hBH).coarseTag ⁻¹' {kind j})) :=
    cond_isProbabilityMeasure (native_source_category_ne_zero D P t ht hdR H hBH πL π
      upperBid hupperBid hfloor (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare))
      (game_original_joint D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare)) (kind j))
  unfold fiberMeasure
  infer_instance

def fiberCount (kind : Fin N → Fin 4) (i : Fin (N+1)) (a : JointAction 2) : CountLaw 2 :=
  FiniteLaw.ofMeasure
    (fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind)
    (deletedCount (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare)) i a) (measurable_deletedCount (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare)) i a)

theorem native_count_mixture (i : Fin (N+1)) (a : JointAction 2) :
    (problem (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare)) i).outcome a=FiniteLaw.finiteMix (CommonList.iid (originalCategories P t ht) N)
      (fun kind => fiberCount D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind i a) := by
  have hmap := native_count_finite_fibers (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare)) (regions D P hdR H hBH).coarseTag (regions D P hdR H hBH).measurable_coarseTag i a
  simp_rw [native_pattern_weight D P t ht hdR H hBH πL π upperBid hupperBid hfloor (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare))
    (game_original_joint D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare))] at hmap
  have htarget : (sampleLaw (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare))).map (focalCount (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare)) i a)=
      FiniteLaw.probabilityMeasure (FiniteLaw.finiteMix (CommonList.iid (originalCategories P t ht) N)
        (fun kind => fiberCount D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind i a)) := by
    rw [probabilityMeasure_finiteMix]
    simp only [fiberCount,FiniteLaw.probabilityMeasure_ofMeasure]
    exact hmap
  have hh := FiniteLaw.ofMeasure_eq_of_map_eq_probabilityMeasure (sampleLaw (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare)))
    (focalCount (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare)) i a) (measurable_focalCount (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare)) i a) _ htarget
  apply Eq.trans ?_ hh
  let Γ0 := game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1)
    (by simpa only [Nat.cast_add,Nat.cast_one] using hrare)
  change (problem Γ0 i).outcome a=FiniteLaw.ofMeasure (sampleLaw Γ0)
    (focalCount Γ0 i a) (measurable_focalCount Γ0 i a)
  apply FiniteLaw.ext
  intro r
  change (∫ω,if focalCount Γ0 i a ω=r then (1:ℝ) else 0 ∂sampleLaw Γ0)=_
  apply integral_congr_ae
  exact ae_of_all _ (fun ω=>by
    by_cases h : focalCount Γ0 i a ω=r <;> simp [h])

theorem native_count_statistic_mixture (i : Fin (N+1)) (a : JointAction 2) (f : Fin 3 → ℝ) :
    ((problem (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare)) i).outcome a).expect f=(CommonList.iid (originalCategories P t ht) N).expect (fun kind =>
      (fiberCount D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind i a).expect f) := by
  rw [native_count_mixture D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i a,
    FiniteLaw.expect_finiteMix]

end Focal
end FCAppendix.Affine.Tail04.OrderedNoisyNativeCategories
