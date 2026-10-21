import FCAppendix.Affine.Tail04.NativeZeroNoiseSource
import FCAppendix.Affine.Tail04.NativeCountGuards
import FCAppendix.Affine.Tail04.NativeDeletedCounts

noncomputable section
namespace FCAppendix.Affine.Tail04.ZeroNativeCategories
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation CompactSourceBidLaws
open SourceTailNoisyFixedPoint NativeZeroNoiseSource OriginalFiniteFibers NativeDeletedCounts
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

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
    (hdR : P.d0< D.R) (H : ℝ) (hUH : D.U< H)
    (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
    (π : JointProfile D P t ht)
    (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)
    (hfloor : ∀ v,t< v → H≤ upperBid v)

local notation "E" => regions D P hdR H hUH
local notation "z" => activeMass P.theta*P.zeta*powerTail P.M 10 t
local notation "C" => originalCategories P t ht
local notation "J" => joint D P t ht πL π upperBid hupperBid

lemma source_category_positive (k : Fin 4) : 0< (C).mass k := by
  fin_cases k
  · exact P.low_mass_pos
  · exact add_pos P.bulkWeight_pos (P.truncatedTailWeight_pos t ht)
  · change 0<(partialMass+z)/2
    exact div_pos (add_pos_of_pos_of_nonneg (by norm_num [partialMass]) (P.tailMass_nonneg t ht.le)) (by norm_num)
  · change 0<(partialMass+z)/2
    exact div_pos (add_pos_of_pos_of_nonneg (by norm_num [partialMass]) (P.tailMass_nonneg t ht.le)) (by norm_num)

section GivenGame
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (hjoint : (Γ).F ⊗ₘ (Γ).σ=(joint D P t ht πL π upperBid hupperBid : Measure _))

include πL π upperBid hupperBid hfloor hjoint in
theorem native_source_category_law :
    FiniteLaw.ofMeasure (userLaw Γ) (E).coarseTag (E).measurable_coarseTag=C := by
  have hsum : lowMass P.theta+(activeMass P.theta-z)+(partialMass+z)=1 := by
    linarith [mass_sum P.theta]
  have hh : 0≤ partialMass+z := add_nonneg (by norm_num [partialMass]) (P.tailMass_nonneg t ht.le)
  have hr := native_original_exact_low_row E P rfl t ht.le πL
    («partial» D P t ht π) (active D P t ht π) upperBid hupperBid hfloor Γ hjoint
  rw [NativeCountGuards.one_native_category_law Γ E (lowMass P.theta) (activeMass P.theta-z)
    (partialMass+z) P.low_mass_pos.le (P.movingActiveMass_positive t ht.le).le hh hsum
    (LowBody.realLowBidLaw πL.1 : Measure ℝ) hr]
  apply FiniteLaw.ext
  intro k
  rw [LowBody.categoryLaw_mass]
  fin_cases k
  · rfl
  · exact (P.component_weight_sum t).symm
  · rfl
  · rfl

include πL π upperBid hupperBid hfloor hjoint in
theorem native_source_category_mass (k : Fin 4) :
    (userLaw Γ) ((E).coarseTag ⁻¹' {k})=ENNReal.ofReal ((C).mass k) := by
  have h := congrArg (fun ν : FiniteLaw (Fin 4) => ν.mass k)
    (native_source_category_law D P t ht hdR H hUH πL π upperBid hupperBid hfloor Γ hjoint)
  rw [FiniteLaw.ofMeasure_mass] at h
  have he : {x : UserDraw 2 | (E).coarseTag x=k}=(E).coarseTag ⁻¹' {k} := rfl
  rw [he] at h
  rw [←h,ENNReal.ofReal_toReal (measure_ne_top _ _)]

include t ht πL π upperBid hupperBid hfloor hjoint in
theorem native_source_category_ne_zero (k : Fin 4) :
    (userLaw Γ) ((E).coarseTag ⁻¹' {k})≠0 := by
  rw [native_source_category_mass D P t ht hdR H hUH πL π upperBid hupperBid hfloor Γ hjoint]
  exact (ENNReal.ofReal_pos.mpr (source_category_positive P t ht k)).ne'

include πL π upperBid hupperBid hfloor hjoint in
theorem native_pattern_weight {N : ℕ} (kind : Fin N → Fin 4) :
    (∏ i,userLaw Γ ((E).coarseTag ⁻¹' {kind i}))=
      ENNReal.ofReal ((CommonList.iid C N).mass kind) := by
  simp_rw [native_source_category_mass D P t ht hdR H hUH πL π upperBid hupperBid hfloor Γ hjoint]
  change (∏ i,ENNReal.ofReal ((C).mass (kind i)))=ENNReal.ofReal (∏ i,(C).mass (kind i))
  exact (ENNReal.ofReal_prod_of_nonneg (fun i _ => (C).nonneg (kind i))).symm

end GivenGame

section Focal
variable (N : ℕ)
local notation "m" => N+1
variable (hrare : (1-D.ξ)*D.U+D.ξ*D.U*((N+1:ℝ)*
  ((activeMass P.theta*P.zeta*powerTail P.M 10 t)/
    (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t)))≤ D.R)
private lemma castMarketRare {N : ℕ} {x y p q : ℝ}
    (h : x+y*((N+1:ℝ)*p)≤q) : x+y*((((N+1:ℕ):ℝ))*p)≤q := by
  simpa only [Nat.cast_add,Nat.cast_one] using h

local notation "Γ" => game D P t ht hdR H hUH πL π upperBid hupperBid hfloor m (castMarketRare hrare)

def fiberMeasure (kind : Fin N → Fin 4) : Measure (DeletedSample N NativeLocalPolicy.Seed) :=
  ((Measure.pi (fun j => cond (userLaw Γ) ((E).coarseTag ⁻¹' {kind j}))).prod
    (Measure.pi (fun _ : Fin 2 => (Γ).seedLaw))).prod (permLaw 2)

instance fiberMeasure_probability (kind : Fin N → Fin 4) :
    IsProbabilityMeasure (fiberMeasure D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare kind) := by
  haveI (j : Fin N) : IsProbabilityMeasure (cond (userLaw Γ) ((E).coarseTag ⁻¹' {kind j})) :=
    cond_isProbabilityMeasure (native_source_category_ne_zero D P t ht hdR H hUH πL π
      upperBid hupperBid hfloor Γ
      (game_original_joint D P t ht hdR H hUH πL π upperBid hupperBid hfloor m (castMarketRare hrare)) (kind j))
  unfold fiberMeasure
  infer_instance

def fiberCount (kind : Fin N → Fin 4) (i : Fin m) (a : JointAction 2) : CountLaw 2 :=
  FiniteLaw.ofMeasure
    (fiberMeasure D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare kind)
    (deletedCount Γ i a) (measurable_deletedCount Γ i a)

theorem native_count_mixture (i : Fin m) (a : JointAction 2) :
    (problem Γ i).outcome a=FiniteLaw.finiteMix (CommonList.iid C N)
      (fun kind => fiberCount D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare kind i a) := by
  have hmap := native_count_finite_fibers Γ (E).coarseTag (E).measurable_coarseTag i a
  simp_rw [native_pattern_weight D P t ht hdR H hUH πL π upperBid hupperBid hfloor Γ
    (game_original_joint D P t ht hdR H hUH πL π upperBid hupperBid hfloor m (castMarketRare hrare))] at hmap
  have htarget : (sampleLaw Γ).map (focalCount Γ i a)=
      FiniteLaw.probabilityMeasure (FiniteLaw.finiteMix (CommonList.iid C N)
        (fun kind => fiberCount D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare kind i a)) := by
    rw [probabilityMeasure_finiteMix]
    simp only [fiberCount,FiniteLaw.probabilityMeasure_ofMeasure]
    exact hmap
  have hh := FiniteLaw.ofMeasure_eq_of_map_eq_probabilityMeasure (sampleLaw Γ)
    (focalCount Γ i a) (measurable_focalCount Γ i a) _ htarget
  apply Eq.trans ?_ hh
  apply FiniteLaw.ext
  intro r
  change (∫ω,if focalCount Γ i a ω=r then (1:ℝ) else 0 ∂sampleLaw Γ)=_
  apply integral_congr_ae
  exact ae_of_all _ (fun ω=>by
    by_cases h : focalCount Γ i a ω=r <;> simp [h])

theorem native_count_statistic_mixture (i : Fin m) (a : JointAction 2) (f : Fin 3 → ℝ) :
    ((problem Γ i).outcome a).expect f=(CommonList.iid C N).expect (fun kind =>
      (fiberCount D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare kind i a).expect f) := by
  rw [native_count_mixture D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare i a,
    FiniteLaw.expect_finiteMix]

end Focal
end FCAppendix.Affine.Tail04.ZeroNativeCategories
