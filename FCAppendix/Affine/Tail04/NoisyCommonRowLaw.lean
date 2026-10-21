import FCAppendix.Affine.Tail04.NoisyNativeRowLaws
import FCAppendix.Affine.Tail04.OriginalCommonLaw

noncomputable section
namespace FCAppendix.Affine.Tail04.NoisyCommonRowLaw
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues CompactSourceBidLaws
open SourceTailNoisyFixedPoint NativeNoisySource NoisyNativeRowLaws ActiveJointMerge

section Noise
variable {L U V eps : ℝ} (hL : 0< L) (heps : 0≤ eps)

lemma noisyBidLaw_mixture (p : unitInterval)
    (μ ν : ProbabilityMeasure (Icc L U)) :
    noisyBidLaw hL heps (mixture p μ ν)=
      mixture p (noisyBidLaw hL heps μ) (noisyBidLaw hL heps ν) := by
  apply Subtype.ext
  change ((ENNReal.ofReal (p:ℝ) • (μ : Measure (Icc L U))+
    ENNReal.ofReal (1-(p:ℝ)) • (ν : Measure (Icc L U))).prod (volume : Measure unitInterval)).map
      (noisyBid hL heps)=_
  rw [Measure.add_prod,Measure.prod_smul_left,Measure.prod_smul_left,
    Measure.map_add _ _ (continuous_noisyBid hL heps).measurable,
    Measure.map_smul,Measure.map_smul]
  rfl

lemma noisyBidLaw_extend (hUV : U≤ V) (μ : ProbabilityMeasure (Icc L U)) :
    noisyBidLaw hL heps (μ.map (continuous_extendBid hUV).measurable.aemeasurable)=
      (noisyBidLaw hL heps μ).map
        (continuous_extendBid (mul_le_mul_of_nonneg_right hUV (by linarith : 0≤1+eps))).measurable.aemeasurable := by
  apply Subtype.ext
  have he : Measurable (extendBid (L:=L) hUV) := (continuous_extendBid hUV).measurable
  have he' : Measurable (extendBid (L:=L)
      (mul_le_mul_of_nonneg_right hUV (by linarith : 0≤1+eps))) := (continuous_extendBid _).measurable
  change (((μ : Measure (Icc L U)).map (extendBid hUV)).prod (volume : Measure unitInterval)).map
      (noisyBid hL heps)=
    (((μ : Measure (Icc L U)).prod (volume : Measure unitInterval)).map (noisyBid hL heps)).map (extendBid _)
  have hp : ((μ : Measure (Icc L U)).map (extendBid hUV)).prod (volume : Measure unitInterval)=
      ((μ : Measure (Icc L U)).prod (volume : Measure unitInterval)).map (Prod.map (extendBid hUV) id) := by
    rw [←Measure.map_prod_map _ _ he measurable_id,Measure.map_id]
  rw [hp,Measure.map_map (continuous_noisyBid hL heps).measurable (he.prodMap measurable_id),
    Measure.map_map he' (continuous_noisyBid hL heps).measurable]
  congr 1
end Noise

section Merge
variable {X : Type*} [MeasurableSpace X]

lemma normalizedTwo_eq_mixture (x y : ℝ) (hx : 0≤ x) (hy : 0≤ y) (hs : 0< x+y)
    (μ ν : ProbabilityMeasure X) :
    normalizedTwo x y hx hy hs μ ν=
      mixture (⟨x/(x+y),div_nonneg hx hs.le,(div_le_one hs).mpr (le_add_of_nonneg_right hy)⟩ : unitInterval) μ ν := by
  apply Subtype.ext
  have he : y/(x+y)=1-x/(x+y) := by field_simp [hs.ne'];ring
  change ENNReal.ofReal (x/(x+y)) • (μ : Measure X)+ENNReal.ofReal (y/(x+y)) • (ν : Measure X)=_
  rw [he]
  rfl

end Merge

private lemma bidMarginal_cast_extend {vlo vhi L U U' V : ℝ}
    (μ : Measure (Icc vlo vhi)) [IsProbabilityMeasure μ]
    (h : U=U') (π : Law (A:=Icc L U') μ) (hUV : U≤V) (hUV' : U'≤V) :
    (bidMarginal (show Law (A:=Icc L U) μ from by rw [h];exact π).1).map
      (continuous_extendBid hUV).measurable.aemeasurable =
    (bidMarginal π.1).map (continuous_extendBid hUV').measurable.aemeasurable := by
  cases h
  rfl

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
    (π : JointProfile D P t ht)
local notation "Ds" => installOriginal D P t ht

lemma bulkPhysical_project_extend :
    (bidMarginal (bulkPhysical D P t ht π).1).map
      (continuous_extendBid (bulkPhysicalWidth_le D)).measurable.aemeasurable=
      noisyBidLaw (by norm_num : (0:ℝ)<1) D.heps.le
        ((bidMarginal (π 0).1).map (continuous_extendBid D.huU).measurable.aemeasurable) := by
  change _=noisyBidLaw (by norm_num : (0:ℝ)<1) D.heps.le
    ((show ProbabilityMeasure (Icc (1:ℝ) (1+D.u)) from bidMarginal (π 0).1).map
      (continuous_extendBid D.huU).measurable.aemeasurable)
  rw [noisyBidLaw_extend]
  have h := congrArg
    (fun μ : ProbabilityMeasure (Icc (1:ℝ) ((1+D.u)*(1+D.eps))) =>
      μ.map (continuous_extendBid
        (mul_le_mul_of_nonneg_right D.huU (by linarith [D.heps] : 0≤1+D.eps))).measurable.aemeasurable)
    (noisy_joint_bid_projection (by norm_num : (0:ℝ)<1) D.heps.le
      P.originalBulkLaw (bulkBase D P t ht π))
  apply Eq.trans ?_ h
  convert! bidMarginal_cast_extend P.originalBulkLaw (one_add_bulkPhysicalWidth D)
    (Hybrid.activeNoisyLaw (by norm_num : (0:ℝ)<1) D.heps.le P.originalBulkLaw (π 0))
    (bulkPhysicalWidth_le D)
    (mul_le_mul_of_nonneg_right D.huU (by linarith [D.heps] : 0≤1+D.eps)) using 1

lemma tailPhysical_project :
    bidMarginal (tailPhysical D P t ht π).1=
      noisyBidLaw (by norm_num : (0:ℝ)<1) D.heps.le (bidMarginal (π 1).1) :=
  noisy_joint_bid_projection (by norm_num : (0:ℝ)<1) D.heps.le
    (P.originalTruncatedTailLaw t ht) (tailBase D P t ht π)

lemma merged_projection :
    bidMarginal (activePhysical D P t ht π).1=
      mixture (originalBulkShare P t ht)
        ((bidMarginal (bulkPhysical D P t ht π).1).map
          (continuous_extendBid (bulkPhysicalWidth_le D)).measurable.aemeasurable)
        (bidMarginal (tailPhysical D P t ht π).1) := by
  apply Subtype.ext
  change (mergedActiveJoint P t ht (bulkPhysicalWidth D) D.B (bulkPhysicalWidth_le D)
      (bulkPhysical D P t ht π) (tailPhysical D P t ht π) : Measure (Icc (P.vA-P.w) t×Icc (1:ℝ) D.B)).map Prod.snd=_
  rw [mergedActiveJoint,normalizedTwo_eq_mixture]
  rw [NoisyPrivateLaws.map_mixture _ _ _ Prod.snd measurable_snd]
  congr 1
  · congr 1
    change (((bulkPhysical D P t ht π).1 : Measure (Icc (P.vA-P.w) (P.vA+P.w)×Icc (1:ℝ) (1+bulkPhysicalWidth D))).map
      (bulkEmbedding P t ht (bulkPhysicalWidth D) D.B (bulkPhysicalWidth_le D))).map Prod.snd=_
    rw [Measure.map_map measurable_snd
      (continuous_bulkEmbedding P t ht (bulkPhysicalWidth D) D.B (bulkPhysicalWidth_le D)).measurable]
    change ((bulkPhysical D P t ht π).1 : Measure (Icc (P.vA-P.w) (P.vA+P.w)×Icc (1:ℝ) (1+bulkPhysicalWidth D))).map
      ((extendBid (bulkPhysicalWidth_le D)) ∘ Prod.snd)=_
    exact (Measure.map_map (continuous_extendBid _).measurable measurable_snd).symm
  · congr 1
    change (((tailPhysical D P t ht π).1 : Measure (Icc P.M t×Icc (1:ℝ) D.B)).map (tailEmbedding P t D.B)).map Prod.snd=_
    rw [Measure.map_map measurable_snd (continuous_tailEmbedding P t D.B).measurable]
    rfl

theorem original_common_noisy_law :
    bidMarginal (activePhysical D P t ht π).1=
      noisyBidLaw (by norm_num : (0:ℝ)<1) D.heps.le
        ((Ds).commonLaw (bidLaws D P t ht π)) := by
  rw [merged_projection D P t ht π,bulkPhysical_project_extend D P t ht π,
    tailPhysical_project D P t ht π]
  exact (noisyBidLaw_mixture (by norm_num : (0:ℝ)<1) D.heps.le
    (originalBulkShare P t ht) _ _).symm

variable (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H)
    (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
    (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)
    (hfloor : ∀ v,t< v → H≤ upperBid v)
local notation "E" => regions D P hdR H hBH

include hfloor in
theorem native_original_common_noisy {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed)
    (hjoint : Γ.F ⊗ₘ Γ.σ=(joint D P t ht πL π upperBid hupperBid : Measure (ℝ×JointAction 2))) :
    (ProbabilityTheory.cond (userLaw Γ) ((E).coarseTag ⁻¹' {(1:Fin 4)})).map
      (fun x : UserDraw 2 => OriginalCommonLaw.commonDecode E x.1)=
      (noisyBidLaw (by norm_num : (0:ℝ)<1) D.heps.le
        ((Ds).commonLaw (bidLaws D P t ht π))).toMeasure := by
  rw [OriginalCommonLaw.native_original_common_bid E P rfl t ht.le πL
    (partialPhysical D P t ht π) (activePhysical D P t ht π) upperBid hupperBid hfloor
    Γ hjoint]
  convert! congrArg (fun ν : ProbabilityMeasure (Icc (1:ℝ) D.B) => ν.toMeasure)
    (original_common_noisy_law D P t ht π) using 1

end FCAppendix.Affine.Tail04.NoisyCommonRowLaw
