/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
Modified for publication: explanatory comments removed;
namespace and Lean/Mathlib compatibility adapted where needed.
-/
module

public import Mathlib

@[expose] public section

open scoped ENNReal BoundedContinuousFunction
open TopologicalSpace

noncomputable instance WeakDual.instLocallyConvexSpaceReal (F : Type*)
    [SeminormedAddCommGroup F] [NormedSpace ℝ F] : LocallyConvexSpace ℝ (WeakDual ℝ F) :=
  Topology.IsInducing.locallyConvexSpace
    (f := { toFun := fun x : WeakDual ℝ F => (x : F → ℝ)
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl })
    ⟨rfl⟩

namespace MeasureTheory.ProbabilityMeasure

variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

noncomputable def toWeakDualBCF (μ : ProbabilityMeasure Ω) : WeakDual ℝ (Ω →ᵇ ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ ω, f ω ∂(μ : Measure Ω)
      map_add' := fun f g => integral_add (f.integrable _) (g.integrable _)
      map_smul' := fun c f => by simpa using integral_smul c (f : Ω → ℝ) }
    1
    (fun f => by
      simpa using norm_integral_le_of_norm_le_const
        (μ := (μ : Measure Ω)) (ae_of_all _ fun ω => f.norm_coe_le_norm ω))

@[simp] lemma toWeakDualBCF_apply (μ : ProbabilityMeasure Ω) (f : Ω →ᵇ ℝ) :
    toWeakDualBCF μ f = ∫ ω, f ω ∂(μ : Measure Ω) := rfl

lemma continuous_toWeakDualBCF :
    Continuous (toWeakDualBCF : ProbabilityMeasure Ω → WeakDual ℝ (Ω →ᵇ ℝ)) := by
  refine WeakDual.continuous_of_continuous_eval (fun f => ?_)
  simpa only [toWeakDualBCF_apply] using continuous_integral_boundedContinuousFunction f

lemma toWeakDualBCF_injective [BorelSpace Ω] [PseudoMetrizableSpace Ω] :
    Function.Injective (toWeakDualBCF : ProbabilityMeasure Ω → WeakDual ℝ (Ω →ᵇ ℝ)) := by
  intro μ ν hμν
  apply ProbabilityMeasure.toMeasure_injective
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure (fun f => ?_)
  simpa only [toWeakDualBCF_apply] using DFunLike.congr_fun hμν f

lemma convex_image_toWeakDualBCF {D : Set (ProbabilityMeasure Ω)}
    (hD : ∀ μ ν : ProbabilityMeasure Ω, μ ∈ D → ν ∈ D → ∀ a b : ℝ≥0∞, a + b = 1 →
      ∃ ξ ∈ D, (ξ : Measure Ω) = a • (μ : Measure Ω) + b • (ν : Measure Ω)) :
    Convex ℝ (toWeakDualBCF '' D) := by
  rintro _ ⟨μ, hμ, rfl⟩ _ ⟨ν, hν, rfl⟩ a b ha hb hab
  have hsum : ENNReal.ofReal a + ENNReal.ofReal b = 1 := by
    rw [← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one]
  obtain ⟨ξ, hξD, hξ⟩ := hD μ ν hμ hν (ENNReal.ofReal a) (ENNReal.ofReal b) hsum
  refine ⟨ξ, hξD, ?_⟩
  have hintμ : ∀ f : Ω →ᵇ ℝ, Integrable (f : Ω → ℝ) (μ : Measure Ω) := fun f => f.integrable _
  have hintν : ∀ f : Ω →ᵇ ℝ, Integrable (f : Ω → ℝ) (ν : Measure Ω) := fun f => f.integrable _
  refine ContinuousLinearMap.ext (fun f => ?_)
  have hlhs : toWeakDualBCF ξ f
      = a * (∫ ω, f ω ∂(μ : Measure Ω)) + b * (∫ ω, f ω ∂(ν : Measure Ω)) := by
    rw [toWeakDualBCF_apply, hξ,
      integral_add_measure ((hintμ f).smul_measure (by simp)) ((hintν f).smul_measure (by simp)),
      integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal ha,
      ENNReal.toReal_ofReal hb, smul_eq_mul, smul_eq_mul]

  have hrhs : (a • toWeakDualBCF μ + b • toWeakDualBCF ν) f
      = a * (∫ ω, f ω ∂(μ : Measure Ω)) + b * (∫ ω, f ω ∂(ν : Measure Ω)) := by
    have heval : ((a • toWeakDualBCF μ + b • toWeakDualBCF ν) : WeakDual ℝ (Ω →ᵇ ℝ)) f
        = a • (toWeakDualBCF μ f) + b • (toWeakDualBCF ν f) := rfl
    rw [heval, toWeakDualBCF_apply, toWeakDualBCF_apply, smul_eq_mul, smul_eq_mul]
  exact hlhs.trans hrhs.symm

lemma isEmbedding_restrict_toWeakDualBCF [BorelSpace Ω] [PseudoMetrizableSpace Ω]
    {D : Set (ProbabilityMeasure Ω)} (hD : IsCompact D) :
    Topology.IsEmbedding (fun μ : D => toWeakDualBCF (μ : ProbabilityMeasure Ω)) := by
  haveI : CompactSpace D := isCompact_iff_compactSpace.mp hD
  exact (Continuous.isClosedEmbedding
    (continuous_toWeakDualBCF.comp continuous_subtype_val)
    (toWeakDualBCF_injective.comp Subtype.val_injective)).isEmbedding

end MeasureTheory.ProbabilityMeasure
