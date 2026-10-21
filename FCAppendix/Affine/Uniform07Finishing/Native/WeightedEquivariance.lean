import FCAppendix.Affine.Uniform07Finishing.Native.LiteralSourceGame
import FCAppendix.Affine.Hybrid.EqualRelabel
import FCAppendix.Affine.Hybrid.PureRelabel

noncomputable section
namespace FCAppendix.Affine.WeightedSampling
open Set Classical
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def relabelWeights (w : Weights ι) (e : Equiv.Perm ι) : Weights ι :=
  ⟨w.1 ∘ e.symm, fun i => w.2 (e.symm i)⟩

omit [DecidableEq ι] in
theorem totalWeight_relabel (w : Weights ι) (e : Equiv.Perm ι) :
    totalWeight (relabelWeights w e) = totalWeight w :=
  Equiv.sum_comp e.symm w.1

theorem remainingWeight_relabel (w : Weights ι) (S : Finset ι) (e : Equiv.Perm ι) :
    remainingWeight (relabelWeights w e) (S.map e.toEmbedding) = remainingWeight w S := by
  unfold remainingWeight
  calc
    _ = ∑ i, if e i ∈ S.map e.toEmbedding then 0 else (relabelWeights w e).1 (e i) :=
      (Equiv.sum_comp e _).symm
    _ = _ := by simp only [Finset.mem_map_equiv, Equiv.symm_apply_apply,
      relabelWeights, Function.comp_apply]

variable [Nonempty ι]

theorem oneDraw_relabel (w : Weights ι) (S : Finset ι) (e : Equiv.Perm ι)
    (hW : 0 < remainingWeight w S) :
    oneDraw (relabelWeights w e) (S.map e.toEmbedding) = (oneDraw w S).map e := by
  have hW' : 0 < remainingWeight (relabelWeights w e) (S.map e.toEmbedding) := by
    rwa [remainingWeight_relabel]
  apply FiniteLaw.ext_expect
  intro f
  rw [FiniteLaw.expect_map]
  unfold FiniteLaw.expect
  calc
    _ = ∑ i, (oneDraw (relabelWeights w e) (S.map e.toEmbedding)).mass (e i)*f (e i) :=
      (Equiv.sum_comp e _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [oneDraw_mass _ _ hW', oneDraw_mass _ _ hW, remainingWeight_relabel]
      simp only [Finset.mem_map_equiv, Equiv.symm_apply_apply,
        relabelWeights, Function.comp_apply]

def pathEquiv (e : Equiv.Perm ι) : (n : ℕ) → Equiv.Perm (Path ι n)
  | 0 => Equiv.refl _
  | n+1 => Equiv.prodCongr e (pathEquiv e n)

theorem pathLaw_relabel (w : Weights ι) (n : ℕ) (S : Finset ι) (e : Equiv.Perm ι)
    (hW : (S.card : ℝ)+n < totalWeight w) :
    pathLaw (relabelWeights w e) n (S.map e.toEmbedding) =
      (pathLaw w n S).map (pathEquiv e n) := by
  induction n generalizing S with
  | zero =>
      apply FiniteLaw.ext_expect
      intro f
      simp only [pathLaw, FiniteLaw.expect_dirac, FiniteLaw.expect_map, pathEquiv,
        Equiv.refl_apply]
  | succ n ih =>
      have hd : 0 < remainingWeight w S := by
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        push_cast at hW
        linarith [denominator_lower w S]
      apply FiniteLaw.ext_expect
      intro f
      rw [expect_path_succ, oneDraw_relabel w S e hd, FiniteLaw.expect_map,
        FiniteLaw.expect_map, expect_path_succ]
      apply FiniteLaw.expect_congr
      intro i
      have hW' : ((insert i S).card : ℝ)+n < totalWeight w := by
        have hc : ((insert i S).card : ℝ) ≤ (S.card : ℝ)+1 := by
          exact_mod_cast Finset.card_insert_le i S
        push_cast at hW
        linarith
      have hmap : insert (e i) (S.map e.toEmbedding) = (insert i S).map e.toEmbedding :=
        (Finset.map_insert e.toEmbedding i S).symm
      simp only [hmap, ih (insert i S) hW', FiniteLaw.expect_map]
      rfl

omit [Fintype ι] [Nonempty ι] in
theorem finalSet_relabel (e : Equiv.Perm ι) (n : ℕ) (S : Finset ι) (p : Path ι n) :
    finalSet n (S.map e.toEmbedding) (pathEquiv e n p) =
      (finalSet n S p).map e.toEmbedding := by
  induction n generalizing S with
  | zero => rfl
  | succ n ih =>
      change finalSet n (insert (e p.1) (S.map e.toEmbedding)) (pathEquiv e n p.2) = _
      have hmap : insert (e p.1) (S.map e.toEmbedding) = (insert p.1 S).map e.toEmbedding :=
        (Finset.map_insert e.toEmbedding p.1 S).symm
      simp only [hmap, ih]
      rfl

end FCAppendix.Affine.WeightedSampling

namespace FCAppendix.Affine.Uniform07Finishing.Weighted
open FCAppendix.Bayes
open MeasureTheory Game Set Classical
open FCAppendix.Affine StrictNative
open scoped BigOperators
variable {m : ℕ} [Nonempty (Fin m)]

def relabelContext (e : Equiv.Perm (Fin m)) (X : ClassifiedContext m) : ClassifiedContext m :=
  (X.1 ∘ e.symm, X.2)

omit [Nonempty (Fin m)] in
theorem presentSet_relabel (L : LocalList m) (e : Equiv.Perm (Fin m)) :
    presentSet (L ∘ e.symm) = (presentSet L).map e.toEmbedding := by
  ext i
  simp only [presentSet, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_map_equiv, Function.comp_apply]

omit [Nonempty (Fin m)] in
theorem budget_relabel (c : ℕ) (j : Fin 2) (X : ClassifiedContext m)
    (e : Equiv.Perm (Fin m)) : budget c j (relabelContext e X) = budget c j X := by
  simp only [budget, relabelContext, contextUpper, presentSet_relabel, Finset.card_map]

omit [Nonempty (Fin m)] in
theorem commonBudget_relabel (c : ℕ) (X : ClassifiedContext m)
    (e : Equiv.Perm (Fin m)) : commonBudget c (relabelContext e X) = commonBudget c X := by
  simp only [commonBudget, budget_relabel]

omit [Nonempty (Fin m)] in
theorem sourceWeights_relabel (ξ Λ r U : ℝ) (L : LocalList m)
    (e : Equiv.Perm (Fin m)) :
    sourceWeights ξ Λ r U (L ∘ e.symm) =
      WeightedSampling.relabelWeights (sourceWeights ξ Λ r U L) e := by
  apply Subtype.ext
  rfl

theorem planLaw_relabel (Δ : ℕ) (α : unitInterval) (w : WeightedSampling.Weights (Fin m))
    (e : Equiv.Perm (Fin m)) (hW : (Δ : ℝ) < WeightedSampling.totalWeight w) :
    planLaw Δ α (WeightedSampling.relabelWeights w e) =
      (planLaw Δ α w).map (Option.map (fun E : Finset (Fin m) => E.map e.toEmbedding)) := by
  have hp := WeightedSampling.pathLaw_relabel w Δ ∅ e (by simpa using hW)
  simp only [Finset.map_empty] at hp
  apply FiniteLaw.ext_expect
  intro f
  rw [FiniteLaw.expect_map, planLaw_expect, planLaw_expect, hp, FiniteLaw.expect_map]
  have hset (p : WeightedSampling.Path (Fin m) Δ) :
      WeightedSampling.finalSet Δ ∅ (WeightedSampling.pathEquiv e Δ p) =
        (WeightedSampling.finalSet Δ ∅ p).map e.toEmbedding := by
    simpa only [Finset.map_empty] using WeightedSampling.finalSet_relabel e Δ ∅ p
  simp only [hset, Option.map_some, Option.map_none]

omit [Nonempty (Fin m)] in
theorem sourceDemand_relabel (ξ z : ℝ) (L : LocalList m) (e : Equiv.Perm (Fin m)) :
    sourceDemand ξ z (L ∘ e.symm) = sourceDemand ξ z L :=
  Equiv.sum_comp e.symm (fun k => ClippedResidual.exposure ξ z (entryBid (L k)))

omit [Nonempty (Fin m)] in
theorem sourceRejectionDemand_relabel (d₀ z : ℝ) (L : LocalList m)
    (e : Equiv.Perm (Fin m)) :
    sourceRejectionDemand d₀ z (L ∘ e.symm) = sourceRejectionDemand d₀ z L :=
  Equiv.sum_comp e.symm (fun k => sourcePsi d₀ z (entryBid (L k)))

omit [Nonempty (Fin m)] in
theorem sourceCountMargin_relabel (t width : ℝ) (X : ClassifiedContext m)
    (e : Equiv.Perm (Fin m)) :
    sourceCountMargin t width (relabelContext e X) = sourceCountMargin t width X := by
  simp only [sourceCountMargin, relabelContext, presentSet_relabel, Finset.card_map]

omit [Nonempty (Fin m)] in
theorem sourceCountSlacks_relabel (t width : ℝ) (X : ClassifiedContext m)
    (e : Equiv.Perm (Fin m)) :
    sourceCountSlacks t width (relabelContext e X) = sourceCountSlacks t width X := by
  simp only [sourceCountSlacks,relabelContext,presentSet_relabel,Finset.card_map]

omit [Nonempty (Fin m)] in
theorem sourceSlacks_relabel (ξ Λ a r U d₀ z t width : ℝ) (c : ℕ)
    (X : ClassifiedContext m) (e : Equiv.Perm (Fin m)) :
    sourceSlacks ξ Λ a r U d₀ z t width c (relabelContext e X) =
      sourceSlacks ξ Λ a r U d₀ z t width c X := by
  have hd := commonBudget_relabel c X e
  have h0 := budget_relabel c 0 X e
  have h1 := budget_relabel c 1 X e
  have hD (y : ℝ) : sourceDemand ξ y (relabelContext e X).1 = sourceDemand ξ y X.1 :=
    sourceDemand_relabel ξ y X.1 e
  have hW : WeightedSampling.totalWeight (sourceWeights ξ Λ r U (relabelContext e X).1) =
      WeightedSampling.totalWeight (sourceWeights ξ Λ r U X.1) := by
    change WeightedSampling.totalWeight (sourceWeights ξ Λ r U (X.1 ∘ e.symm)) = _
    rw [sourceWeights_relabel, WeightedSampling.totalWeight_relabel]
  have hP : sourceRejectionDemand d₀ z (relabelContext e X).1 = sourceRejectionDemand d₀ z X.1 :=
    sourceRejectionDemand_relabel d₀ z X.1 e
  simp only [sourceSlacks, hd, h0, h1, hD, hW, hP, sourceCountMargin_relabel]

omit [Nonempty (Fin m)] in

theorem sourceGuardAlpha_relabel (ξ Λ a r U d₀ z t width ε : ℝ) (c : ℕ)
    (X : ClassifiedContext m) (e : Equiv.Perm (Fin m)) :
    sourceGuardAlpha ξ Λ a r U d₀ z t width ε c (relabelContext e X) =
      sourceGuardAlpha ξ Λ a r U d₀ z t width ε c X := by
  apply Subtype.ext
  simp only [sourceGuardAlpha,sourcePolicySlacks,sourceSlacks_relabel,sourceCountSlacks_relabel]

end FCAppendix.Affine.Uniform07Finishing.Weighted

namespace FCAppendix.Affine.Uniform07Finishing
open StrictNative

theorem literalSourceAlpha_relabel {m : ℕ} [Nonempty (Fin m)]
    (row : Uniform07.Row) (Λ z width ε : ℝ)
    (X : ClassifiedContext m) (e : Equiv.Perm (Fin m)) :
    literalSourceAlpha row Λ z width ε (Weighted.relabelContext e X) =
      literalSourceAlpha row Λ z width ε X :=
  Weighted.sourceGuardAlpha_relabel _ _ _ _ _ _ _ _ _ _ _ X e

end FCAppendix.Affine.Uniform07Finishing
