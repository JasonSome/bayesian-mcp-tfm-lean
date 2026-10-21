import FCAppendix.Affine.UniformFinite.WeightedContinuation

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set
open scoped BigOperators

namespace GuardedPathRelabel
open WeightedSampling

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def relabelWeights (e : Equiv.Perm ι) (w : Weights ι) : Weights ι :=
  ⟨w.1 ∘ e.symm, fun j => w.2 (e.symm j)⟩

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem relabelWeights_apply (e : Equiv.Perm ι) (w : Weights ι) (j : ι) :
    (relabelWeights e w).1 (e j) = w.1 j := by
  simp [relabelWeights]

def relabelPath (e : Equiv.Perm ι) : (n : ℕ) → Equiv.Perm (Path ι n)
  | 0 => Equiv.refl _
  | n + 1 => e.prodCongr (relabelPath e n)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem relabelPath_zero (e : Equiv.Perm ι) (p : Path ι 0) :
    relabelPath e 0 p = p := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem relabelPath_succ (e : Equiv.Perm ι) (n : ℕ)
    (p : Path ι (n + 1)) :
    relabelPath e (n + 1) p = (e p.1, relabelPath e n p.2) := rfl

omit [DecidableEq ι] in
@[simp] theorem totalWeight_relabel (e : Equiv.Perm ι) (w : Weights ι) :
    totalWeight (relabelWeights e w) = totalWeight w := by
  exact Equiv.sum_comp e.symm w.1

@[simp] theorem remainingWeight_relabel (e : Equiv.Perm ι) (w : Weights ι)
    (S : Finset ι) :
    remainingWeight (relabelWeights e w) (S.map e.toEmbedding) =
      remainingWeight w S := by
  classical
  unfold remainingWeight
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro j _
  simp

omit [Fintype ι] in
@[simp] theorem finalSet_relabel (e : Equiv.Perm ι) (n : ℕ)
    (S : Finset ι) (p : Path ι n) :
    finalSet n (S.map e.toEmbedding) (relabelPath e n p) =
      (finalSet n S p).map e.toEmbedding := by
  induction n generalizing S with
  | zero => rfl
  | succ n ih =>
    rcases p with ⟨a, p⟩
    change finalSet n (insert (e a) (S.map e.toEmbedding))
      (relabelPath e n p) = (finalSet n (insert a S) p).map e.toEmbedding
    convert! ih (insert a S) p using 1; simp only [Finset.map_insert]
    rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem selectedSum_relabel (e : Equiv.Perm ι) (h : ι → ℝ)
    (n : ℕ) (p : Path ι n) :
    selectedSum (h ∘ e.symm) n (relabelPath e n p) = selectedSum h n p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change h (e.symm (e p.1)) + selectedSum (h ∘ e.symm) n
      (relabelPath e n p.2) = h p.1 + selectedSum h n p.2
    simp only [Equiv.symm_apply_apply, ih]

variable [Nonempty ι]

theorem oneDraw_mass_relabel (e : Equiv.Perm ι) (w : Weights ι)
    (S : Finset ι) (hS : 0 < remainingWeight w S) (j : ι) :
    (oneDraw (relabelWeights e w) (S.map e.toEmbedding)).mass (e j) =
      (oneDraw w S).mass j := by
  have hS' : 0 < remainingWeight (relabelWeights e w) (S.map e.toEmbedding) := by
    simpa using hS
  rw [oneDraw_mass _ _ hS', oneDraw_mass _ _ hS]
  simp

theorem pathLaw_mass_relabel (e : Equiv.Perm ι) (w : Weights ι)
    (n : ℕ) (S : Finset ι) (hW : (S.card : ℝ) + (n : ℝ) < totalWeight w)
    (p : Path ι n) :
    (pathLaw (relabelWeights e w) n (S.map e.toEmbedding)).mass
        (relabelPath e n p) = (pathLaw w n S).mass p := by
  induction n generalizing S with
  | zero => rfl
  | succ n ih =>
    have hden : 0 < remainingWeight w S := by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      simp only [Nat.cast_add, Nat.cast_one] at hW
      linarith [denominator_lower w S]
    have hnext : ((insert p.1 S).card : ℝ) + (n : ℝ) < totalWeight w := by
      have hc : ((insert p.1 S).card : ℝ) ≤ (S.card : ℝ) + 1 := by
        exact_mod_cast Finset.card_insert_le p.1 S
      simp only [Nat.cast_add, Nat.cast_one] at hW
      linarith
    rw [path_mass_succ, path_mass_succ]
    change (oneDraw (relabelWeights e w) (S.map e.toEmbedding)).mass (e p.1) *
      (pathLaw (relabelWeights e w) n (insert (e p.1) (S.map e.toEmbedding))).mass
        (relabelPath e n p.2) = _
    rw [oneDraw_mass_relabel e w S hden]
    have hins : insert (e p.1) (S.map e.toEmbedding) = (insert p.1 S).map e.toEmbedding :=
      (Finset.map_insert e.toEmbedding p.1 S).symm
    rw [hins, ih _ hnext p.2]

theorem pathLaw_expect_relabel (e : Equiv.Perm ι) (w : Weights ι)
    (n : ℕ) (S : Finset ι) (hW : (S.card : ℝ) + (n : ℝ) < totalWeight w)
    (f : Path ι n → ℝ) :
    (pathLaw (relabelWeights e w) n (S.map e.toEmbedding)).expect f =
      (pathLaw w n S).expect (fun p => f (relabelPath e n p)) := by
  unfold FiniteLaw.expect
  rw [← Equiv.sum_comp (relabelPath e n)]
  apply Finset.sum_congr rfl
  intro p _
  rw [pathLaw_mass_relabel e w n S hW]

theorem pathLaw_relabel (e : Equiv.Perm ι) (w : Weights ι)
    (n : ℕ) (S : Finset ι) (hW : (S.card : ℝ) + (n : ℝ) < totalWeight w) :
    pathLaw (relabelWeights e w) n (S.map e.toEmbedding) =
      (pathLaw w n S).map (relabelPath e n) := by
  apply FiniteLaw.ext_expect
  intro f
  rw [FiniteLaw.expect_map]
  exact pathLaw_expect_relabel e w n S hW f

theorem guarded_empty_path_expect (e : Equiv.Perm ι) (w : Weights ι)
    (n : ℕ) (hW : (n : ℝ) < totalWeight w) (f : Path ι n → ℝ) :
    (pathLaw (relabelWeights e w) n ∅).expect f =
      (pathLaw w n ∅).expect (fun p => f (relabelPath e n p)) := by
  simpa using pathLaw_expect_relabel e w n ∅ (by simpa using hW) f

end GuardedPathRelabel

namespace Literal
open ClippedResidual
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[simp] theorem remainingDemand_relabel (e : Equiv.Perm ι)
    (ξ z : ℝ) (b : ι → ℝ) (E : Finset ι) :
    remainingDemand ξ (b ∘ e.symm) (E.map e.toEmbedding) z =
      remainingDemand ξ b E z := by
  classical
  unfold remainingDemand
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro j _
  simp

@[simp] theorem root_relabel (e : Equiv.Perm ι) (ξ lo hi : ℝ)
    (b : ι → ℝ) (E : Finset ι) (d : ℕ) :
    root ξ lo hi (b ∘ e.symm) (E.map e.toEmbedding) d =
      root ξ lo hi b E d := by
  classical
  have hf : remainingDemand ξ (b ∘ e.symm) (E.map e.toEmbedding) =
      remainingDemand ξ b E := by
    funext z
    exact remainingDemand_relabel e ξ z b E
  exact congrArg (fun F : ℝ → ℝ =>
    if h : ∃ z, z ∈ Icc lo hi ∧ F z = (d : ℝ) then h.choose else 0) hf

omit [Fintype ι] in
@[simp] theorem smallMarginal_relabel (e : Equiv.Perm ι)
    (ξ z : ℝ) (b : ι → ℝ) (E : Finset ι) (j : ι) :
    smallMarginal ξ z (b ∘ e.symm) (E.map e.toEmbedding) (e j) =
      smallMarginal ξ z b E j := by
  simp [smallMarginal]

omit [Fintype ι] in
@[simp] theorem largeMarginal_relabel (e : Equiv.Perm ι)
    (ξ z : ℝ) (b : ι → ℝ) (E : Finset ι) (j : ι) :
    largeMarginal ξ z (b ∘ e.symm) (E.map e.toEmbedding) (e j) =
      largeMarginal ξ z b E j := by
  simp [largeMarginal]

end Literal
end FCAppendix.Affine.UniformFinite
