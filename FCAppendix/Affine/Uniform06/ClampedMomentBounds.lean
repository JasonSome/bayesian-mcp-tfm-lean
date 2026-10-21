import FCAppendix.Affine.Uniform06.RawMomentPartition

noncomputable section
namespace FCAppendix.Affine.Uniform06.ClampedMomentBounds

open Set MeasureTheory LowBody
open scoped BigOperators
open FixedPriceRawDerivative
open Uniform07 LiteralExperiment RawMixedSource RawTiltedSource RawMarkedLaplace
open RawPathAdapter RawMomentPartition RawDeficitGeometry LiteralCoarsePath LiteralKernelIdentity
open FCAppendix.Affine.ClippedResidual FCAppendix.Affine.WeightedSampling
open FiniteMarkedExchangeability

variable {N : ℕ}

theorem actual_selected_h_nonneg (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) {b : ℝ} (hbL : b≤ g.multiplier)
    (hε : 0< g.margin) (hM : 0< g.population) (hr : 0< g.requiredDemand)
    (ω : Fin N → RowRival) (hh : ∀ j,0≤ rawH (xi i) b (ω j))
    (hbranch : 0< branchWeight (xi i) {g with countMargin:=cm (fun j => (ω j).1)}
      (patternTemplate c (fun j => (ω j).1)) (rowBids b ω))
    (p : Path (Fin (N+1)) (imbalance (patternTemplate c (fun j => (ω j).1))))
    (hp : 0<(pathLaw (weights (xi i) g (patternTemplate c (fun j => (ω j).1))
      (rowBids b ω)) (imbalance (patternTemplate c (fun j => (ω j).1))) ∅).mass p) :
    0≤∑ j ∈ finalSet (imbalance (patternTemplate c (fun j => (ω j).1))) ∅ p,
      (1/2-exposure (xi i) b (rowBids b ω j)) := by
  let T := patternTemplate c (fun j => (ω j).1)
  let B := rowBids b ω
  let E := finalSet (imbalance T) ∅ p
  let g' := {g with countMargin:=cm (fun j => (ω j).1)}
  change 0<branchWeight (xi i) g' T B at hbranch
  have he := branch_path_geometry g' T B 0 hε hM hr
    (by change b≤g.multiplier; exact hbL) hbranch p hp
  by_cases hEq : T.residual₀=T.residual₁
  · have hk : imbalance T=0 := by simp [imbalance,small,hEq]
    have hE : E=∅ := Finset.card_eq_zero.mp (he.1.trans hk)
    change 0≤(∑ j ∈ E,(1/2-exposure (xi i) b (B j)))
    rw [hE,Finset.sum_empty]
  · have hα : 0< guardAlpha (xi i) g' T B := by
      simpa only [branchWeight,if_neg hEq] using hbranch
    have hW : (imbalance T:ℝ)< totalWeight (weights (xi i) g T B) := by
      have hw := SourceGuardGeometry.positive_guard_weight g' T B hε hM hα
      change (imbalance T:ℝ)+g.margin*g.population < totalWeight (weights (xi i) g T B) at hw
      linarith [mul_pos hε hM]
    have hpos := finalSet_weight_pos (weights (xi i) g T B) (imbalance T) ∅
      (by simpa only [Finset.card_empty,Nat.cast_zero,zero_add] using hW) (by simp) p hp
    apply Finset.sum_nonneg
    intro j hj
    revert hj
    refine Fin.cases ?_ (fun z => ?_) j
    · intro hj
      exact (he.2 hj).elim
    · intro hj
      have ht : (ω z).1=0 := by
        by_contra hn
        have hw := hpos z.succ hj
        change 0<(weights (xi i) g (patternTemplate c (fun j => (ω j).1)) (rowBids b ω)).1 z.succ at hw
        simp only [weights,succ_mem,hn,if_false] at hw
        exact (lt_irrefl (0:ℝ)) hw
      simpa only [rawH,RawMixedSource.demand,if_pos ht,rowBids,Fin.cons_succ,ht,if_true] using hh z

theorem actual_positive_deficit_le_raw (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) {b : ℝ} (hb : 0< b) (hbL : b≤ g.multiplier)
    (hε : 0< g.margin) (hM : 0< g.population) (hr : 0< g.requiredDemand)
    (ω : Fin N → RowRival) (hh : ∀ j,0≤ rawH (xi i) b (ω j))
    (hbranch : 0< branchWeight (xi i) {g with countMargin:=cm (fun j => (ω j).1)}
      (patternTemplate c (fun j => (ω j).1)) (rowBids b ω))
    (p : Path (Fin (N+1)) (imbalance (patternTemplate c (fun j => (ω j).1))))
    (hp : 0<(pathLaw (weights (xi i) g (patternTemplate c (fun j => (ω j).1))
      (rowBids b ω)) (imbalance (patternTemplate c (fun j => (ω j).1))) ∅).mass p)
    (hD : 0< focalDeficit (xi i) (patternTemplate c (fun j => (ω j).1)) (rowBids b ω)
      (finalSet (imbalance (patternTemplate c (fun j => (ω j).1))) ∅ p) 0) :
    focalDeficit (xi i) (patternTemplate c (fun j => (ω j).1)) (rowBids b ω)
      (finalSet (imbalance (patternTemplate c (fun j => (ω j).1))) ∅ p) 0≤ deficit i b c ω ∧
      0< deficit i b c ω := by
  let T := patternTemplate c (fun j => (ω j).1)
  let B := rowBids b ω
  let E := finalSet (imbalance T) ∅ p
  have he := branch_path_geometry {g with countMargin:=cm (fun j => (ω j).1)} T B 0
    hε hM hr (by change b≤g.multiplier; exact hbL) hbranch p hp
  have hsum := actual_selected_h_nonneg i c g cm hbL hε hM hr ω hh hbranch p hp
  have hsmall : 0< small T := by
    have hdemand : 0≤ remainingDemand (xi i) B (insert 0 E) b := by
      unfold remainingDemand
      apply Finset.sum_nonneg
      intro j hj
      split_ifs
      · rfl
      · exact exposure_nonneg (xi_pos i) hb
    have hd : (0:ℝ)< small T := by
      change 0<(small T:ℝ)-remainingDemand (xi i) B (insert 0 E) b at hD
      linarith
    exact_mod_cast hd
  have ht := template_deficit_le_raw_of_positive_small i c hb ω hsmall
  have hDf := focalDeficit_eq_balanced (xi i) T B E 0 he.2 he.1
  have hle : focalDeficit (xi i) T B E 0≤ deficit i b c ω := by
    rw [hDf]
    change 0≤(∑ j ∈ E,(1/2-exposure (xi i) (B 0) (B j))) at hsum
    linarith
  exact ⟨hle,hD.trans_le hle⟩

theorem literalMoment_polynomial (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) {b θ : ℝ} (hb : 0< b) (hbL : b≤ g.multiplier)
    (hθ : 0≤θ) (q : ℕ) (hc : (c:ℝ)≤ N)
    (hε : 0< g.margin) (hM : 0< g.population) (hr : 0< g.requiredDemand)
    (ω : Fin N → RowRival) (hh : ∀ j,0≤ rawH (xi i) b (ω j)) :
    literalMoment i c g cm b θ q ω ∈ Icc (0:ℝ) ((N:ℝ)^q) := by
  let T := patternTemplate c (fun j => (ω j).1)
  let B := rowBids b ω
  let g' := {g with countMargin:=cm (fun j => (ω j).1)}
  let P := pathLaw (weights (xi i) g T B) (imbalance T) ∅
  let f := fun p : Path (Fin (N+1)) (imbalance T) =>
    Real.exp (-θ*deficit i b c ω)*strictPower q (focalDeficit (xi i) T B (finalSet (imbalance T) ∅ p) 0)
  have heq : literalMoment i c g cm b θ q ω=branchWeight (xi i) g' T B*P.expect f := by
    rw [FCAppendix.FiniteLaw.expect_const_mul]
    change Real.exp (-θ*((c:ℝ)-sumX (RawMixedSource.demand (xi i) b) ω))*branchWeight (xi i) g' T B*
      (pathLaw (weights (xi i) g' T B) (imbalance T) ∅).expect
        (fun p => strictPower q (focalDeficit (xi i) T B (finalSet (imbalance T) ∅ p) 0))=
      branchWeight (xi i) g' T B*(Real.exp (-θ*deficit i b c ω)*
        (pathLaw (weights (xi i) g T B) (imbalance T) ∅).expect
          (fun p => strictPower q (focalDeficit (xi i) T B (finalSet (imbalance T) ∅ p) 0)))
    have hcost : deficit i b c ω=(c:ℝ)-sumX (RawMixedSource.demand (xi i) b) ω := rfl
    have hw : weights (xi i) g' T B=weights (xi i) g T B := rfl
    rw [hcost,hw]
    ring
  have hα := branchWeight_bounds (xi i) g' T B
  have hf0 (p) : 0≤ f p := mul_nonneg (Real.exp_pos _).le (strictPower_nonneg _ _)
  have hfnonneg := expect_nonneg P f hf0
  rw [heq]
  refine ⟨mul_nonneg hα.1 hfnonneg,?_⟩
  by_cases hz : branchWeight (xi i) g' T B=0
  · rw [hz,zero_mul]
    positivity
  · have hαp : 0< branchWeight (xi i) g' T B := lt_of_le_of_ne hα.1 (Ne.symm hz)
    have hbound : P.expect f≤(N:ℝ)^q := by
      apply expect_le_const
      intro p hp
      by_cases hd : 0< focalDeficit (xi i) T B (finalSet (imbalance T) ∅ p) 0
      · have hraw := actual_positive_deficit_le_raw i c g cm hb hbL hε hM hr ω hh hαp p hp hd
        have hWcap : deficit i b c ω≤(N:ℝ) := by
          have hx : 0≤ sumX (RawMixedSource.demand (xi i) b) ω :=
            Finset.sum_nonneg (fun j hj => (demand_bounds (xi_pos i) hb (ω j)).1)
          change (c:ℝ)-sumX (RawMixedSource.demand (xi i) b) ω≤(N:ℝ)
          linarith
        have hexp : Real.exp (-θ*deficit i b c ω)≤1 :=
          Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hθ hraw.2.le])
        dsimp only [f]
        rw [strictPower,if_pos hd]
        exact (mul_le_mul_of_nonneg_right hexp (pow_nonneg hd.le q)).trans
          (by simpa only [one_mul] using pow_le_pow_left₀ hd.le (hraw.1.trans hWcap) q)
      · simp only [f,strictPower,if_neg hd,mul_zero]
        positivity
    exact (mul_le_mul_of_nonneg_left hbound hα.1).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hα.2 (pow_nonneg (Nat.cast_nonneg N) q))

end FCAppendix.Affine.Uniform06.ClampedMomentBounds
