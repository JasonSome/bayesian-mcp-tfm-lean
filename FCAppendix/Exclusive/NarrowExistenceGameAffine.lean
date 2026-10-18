import FCAppendix.Exclusive.NarrowExistenceGameCalculus

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Existence
open Set

theorem polynomialSecond_linear (n : ℕ) (f k : ℕ → ℝ) (a b p : ℝ) :
    polynomialSecond n (fun j => a*f j+b*k j) p =
      a*polynomialSecond n f p+b*polynomialSecond n k p := by
  have he : polynomialFirst n (fun j => a*f j+b*k j) =
      fun x => a*polynomialFirst n f x+b*polynomialFirst n k x :=
    funext (binomialPolynomialDerivative_linear n f k a b)
  change deriv (polynomialFirst n (fun j => a*f j+b*k j)) p = _
  rw [he]
  exact (((hasDerivAt_polynomialFirst n f p).const_mul a).add
    ((hasDerivAt_polynomialFirst n k p).const_mul b)).deriv

theorem sourceStateScore_affine (d : ℕ) (eta : ℝ) (G : Schedule (d+1))
    (p0 : ℝ) (x : RowState) :
    sourceStateScore d (.affine eta) G p0 x =
      (1-eta)*sourceStateScore d (.affine 0) G p0 x+
        eta*sourceStateScore d (.affine 1) G p0 x := by
  dsimp [sourceStateScore, normalizedR, sourceSFirst, sourceHFirst, sourceValueFactor]
  simp only [affine_charge_mix eta, polynomialFirst, binomialPolynomial_linear,
    binomialPolynomialDerivative_linear, fTariff, sub_zero, one_mul, zero_mul,
    add_zero, sub_self, zero_add]
  ring

theorem sourceStateCurvature_affine (d : ℕ) (eta : ℝ) (G : Schedule (d+1))
    (p0 : ℝ) (x : RowState) :
    sourceStateCurvature d (.affine eta) G p0 x =
      (1-eta)*sourceStateCurvature d (.affine 0) G p0 x+
        eta*sourceStateCurvature d (.affine 1) G p0 x := by
  dsimp [sourceStateCurvature, normalizedCurvature, ownHessian, normalizedR,
    sourceSFirst, sourceSSecond, sourceHFirst, sourceHSecond, sourceValueFactor]
  simp only [affine_charge_mix eta, polynomialFirst, binomialPolynomial_linear,
    binomialPolynomialDerivative_linear, polynomialSecond_linear, fTariff,
    sub_zero, one_mul, zero_mul, add_zero, sub_self, zero_add]
  ring

theorem sourceStateInfluence_affine (d : ℕ) (eta : ℝ) (G : Schedule (d+1))
    (p0 : ℝ) (x : RowState) :
    sourceStateInfluence d (.affine eta) G p0 x =
      (1-eta)*sourceStateInfluence d (.affine 0) G p0 x+
        eta*sourceStateInfluence d (.affine 1) G p0 x := by
  dsimp [sourceStateInfluence, normalizedInfluence, crossCoefficient, normalizedR,
    sourceSFirst, sourceSSecond, sourceHFirst, sourceHSecond, sourceValueFactor]
  simp only [affine_charge_mix eta, polynomialFirst, binomialPolynomialDerivative_linear,
    polynomialSecond_linear, fTariff, sub_zero, one_mul, zero_mul, add_zero, sub_self, zero_add]
  ring

theorem literalReferenceCurvature_affine (d : ℕ) (hd : 1 ≤ d) (eta p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) :
    literalReferenceCurvature d (.affine eta) p =
      (1-eta)*literalReferenceCurvature d (.affine 0) p+
        eta*literalReferenceCurvature d (.affine 1) p := by
  rw [(literal_reference_model d hd (.affine eta) p hp0 hp1).1,
    (literal_reference_model d hd (.affine 0) p hp0 hp1).1,
    (literal_reference_model d hd (.affine 1) p hp0 hp1).1]
  dsimp [referenceCurvatureModel]
  ring

theorem literalReferenceCross_affine (d : ℕ) (hd : 1 ≤ d) (eta p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) :
    literalReferenceCross d (.affine eta) p =
      (1-eta)*literalReferenceCross d (.affine 0) p+
        eta*literalReferenceCross d (.affine 1) p := by
  rw [(literal_reference_model d hd (.affine eta) p hp0 hp1).2,
    (literal_reference_model d hd (.affine 0) p hp0 hp1).2,
    (literal_reference_model d hd (.affine 1) p hp0 hp1).2]
  dsimp [referenceCrossModel]
  ring

theorem affine_abs_bound {eta x y A B : ℝ} (he0 : 0 ≤ eta) (he1 : eta ≤ 1)
    (hx : |x| < A) (hy : |y| < B) :
    |(1-eta)*x+eta*y| < (1-eta)*A+eta*B := by
  have he : 0 ≤ 1-eta := sub_nonneg.mpr he1
  have ht := abs_add_le ((1-eta)*x) (eta*y)
  rw [abs_mul, abs_of_nonneg he, abs_mul, abs_of_nonneg he0] at ht
  by_cases h1 : eta = 1
  · simpa only [h1, sub_self, zero_mul, one_mul, zero_add] using hy
  · have hep : 0 < 1-eta := sub_pos.mpr (lt_of_le_of_ne he1 h1)
    have hleft := mul_lt_mul_of_pos_left hx hep
    have hright := mul_le_mul_of_nonneg_left hy.le he0
    linarith

theorem affine_abs_le {eta x y B : ℝ} (he0 : 0 ≤ eta) (he1 : eta ≤ 1)
    (hx : |x| ≤ B) (hy : |y| ≤ B) : |(1-eta)*x+eta*y| ≤ B := by
  have he : 0 ≤ 1-eta := sub_nonneg.mpr he1
  have ht := abs_add_le ((1-eta)*x) (eta*y)
  rw [abs_mul, abs_of_nonneg he, abs_mul, abs_of_nonneg he0] at ht
  have hleft := mul_le_mul_of_nonneg_left hx he
  have hright := mul_le_mul_of_nonneg_left hy he0
  nlinarith

theorem source_uniform_neighborhood (d : ℕ) (hd : 1 ≤ d) (G : Schedule (d+1))
    (p0 scoreTolerance : ℝ) (hp0 : 0 < p0) (hp1 : p0 < 1) (htol : 0 < scoreTolerance) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ a : UserTariff, a.Allowed → ∀ x : RowState,
      dist x (sourceReferenceState p0) < delta →
        |sourceStateCurvature d a G p0 x-literalReferenceCurvature d a p0| <
          literalReferenceCurvature d a p0/12 ∧
        |sourceStateInfluence d a G p0 x-literalReferenceCross d a p0| <
          literalReferenceCurvature d a p0/24 ∧
        |sourceStateScore d a G p0 x| < scoreTolerance := by
  obtain ⟨du, hdu, hu⟩ := source_endpoint_neighborhood d hd .unique trivial G p0 scoreTolerance hp0 hp1 htol
  obtain ⟨d0, hd0, h0⟩ := source_endpoint_neighborhood d hd (.affine 0) (by constructor <;> norm_num)
    G p0 scoreTolerance hp0 hp1 htol
  obtain ⟨d1, hd1, h1⟩ := source_endpoint_neighborhood d hd (.affine 1) (by constructor <;> norm_num)
    G p0 scoreTolerance hp0 hp1 htol
  refine ⟨min du (min d0 d1), by positivity, ?_⟩
  intro a ha x hx
  cases a with
  | unique => exact hu x (hx.trans_le (min_le_left _ _))
  | affine eta =>
    have hh0 := h0 x (hx.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    have hh1 := h1 x (hx.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    have hK := affine_abs_bound ha.1 ha.2 hh0.1 hh1.1
    have hC := affine_abs_bound ha.1 ha.2 hh0.2.1 hh1.2.1
    have hS := affine_abs_bound ha.1 ha.2 hh0.2.2 hh1.2.2
    rw [sourceStateCurvature_affine, literalReferenceCurvature_affine d hd eta p0 hp0 hp1]
    rw [sourceStateInfluence_affine, literalReferenceCross_affine d hd eta p0 hp0 hp1,
      sourceStateScore_affine]
    have hKarg : (1-eta)*(sourceStateCurvature d (.affine 0) G p0 x-
        literalReferenceCurvature d (.affine 0) p0)+
        eta*(sourceStateCurvature d (.affine 1) G p0 x-literalReferenceCurvature d (.affine 1) p0) =
      (1-eta)*sourceStateCurvature d (.affine 0) G p0 x+
        eta*sourceStateCurvature d (.affine 1) G p0 x-
          ((1-eta)*literalReferenceCurvature d (.affine 0) p0+
            eta*literalReferenceCurvature d (.affine 1) p0) := by ring
    have hCarg : (1-eta)*(sourceStateInfluence d (.affine 0) G p0 x-
        literalReferenceCross d (.affine 0) p0)+
        eta*(sourceStateInfluence d (.affine 1) G p0 x-literalReferenceCross d (.affine 1) p0) =
      (1-eta)*sourceStateInfluence d (.affine 0) G p0 x+
        eta*sourceStateInfluence d (.affine 1) G p0 x-
          ((1-eta)*literalReferenceCross d (.affine 0) p0+
            eta*literalReferenceCross d (.affine 1) p0) := by ring
    rw [hKarg] at hK
    rw [hCarg] at hC
    refine ⟨?_, ?_, ?_⟩
    · convert hK using 1; ring
    · convert hC using 1; ring
    · convert hS using 1; ring

theorem source_uniform_bounds (d : ℕ) (G : Schedule (d+1)) (p0 : ℝ)
    (A : Set RowState) (hA : IsCompact A) :
    ∃ B : ℝ, 0 < B ∧ ∀ a : UserTariff, a.Allowed → ∀ x ∈ A,
      |sourceStateScore d a G p0 x| ≤ B ∧
        |sourceStateCurvature d a G p0 x| ≤ B ∧ |sourceStateInfluence d a G p0 x| ≤ B := by
  obtain ⟨Bu, hBu, hbu⟩ := compact_curvature_bounds _ _
    (continuous_sourceStateCurvature d .unique G p0) (continuous_sourceStateInfluence d .unique G p0) A hA
  obtain ⟨B0, hB0, hb0⟩ := compact_curvature_bounds _ _
    (continuous_sourceStateCurvature d (.affine 0) G p0) (continuous_sourceStateInfluence d (.affine 0) G p0) A hA
  obtain ⟨B1, hB1, hb1⟩ := compact_curvature_bounds _ _
    (continuous_sourceStateCurvature d (.affine 1) G p0) (continuous_sourceStateInfluence d (.affine 1) G p0) A hA
  obtain ⟨Su, hSu, hsu⟩ := compact_curvature_bounds _ _
    (continuous_sourceStateScore d .unique G p0) (continuous_sourceStateScore d .unique G p0) A hA
  obtain ⟨S0, hS0, hs0⟩ := compact_curvature_bounds _ _
    (continuous_sourceStateScore d (.affine 0) G p0) (continuous_sourceStateScore d (.affine 0) G p0) A hA
  obtain ⟨S1, hS1, hs1⟩ := compact_curvature_bounds _ _
    (continuous_sourceStateScore d (.affine 1) G p0) (continuous_sourceStateScore d (.affine 1) G p0) A hA
  let B := Bu+B0+B1+Su+S0+S1
  have hlu : Bu ≤ B := by dsimp [B]; linarith
  have hl0 : B0 ≤ B := by dsimp [B]; linarith
  have hl1 : B1 ≤ B := by dsimp [B]; linarith
  have hlsu : Su ≤ B := by dsimp [B]; linarith
  have hls0 : S0 ≤ B := by dsimp [B]; linarith
  have hls1 : S1 ≤ B := by dsimp [B]; linarith
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  intro a ha x hx
  cases a with
  | unique => exact ⟨(hsu x hx).1.trans hlsu, (hbu x hx).1.trans hlu, (hbu x hx).2.trans hlu⟩
  | affine eta =>
    rw [sourceStateScore_affine, sourceStateCurvature_affine, sourceStateInfluence_affine]
    exact ⟨affine_abs_le ha.1 ha.2 ((hs0 x hx).1.trans hls0) ((hs1 x hx).1.trans hls1),
      affine_abs_le ha.1 ha.2 ((hb0 x hx).1.trans hl0) ((hb1 x hx).1.trans hl1),
      affine_abs_le ha.1 ha.2 ((hb0 x hx).2.trans hl0) ((hb1 x hx).2.trans hl1)⟩

end FCAppendix.Exclusive.Narrow.Existence
