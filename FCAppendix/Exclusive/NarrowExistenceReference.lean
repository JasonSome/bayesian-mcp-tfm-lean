import FCAppendix.Exclusive.NarrowExistenceCalculus

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Existence

def referenceCurvature (d q T Tp Tpp : ℝ) : ℝ :=
  (2+1/d)*T + 3*q/d*Tp + q^2/d^2*Tpp

def referenceCross (d q T Tp Tpp : ℝ) : ℝ :=
  referenceCurvature d q T Tp Tpp - (q/d*Tp+T)

theorem reference_ownHessian (d q b T Tp Tpp : ℝ)
    (hd : d ≠ 0) (hq : q ≠ 0) :
    -ownHessian (1/d) q 0 b (b*d*T/q)
        (-b*d/q*(Tp+d*T/q)-b*Tpp) T Tp =
      b*referenceCurvature d q T Tp Tpp := by
  dsimp [ownHessian, referenceCurvature]
  field_simp [hd, hq]
  ring

theorem reference_crossCoefficient (d q b T Tp Tpp : ℝ)
    (hd : d ≠ 0) (hq : q ≠ 0) :
    crossCoefficient (1/d) q 0 b (b*d*T/q)
        (-b*d/q*(Tp+d*T/q)-b*Tpp) Tp =
      b*referenceCross d q T Tp Tpp := by
  dsimp [crossCoefficient, referenceCross, referenceCurvature]
  field_simp [hd, hq]
  ring

theorem reference_at_firstOrder (d q b v NQ T Tp Tpp : ℝ)
    (hd : d ≠ 0) (hq : q ≠ 0)
    (hFOC : v*NQ = b*(Tp+d*T/q)) :
    -ownHessian (1/d) q 0 b (v*NQ-b*Tp) (-v*d*NQ/q-b*Tpp) T Tp =
        b*referenceCurvature d q T Tp Tpp ∧
      crossCoefficient (1/d) q 0 b (v*NQ-b*Tp) (-v*d*NQ/q-b*Tpp) Tp =
        b*referenceCross d q T Tp Tpp := by
  have hR : v*NQ-b*Tp = b*d*T/q := by rw [hFOC]; ring
  have hRp : -v*d*NQ/q-b*Tpp = -b*d/q*(Tp+d*T/q)-b*Tpp := by
    calc
      _ = -(d/q)*(v*NQ)-b*Tpp := by ring
      _ = _ := by rw [hFOC]; ring
  rw [hR, hRp]
  exact ⟨reference_ownHessian d q b T Tp Tpp hd hq,
    reference_crossCoefficient d q b T Tp Tpp hd hq⟩

def uniqueJet (d q Q : ℝ) : ℝ × ℝ × ℝ :=
  ((d+1)*(1-q)*Q,
    (d+1)*Q/q*(q-d*(1-q)),
    (d+1)*d*Q/q^2*((d-1)*(1-q)-2*q))

def onceJet (d q Q : ℝ) : ℝ × ℝ × ℝ :=
  (1-q*Q, (d+1)*Q, -(d+1)*d*Q/q)

def perInclusionJet (d q : ℝ) : ℝ × ℝ × ℝ :=
  ((d+1)*(1-q), d+1, 0)

theorem reference_unique (d q Q : ℝ) (hd : d ≠ 0) (hq : q ≠ 0) :
    referenceCurvature d q (uniqueJet d q Q).1 (uniqueJet d q Q).2.1
        (uniqueJet d q Q).2.2 = (d+1)*q*Q/d ∧
      referenceCross d q (uniqueJet d q Q).1 (uniqueJet d q Q).2.1
        (uniqueJet d q Q).2.2 = 0 := by
  dsimp [referenceCurvature, referenceCross, uniqueJet]
  constructor <;> (field_simp [hd, hq]; ring)

theorem reference_once (d q Q : ℝ) (hd : d ≠ 0) :
    referenceCurvature d q (onceJet d q Q).1 (onceJet d q Q).2.1
        (onceJet d q Q).2.2 = (2*d+1+q*Q)/d ∧
      referenceCross d q (onceJet d q Q).1 (onceJet d q Q).2.1
        (onceJet d q Q).2.2 = (d+1)/d := by
  dsimp [referenceCurvature, referenceCross, onceJet]
  constructor <;> (field_simp [hd]; ring)

theorem reference_perInclusion (d q : ℝ) (hd : d ≠ 0) :
    referenceCurvature d q (perInclusionJet d q).1 (perInclusionJet d q).2.1
        (perInclusionJet d q).2.2 = (d+1)*(2*d+1-2*(d-1)*q)/d ∧
      referenceCross d q (perInclusionJet d q).1 (perInclusionJet d q).2.1
        (perInclusionJet d q).2.2 = (d+1)*(d+1-(d-1)*q)/d := by
  dsimp [referenceCurvature, referenceCross, perInclusionJet]
  constructor <;> (field_simp [hd]; ring)

theorem reference_affine (d q eta T0 T0p T0pp T1 T1p T1pp : ℝ) :
    referenceCurvature d q ((1-eta)*T0+eta*T1)
        ((1-eta)*T0p+eta*T1p) ((1-eta)*T0pp+eta*T1pp) =
      (1-eta)*referenceCurvature d q T0 T0p T0pp +
        eta*referenceCurvature d q T1 T1p T1pp ∧
    referenceCross d q ((1-eta)*T0+eta*T1)
        ((1-eta)*T0p+eta*T1p) ((1-eta)*T0pp+eta*T1pp) =
      (1-eta)*referenceCross d q T0 T0p T0pp +
        eta*referenceCross d q T1 T1p T1pp := by
  constructor <;> dsimp [referenceCurvature, referenceCross] <;> ring

def referenceCurvatureModel (d q Q : ℝ) (tariff : UserTariff) : ℝ :=
  match tariff with
  | .unique => (d+1)*q*Q/d
  | .affine eta => (1-eta)*(2*d+1+q*Q)/d +
      eta*((d+1)*(2*d+1-2*(d-1)*q)/d)

def referenceCrossModel (d q : ℝ) (tariff : UserTariff) : ℝ :=
  match tariff with
  | .unique => 0
  | .affine eta => (1-eta)*(d+1)/d + eta*((d+1)*(d+1-(d-1)*q)/d)

theorem once_curvature_bounds (d q Q : ℝ) (hd : 1 ≤ d)
    (hq : 0 ≤ q) (hQ : 0 ≤ Q) :
    0 < (2*d+1+q*Q)/d ∧
      0 ≤ (d+1)/d ∧ (d+1)/d ≤ (2/3:ℝ)*((2*d+1+q*Q)/d) := by
  have hd0 : 0 < d := by linarith
  have hqQ := mul_nonneg hq hQ
  refine ⟨div_pos (by linarith) hd0, (div_pos (by linarith) hd0).le, ?_⟩
  rw [← mul_div_assoc]
  apply (div_le_div_iff_of_pos_right hd0).2
  nlinarith

theorem perInclusion_curvature_bounds (d q : ℝ) (hd : 1 ≤ d)
    (hq1 : q ≤ 1) :
    0 < (d+1)*(2*d+1-2*(d-1)*q)/d ∧
      0 ≤ (d+1)*(d+1-(d-1)*q)/d ∧
      (d+1)*(d+1-(d-1)*q)/d ≤
        (2/3:ℝ)*((d+1)*(2*d+1-2*(d-1)*q)/d) := by
  have hd0 : 0 < d := by linarith
  have hdp : 0 < d+1 := by linarith
  have hm : (d-1)*q ≤ d-1 := by nlinarith
  refine ⟨div_pos (mul_pos hdp (by linarith)) hd0,
    (div_pos (mul_pos hdp (by linarith)) hd0).le, ?_⟩
  rw [← mul_div_assoc]
  apply (div_le_div_iff_of_pos_right hd0).2
  calc
    (d+1)*(d+1-(d-1)*q) ≤ (d+1)*((2/3:ℝ)*(2*d+1-2*(d-1)*q)) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hdp.le
    _ = (2/3:ℝ)*((d+1)*(2*d+1-2*(d-1)*q)) := by ring

theorem reference_model_bounds (d q Q : ℝ) (hd : 1 ≤ d)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hQ : 0 < Q)
    (tariff : UserTariff) (ha : tariff.Allowed) :
    0 < referenceCurvatureModel d q Q tariff ∧
      |referenceCrossModel d q tariff| ≤
        (2/3:ℝ)*referenceCurvatureModel d q Q tariff := by
  have hd0 : 0 < d := by linarith
  cases tariff with
  | unique =>
    dsimp [referenceCurvatureModel, referenceCrossModel]
    refine ⟨div_pos (mul_pos (mul_pos (by linarith) hq0) hQ) hd0, ?_⟩
    simp only [abs_zero]
    positivity
  | affine eta =>
    have h0 := once_curvature_bounds d q Q hd hq0.le hQ.le
    have h1 := perInclusion_curvature_bounds d q hd hq1
    have he0 : 0 ≤ eta := ha.1
    have he1 : 0 ≤ 1-eta := sub_nonneg.mpr ha.2
    dsimp [referenceCurvatureModel, referenceCrossModel]
    have hnonneg : 0 ≤ (1-eta)*(d+1)/d + eta*((d+1)*(d+1-(d-1)*q)/d) := by
      simpa [mul_div_assoc] using
        add_nonneg (mul_nonneg he1 h0.2.1) (mul_nonneg he0 h1.2.1)
    rw [abs_of_nonneg hnonneg]
    constructor
    · by_cases he : eta = 0
      · simp only [he, sub_zero, one_mul, zero_mul, add_zero]
        exact h0.1
      · have hep : 0 < eta := lt_of_le_of_ne he0 (Ne.symm he)
        have hx := mul_pos hep h1.1
        have hy := mul_nonneg he1 h0.1.le
        simpa [mul_div_assoc] using add_pos_of_nonneg_of_pos hy hx
    · have hx := mul_le_mul_of_nonneg_left h0.2.2 he1
      have hy := mul_le_mul_of_nonneg_left h1.2.2 he0
      simp only [mul_div_assoc] at hx hy ⊢
      nlinarith

end FCAppendix.Exclusive.Narrow.Existence
