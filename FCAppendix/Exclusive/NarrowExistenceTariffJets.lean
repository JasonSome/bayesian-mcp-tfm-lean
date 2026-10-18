import FCAppendix.Exclusive.NarrowExistenceReference
import FCAppendix.Exclusive.NarrowLocalIdentification

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Existence
open Set Filter Topology

def tariffFormula (d : ℕ) (a : UserTariff) (p : ℝ) : ℝ :=
  match a with
  | .unique => ((d+1:ℕ):ℝ)*p*(1-p)^d
  | .affine eta => (1-eta)*PayOnce.success (d+1) p + eta*(((d+1:ℕ):ℝ)*p)

def tariffFirst (d : ℕ) (a : UserTariff) (p : ℝ) : ℝ :=
  match a with
  | .unique => ((d+1:ℕ):ℝ)*(1-p)^d/(1-p)*((1-p)-(d:ℝ)*p)
  | .affine eta => (1-eta)*(((d+1:ℕ):ℝ)*(1-p)^d)+eta*((d+1:ℕ):ℝ)

def tariffSecond (d : ℕ) (a : UserTariff) (p : ℝ) : ℝ :=
  match a with
  | .unique => ((d+1:ℕ):ℝ)*(d:ℝ)*(1-p)^d/(1-p)^2*
      (((d:ℝ)-1)*p-2*(1-p))
  | .affine eta => (1-eta)*(-((d+1:ℕ):ℝ)*(d:ℝ)*(1-p)^d/(1-p))

theorem binomialPolynomial_tariff_eq (d : ℕ) (a : UserTariff) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    binomialPolynomial (d+1) a.charge p = tariffFormula d a p := by
  rw [binomialPolynomial_eq_expect (d+1) a.charge p hp0 hp1]
  cases a with
  | unique =>
    simpa only [UserTariff.expected, tariffFormula, Nat.add_sub_cancel] using
      UserTariff.expected_unique_binomial (d+1) p hp0 hp1
  | affine eta =>
    exact UserTariff.expected_affine_binomial (d+1) eta p hp0 hp1

theorem hasDerivAt_failurePower (d : ℕ) (hd : 1 ≤ d) (p : ℝ) (hp : p < 1) :
    HasDerivAt (fun x : ℝ => (1-x)^d) (-(d:ℝ)*(1-p)^d/(1-p)) p := by
  have hq : 1-p ≠ 0 := (sub_pos.mpr hp).ne'
  have hpow : (1-p)^(d-1) = (1-p)^d/(1-p) := by
    apply (eq_div_iff hq).2
    rw [← pow_succ, Nat.sub_add_cancel hd]
  apply (((hasDerivAt_id p).const_sub 1).pow d).congr_deriv
  simp only [hpow, id_eq]
  ring

theorem hasDerivAt_tariffFormula (d : ℕ) (hd : 1 ≤ d) (a : UserTariff)
    (p : ℝ) (hp : p < 1) :
    HasDerivAt (tariffFormula d a) (tariffFirst d a p) p := by
  have hQ := hasDerivAt_failurePower d hd p hp
  have hqne : 1-p ≠ 0 := (sub_pos.mpr hp).ne'
  cases a with
  | unique =>
    apply (((hasDerivAt_id p).const_mul ((d+1:ℕ):ℝ)).mul hQ).congr_deriv
    dsimp [tariffFirst]
    field_simp [hqne]
    ring
  | affine eta =>
    apply (((hasDerivAt_success d p).const_mul (1-eta)).add
      (((hasDerivAt_id p).const_mul ((d+1:ℕ):ℝ)).const_mul eta)).congr_deriv
    dsimp [tariffFirst]
    ring

theorem hasDerivAt_tariffFirst (d : ℕ) (hd : 1 ≤ d) (a : UserTariff)
    (p : ℝ) (hp : p < 1) :
    HasDerivAt (tariffFirst d a) (tariffSecond d a p) p := by
  have hQ := hasDerivAt_failurePower d hd p hp
  have hq := (hasDerivAt_id p).const_sub 1
  have hqne : 1-p ≠ 0 := (sub_pos.mpr hp).ne'
  cases a with
  | unique =>
    apply ((((hQ.const_mul ((d+1:ℕ):ℝ)).div hq hqne).mul
      (hq.sub ((hasDerivAt_id p).const_mul (d:ℝ))))).congr_deriv
    dsimp [tariffSecond]
    field_simp [hqne]
    ring
  | affine eta =>
    apply (((hQ.const_mul ((d+1:ℕ):ℝ)).const_mul (1-eta)).add
      (hasDerivAt_const p (eta*((d+1:ℕ):ℝ)))).congr_deriv
    dsimp [tariffSecond]
    ring

theorem binomialPolynomial_tariff_first_eq (d : ℕ) (hd : 1 ≤ d)
    (a : UserTariff) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    binomialPolynomialDerivative (d+1) a.charge p = tariffFirst d a p := by
  have he : binomialPolynomial (d+1) a.charge =ᶠ[𝓝 p] tariffFormula d a := by
    filter_upwards [Ioo_mem_nhds hp0 hp1] with x hx
    exact binomialPolynomial_tariff_eq d a x hx.1.le hx.2.le
  exact (hasDerivAt_binomialPolynomial (d+1) a.charge p).unique
    ((hasDerivAt_tariffFormula d hd a p hp1).congr_of_eventuallyEq he)

theorem binomialPolynomial_tariff_second_eq (d : ℕ) (hd : 1 ≤ d)
    (a : UserTariff) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    deriv (binomialPolynomialDerivative (d+1) a.charge) p = tariffSecond d a p := by
  have he : binomialPolynomialDerivative (d+1) a.charge =ᶠ[𝓝 p] tariffFirst d a := by
    filter_upwards [Ioo_mem_nhds hp0 hp1] with x hx
    exact binomialPolynomial_tariff_first_eq d hd a x hx.1 hx.2
  exact ((hasDerivAt_tariffFirst d hd a p hp1).congr_of_eventuallyEq he).deriv

theorem unique_tariff_jet (d : ℕ) (hd : 1 ≤ d) (p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) :
    (binomialPolynomial (d+1) UserTariff.unique.charge p,
      binomialPolynomialDerivative (d+1) UserTariff.unique.charge p,
      deriv (binomialPolynomialDerivative (d+1) UserTariff.unique.charge) p) =
      uniqueJet (d:ℝ) (1-p) ((1-p)^d) := by
  rw [binomialPolynomial_tariff_eq d .unique p hp0.le hp1.le,
    binomialPolynomial_tariff_first_eq d hd .unique p hp0 hp1,
    binomialPolynomial_tariff_second_eq d hd .unique p hp0 hp1]
  simp only [tariffFormula, tariffFirst, tariffSecond, uniqueJet,
    Nat.cast_add, Nat.cast_one, sub_sub_cancel]

theorem affine_tariff_jet (d : ℕ) (hd : 1 ≤ d) (eta p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) :
    binomialPolynomial (d+1) (UserTariff.affine eta).charge p =
      (1-eta)*(onceJet (d:ℝ) (1-p) ((1-p)^d)).1+
        eta*(perInclusionJet (d:ℝ) (1-p)).1 ∧
    binomialPolynomialDerivative (d+1) (UserTariff.affine eta).charge p =
      (1-eta)*(onceJet (d:ℝ) (1-p) ((1-p)^d)).2.1+
        eta*(perInclusionJet (d:ℝ) (1-p)).2.1 ∧
    deriv (binomialPolynomialDerivative (d+1) (UserTariff.affine eta).charge) p =
      (1-eta)*(onceJet (d:ℝ) (1-p) ((1-p)^d)).2.2+
        eta*(perInclusionJet (d:ℝ) (1-p)).2.2 := by
  rw [binomialPolynomial_tariff_eq d (.affine eta) p hp0.le hp1.le,
    binomialPolynomial_tariff_first_eq d hd (.affine eta) p hp0 hp1,
    binomialPolynomial_tariff_second_eq d hd (.affine eta) p hp0 hp1]
  simp only [tariffFormula, tariffFirst, tariffSecond, onceJet, perInclusionJet,
    PayOnce.success, pow_succ, Nat.cast_add, Nat.cast_one, sub_sub_cancel]
  constructor
  · ring
  · constructor
    · trivial
    · simp only [mul_zero, add_zero]

def literalReferenceCurvature (d : ℕ) (a : UserTariff) (p : ℝ) : ℝ :=
  referenceCurvature (d:ℝ) (1-p)
    (binomialPolynomial (d+1) a.charge p)
    (binomialPolynomialDerivative (d+1) a.charge p)
    (deriv (binomialPolynomialDerivative (d+1) a.charge) p)

def literalReferenceCross (d : ℕ) (a : UserTariff) (p : ℝ) : ℝ :=
  referenceCross (d:ℝ) (1-p)
    (binomialPolynomial (d+1) a.charge p)
    (binomialPolynomialDerivative (d+1) a.charge p)
    (deriv (binomialPolynomialDerivative (d+1) a.charge) p)

theorem literal_reference_model (d : ℕ) (hd : 1 ≤ d) (a : UserTariff) (p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) :
    literalReferenceCurvature d a p = referenceCurvatureModel (d:ℝ) (1-p) ((1-p)^d) a ∧
      literalReferenceCross d a p = referenceCrossModel (d:ℝ) (1-p) a := by
  have hdne : (d:ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hqne : 1-p ≠ 0 := (sub_pos.mpr hp1).ne'
  cases a with
  | unique =>
    have hjet := unique_tariff_jet d hd p hp0 hp1
    have h0 := congrArg Prod.fst hjet
    have h1 := congrArg (fun t : ℝ×ℝ×ℝ => t.2.1) hjet
    have h2 := congrArg (fun t : ℝ×ℝ×ℝ => t.2.2) hjet
    dsimp only [Prod.fst, Prod.snd] at h0 h1 h2
    dsimp only [literalReferenceCurvature, literalReferenceCross]
    rw [h0, h1, h2]
    exact reference_unique (d:ℝ) (1-p) ((1-p)^d) hdne hqne
  | affine eta =>
    obtain ⟨h0, h1, h2⟩ := affine_tariff_jet d hd eta p hp0 hp1
    dsimp only [literalReferenceCurvature, literalReferenceCross]
    rw [h0, h1, h2]
    have hm := reference_affine (d:ℝ) (1-p) eta
      (onceJet (d:ℝ) (1-p) ((1-p)^d)).1
      (onceJet (d:ℝ) (1-p) ((1-p)^d)).2.1
      (onceJet (d:ℝ) (1-p) ((1-p)^d)).2.2
      (perInclusionJet (d:ℝ) (1-p)).1
      (perInclusionJet (d:ℝ) (1-p)).2.1
      (perInclusionJet (d:ℝ) (1-p)).2.2
    have ho := reference_once (d:ℝ) (1-p) ((1-p)^d) hdne
    have hp := reference_perInclusion (d:ℝ) (1-p) hdne
    rw [ho.1, hp.1] at hm
    rw [ho.2, hp.2] at hm
    dsimp only [referenceCurvatureModel, referenceCrossModel]
    simpa only [mul_div_assoc] using hm

theorem literal_reference_bounds (d : ℕ) (hd : 1 ≤ d) (a : UserTariff) (ha : a.Allowed)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    0 < literalReferenceCurvature d a p ∧
      |literalReferenceCross d a p| ≤ (2/3:ℝ)*literalReferenceCurvature d a p := by
  obtain ⟨hK, hC⟩ := literal_reference_model d hd a p hp0 hp1
  rw [hK, hC]
  exact reference_model_bounds (d:ℝ) (1-p) ((1-p)^d) (by exact_mod_cast hd)
    (sub_pos.mpr hp1) (by linarith) (pow_pos (sub_pos.mpr hp1) d) a ha

theorem tariff_marginal_identity (d : ℕ) (a : UserTariff) (p : ℝ) (hp : p < 1) :
    tariffFirst d a p+(d:ℝ)*tariffFormula d a p/(1-p) =
      ((d+1:ℕ):ℝ)*((1-p)^d)^2*fTariff d a p := by
  have hq : 1-p ≠ 0 := (sub_pos.mpr hp).ne'
  have hn : ((d+1:ℕ):ℝ) ≠ 0 := by positivity
  have hpow : (1-p)^(2*d+1) = ((1-p)^d)^2*(1-p) := by
    rw [pow_succ, show 2*d = d*2 by omega, pow_mul]
  cases a with
  | unique =>
    dsimp [tariffFirst, tariffFormula, fTariff, fUnique]
    field_simp [hq, pow_ne_zero d hq]
    ring
  | affine eta =>
    dsimp [tariffFirst, tariffFormula, fTariff, fOnce, fPerInclusion, PayOnce.success]
    rw [hpow, pow_succ]
    field_simp [hq, hn, pow_ne_zero d hq]
    push_cast
    ring

def referenceBidScale (d : ℕ) (a : UserTariff) (p : ℝ) : ℝ :=
  (1/fTariff d a p)/(1-p)^d

theorem referenceBidScale_pos (d : ℕ) (hd : 1 ≤ d) (a : UserTariff) (ha : a.Allowed)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) : 0 < referenceBidScale d a p := by
  exact div_pos (one_div_pos.mpr (fTariff_pos_and_derivative_pos d hd a ha hp0 hp1).1)
    (pow_pos (sub_pos.mpr hp1) d)

theorem referenceBidScale_firstOrder (d : ℕ) (hd : 1 ≤ d)
    (a : UserTariff) (ha : a.Allowed) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) :
    ((d+1:ℕ):ℝ)*(1-p)^d = referenceBidScale d a p*
      (tariffFirst d a p+(d:ℝ)*tariffFormula d a p/(1-p)) := by
  have hf := (fTariff_pos_and_derivative_pos d hd a ha hp0 hp1).1.ne'
  have hQ := (pow_pos (sub_pos.mpr hp1) d).ne'
  rw [tariff_marginal_identity d a p hp1]
  dsimp [referenceBidScale]
  field_simp [hf, hQ]

end FCAppendix.Exclusive.Narrow.Existence
