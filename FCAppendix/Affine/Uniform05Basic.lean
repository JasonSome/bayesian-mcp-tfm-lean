import Mathlib
import FCAppendix.Affine.Uniform07.ParameterCertificate
import FCAppendix.Affine.ClippedResidualRoots

noncomputable section
namespace FCAppendix.Affine.Uniform05
open Set
open scoped BigOperators

abbrev Row := Uniform07.Row

def eta : Row → ℝ | .first => 1 / 10 | .second => 9 / 50

def x : Row → ℝ | .first => 3 / 4 | .second => 7 / 10

def delta : ℝ := 1 / 1000

def rho : ℝ := 999 / 2000

def chi : ℝ := 69 / 100

def xi (i : Row) : ℝ := (1 - eta i) / 2

def kappa (i : Row) : ℝ := 1 - xi i

def t (i : Row) : ℝ := delta / (2 * x i * (1 - Real.log (x i)) - 1)

def lambda (i : Row) : ℝ := x i * t i

def activeBid (i : Row) (v : ℝ) : ℝ :=
  lambda i * v / (kappa i * v + xi i * lambda i)

def upperFloorLimit (i : Row) : ℝ :=
  2 * lambda i - (lambda i)^2 / t i

def v0 (i : Row) : ℝ := t i / 200

def s (i : Row) : ℝ := lambda i + t i / 400

def zc (i : Row) : ℝ := lambda i + t i / 200

def cap (i : Row) : ℝ := activeBid i (t i) + t i / 200

def clip01 (y : ℝ) : ℝ := max 0 (min 1 y)

def floorBid (i : Row) (v : ℝ) : ℝ :=
  chi * max 0 (v - v0 i) * clip01 ((v - s i) / (zc i - s i))

def requiredDemand (i : Row) : ℝ := (t i - delta) / (2 * t i)

abbrev eligibleCapacity (m : ℕ) : ℕ := Uniform07.capacity m

theorem eta_eq_canonical (i : Row) : eta i = Uniform07.eta i := by
  cases i <;> norm_num [eta, Uniform07.eta, Uniform07.etaQ]
theorem x_eq_canonical (i : Row) : x i = Uniform07.x i := by
  cases i <;> norm_num [x, Uniform07.x, Uniform07.xQ]
theorem xi_eq_canonical (i : Row) : xi i = Uniform07.xi i := by
  cases i <;> norm_num [xi, eta, Uniform07.xi, Uniform07.xiQ, Uniform07.etaQ]
theorem kappa_eq_canonical (i : Row) : kappa i = Uniform07.kappa i := by
  cases i <;> norm_num [kappa, xi, eta, Uniform07.kappa, Uniform07.kappaQ,
    Uniform07.xiQ, Uniform07.etaQ]
theorem delta_eq_canonical : delta = Uniform07.delta := rfl
theorem rho_eq_canonical : rho = Uniform07.rho := rfl
theorem t_eq_canonical (i : Row) : t i = Uniform07.cutoff i := by
  simp only [t, Uniform07.cutoff, delta_eq_canonical, x_eq_canonical]
theorem lambda_eq_canonical (i : Row) : lambda i = Uniform07.entry i := by
  simp only [lambda, Uniform07.entry, x_eq_canonical, t_eq_canonical]
theorem upperFloorLimit_eq_canonical (i : Row) :
    upperFloorLimit i = Uniform07.limitingFloor i := by
  simp only [upperFloorLimit, Uniform07.limitingFloor, lambda_eq_canonical, t_eq_canonical]

lemma eta_range (i : Row) : 0 < eta i ∧ eta i < 1 := by
  cases i <;> norm_num [eta]

lemma xi_range (i : Row) : 0 < xi i ∧ xi i < 1 := by
  cases i <;> norm_num [xi, eta]

lemma kappa_range (i : Row) : 0 < kappa i ∧ kappa i < 1 := by
  cases i <;> norm_num [kappa, xi, eta]

lemma chi_margins (i : Row) :
    (1 : ℝ) / 2 < chi ∧ chi < 1 / (1 + eta i) := by
  cases i <;> norm_num [chi, eta]

lemma clip01_nonneg (y : ℝ) : 0 ≤ clip01 y := le_max_left _ _

lemma clip01_le_one (y : ℝ) : clip01 y ≤ 1 := by
  exact max_le (by norm_num) (min_le_left _ _)

lemma clip01_eq_zero {y : ℝ} (hy : y ≤ 0) : clip01 y = 0 := by
  simp only [clip01]
  exact max_eq_left ((min_le_right _ _).trans hy)

lemma clip01_eq_one {y : ℝ} (hy : 1 ≤ y) : clip01 y = 1 := by
  simp [clip01, min_eq_left hy]

lemma clip01_eq_self {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    clip01 y = y := by
  simp [clip01, min_eq_right hy.2, max_eq_right hy.1]

lemma continuous_clip01 : Continuous clip01 := by
  unfold clip01
  fun_prop

lemma floor_nonneg (i : Row) (v : ℝ) : 0 ≤ floorBid i v := by
  unfold floorBid
  exact mul_nonneg (mul_nonneg (by norm_num [chi]) (le_max_left _ _))
    (clip01_nonneg _)

lemma floor_le_chi_positivePart (i : Row) (v : ℝ) :
    floorBid i v ≤ chi * max 0 (v - v0 i) := by
  unfold floorBid
  simpa using mul_le_mul_of_nonneg_left (clip01_le_one ((v-s i)/(zc i-s i)))
    (mul_nonneg (by norm_num [chi]) (le_max_left _ _))

lemma floor_le_chi_mul (i : Row) {v : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t i) :
    floorBid i v ≤ chi * v := by
  apply (floor_le_chi_positivePart i v).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num [chi])
  apply max_le hv
  have : 0 ≤ v0 i := by dsimp [v0]; positivity
  linarith

lemma floor_le_value (i : Row) {v : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t i) :
    floorBid i v ≤ v := by
  have h := floor_le_chi_mul i hv ht
  norm_num [chi] at h ⊢
  nlinarith

lemma floor_zero_below_s (i : Row) {v : ℝ} (ht : 0 < t i) (hv : v ≤ s i) :
    floorBid i v = 0 := by
  have hz : 0 < zc i - s i := by dsimp [zc, s]; linarith
  have hq : (v - s i) / (zc i - s i) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hv) hz.le
  simp [floorBid, clip01_eq_zero hq]

lemma floor_full (i : Row) {v : ℝ} (ht : 0 < t i) (hv : zc i ≤ v) :
    floorBid i v = chi * max 0 (v-v0 i) := by
  have hz : 0 < zc i - s i := by dsimp [zc, s]; linarith
  have hq : 1 ≤ (v-s i)/(zc i-s i) := (le_div_iff₀ hz).2 (by linarith)
  simp [floorBid, clip01_eq_one hq]

lemma continuous_floor (i : Row) : Continuous (floorBid i) := by
  unfold floorBid
  exact (continuous_const.mul (continuous_const.max (continuous_id.sub continuous_const))).mul
    (continuous_clip01.comp ((continuous_id.sub continuous_const).div_const _))

lemma low_category_imp_value_le (i : Row) (ht : 0 < t i)
    (hreceipt : kappa i * cap i < chi * (zc i-v0 i))
    {v b : ℝ} (hf : floorBid i v ≤ b) (hb : b ≤ kappa i * cap i) :
    v ≤ zc i := by
  by_contra h
  have hv : zc i < v := lt_of_not_ge h
  have hfloor := floor_full i ht hv.le
  have hpart : v-v0 i ≤ max 0 (v-v0 i) := le_max_right _ _
  have hchi : 0 < chi := by norm_num [chi]
  have hlin : chi * (zc i-v0 i) < chi * (v-v0 i) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hpart hchi.le
  rw [hfloor] at hf
  linarith

lemma requiredDemand_eq (i : Row)
    (hd : 2*x i*(1-Real.log (x i))-1 ≠ 0) :
    requiredDemand i = 1 - x i + x i * Real.log (x i) := by
  have hδ : delta ≠ 0 := by norm_num [delta]
  unfold requiredDemand t
  field_simp [hd, hδ]
  ring

export ClippedResidual
  (exposure exposure_nonneg exposure_le_one exposure_zero exposure_of_between
    continuous_exposure)

theorem exposure_eq_source_clip {ξ z b : ℝ}
    (hξ : 0 < ξ) (_hz : 0 < z) (hb : 0 < b) :
    exposure ξ z b = clip01 ((1-z/b)/ξ) := by
  by_cases h : b ≤ z
  · rw [exposure_zero h]
    apply (clip01_eq_zero ?_).symm
    apply div_nonpos_of_nonpos_of_nonneg _ hξ.le
    have he : 1 ≤ z/b := (le_div_iff₀ hb).2 (by simpa using h)
    linarith
  · have hzb : z < b := lt_of_not_ge h
    have hnum : 0 ≤ b-z := sub_nonneg.mpr hzb.le
    have hratio : 0 ≤ (1-z/b)/ξ := by
      apply div_nonneg _ hξ.le
      have he : z/b ≤ 1 := (div_le_iff₀ hb).2 (by simpa using hzb.le)
      linarith
    rw [ClippedResidual.exposure, max_eq_left hzb.le, max_eq_right hnum]
    have he : (b-z)/(ξ*b) = (1-z/b)/ξ := by
      field_simp [hξ.ne', hb.ne']
    rw [he]
    unfold clip01
    exact (max_eq_right (le_min (by norm_num) hratio)).symm

def guardWeight (r p : ℝ) : ℝ := clip01 ((4*p-r)/r)

lemma guardWeight_nonneg (r p : ℝ) : 0 ≤ guardWeight r p := clip01_nonneg _

lemma guardWeight_le_one (r p : ℝ) : guardWeight r p ≤ 1 := clip01_le_one _

lemma guardWeight_zero {r p : ℝ} (hr : 0 < r) (hp : p ≤ r/4) :
    guardWeight r p = 0 := by
  apply clip01_eq_zero
  apply (div_le_iff₀ hr).2
  nlinarith

lemma guardWeight_one {r p : ℝ} (hr : 0 < r) (hp : r/2 ≤ p) :
    guardWeight r p = 1 := by
  apply clip01_eq_one
  apply (le_div_iff₀ hr).2
  nlinarith

lemma guardWeight_positive_imp {r p : ℝ} (hr : 0 < r)
    (hw : 0 < guardWeight r p) : r/4 < p := by
  by_contra hp
  have := guardWeight_zero hr (le_of_not_gt hp)
  linarith

lemma demand_le_weight_chord {r p : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p ≤ r/2 + (1-r/2) * guardWeight r p := by
  by_cases h : p ≤ r/2
  · have hw := guardWeight_nonneg r p
    have hc : 0 ≤ 1-r/2 := by linarith
    have := mul_nonneg hc hw
    linarith
  · rw [guardWeight_one hr (le_of_not_ge h)]
    linarith

lemma weight_mean_lower {r W : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hmean : r ≤ r/2+(1-r/2)*W) : r/(2-r) ≤ W := by
  have hd : 0 < 2-r := by linarith
  apply (div_le_iff₀ hd).2
  nlinarith

lemma exclusive_receipt_separation {κ U Λ a L b : ℝ}
    (hκ : 0 ≤ κ) (hbU : b ≤ U) (hb : Λ+3*a < b)
    (ha : 0 < a) (hroot : L ∈ Icc (Λ-a) (Λ+a))
    (hguard : κ*U < Λ-a) : κ*b < L ∧ L < b := by
  constructor
  · exact (mul_le_mul_of_nonneg_left hbU hκ).trans_lt (hguard.trans_le hroot.1)
  · linarith [hroot.2]

def bidPayoff (η v b S D : ℝ) : ℝ := (v-b)*S-η*b*D

lemma product_payoff_complete_square {v Λ p : ℝ}
    (hv : v ≠ 0) :
    v*(2*p-p^2)-2*Λ*p =
      (v-Λ)^2/v-v*(p-(1-Λ/v))^2 := by
  field_simp [hv]
  ring

lemma product_optimal_exposure {v Λ p : ℝ} (hv : 0 < v) :
    v*(2*p-p^2)-2*Λ*p ≤ (v-Λ)^2/v := by
  rw [product_payoff_complete_square hv.ne']
  have := mul_nonneg hv.le (sq_nonneg (p-(1-Λ/v)))
  linarith

lemma broadcast_singleton_identity (η v b q D : ℝ) :
    bidPayoff η v b (2*q-D) D - (v-b)*q =
      (v-b)*q-((v-b)+η*b)*D := by
  unfold bidPayoff
  ring

lemma broadcast_strictly_better_low {η v b q D L : ℝ}
    (hv : 0 < v) (hb : 0 ≤ b) (hη : η ≤ 1) (hD : 0 ≤ D)
    (hbest : v*L/2 ≤ (v-b)*q) (hsmall : D < L/2) :
    (v-b)*q < bidPayoff η v b (2*q-D) D := by
  have hc : ((v-b)+η*b)*D ≤ v*D := by
    apply mul_le_mul_of_nonneg_right _ hD
    nlinarith
  have hp := mul_pos hv (sub_pos.mpr hsmall)
  have hid := broadcast_singleton_identity η v b q D
  nlinarith

lemma two_type_success_order {v w ba bb Sa Sb Da Db η : ℝ}
    (hvw : v < w)
    (hva : bidPayoff η v bb Sb Db ≤ bidPayoff η v ba Sa Da)
    (hwb : bidPayoff η w ba Sa Da ≤ bidPayoff η w bb Sb Db) : Sa ≤ Sb := by
  unfold bidPayoff at hva hwb
  by_contra h
  have hpos := mul_pos (sub_pos.mpr hvw) (sub_pos.mpr (lt_of_not_ge h))
  nlinarith

lemma same_success_higher_bid_worse {η v a b S Da Db : ℝ}
    (hη : 0 ≤ η) (ha : 0 ≤ a) (hab : a < b)
    (hS : 0 < S) (hD0 : 0 ≤ Da) (hD : Da ≤ Db) :
    bidPayoff η v b S Db < bidPayoff η v a S Da := by
  have hcost : a*Da ≤ b*Db :=
    (mul_le_mul_of_nonneg_left hD ha).trans
      (mul_le_mul_of_nonneg_right hab.le (hD0.trans hD))
  have hηcost := mul_le_mul_of_nonneg_left hcost hη
  have hstrict := mul_pos (sub_pos.mpr hab) hS
  unfold bidPayoff
  nlinarith

end FCAppendix.Affine.Uniform05
