import FCAppendix.Affine.Tail04.TypicalPrivateReceipts
import FCAppendix.Affine.Tail04.EmpiricalStatistics

noncomputable section
namespace FCAppendix.Affine.Tail04.Central
open Set MeasureTheory

def h : ℝ := 8/25
def activeMass (δ : ℝ) : ℝ := 67/100-δ
def mixedA (δ : ℝ) : ℝ := 10*δ/9
def mixedR (δ : ℝ) : ℝ := 5*(h+δ)/4
def ownersA (δ : ℝ) : ℝ := (activeMass δ-mixedA δ)/2
def ownersR (δ : ℝ) : ℝ := (activeMass δ-mixedR δ)/2
def B (ξ : ℝ) : ℝ := 1+ξ/50
def R (ξ : ℝ) : ℝ := 1-37*ξ/40
def lamA (ξ : ℝ) : ℝ := 1-19*ξ/20
def lamR (ξ : ℝ) : ℝ := 1-9*ξ/10

def harmonicMultiplier (ξ mixed reciprocal cap privateCount owners : ℝ) : ℝ :=
  (mixed-ξ*(cap-privateCount-owners))/reciprocal

theorem accept_realized_residual (δ : ℝ) :
    (99/200:ℝ)-h/2-ownersA δ=(19/20)*mixedA δ := by
  norm_num [h,ownersA,activeMass,mixedA]
  ring

theorem reject_realized_residual (δ p : ℝ) :
    (99/200:ℝ)-p-ownersR δ=(9/10)*mixedR δ-p := by
  norm_num [h,ownersR,activeMass,mixedR]
  ring

theorem accept_realized_multiplier (ξ δ : ℝ) (hδ : 0< δ) :
    harmonicMultiplier ξ (mixedA δ) (mixedA δ) (99/200) (h/2) (ownersA δ)=lamA ξ := by
  unfold harmonicMultiplier
  rw [accept_realized_residual]
  have hM : mixedA δ≠0 := by unfold mixedA; positivity
  unfold lamA
  field_simp [hM]

theorem reject_realized_marginal (δ p : ℝ) (hδ : 0≤ δ) :
    ((99/200:ℝ)-p-ownersR δ)/(mixedR δ)=9/10-4*p/(5*(h+δ)) := by
  rw [reject_realized_residual]
  have hh : 0< h+δ := by norm_num [h]; linarith
  unfold mixedR
  field_simp [hh.ne']

theorem reject_all_private_compositions (δ p : ℝ) (hδ : 0≤ δ)
    (hp : p∈Icc 0 (h/2)) :
    1/2+2*δ/(5*(h+δ)) ≤ ((99/200:ℝ)-p-ownersR δ)/(mixedR δ) ∧
      ((99/200:ℝ)-p-ownersR δ)/(mixedR δ) ≤ 9/10 := by
  have hh : 0< h+δ := by norm_num [h]; linarith
  rw [reject_realized_marginal δ p hδ]
  constructor
  · have he : (9/10-4*p/(5*(h+δ)))-(1/2+2*δ/(5*(h+δ))) =
        (2*h-4*p)/(5*(h+δ)) := by
      field_simp [hh.ne']
      ring
    have hn : 0≤(2*h-4*p)/(5*(h+δ)) :=
      div_nonneg (by linarith [hp.2]) (by positivity)
    exact sub_nonneg.mp (he.symm ▸ hn)
  · have hn : 0≤4*p/(5*(h+δ)) := div_nonneg (by linarith [hp.1]) (by positivity)
    linarith

theorem reject_marginal_half_to_nine_tenths (δ p : ℝ) (hδ : 0≤ δ)
    (hp : p∈Icc 0 (h/2)) :
    (1/2:ℝ) ≤ ((99/200:ℝ)-p-ownersR δ)/(mixedR δ) ∧
      ((99/200:ℝ)-p-ownersR δ)/(mixedR δ) ≤ 9/10 := by
  have hfull := reject_all_private_compositions δ p hδ hp
  have hx : 0≤2*δ/(5*(h+δ)) := by
    apply div_nonneg (by positivity)
    norm_num [h]
    linarith
  exact ⟨by linarith [hfull.1],hfull.2⟩

theorem reject_multiplier_formula (ξ δ p : ℝ) (hδ : 0≤ δ) :
    harmonicMultiplier ξ (mixedR δ) (mixedR δ) (99/200) p (ownersR δ) =
      1-ξ*(((99/200:ℝ)-p-ownersR δ)/(mixedR δ)) := by
  have hm : mixedR δ≠0 := by unfold mixedR h; positivity
  unfold harmonicMultiplier
  field_simp [hm]

theorem receipt_margins (ξ : ℝ) (hξ : 0< ξ) (_hξh : ξ<1/2) :
    (1-ξ)*B ξ+ξ/50< lamA ξ ∧ lamA ξ+ξ/100< R ξ ∧
      R ξ+ξ/100< lamR ξ ∧ lamA ξ+ξ/100<1 ∧ lamR ξ+ξ/100<1 := by
  norm_num [B,R,lamA,lamR]
  constructor
  · nlinarith [sq_nonneg ξ]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem reject_multiplier_robust (ξ δ p Λ : ℝ) (hξ : 0< ξ) (hξh : ξ<1/2)
    (hδ : 0≤ δ) (hp : p∈Icc 0 (h/2))
    (hΛ : |Λ-harmonicMultiplier ξ (mixedR δ) (mixedR δ)
      (99/200) p (ownersR δ)|≤ ξ/100) :
    (1-ξ)*B ξ< Λ ∧ Λ<1 := by
  have hq := reject_marginal_half_to_nine_tenths δ p hδ hp
  rw [reject_multiplier_formula ξ δ p hδ] at hΛ
  have he := abs_le.mp hΛ
  have hκ : (1-ξ)*B ξ < 1-(91/100)*ξ := by
    unfold B
    nlinarith [sq_nonneg ξ]
  constructor
  · have hlo : 1-(91/100)*ξ≤ Λ := by nlinarith [he.1,hq.2]
    exact hκ.trans_le hlo
  · nlinarith [he.2,hq.1]

theorem accept_multiplier_robust (ξ Λ : ℝ) (hξ : 0< ξ) (hξh : ξ<1/2)
    (hΛ : |Λ-lamA ξ|≤ ξ/100) :
    (1-ξ)*B ξ< Λ ∧ Λ< R ξ ∧ Λ<1 := by
  have he := abs_le.mp hΛ
  have hm := receipt_margins ξ hξ hξh
  refine ⟨by linarith [hm.1],by linarith [hm.2.1],by linarith [hm.2.2.2.1]⟩

theorem opposite_mean_receipt_sides (ξ LA LR : ℝ) (hξ : 0< ξ) (hξh : ξ<1/2)
    (hA : |LA-lamA ξ|≤ ξ/100) (hR : |LR-lamR ξ|≤ ξ/100) :
    LA< R ξ ∧ R ξ< LR := by
  have hm := receipt_margins ξ hξ hξh
  have ha := abs_le.mp hA
  have hr := abs_le.mp hR
  exact ⟨by linarith [hm.2.1],by linarith [hm.2.2.1]⟩

theorem marginal_strict_bounds (ξ Λ b : ℝ) (hξ : 0< ξ) (hξ1 : ξ<1)
    (hb : b∈Icc 1 (B ξ)) (hΛlo : (1-ξ)*B ξ< Λ) (hΛhi : Λ<1) :
    0<(1-Λ/b)/ξ ∧ (1-Λ/b)/ξ<1 := by
  have hb0 : 0< b := by linarith [hb.1]
  have hlow : Λ< b := hΛhi.trans_le hb.1
  have hhigh : (1-ξ)*b< Λ :=
    (mul_le_mul_of_nonneg_left hb.2 (by linarith)).trans_lt hΛlo
  constructor
  · apply div_pos _ hξ
    exact sub_pos.mpr ((div_lt_one hb0).mpr hlow)
  · apply (div_lt_one hξ).mpr
    have hdiv : 1-ξ< Λ/b := (lt_div_iff₀ hb0).mpr hhigh
    linarith

theorem ratio_error {n w n₀ w₀ L A E : ℝ}
    (hL : 0< L) (hw : L≤ w) (hw₀ : 0< w₀) (hn₀ : |n₀|≤ w₀)
    (hn : |n-n₀|≤ A) (hW : |w-w₀|≤ E) :
    |n/w-n₀/w₀|≤(A+E)/L := by
  have hw0 : 0< w := hL.trans_le hw
  have hratio : |n₀/w₀|≤1 := by
    rw [abs_div,abs_of_pos hw₀]
    exact (div_le_one hw₀).mpr hn₀
  have hE : 0≤ E := (abs_nonneg _).trans hW
  have hA : 0≤ A := (abs_nonneg _).trans hn
  have he : n/w-n₀/w₀=((n-n₀)-(n₀/w₀)*(w-w₀))/w := by
    field_simp [hw0.ne',hw₀.ne']
    ring
  rw [he,abs_div,abs_of_pos hw0]
  calc
    _ ≤ (|n-n₀|+|(n₀/w₀)*(w-w₀)|)/w :=
      div_le_div_of_nonneg_right (abs_sub _ _) hw0.le
    _ ≤ (A+E)/w := by
      apply div_le_div_of_nonneg_right _ hw0.le
      rw [abs_mul]
      have hh := mul_le_mul hratio hW (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
      linarith
    _ ≤ (A+E)/L := div_le_div_of_nonneg_left (by linarith) hL hw

theorem harmonic_multiplier_error (ξ M W C P O M₀ W₀ C₀ O₀ L εM εW εC εO : ℝ)
    (hξ : 0≤ ξ) (hL : 0< L) (hW : L≤ W) (hW₀ : 0< W₀)
    (hcentral : |M₀-ξ*(C₀-P-O₀)|≤ W₀)
    (hM : |M-M₀|≤ εM) (hrecip : |W-W₀|≤ εW)
    (hC : |C-C₀|≤ εC) (hO : |O-O₀|≤ εO) :
    |harmonicMultiplier ξ M W C P O-harmonicMultiplier ξ M₀ W₀ C₀ P O₀|≤
      (εM+ξ*(εC+εO)+εW)/L := by
  apply ratio_error hL hW hW₀ hcentral _ hrecip
  have he : (M-ξ*(C-P-O))-(M₀-ξ*(C₀-P-O₀)) =
      (M-M₀)-ξ*((C-C₀)-(O-O₀)) := by ring
  rw [he]
  calc
    _ ≤ |M-M₀|+|ξ*((C-C₀)-(O-O₀))| := abs_sub _ _
    _ ≤ εM+ξ*(εC+εO) := by
      rw [abs_mul,abs_of_nonneg hξ]
      have hh : |(C-C₀)-(O-O₀)|≤ εC+εO :=
        (abs_sub _ _).trans (add_le_add hC hO)
      exact add_le_add hM (mul_le_mul_of_nonneg_left hh hξ)

end FCAppendix.Affine.Tail04.Central
