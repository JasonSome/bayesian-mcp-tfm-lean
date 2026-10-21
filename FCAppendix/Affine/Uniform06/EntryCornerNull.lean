import FCAppendix.Affine.Uniform06.EntryThresholdNull
import FCAppendix.Affine.Uniform06.RegularRootDifferentiability

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryCornerNull

open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.LowBody
open FCAppendix.Affine.ClippedResidual
open EntryThresholdNull
open scoped BigOperators

def without {N : ℕ} (ξ : ℝ) (E : Finset (Fin N)) (j : Fin N)
    (r : Fin N → RowRival) (z : ℝ) : ℝ :=
  ∑ k ∈ Finset.univ.erase j, contribution ξ z E k (r k)

def curve {N : ℕ} (ξ b : ℝ) (E : Finset (Fin N)) (j : Fin N)
    (r : Fin N → RowRival) (z : ℝ) : ℝ :=
  exposure ξ z b+without ξ E j r z

lemma without_antitone {N : ℕ} {ξ x y : ℝ} (hξ : 0 < ξ)
    (E : Finset (Fin N)) (j : Fin N) (r : Fin N → RowRival)
    (hx : 0 < x) (hxy : x ≤ y) : without ξ E j r y ≤ without ξ E j r x := by
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : k ∈ E
  · simp only [contribution,if_pos hk,le_refl]
  · by_cases htag : (r k).1=0
    · simp only [contribution,if_neg hk,if_pos htag]
      exact EntryOwnImpact.exposure_antitone_price hξ hx hxy
    · simp only [contribution,if_neg hk,if_neg htag,le_refl]

lemma curve_strictAntiOn {N : ℕ} {ξ b : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hb : 0 < b)
    (E : Finset (Fin N)) (j : Fin N) (r : Fin N → RowRival) :
    StrictAntiOn (curve ξ b E j r) (Ioo ((1-ξ)*b) b) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := (mul_pos (sub_pos.mpr hξ1) hb).trans hx.1
  have hy0 := hx0.trans hxy
  have hpart : exposure ξ y b < exposure ξ x b := by
    rw [exposure_of_between hξ hy0 hy.2 hy.1.le,exposure_of_between hξ hx0 hx.2 hx.1.le]
    exact div_lt_div_of_pos_right (sub_lt_sub_left (div_lt_div_of_pos_right hxy hb) 1) hξ
  have hrem := without_antitone hξ E j r hx0 hxy.le
  unfold curve
  linarith

lemma curve_update {N : ℕ} (ξ b : ℝ) (E : Finset (Fin N)) (j : Fin N)
    (r : Fin N → RowRival) (u : RowRival) (z : ℝ) :
    curve ξ b E j (Function.update r j u) z=curve ξ b E j r z := by
  unfold curve without
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

lemma measurable_curve {N : ℕ} (ξ b : ℝ) (E : Finset (Fin N)) (j : Fin N) :
    Measurable (fun p : (Fin N → RowRival) × ℝ => curve ξ b E j p.1 p.2) := by
  unfold curve without
  apply Measurable.add
  · unfold exposure
    fun_prop
  · apply Finset.measurable_sum
    intro k _
    by_cases hk : k ∈ E
    · simp only [contribution,if_pos hk]
      exact measurable_const
    · simp only [contribution,if_neg hk]
      apply Measurable.ite
        (measurableSet_eq_fun
          (show Measurable (fun p : (Fin N → RowRival) × ℝ => (p.1 k).1) by fun_prop)
          measurable_const)
      · unfold exposure
        fun_prop
      · exact measurable_const

theorem ae_scaled_curve_ne (μ : Measure RowRival)
    (hnull : ∀ y : ℝ, ∀ᵐ u ∂μ, u.1=0 → u.2 ≠ y)
    {N : ℕ} {ξ b a : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hb : 0 < b) (ha : 0 < a)
    (E : Finset (Fin N)) (j : Fin N) (r : Fin N → RowRival) (d : ℝ) :
    ∀ᵐ u ∂μ, u.1=0 → a*u.2 ∈ Ioo ((1-ξ)*b) b →
      curve ξ b E j r (a*u.2) ≠ d := by
  by_cases he : ∃ y : ℝ, a*y ∈ Ioo ((1-ξ)*b) b ∧ curve ξ b E j r (a*y)=d
  · obtain ⟨y,hy,hey⟩ := he
    filter_upwards [hnull y] with u hu htag huy heu
    apply hu htag
    have hinj := (curve_strictAntiOn hξ hξ1 hb E j r).injOn huy hy (heu.trans hey.symm)
    exact mul_left_cancel₀ ha.ne' hinj
  · exact ae_of_all _ fun u _ huy heu => he ⟨u.2,huy,heu⟩

theorem singled_corner_coordinate (μ : Measure RowRival) [IsProbabilityMeasure μ]
    (hnull : ∀ y : ℝ, ∀ᵐ u ∂μ, u.1=0 → u.2 ≠ y)
    {N : ℕ} {ξ b a : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hb : 0 < b) (ha : 0 < a)
    (E : Finset (Fin N)) (j : Fin N) (d : ℝ) :
    ∀ᵐ r ∂Measure.pi (fun _ : Fin N => μ), (r j).1=0 →
      a*(r j).2 ∈ Ioo ((1-ξ)*b) b → curve ξ b E j r (a*(r j).2) ≠ d := by
  let P := fun (u : RowRival) (r : Fin N → RowRival) => u.1=0 →
    a*u.2 ∈ Ioo ((1-ξ)*b) b → curve ξ b E j r (a*u.2) ≠ d
  have hPm : MeasurableSet {p : RowRival × (Fin N → RowRival) | P p.1 p.2} := by
    have hc : Measurable (fun p : RowRival × (Fin N → RowRival) => curve ξ b E j p.2 (a*p.1.2)) :=
      (measurable_curve ξ b E j).comp
        (show Measurable (fun p : RowRival × (Fin N → RowRival) => (p.2,a*p.1.2)) by fun_prop)
    have hmTag : Measurable (fun p : RowRival × (Fin N → RowRival) => p.1.1) := by fun_prop
    have hmBid : Measurable (fun p : RowRival × (Fin N → RowRival) => a*p.1.2) := by fun_prop
    have ht := measurableSet_eq_fun hmTag (measurable_const (a := (0:Fin 4)))
    have hi : MeasurableSet {p : RowRival × (Fin N → RowRival) |
        a*p.1.2 ∈ Ioo ((1-ξ)*b) b} := measurableSet_Ioo.preimage hmBid
    have he := (measurableSet_eq_fun hc (measurable_const (a := d))).compl
    convert! ht.compl.union (hi.compl.union he) using 1
    ext p
    simp only [P,mem_setOf_eq,mem_union,mem_compl_iff,imp_iff_not_or,ne_eq]

  have hPi : ∀ u r u', P u (Function.update r j u') ↔ P u r := by
    intro u r u'
    simp only [P,curve_update]
  have hAE : ∀ᵐ u ∂μ, ∀ᵐ r ∂Measure.pi (fun _ : Fin N => μ), P u r := by
    apply (Measure.ae_ae_comm hPm).mpr
    exact ae_of_all _ fun r => ae_scaled_curve_ne μ hnull hξ hξ1 hb ha E j r d
  exact FCAppendix.Resample.ae_resample μ j P hPm hPi hAE

lemma upper_corner_identity {N : ℕ} (ξ b : ℝ)
    (E : Finset (Fin N)) (j : Fin N) (r : Fin N → RowRival) :
    exposure ξ (r j).2 b+demand ξ (r j).2 E r=curve ξ b E j r (r j).2 := by
  have hz : contribution ξ (r j).2 E j (r j)=0 := by
    unfold contribution
    split_ifs <;> simp only [exposure_zero le_rfl]
  unfold demand curve without
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),hz,zero_add]

lemma lower_corner_exposure {ξ B : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1) (hB : 0 < B) :
    exposure ξ ((1-ξ)*B) B=1 := by
  have hz := mul_pos (sub_pos.mpr hξ1) hB
  have hzB : (1-ξ)*B < B := by nlinarith [mul_pos hξ hB]
  rw [exposure_of_between hξ hz hzB le_rfl]
  field_simp [hB.ne',hξ.ne']
  ring

lemma lower_corner_identity {N : ℕ} {ξ b : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (E : Finset (Fin N)) (j : Fin N) (r : Fin N → RowRival)
    (hB : 0 < (r j).2) :
    exposure ξ ((1-ξ)*(r j).2) b+demand ξ ((1-ξ)*(r j).2) E r=
      curve ξ b E j r ((1-ξ)*(r j).2)+(if j ∉ E ∧ (r j).1=0 then 1 else 0) := by
  have hz : contribution ξ ((1-ξ)*(r j).2) E j (r j)=
      if j ∉ E ∧ (r j).1=0 then 1 else 0 := by
    by_cases hj : j ∈ E
    · simp [contribution,hj]
    · by_cases ht : (r j).1=0
      · simp [contribution,hj,ht,lower_corner_exposure hξ hξ1 hB]
      · simp [contribution,hj,ht]
  unfold demand curve without
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),hz]
  ring

theorem original_fixed_price_corner_null (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G] (hnull : ∀ a : ℝ, (G.map Prod.snd) {a}=0)
    (N : ℕ) {b : ℝ} (hb : 0 < b) :
    ∀ᵐ r ∂Measure.pi (fun _ : Fin N => RawMixedSource.source i G),
      ∀ (E : Finset (Fin N)) (c : ℕ) (j : Fin N), (r j).1=0 →
      ((r j).2 ∈ Ioo ((1-xi i)*b) b →
        exposure (xi i) (r j).2 b+demand (xi i) (r j).2 E r ≠ (c:ℝ)) ∧
      ((1-xi i)*(r j).2 ∈ Ioo ((1-xi i)*b) b →
        exposure (xi i) ((1-xi i)*(r j).2) b+
          demand (xi i) ((1-xi i)*(r j).2) E r ≠ (c:ℝ)) := by
  have hξ := xi_pos i
  have hξ1 : xi i < 1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  have hall (E : Finset (Fin N)) (c : ℕ) (j : Fin N) :
      ∀ᵐ r ∂Measure.pi (fun _ : Fin N => RawMixedSource.source i G),
        (r j).1=0 →
        ((r j).2 ∈ Ioo ((1-xi i)*b) b →
          exposure (xi i) (r j).2 b+demand (xi i) (r j).2 E r ≠ (c:ℝ)) ∧
        ((1-xi i)*(r j).2 ∈ Ioo ((1-xi i)*b) b →
          exposure (xi i) ((1-xi i)*(r j).2) b+
            demand (xi i) ((1-xi i)*(r j).2) E r ≠ (c:ℝ)) := by
    have hn := raw_lower_bid_ne i G hnull
    filter_upwards [singled_corner_coordinate (RawMixedSource.source i G) hn hξ hξ1 hb
      (by norm_num : (0:ℝ)<1) E j (c:ℝ),
      singled_corner_coordinate (RawMixedSource.source i G) hn hξ hξ1 hb
        (sub_pos.mpr hξ1) E j (c:ℝ),
      singled_corner_coordinate (RawMixedSource.source i G) hn hξ hξ1 hb
        (sub_pos.mpr hξ1) E j ((c:ℝ)-1)] with r hu hl0 hl1 htag
    constructor
    · intro hstrip he
      rw [upper_corner_identity] at he
      exact hu htag (by simpa only [one_mul] using hstrip) (by simpa only [one_mul] using he)
    · intro hstrip he
      have hBp : 0 < (r j).2 := by
        have hp : 0 < (1-xi i)*(r j).2 := (mul_pos (sub_pos.mpr hξ1) hb).trans hstrip.1
        exact (mul_pos_iff_of_pos_left (sub_pos.mpr hξ1)).mp hp
      rw [lower_corner_identity hξ hξ1 E j r hBp] at he
      by_cases hj : j ∈ E
      · simp only [hj,not_true_eq_false,false_and,if_false,add_zero] at he
        exact hl0 htag hstrip he
      · simp only [hj,not_false_eq_true,htag,and_self,if_true] at he
        exact hl1 htag hstrip (by linarith)
  exact ae_all_iff.mpr fun E => ae_all_iff.mpr fun c => ae_all_iff.mpr fun j => hall E c j

end FCAppendix.Affine.Uniform06.EntryCornerNull
