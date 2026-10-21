import FCAppendix.Affine.Uniform06.Rank
import FCAppendix.Affine.Uniform06.LowChernoffSource
import FCAppendix.Finite.EnvelopeIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.ValueEnvelope
open MeasureTheory Set Filter

def utility (η : ℝ) (S D : ℝ → ℝ) (v b : ℝ) : ℝ :=
  Rank.payoff η v b (S b) (D b)

def optimized (η U : ℝ) (S D : ℝ → ℝ) (v : ℝ) : ℝ :=
  sSup ((utility η S D v) '' Icc (0:ℝ) U)

variable {η U : ℝ} {S D : ℝ → ℝ}

theorem utility_affine (v w b : ℝ) :
    utility η S D w b=utility η S D v b+(w-v)*S b := by
  unfold utility Rank.payoff
  ring

theorem utility_upper (hη : 0 ≤ η) (hS : ∀ b ∈ Icc (0:ℝ) U, S b ∈ Icc (0:ℝ) 1)
    (hD : ∀ b ∈ Icc (0:ℝ) U, 0 ≤ D b) (v : ℝ) {b : ℝ} (hb : b ∈ Icc (0:ℝ) U) :
    utility η S D v b ≤ |v| := by
  have hc := mul_nonneg hη (mul_nonneg hb.1 (hD b hb))
  have hbS := mul_nonneg hb.1 (hS b hb).1
  have hvS : v*S b ≤ |v| := by
    by_cases hv : 0 ≤ v
    · rw [abs_of_nonneg hv]
      exact mul_le_of_le_one_right hv (hS b hb).2
    · have hp := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hv) (hS b hb).1
      exact hp.trans (abs_nonneg v)
  unfold utility Rank.payoff
  nlinarith

theorem range_nonempty (hU : 0 ≤ U) (v : ℝ) :
    ((utility η S D v) '' Icc (0:ℝ) U).Nonempty :=
  ⟨utility η S D v 0,0,⟨le_rfl,hU⟩,rfl⟩

theorem range_bounded (hη : 0 ≤ η)
    (hS : ∀ b ∈ Icc (0:ℝ) U, S b ∈ Icc (0:ℝ) 1)
    (hD : ∀ b ∈ Icc (0:ℝ) U, 0 ≤ D b) (v : ℝ) :
    BddAbove ((utility η S D v) '' Icc (0:ℝ) U) := by
  refine ⟨|v|,?_⟩
  rintro _ ⟨b,hb,rfl⟩
  exact utility_upper hη hS hD v hb

theorem action_le_optimized (hη : 0 ≤ η)
    (hS : ∀ b ∈ Icc (0:ℝ) U, S b ∈ Icc (0:ℝ) 1)
    (hD : ∀ b ∈ Icc (0:ℝ) U, 0 ≤ D b) (v : ℝ) {b : ℝ} (hb : b ∈ Icc (0:ℝ) U) :
    utility η S D v b ≤ optimized η U S D v :=
  le_csSup (range_bounded hη hS hD v) ⟨b,hb,rfl⟩

theorem optimized_le (hU : 0 ≤ U) (v C : ℝ)
    (h : ∀ b ∈ Icc (0:ℝ) U, utility η S D v b ≤ C) : optimized η U S D v ≤ C := by
  apply csSup_le (range_nonempty hU v)
  rintro _ ⟨b,hb,rfl⟩
  exact h b hb

theorem optimized_eq_of_max (hU : 0 ≤ U) (hη : 0 ≤ η)
    (hS : ∀ b ∈ Icc (0:ℝ) U, S b ∈ Icc (0:ℝ) 1)
    (hD : ∀ b ∈ Icc (0:ℝ) U, 0 ≤ D b) (v : ℝ) {b : ℝ} (hb : b ∈ Icc (0:ℝ) U)
    (hmax : ∀ a ∈ Icc (0:ℝ) U, utility η S D v a ≤ utility η S D v b) :
    optimized η U S D v=utility η S D v b :=
  le_antisymm (optimized_le hU v _ hmax) (action_le_optimized hη hS hD v hb)

theorem optimized_monotone (hU : 0 ≤ U) (hη : 0 ≤ η)
    (hS : ∀ b ∈ Icc (0:ℝ) U, S b ∈ Icc (0:ℝ) 1)
    (hD : ∀ b ∈ Icc (0:ℝ) U, 0 ≤ D b) : Monotone (optimized η U S D) := by
  intro v w hvw
  apply optimized_le hU
  intro b hb
  have hh := action_le_optimized hη hS hD w hb
  rw [utility_affine v w b] at hh
  nlinarith [mul_nonneg (sub_nonneg.mpr hvw) (hS b hb).1]

theorem optimized_increment (hU : 0 ≤ U) (hη : 0 ≤ η)
    (hS : ∀ b ∈ Icc (0:ℝ) U, S b ∈ Icc (0:ℝ) 1)
    (hD : ∀ b ∈ Icc (0:ℝ) U, 0 ≤ D b) {v w : ℝ} (hvw : v ≤ w) :
    optimized η U S D w-optimized η U S D v ≤ w-v := by
  have hh : optimized η U S D w ≤ optimized η U S D v+(w-v) := by
    apply optimized_le hU
    intro b hb
    rw [utility_affine v w b]
    have hv := action_le_optimized hη hS hD v hb
    have hs := mul_le_mul_of_nonneg_left (hS b hb).2 (sub_nonneg.mpr hvw)
    linarith
  linarith

theorem optimized_lipschitz (hU : 0 ≤ U) (hη : 0 ≤ η)
    (hS : ∀ b ∈ Icc (0:ℝ) U, S b ∈ Icc (0:ℝ) 1)
    (hD : ∀ b ∈ Icc (0:ℝ) U, 0 ≤ D b) : LipschitzWith 1 (optimized η U S D) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [Real.dist_eq,NNReal.coe_one,one_mul]
  rcases le_total v w with hvw | hwv
  · rw [abs_of_nonpos (sub_nonpos.mpr (optimized_monotone hU hη hS hD hvw)),
      abs_of_nonpos (sub_nonpos.mpr hvw)]
    simpa only [neg_sub] using optimized_increment hU hη hS hD hvw
  · rw [abs_of_nonneg (sub_nonneg.mpr (optimized_monotone hU hη hS hD hwv)),
      abs_of_nonneg (sub_nonneg.mpr hwv)]
    exact optimized_increment hU hη hS hD hwv

theorem optimized_convex (hU : 0 ≤ U) (hη : 0 ≤ η)
    (hS : ∀ b ∈ Icc (0:ℝ) U, S b ∈ Icc (0:ℝ) 1)
    (hD : ∀ b ∈ Icc (0:ℝ) U, 0 ≤ D b) : ConvexOn ℝ univ (optimized η U S D) := by
  refine ⟨convex_univ,?_⟩
  intro v _ w _ a d ha hd had
  simp only [smul_eq_mul]
  apply optimized_le hU
  intro b hb
  have he : utility η S D (a*v+d*w) b=a*utility η S D v b+d*utility η S D w b := by
    have hdd : d=1-a := by linarith
    rw [hdd]
    unfold utility Rank.payoff
    ring
  rw [he]
  exact add_le_add (mul_le_mul_of_nonneg_left (action_le_optimized hη hS hD v hb) ha)
    (mul_le_mul_of_nonneg_left (action_le_optimized hη hS hD w hb) hd)

theorem optimized_AC_and_FTC (hU : 0 ≤ U) (hη : 0 ≤ η)
    (hS : ∀ b ∈ Icc (0:ℝ) U, S b ∈ Icc (0:ℝ) 1)
    (hD : ∀ b ∈ Icc (0:ℝ) U, 0 ≤ D b) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (optimized η U S D) a b ∧
      optimized η U S D b-optimized η U S D a=
        ∫ v in a..b, deriv (optimized η U S D) v := by
  have hAC : AbsolutelyContinuousOnInterval (optimized η U S D) a b := (optimized_lipschitz hU hη hS hD).lipschitzOnWith.absolutelyContinuousOnInterval
  exact ⟨hAC,hAC.integral_deriv_eq_sub.symm⟩

theorem optimized_supporting_line (hη : 0 ≤ η)
    (hS : ∀ b ∈ Icc (0:ℝ) U, S b ∈ Icc (0:ℝ) 1)
    (hD : ∀ b ∈ Icc (0:ℝ) U, 0 ≤ D b) {v b : ℝ}
    (hb : b ∈ Icc (0:ℝ) U) (he : optimized η U S D v=utility η S D v b) (w : ℝ) :
    optimized η U S D v+(w-v)*S b ≤ optimized η U S D w := by
  have hh := action_le_optimized hη hS hD w hb
  rwa [utility_affine v w b,← he] at hh

theorem restricted_IC_attains_common_menu (hU : 0 ≤ U) (hη : 0 ≤ η)
    (hS : ∀ b ∈ Icc (0:ℝ) U, S b ∈ Icc (0:ℝ) 1)
    (hD : ∀ b ∈ Icc (0:ℝ) U, 0 ≤ D b) {v b : ℝ}
    (hv : 0 ≤ v) (hb : b ∈ Icc (0:ℝ) (min v U))
    (hIC : ∀ a ∈ Icc (0:ℝ) (min v U), utility η S D v a ≤ utility η S D v b) :
    optimized η U S D v=utility η S D v b := by
  have hbU : b ∈ Icc (0:ℝ) U := ⟨hb.1,hb.2.trans (min_le_right _ _)⟩
  have h0 : utility η S D v 0 ≤ utility η S D v b :=
    hIC 0 ⟨le_rfl,le_min hv hU⟩
  have hused : 0 ≤ utility η S D v b := by
    have hs0 := (hS 0 ⟨le_rfl,hU⟩).1
    unfold utility Rank.payoff at h0 ⊢
    nlinarith
  apply optimized_eq_of_max hU hη hS hD v hbU
  intro a ha
  by_cases hav : a ≤ v
  · exact hIC a ⟨ha.1,le_min hav ha.2⟩
  · have hcharge := mul_nonneg (mul_nonneg hη ha.1) (hD a ha)
    have hmain := mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (le_of_not_ge hav)) (hS a ha).1
    unfold utility Rank.payoff at ⊢
    exact (sub_nonpos.mpr (by linarith)).trans hused

theorem envelope_of_ae_attainment (hU : 0 ≤ U) (hη : 0 ≤ η)
    (hS : ∀ b ∈ Icc (0:ℝ) U, S b ∈ Icc (0:ℝ) 1)
    (hD : ∀ b ∈ Icc (0:ℝ) U, 0 ≤ D b) (B : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hattain : ∀ᵐ v ∂volume, v ∈ Icc a b →
      B v ∈ Icc (0:ℝ) U ∧ optimized η U S D v=utility η S D v (B v)) :
    optimized η U S D b-optimized η U S D a=∫ v in a..b, S (B v) := by
  apply Subgradient.sub_eq_integral_of_ae_subgradient (optimized_convex hU hη hS hD)
    (S := univ) (by simp) hab
  filter_upwards [hattain] with v hv hvI w _
  exact optimized_supporting_line hη hS hD (hv hvI).1 (hv hvI).2 w

theorem same_joint_uniform_value_envelope (i : Uniform07.Row)
    (G : Measure (ℝ × ℝ)) (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hU : 0 ≤ U) (hη : 0 ≤ η)
    (hS : ∀ b ∈ Icc (0:ℝ) U, S b ∈ Icc (0:ℝ) 1)
    (hD : ∀ b ∈ Icc (0:ℝ) U, 0 ≤ D b)
    (hSm : Measurable S) (hDm : Measurable D) (B : ℝ → ℝ) (hB : Measurable B)
    {top a b : ℝ} (htop : top ≤ Uniform07.cutoff i)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ top)
    (hIC : ∀ᵐ p ∂G, p.1 ∈ Icc (0:ℝ) top →
      p.2=B p.1 ∧ p.2 ∈ Icc (0:ℝ) (min p.1 U) ∧
        ∀ q ∈ Icc (0:ℝ) (min p.1 U), utility η S D p.1 q ≤ utility η S D p.1 p.2) :
    optimized η U S D b-optimized η U S D a=∫ v in a..b, S (B v) := by
  let Good : Set ℝ := {v | v ∈ Icc (0:ℝ) top →
    B v ∈ Icc (0:ℝ) U ∧ optimized η U S D v=utility η S D v (B v)}
  have hoptm : Measurable (optimized η U S D) :=
    (optimized_lipschitz hU hη hS hD).continuous.measurable
  have hum : Measurable (fun v => utility η S D v (B v)) := by
    unfold utility Rank.payoff
    exact ((measurable_id.sub hB).mul (hSm.comp hB)).sub
      ((measurable_const.mul hB).mul (hDm.comp hB))
  have hGm : MeasurableSet Good := by
    have he : Good=(Icc (0:ℝ) top)ᶜ ∪
        ({v | B v ∈ Icc (0:ℝ) U} ∩ {v | optimized η U S D v=utility η S D v (B v)}) := by
      ext v
      change (_ → _ ∧ _) ↔ ¬_ ∨ _ ∧ _
      tauto
    rw [he]
    exact measurableSet_Icc.compl.union ((hB measurableSet_Icc).inter (measurableSet_eq_fun hoptm hum))
  have hGgood : ∀ᵐ p ∂G, p.1 ∈ Good := by
    filter_upwards [hIC] with p hp hv
    obtain ⟨hgraph,hbox,hic⟩ := hp hv
    have hcommon := restricted_IC_attains_common_menu hU hη hS hD hv.1 hbox hic
    rw [hgraph] at hbox hcommon
    exact ⟨⟨hbox.1,hbox.2.trans (min_le_right _ _)⟩,hcommon⟩
  have hpush : ∀ᵐ v ∂G.map Prod.fst, v ∈ Good :=
    (ae_map_iff measurable_fst.aemeasurable hGm).mpr hGgood
  rw [hvalue] at hpush
  have hc : ENNReal.ofReal (1/Uniform07.cutoff i) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (one_div_pos.mpr (Uniform07.cutoff_pos i)))
  have hrestricted : ∀ᵐ v ∂volume.restrict (Icc (0:ℝ) (Uniform07.cutoff i)), v ∈ Good := by
    rw [ae_iff] at hpush ⊢
    change ENNReal.ofReal (1/Uniform07.cutoff i)*
      (volume.restrict (Icc (0:ℝ) (Uniform07.cutoff i))) {v | v ∉ Good}=0 at hpush
    exact (mul_eq_zero.mp hpush).resolve_left hc
  have hvol := (ae_restrict_iff' measurableSet_Icc).mp hrestricted
  apply envelope_of_ae_attainment hU hη hS hD B hab
  filter_upwards [hvol] with v hv hvI
  have hvtop : v ∈ Icc (0:ℝ) top := ⟨ha.trans hvI.1,hvI.2.trans hb⟩
  exact hv ⟨hvtop.1,hvtop.2.trans htop⟩ hvtop

end FCAppendix.Affine.Uniform06.ValueEnvelope
