import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Data.Rat.Encodable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

noncomputable section
namespace FCAppendix.Existence.PayOnceBounded.Purity
open Set MeasureTheory ProbabilityTheory

def Best (Q : ℝ → ℝ) (w b : ℝ) : Prop :=
  0 < b ∧ 0 < Q b ∧ 0 < (w - b) * Q b ∧
    ∀ c : ℝ, 0 < c → (w - c) * Q c ≤ (w - b) * Q b

theorem value_pos {Q : ℝ → ℝ} {w b : ℝ} (hb : Best Q w b) : 0 < w := by
  have hs : 0 < w - b := pos_of_mul_pos_left hb.2.2.1 hb.2.1.le
  linarith [hb.1]

theorem success_order {Q : ℝ → ℝ} {w w' b b' : ℝ}
    (hw : w < w') (hb : Best Q w b) (hb' : Best Q w' b') : Q b ≤ Q b' := by
  have h₁ := hb.2.2.2 b' hb'.1
  have h₂ := hb'.2.2.2 b hb.1
  by_contra hnot
  have hgap : 0 < (w' - w) * (Q b - Q b') :=
    mul_pos (sub_pos.mpr hw) (sub_pos.mpr (lt_of_not_ge hnot))
  nlinarith

theorem equal_success_eq_bid {Q : ℝ → ℝ} {w b b' : ℝ}
    (hb : Best Q w b) (hb' : Best Q w b') (hQ : Q b = Q b') : b = b' := by
  have h₁ := hb.2.2.2 b' hb'.1
  have h₂ := hb'.2.2.2 b hb.1
  rw [← hQ] at h₁ h₂
  have he : b * Q b = b' * Q b := by nlinarith
  exact (mul_right_cancel₀ (ne_of_gt hb.2.1)) he

theorem bid_order {Q : ℝ → ℝ} (hQ : MonotoneOn Q (Ioi 0))
    {w w' b b' : ℝ} (hw : w < w') (hb : Best Q w b) (hb' : Best Q w' b') : b ≤ b' := by
  have hs := success_order hw hb hb'
  by_contra hnot
  have hbb' : b' < b := lt_of_not_ge hnot
  have hs' := hQ hb'.1 hb.1 hbb'.le
  have heQ := le_antisymm hs hs'
  have h₁ := hb.2.2.2 b' hb'.1
  have hpos : 0 < (b - b') * Q b := mul_pos (sub_pos.mpr hbb') hb.2.1
  rw [← heQ] at h₁
  nlinarith

def exceptional (Q : ℝ → ℝ) : Set ℝ :=
  {w | ∃ b c : ℝ, b < c ∧ Best Q w b ∧ Best Q w c}

theorem exceptional_countable (Q : ℝ → ℝ) (hQ : MonotoneOn Q (Ioi 0)) :
    (exceptional Q).Countable := by
  classical
  have hpair : ∀ w : exceptional Q, ∃ b c : ℝ,
      Best Q w.1 b ∧ Best Q w.1 c ∧ Q b < Q c := by
    rintro ⟨w, b, c, hbc, hb, hc⟩
    refine ⟨b, c, hb, hc, lt_of_le_of_ne (hQ hb.1 hc.1 hbc.le) ?_⟩
    intro he
    exact hbc.ne (equal_success_eq_bid hb hc he)
  choose b c hb hc hs using hpair
  have hrat : ∀ w : exceptional Q, ∃ r : ℚ, Q (b w) < r ∧ (r : ℝ) < Q (c w) :=
    fun w => exists_rat_btwn (hs w)
  choose r hr₁ hr₂ using hrat
  have hstrict : ∀ w w' : exceptional Q, w.1 < w'.1 → r w < r w' := by
    intro w w' hww'
    have he := success_order hww' (hc w) (hb w')
    have hh : (r w : ℝ) < (r w' : ℝ) := (hr₂ w).trans_le he |>.trans (hr₁ w')
    exact_mod_cast hh
  have hinj : Function.Injective r := by
    intro w w' he
    apply Subtype.ext
    rcases lt_trichotomy w.1 w'.1 with h | h | h
    · have hr := hstrict w w' h
      rw [he] at hr
      exact False.elim (lt_irrefl _ hr)
    · exact h
    · have hr := hstrict w' w h
      rw [he] at hr
      exact False.elim (lt_irrefl _ hr)
  letI : Countable (exceptional Q) := hinj.countable
  have hc : (Subtype.val '' (univ : Set (exceptional Q))).Countable :=
    (Set.to_countable _).image Subtype.val
  simpa using hc

theorem exceptional_null (Q : ℝ → ℝ) (hQ : MonotoneOn Q (Ioi 0))
    (μ : Measure ℝ) (hμ : ∀ w, 0 < w → μ {w} = 0) : μ (exceptional Q) = 0 := by
  have hc := exceptional_countable Q hQ
  letI : Countable (exceptional Q) := hc.to_subtype
  have hs : exceptional Q ⊆ ⋃ w : exceptional Q, ({w.1} : Set ℝ) := by
    intro w hw
    exact mem_iUnion.mpr ⟨⟨w, hw⟩, rfl⟩
  apply measure_mono_null hs
  apply measure_iUnion_null
  rintro ⟨w, b, c, hbc, hb, hc⟩
  exact hμ w (value_pos hb)

theorem unique_best_ae (Q : ℝ → ℝ) (hQ : MonotoneOn Q (Ioi 0))
    (μ : Measure ℝ) (hμ : ∀ w, 0 < w → μ {w} = 0) :
    ∀ᵐ w ∂μ, ∀ b c : ℝ, Best Q w b → Best Q w c → b = c := by
  have he := exceptional_null Q hQ μ hμ
  have hout : ∀ᵐ w ∂μ, w ∉ exceptional Q := by
    rw [ae_iff]
    simpa using he
  filter_upwards [hout] with w hw
  intro b c hb hc
  rcases lt_trichotomy b c with h | h | h
  · exact False.elim (hw ⟨b, c, h, hb, hc⟩)
  · exact h
  · exact False.elim (hw ⟨c, b, h, hc, hb⟩)

theorem pure_kernel_ae (Q : ℝ → ℝ) (hQ : MonotoneOn Q (Ioi 0))
    (μ : Measure ℝ) (hμ : ∀ w, 0 < w → μ {w} = 0)
    (σ : Kernel ℝ ℝ) [IsMarkovKernel σ]
    (hbest : ∀ᵐ w ∂μ, ∀ᵐ b ∂σ w, Best Q w b) :
    ∀ᵐ w ∂μ, ∃ b : ℝ, Best Q w b ∧ σ w = Measure.dirac b := by
  filter_upwards [unique_best_ae Q hQ μ hμ, hbest] with w hu hw
  obtain ⟨b, hb⟩ := hw.exists
  refine ⟨b, hb, ?_⟩
  have he : (fun b' : ℝ => b) =ᵐ[σ w] id := by
    filter_upwards [hw] with b' hb'
    exact hu b b' hb hb'
  have hm : (σ w).map (fun _ : ℝ => b) = (σ w).map (id : ℝ → ℝ) := Measure.map_congr he
  simpa using hm.symm
end FCAppendix.Existence.PayOnceBounded.Purity
