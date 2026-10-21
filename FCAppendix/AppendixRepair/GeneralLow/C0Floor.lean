import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

namespace FCAppendix.Appendix08.GeneralLow
open Set

def ReceiptFloor (d : ℝ) (receipts : Set ℝ) : Prop :=
  receipts.Nonempty → d < sInf receipts

theorem strict_inf_iff_uniform_gap {d : ℝ} (hd : 0 ≤ d)
    {receipts : Set ℝ} (hne : receipts.Nonempty) :
    d < sInf receipts ↔
      ∃ ε : ℝ, 0 < ε ∧ ∀ r ∈ receipts, d + ε ≤ r := by
  constructor
  · intro h
    have hbounded : BddBelow receipts := by
      by_contra hb
      rw [Real.sInf_of_not_bddBelow hb] at h
      exact (not_lt_of_ge hd) h
    refine ⟨(sInf receipts - d) / 2, by linarith, ?_⟩
    intro r hr
    have hinf := csInf_le hbounded hr
    linarith
  · rintro ⟨ε, hε, hgap⟩
    have hle : d + ε ≤ sInf receipts := le_csInf hne hgap
    linarith

theorem receiptFloor_iff_uniform_gap {d : ℝ} (hd : 0 ≤ d) (receipts : Set ℝ) :
    ReceiptFloor d receipts ↔
      receipts.Nonempty → ∃ ε : ℝ, 0 < ε ∧ ∀ r ∈ receipts, d + ε ≤ r := by
  constructor
  · intro h hne
    exact (strict_inf_iff_uniform_gap hd hne).mp (h hne)
  · intro h hne
    exact (strict_inf_iff_uniform_gap hd hne).mpr (h hne)

theorem ReceiptFloor.pointwise {d : ℝ} {receipts : Set ℝ}
    (h : ReceiptFloor d receipts) (hd : 0 ≤ d) {r : ℝ} (hr : r ∈ receipts) : d < r := by
  obtain ⟨ε, hε, hgap⟩ := (receiptFloor_iff_uniform_gap hd receipts).mp h ⟨r, hr⟩
  have hh := hgap r hr
  linarith

@[simp] theorem receiptFloor_empty (d : ℝ) : ReceiptFloor d ∅ := by
  simp [ReceiptFloor]

theorem c0_pointwise {d κ : ℝ} (hd : 0 ≤ d) (activeSet privateSet : Set ℝ)
    (hactive : ReceiptFloor d ((fun b : ℝ => κ * b) '' activeSet))
    (hprivate : ReceiptFloor d privateSet) :
    (∀ b ∈ activeSet, d < κ * b) ∧ (∀ b ∈ privateSet, d < b) := by
  constructor
  · intro b hb
    exact hactive.pointwise hd (mem_image_of_mem (fun x : ℝ => κ * x) hb)
  · intro b hb
    exact hprivate.pointwise hd hb

end FCAppendix.Appendix08.GeneralLow
