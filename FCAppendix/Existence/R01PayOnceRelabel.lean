import FCAppendix.Existence.R01PayOnceKernel

noncomputable section
namespace FCAppendix.Existence.PayOnceBounded
open Set

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def activeEquiv {ε W : ℝ} (e : ι ≃ κ) (x : κ → FloorAction ε W) :
    ↥(activeSet (x ∘ e)) ≃ ↥(activeSet x) where
  toFun i := ⟨e i.1, by simpa only [mem_activeSet, Function.comp_apply] using i.2⟩
  invFun i := ⟨e.symm i.1, by simpa only [mem_activeSet, Function.comp_apply,
    Equiv.apply_symm_apply] using i.2⟩
  left_inv i := Subtype.ext (e.symm_apply_apply i.1)
  right_inv i := Subtype.ext (e.apply_symm_apply i.1)

theorem marginal_relabel {ε W : ℝ} (e : ι ≃ κ) (n c : ℕ) (hn : 2 ≤ n)
    (hε : 0 < ε) (x : κ → FloorAction ε W) (i : ι) :
    marginal n c (x ∘ e) i = marginal n c x (e i) := by
  have hmem : i ∈ activeSet (x ∘ e) ↔ e i ∈ activeSet x := by
    simp only [mem_activeSet, Function.comp_apply]
  by_cases hi : i ∈ activeSet (x ∘ e)
  · have hei := hmem.mp hi
    have hp : ∀ j : ↥(activeSet x), 0 < bid (x j.1) := fun j =>
      bid_pos_of_present hε _ ((mem_activeSet x j.1).mp j.2)
    have he := congrFun (kernel_equiv (activeEquiv e x) n c hn
      (fun j : ↥(activeSet x) => bid (x j.1)) hp) ⟨i, hi⟩
    dsimp only [marginal, onSupport]
    rw [dif_pos hi, dif_pos hei]
    exact he
  · have hei : e i ∉ activeSet x := fun h => hi (hmem.mpr h)
    simp only [marginal, onSupport, dif_neg hi, dif_neg hei]

theorem success_relabel {ε W : ℝ} (e : ι ≃ κ) (n c : ℕ) (hn : 2 ≤ n)
    (hε : 0 < ε) (x : κ → FloorAction ε W) (i : ι) :
    success n c (x ∘ e) i = success n c x (e i) := by
  simp only [success, marginal_relabel e n c hn hε x i]

end FCAppendix.Existence.PayOnceBounded
