import FCAppendix.Affine.LowBody.PureFiniteCrossing

noncomputable section
namespace FCAppendix.Affine.LowBody
open Set
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma purePayoff_price_loss {κ w : ℝ} (hκ : 1/2≤κ)
    (b : ι→ℝ) (i : ι) (y : ℝ) (hy : b i≤y)
    (P : Finset ι × Finset ι) :
    purePayoff κ w b P i-purePayoff κ w (Function.update b i y) P i≤2*κ*(y-b i) := by
  simp only [purePayoff,Function.update_self]
  split_ifs <;> nlinarith

namespace PureTemplate

def harmfulInterval (T : PureTemplate ι) (κ : ℝ) (b : ι→ℝ) (i : ι) (y : ℝ) : Prop :=
  0<T.residual₀ ∧ 0<T.residual₁ ∧
    ∃j : ι,j∈T.support ∧ j≠i ∧
      (b j∈Icc (b i) y ∨ b j∈Icc (κ*b i) (κ*y))

def intervalLoss (T : PureTemplate ι) (κ : ℝ) (b : ι→ℝ) (i : ι) (y : ℝ) : ℝ := by
  classical
  exact if T.harmfulInterval κ b i y then (2*κ-1)*b i else 0

theorem finite_payoff_loss {L : ℕ} (T : PureTemplate (Fin L))
    {κ w : ℝ} (hκ : 1/2≤κ) (b : Fin L→ℝ) (hb : ∀j,0≤b j)
    (hz : ∀j,j∉T.support → b j=0) (i : Fin L) (hi : i∈T.support)
    (hbi : 0<b i) (hbw : b i≤w) (y : ℝ) (hy : b i<y) :
    purePayoff κ w b (T.selection κ b) i-
      purePayoff κ w (Function.update b i y) (T.selection κ (Function.update b i y)) i≤
      T.intervalLoss κ b i y+2*κ*(y-b i) := by
  classical
  have hκpos : 0<κ:=by linarith
  let P:=T.selection κ b
  let Q:=T.selection κ (Function.update b i y)
  have hcopy : focalCopy P i≤focalCopy Q i:=T.focalCopy_selection_mono hκpos b i y hy
  have hjump:=purePayoff_loss_le_duplicate (κ:=κ) b i hbw P Q hcopy
  have hprice:=purePayoff_price_loss hκ b i y hy.le Q (w:=w)
  have hbound : (if focalCopy P i≠2 ∧ focalCopy Q i=2 then (2*κ-1)*b i else 0)≤
      T.intervalLoss κ b i y := by
    by_cases hd : focalCopy P i≠2 ∧ focalCopy Q i=2
    · have he : T.harmfulInterval κ b i y:=
        T.duplicate_acquisition_interval hκpos b hb hz i hi hbi y hy hd.1 hd.2
      simp [intervalLoss,hd,he]
    · simp only [if_neg hd]
      unfold intervalLoss
      split_ifs
      · exact mul_nonneg (by linarith) hbi.le
      · exact le_rfl
  dsimp only [P,Q] at *
  linarith

theorem finite_payoff_loss_nonnegative {L : ℕ} (T : PureTemplate (Fin L))
    {κ w : ℝ} (hκ : 1/2≤κ) (b : Fin L→ℝ) (hb : ∀j,0≤b j)
    (hz : ∀j,j∉T.support → b j=0) (i : Fin L) (hi : i∈T.support)
    (hbw : b i≤w) (y : ℝ) (hy : b i<y) :
    purePayoff κ w b (T.selection κ b) i-
      purePayoff κ w (Function.update b i y) (T.selection κ (Function.update b i y)) i≤
      T.intervalLoss κ b i y+2*κ*(y-b i) := by
  by_cases hzero : b i=0
  · have hκpos : 0<κ:=by linarith
    let P:=T.selection κ b
    let Q:=T.selection κ (Function.update b i y)
    have hcopy : focalCopy P i≤focalCopy Q i:=T.focalCopy_selection_mono hκpos b i y hy
    have hjump:=purePayoff_loss_le_duplicate (κ:=κ) b i hbw P Q hcopy
    have hprice:=purePayoff_price_loss hκ b i y hy.le Q (w:=w)
    have hloss : T.intervalLoss κ b i y=0:=by
      classical
      simp [intervalLoss,hzero]
    have hs : purePayoff κ w b P i-purePayoff κ w b Q i≤0:=by
      simpa [hzero] using hjump
    rw [hloss]
    dsimp only [P,Q] at *
    linarith
  · exact T.finite_payoff_loss hκ b hb hz i hi (lt_of_le_of_ne (hb i) (Ne.symm hzero)) hbw y hy

end PureTemplate
end FCAppendix.Affine.LowBody
