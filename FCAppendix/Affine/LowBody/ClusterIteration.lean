import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory Filter Topology Set

theorem no_positive_atoms_of_cluster_bound (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {κ ε : ℝ} (hκ : 0<κ) (hε : 0≤ε) (hsmall : ε<1/2)
    (hcross : ∀b : ℝ,0<b→mu.real {b}≤ε*(mu.real {b}+mu.real {κ*b})) :
    ∀b : ℝ,0<b→mu {b}=0 := by
  let r : ℝ:=ε/(1-ε)
  have hden : 0<1-ε:=by linarith
  have hr0 : 0≤r:=div_nonneg hε hden.le
  have hr1 : r<1:=by dsimp [r]; apply (div_lt_one hden).mpr; linarith
  have hstep (b : ℝ) (hb : 0<b) : mu.real {b}≤r*mu.real {κ*b} := by
    dsimp [r]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hden).mpr
    have hh:=hcross b hb
    nlinarith
  have hpow : ∀k : ℕ,∀b : ℝ,0<b→mu.real {b}≤r^k := by
    intro k
    induction k with
    | zero=>intro b _; simpa only [pow_zero] using (measureReal_le_one (μ:=mu) (s:={b}))
    | succ k ih=>
      intro b hb
      calc
        _≤r*mu.real {κ*b}:=hstep b hb
        _≤r*r^k:=mul_le_mul_of_nonneg_left (ih (κ*b) (mul_pos hκ hb)) hr0
        _=r^(k+1):=by rw [pow_succ]; ring
  intro b hb
  have hz : mu.real {b}≤0:=ge_of_tendsto (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1)
    (Eventually.of_forall (fun k=>hpow k b hb))
  have hreal : mu.real {b}=0:=le_antisymm hz measureReal_nonneg
  exact (ENNReal.toReal_eq_zero_iff (mu {b})).mp hreal |>.resolve_right (measure_ne_top mu {b})

end FCAppendix.Affine.LowBody
