import FCAppendix.Affine.UniformFinite.ActualContinuation
import FCAppendix.Affine.UniformFinite.AtomCrossingAlgebra
import FCAppendix.Affine.LowBody.FirstCopyIntegrated

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped BigOperators

namespace ActualAtoms

lemma twice_kappa (i : Uniform07.Row) :
    2 * Uniform05.kappa i = 1 + Uniform05.eta i := by
  unfold Uniform05.kappa Uniform05.xi
  ring

lemma kappa_ge_half (i : Uniform07.Row) : (1:ℝ)/2 ≤ Uniform05.kappa i := by
  have he := (Uniform05.eta_range i).1
  have hk := twice_kappa i
  linarith

theorem pairPayoff_eq_purePayoff {M : ℕ} (i : Uniform07.Row)
    (v : ℝ) (b : Fin M → ℝ) (focal : Fin M) (P : Allocation M) :
    pairPayoff (Uniform05.eta i) v (b focal) focal P =
      LowBody.purePayoff (Uniform05.kappa i) v b P focal := by
  have hk := twice_kappa i
  by_cases h0 : focal ∈ P.1 <;> by_cases h1 : focal ∈ P.2 <;>
    simp [pairPayoff, Literal.firstCopy, Literal.duplicateCopy,
      WeightedSampling.indicator, LowBody.purePayoff, LowBody.focalCopy,
      h0, h1, Fin.ext_iff]; nlinarith [congrArg (fun x => x*b focal) hk]

lemma lowerBids_update {M : ℕ} (row : Source.CountRow M)
    (b : Fin M → ℝ) (focal : Fin M) (hf : focal ∈ row.lower) (x : ℝ) :
    Source.lowerBids row (Function.update b focal x) =
      Function.update (Source.lowerBids row b) focal x := by
  funext a
  by_cases ha : a=focal
  · subst a
    simp [Source.lowerBids, hf]
  · simp [Source.lowerBids, Function.update_of_ne ha]

lemma lowerBids_pairBids {M : ℕ} (row : Source.CountRow M)
    (b : Fin M → ℝ) (focal rival : Fin M)
    (hf : focal ∈ row.lower) (hr : rival ∈ row.lower) (x y : ℝ) :
    Source.lowerBids row (LowBody.pairBids b focal rival x y) =
      LowBody.pairBids (Source.lowerBids row b) focal rival x y := by
  simp only [LowBody.pairBids, lowerBids_update row _ rival hr,
    lowerBids_update row _ focal hf]

theorem guardAlpha_zero_of_small_zero {M : ℕ} [NeZero M]
    (i : Uniform07.Row) (G : Uniform05.RestrictedLaw i)
    (row : Source.CountRow M) (b : Fin M → ℝ) (hs : Source.small row = 0) :
    Source.guardAlpha i G row b = 0 := by
  have hnonneg := (Source.guardAlpha_bounds i G row b).1
  apply le_antisymm _ hnonneg
  by_contra hn
  have ha : 0 < Source.guardAlpha i G row b := lt_of_not_ge hn
  have hsl := (Source.guardAlpha_pos_slacks i G row b ha).2 1
  have hMr : 0 < (M:ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne M))
  have hr := Source.rootBounds i G
  have hD : 0 ≤ Source.highDemand i G row b :=
    Finset.sum_nonneg (fun a _ => Uniform05.exposure_nonneg
      (Uniform05.xi_range i).1 (hr.1.trans hr.2.1))
  simp only [Source.sourceSlacks, Matrix.cons_val_one, Matrix.cons_val_zero,
    hs, Nat.cast_zero, zero_sub] at hsl
  have hpos := mul_pos (Source.common_guard_margin i) hMr
  have hcontra := (lt_div_iff₀ hMr).mp hsl
  linarith

theorem guardAlpha_zero_of_right_zero {M : ℕ} [NeZero M]
    (i : Uniform07.Row) (G : Uniform05.RestrictedLaw i)
    (row : Source.CountRow M) (b : Fin M → ℝ)
    (hzero : Source.residual row 1 = 0) :
    Source.guardAlpha i G row b = 0 := by
  apply guardAlpha_zero_of_small_zero i G row b
  simp [Source.small, hzero]

theorem rowPayoff_eq_pure_of_right_zero {M : ℕ} [NeZero M]
    (i : Uniform07.Row) (G : Uniform05.RestrictedLaw i)
    (row : Source.CountRow M) (v : ℝ) (b : Fin M → ℝ) (focal : Fin M)
    (hf : focal ∈ row.lower) (hleft : 0 < Source.residual row 0)
    (hzero : Source.residual row 1 = 0) :
    rowPayoff i G row v b focal =
      LowBody.purePayoff (Uniform05.kappa i) v (Source.lowerBids row b)
        ((Source.lowerTemplate row).selection (Uniform05.kappa i)
          (Source.lowerBids row b)) focal := by
  have hne : Source.residual row 0 ≠ Source.residual row 1 := by omega
  unfold rowPayoff
  rw [continuation_alpha_zero i G row b hne
    (guardAlpha_zero_of_right_zero i G row b hzero)]
  simp only [pureLaw, FiniteLaw.expect_dirac]
  rw [← Source.lowerBids_of_mem row b hf]
  exact pairPayoff_eq_purePayoff i v (Source.lowerBids row b) focal _

theorem row_firstCopy_crossing_gain {M : ℕ} [NeZero M]
    (i : Uniform07.Row) (G : Uniform05.RestrictedLaw i)
    (row : Source.CountRow M) (v : ℝ) (b : Fin M → ℝ) (focal : Fin M)
    (hf : focal ∈ row.lower) (hleft : 0 < Source.residual row 0)
    (hzero : Source.residual row 1 = 0)
    (l u x S : ℝ) (hl : l ≤ b focal) (hux : u < x) (hx : 0 < x)
    (hS : S ≤ v - b focal)
    (hcount : (Finset.univ.filter (fun k => k ≠ focal ∧
      u < Source.lowerBids row b k)).card < Source.residual row 0) :
    (if focal ∉ ((Source.lowerTemplate row).selection (Uniform05.kappa i)
      (Source.lowerBids row b)).1 then S else 0) - (x-l) ≤
      rowPayoff i G row v (Function.update b focal x) focal -
        rowPayoff i G row v b focal := by
  rw [rowPayoff_eq_pure_of_right_zero i G row v (Function.update b focal x)
    focal hf hleft hzero, rowPayoff_eq_pure_of_right_zero i G row v b
    focal hf hleft hzero, lowerBids_update row b focal hf]
  exact LowBody.firstCopy_crossing_gain (Source.lowerTemplate row)
    (Uniform05.kappa i) v (Source.lowerBids row b) hzero
    (fun k hk => Source.lowerBids_of_not_mem row b hk) focal hf l u x S
    (by simpa only [Source.lowerBids_of_mem row b hf] using hl) hux hx
    (by simpa only [Source.lowerBids_of_mem row b hf] using hS) hcount

theorem row_zero_bid_right_domination {M : ℕ} [NeZero M]
    (i : Uniform07.Row) (G : Uniform05.RestrictedLaw i)
    (row : Source.CountRow M) (v : ℝ) (b : Fin M → ℝ) (focal : Fin M)
    (hf : focal ∈ row.lower) (hleft : 0 < Source.residual row 0)
    (hzero : Source.residual row 1 = 0) (hbid : b focal=0)
    (hv : 0≤ v) (x : ℝ) (hx : 0< x) :
    rowPayoff i G row v b focal ≤
      rowPayoff i G row v (Function.update b focal x) focal +
        2 * Uniform05.kappa i * x := by
  rw [rowPayoff_eq_pure_of_right_zero i G row v b focal hf hleft hzero,
    rowPayoff_eq_pure_of_right_zero i G row v (Function.update b focal x)
      focal hf hleft hzero, lowerBids_update row b focal hf]
  exact PureAtoms.zero_bid_right_domination (Source.lowerTemplate row)
    (kappa_ge_half i) (Source.lowerBids row b) focal
    (by simpa only [Source.lowerBids_of_mem row b hf] using hbid) v x hv hx

theorem row_pair_rejection_ge_half {M : ℕ} [NeZero M]
    (i : Uniform07.Row) (row : Source.CountRow M)
    (b : Fin M → ℝ) (focal rival : Fin M) (hfr : focal ≠ rival)
    (hf : focal ∈ row.lower) (hr : rival ∈ row.lower)
    (hzero : Source.residual row 1 = 0)
    (u : ℝ) (hcount : Source.residual row 0 - 1 ≤
      (LowBody.pairRestAbove u focal rival (Source.lowerBids row b)).card)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (hμ : ∀ᵐ x ∂μ, x≤ u) :
    (1:ℝ)/2 ≤ (μ.prod μ).real {p : ℝ×ℝ |
      focal ∉ ((Source.lowerTemplate row).selection (Uniform05.kappa i)
        (Source.lowerBids row (LowBody.pairBids b focal rival p.1 p.2))).1} := by
  simp only [lowerBids_pairBids row b focal rival hf hr]
  exact LowBody.pair_rejection_probability_ge_half (Source.lowerTemplate row)
    (Uniform05.kappa i) (Source.lowerBids row b) focal rival hfr hf hr hzero
    (fun k hk => Source.lowerBids_of_not_mem row b hk) u hcount μ hμ

end ActualAtoms
end FCAppendix.Affine.UniformFinite
