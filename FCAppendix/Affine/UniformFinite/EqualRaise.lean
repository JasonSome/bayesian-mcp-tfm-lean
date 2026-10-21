import FCAppendix.Affine.UniformFinite.OwnBidModulus

noncomputable section
namespace FCAppendix.Affine
open Set MeasureTheory Classical
open scoped BigOperators

namespace EqualCapacity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem positiveMarginal_mono_update {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (b : ι → ℝ) (hb : ∀ j, 0 ≤ b j) (a : ι) (y : ℝ)
    (hraise : b a ≤ y) :
    positiveMarginal ξ c b a ≤ positiveMarginal ξ c (Function.update b a y) a := by
  by_cases he : b a = y
  · simp only [← he, Function.update_eq_self]
    exact le_rfl
  have hy : b a < y := lt_of_le_of_ne hraise he
  let p := positiveMarginal ξ c b
  let q := positiveMarginal ξ c (Function.update b a y)
  have hq := positiveMarginal_spec ξ c hξ hξ1 (Function.update b a y)
  have hx := positive_kernel_cross hξ hξ1 c b (Function.update b a y)
  change (∑ j, (q j-p j)*(b j*(1-ξ*p j)-Function.update b a y j*(1-ξ*q j))) ≤ 0 at hx
  have heq : (∑ j, (q j-p j)*(b j*(1-ξ*p j)-Function.update b a y j*(1-ξ*q j))) =
      (∑ j, ξ*b j*(q j-p j)^2) - (q a-p a)*(y-b a)*(1-ξ*q a) := by
    calc
      _ = (∑ j, ξ*b j*(q j-p j)^2) -
          ∑ j, (q j-p j)*(Function.update b a y j-b j)*(1-ξ*q j) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by
        congr 1
        rw [Finset.sum_eq_single a]
        · simp only [Function.update_self]
        · intro j _ hja
          simp only [Function.update_of_ne hja, sub_self, mul_zero, zero_mul]
        · simp
  rw [heq] at hx
  have hsum : 0 ≤ ∑ j, ξ*b j*(q j-p j)^2 :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (mul_nonneg hξ.le (hb j)) (sq_nonneg _))
  have hreceipt : 0 < 1-ξ*q a := by
    have hq1 := hq.2.1 a
    have hh := mul_le_mul_of_nonneg_left hq1 hξ.le
    linarith
  by_contra hn
  have hqp : q a-p a < 0 := sub_neg.mpr (lt_of_not_ge hn)
  have hneg := mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos hqp (sub_pos.mpr hy)) hreceipt
  linarith

theorem firstCopy_mono {p q : ℝ} (_hp : 0 ≤ p) (hq : q ≤ 1) (hpq : p ≤ q) :
    2*p-p^2 ≤ 2*q-q^2 := by
  have hfactor : 0 ≤ (q-p)*(2-p-q) := mul_nonneg (sub_nonneg.mpr hpq) (by linarith)
  nlinarith

theorem clipped_gain_lower_zero {eta v x y p q : ℝ}
    (heta : 0 ≤ eta) (hv : 0 ≤ v) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hp0 : 0 ≤ p) (hq1 : q ≤ 1) (hpq : p ≤ q) :
    -(1+eta)*y ≤ ((v-y)*(2*q-q^2)-eta*y*q^2) -
      ((v-x)*(2*p-p^2)-eta*x*p^2) := by
  have hq0 := hp0.trans hpq
  have hp1 := hpq.trans hq1
  have hs := firstCopy_mono hp0 hq1 hpq
  have hsp0 : 0 ≤ 2*p-p^2 := by nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hp1)]
  have hsq1 : 2*q-q^2 ≤ 1 := by nlinarith [sq_nonneg (q-1)]
  have hdq1 : q^2 ≤ 1 := by nlinarith
  have hval := mul_nonneg hv (sub_nonneg.mpr hs)
  have hold := mul_nonneg hx hsp0
  have holddup := mul_nonneg (mul_nonneg heta hx) (sq_nonneg p)
  have hnew := mul_le_mul_of_nonneg_left hsq1 (hx.trans hxy)
  have hnewdup := mul_le_mul_of_nonneg_left hdq1 (mul_nonneg heta (hx.trans hxy))
  nlinarith

theorem clipped_gain_lower {eta v x y p q : ℝ}
    (heta : 0 ≤ eta) (hx : 0 ≤ x) (hxv : x ≤ v) (hxy : x ≤ y)
    (hp0 : 0 ≤ p) (hq1 : q ≤ 1) (hpq : p ≤ q) :
    -eta*x-(1+eta)*(y-x) ≤ ((v-y)*(2*q-q^2)-eta*y*q^2) -
      ((v-x)*(2*p-p^2)-eta*x*p^2) := by
  have hq0 := hp0.trans hpq
  have hp1 := hpq.trans hq1
  have hs := firstCopy_mono hp0 hq1 hpq
  have hsq1 : 2*q-q^2 ≤ 1 := by nlinarith [sq_nonneg (q-1)]
  have hdq1 : q^2 ≤ 1 := by nlinarith
  have hgain := mul_nonneg (sub_nonneg.mpr hxv) (sub_nonneg.mpr hs)
  have hinc := mul_le_mul_of_nonneg_left hsq1 (sub_nonneg.mpr hxy)
  have hincdup := mul_le_mul_of_nonneg_left hdq1
    (mul_nonneg heta (sub_nonneg.mpr hxy))
  have holddup := mul_le_mul_of_nonneg_left
    (show q^2-p^2 ≤ 1 by nlinarith [sq_nonneg p]) (mul_nonneg heta hx)
  nlinarith

end EqualCapacity

namespace UniformFinite.OwnBid
open Uniform05 SourceContinuity
variable {M : ℕ}

lemma equal_rowPayoff_formula [NeZero M] (i : Row) (row : Source.CountRow M)
    (a : Fin M) (he : Source.residual row 0 = Source.residual row 1) (x : Box i M) :
    rowPayoff i x.2.1 row x.1 (bids i x.2) a =
      ((x.1:ℝ)-bids i x.2 a)*(2*equalMarginal i row a x.2-equalMarginal i row a x.2^2)-
        eta i*bids i x.2 a*equalMarginal i row a x.2^2 := by
  rw [rowPayoff,continuation_equal i x.2.1 row _ he]
  exact equalPayoff_eq i row a (realBox i x)

theorem equal_raise_lower_zero [NeZero M] (i : Row) (row : Source.CountRow M)
    (a : Fin M) (ha : a ∈ row.lower)
    (he : Source.residual row 0 = Source.residual row 1)
    (x : Box i M) (y : Bid i) (hraise : bids i x.2 a ≤ (y:ℝ)) :
    -(1+eta i)*(y:ℝ) ≤
      rowPayoff i x.2.1 row x.1 (bids i (change i x a y).2) a -
        rowPayoff i x.2.1 row x.1 (bids i x.2) a := by
  let b := Source.lowerBids row (bids i x.2)
  have hb : ∀ j, 0 ≤ b j := by
    intro j
    dsimp [b, Source.lowerBids]
    split_ifs
    · exact (bids_bounds i x.2 j).1
    · exact le_rfl
  have hba : b a = bids i x.2 a := by simp [b, ha]
  have heq : Source.lowerBids row (bids i (change i x a y).2) = Function.update b a (y:ℝ) := by
    funext j
    by_cases hja : j=a
    · subst j
      simp [b, Source.lowerBids, bids_change, ha]
    · simp [b, Source.lowerBids, bids_change, Function.update_of_ne hja]
  have hp := EqualCapacity.positiveMarginal_spec (xi i) (Source.small row)
    (xi_range i).1 (xi_range i).2 b
  have hq := EqualCapacity.positiveMarginal_spec (xi i) (Source.small row)
    (xi_range i).1 (xi_range i).2 (Function.update b a (y:ℝ))
  have hm := EqualCapacity.positiveMarginal_mono_update (xi_range i).1 (xi_range i).2
    (Source.small row) b hb a (y:ℝ) (by simpa only [hba] using hraise)
  have hg := EqualCapacity.clipped_gain_lower_zero (eta_range i).1.le x.1.property.1
    (bids_bounds i x.2 a).1 hraise (hp.1 a) (hq.2.1 a) hm
  change _ ≤ rowPayoff i (change i x a y).2.1 row (change i x a y).1
    (bids i (change i x a y).2) a - rowPayoff i x.2.1 row x.1 (bids i x.2) a
  rw [equal_rowPayoff_formula i row a he (change i x a y),
    equal_rowPayoff_formula i row a he x]
  simp only [equalMarginal]
  rw [heq]
  convert! hg using 1
  simp only [change,bids,Function.update_self,b]

theorem equal_raise_lower [NeZero M] (i : Row) (row : Source.CountRow M)
    (a : Fin M) (ha : a ∈ row.lower)
    (he : Source.residual row 0 = Source.residual row 1)
    (x : Box i M) (y : Bid i) (hraise : bids i x.2 a ≤ (y:ℝ))
    (hvalue : bids i x.2 a ≤ (x.1:ℝ)) :
    -eta i*bids i x.2 a-(1+eta i)*((y:ℝ)-bids i x.2 a) ≤
      rowPayoff i x.2.1 row x.1 (bids i (change i x a y).2) a -
        rowPayoff i x.2.1 row x.1 (bids i x.2) a := by
  let b := Source.lowerBids row (bids i x.2)
  have hb : ∀ j, 0 ≤ b j := by
    intro j
    dsimp [b, Source.lowerBids]
    split_ifs
    · exact (bids_bounds i x.2 j).1
    · exact le_rfl
  have hba : b a = bids i x.2 a := by simp [b, ha]
  have heq : Source.lowerBids row (bids i (change i x a y).2) = Function.update b a (y:ℝ) := by
    funext j
    by_cases hja : j=a
    · subst j
      simp [b, Source.lowerBids, bids_change, ha]
    · simp [b, Source.lowerBids, bids_change, Function.update_of_ne hja]
  have hp := EqualCapacity.positiveMarginal_spec (xi i) (Source.small row)
    (xi_range i).1 (xi_range i).2 b
  have hq := EqualCapacity.positiveMarginal_spec (xi i) (Source.small row)
    (xi_range i).1 (xi_range i).2 (Function.update b a (y:ℝ))
  have hm := EqualCapacity.positiveMarginal_mono_update (xi_range i).1 (xi_range i).2
    (Source.small row) b hb a (y:ℝ) (by simpa only [hba] using hraise)
  have hg := EqualCapacity.clipped_gain_lower (eta_range i).1.le
    (bids_bounds i x.2 a).1 hvalue hraise (hp.1 a) (hq.2.1 a) hm
  change _ ≤ rowPayoff i (change i x a y).2.1 row (change i x a y).1
    (bids i (change i x a y).2) a - rowPayoff i x.2.1 row x.1 (bids i x.2) a
  rw [equal_rowPayoff_formula i row a he (change i x a y),
    equal_rowPayoff_formula i row a he x]
  simp only [equalMarginal]
  rw [heq]
  convert! hg using 1
  simp only [change,bids,Function.update_self,b]

end UniformFinite.OwnBid
end FCAppendix.Affine
