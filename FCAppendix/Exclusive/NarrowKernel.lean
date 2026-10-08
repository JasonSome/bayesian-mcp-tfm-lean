import FCAppendix.Exclusive.EquilibriumKernel
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace FCAppendix.Exclusive
open Proposer CommonList MeasureTheory Filter Topology Set
open scoped BigOperators

noncomputable def inverseBid (n : ℕ) (b : ℝ) : ℝ := b ^ (-rate n)

theorem demand_mono_bid (n : ℕ) (hn : 2 ≤ n) {b B lam : ℝ}
    (hb : 0 < b) (hbB : b ≤ B) (hlam : 0 ≤ lam) :
    demand n b lam ≤ demand n B lam := by
  have hB : 0 < B := hb.trans_le hbB
  have hquot : lam / B ≤ lam / b := div_le_div_of_nonneg_left hlam hb hbB
  have hpow := Real.rpow_le_rpow (div_nonneg hlam hB.le) hquot (rate_pos n hn).le
  exact max_le_max le_rfl (by linarith)

theorem inverseBid_pos (n : ℕ) {b : ℝ} (hb : 0 < b) : 0 < inverseBid n b :=
  Real.rpow_pos_of_pos hb _

theorem inverseBid_antitone (n : ℕ) (hn : 2 ≤ n) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) : inverseBid n b ≤ inverseBid n a :=
  Real.rpow_le_rpow_of_nonpos ha hab (neg_nonpos.mpr (rate_pos n hn).le)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem equilibrium_all_active_of_corridor (n : ℕ) (hn : 2 ≤ n)
    (b : ι → ℝ) (c M : ℕ) (hN : Fintype.card ι ≤ M)
    {a B : ℝ} (ha : 0 < a) (hb : ∀ i, b i ∈ Icc a B)
    (hspread : (M : ℝ) * demand n B a < c)
    (μ : FiniteLaw (Finset ι)) (hμ : ExclusiveEquilibrium n c b μ) :
    ∀ i, 0 < marginal μ i := by
  have hbpos i : 0 < b i := ha.trans_le (hb i).1
  by_cases hc : c < Fintype.card ι
  · obtain ⟨lam, hlam, hp, hsum⟩ := equilibrium_kernel n hn b hbpos c hc μ hμ
    intro i
    rw [hp i]
    by_contra hnot
    have hz : demand n (b i) lam = 0 := le_antisymm (le_of_not_gt hnot) (demand_nonneg _ _ _)
    have hbl := (demand_eq_zero_iff n hn (hbpos i) hlam.le).mp hz
    have hal : a ≤ lam := (hb i).1.trans hbl
    have hbound (j : ι) : demand n (b j) lam ≤ demand n B a :=
      (demand_mono_bid n hn (hbpos j) (hb j).2 hlam.le).trans
        (demand_antitone n hn (hbpos i |>.trans_le (hb i).2) ha.le hal)
    have hs := Finset.sum_le_sum (s := (Finset.univ : Finset ι)) (fun j _ => hbound j)
    rw [hsum] at hs
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
    have hNcast : (Fintype.card ι : ℝ) ≤ M := by exact_mod_cast hN
    have hfinal := hs.trans (mul_le_mul_of_nonneg_right hNcast (demand_nonneg n B a))
    linarith
  · rw [exclusive_small_list_unique n hn b hbpos c (by omega) μ hμ]
    intro i
    simp [marginal_dirac]

theorem one_sub_demand_eq_inverseBid (n : ℕ) (hn : 2 ≤ n) {b lam : ℝ}
    (hb : 0 < b) (hlam : 0 < lam) (hp : 0 < demand n b lam) :
    1 - demand n b lam = lam ^ rate n * inverseBid n b := by
  have hlb : lam < b := (demand_pos_iff n hn hb hlam.le).mp hp
  have hpow := Real.rpow_lt_one (div_nonneg hlam.le hb.le)
    ((div_lt_one hb).mpr hlb) (rate_pos n hn)
  rw [demand, max_eq_right (by linarith), sub_sub_cancel]
  rw [Real.div_rpow hlam.le hb.le, inverseBid, Real.rpow_neg hb.le]
  rfl

theorem equilibrium_inverse_power_formula (n : ℕ) (hn : 2 ≤ n)
    (b : ι → ℝ) (hb : ∀ i, 0 < b i) (c : ℕ)
    (hc : c < Fintype.card ι) (μ : FiniteLaw (Finset ι))
    (hμ : ExclusiveEquilibrium n c b μ) (hactive : ∀ i, 0 < marginal μ i) :
    ∃ lam : ℝ, 0 < lam ∧
      lam ^ rate n = ((Fintype.card ι : ℝ) - c) / (∑ j, inverseBid n (b j)) ∧
      (∀ i, marginal μ i = 1 -
        (((Fintype.card ι : ℝ) - c) * inverseBid n (b i)) / (∑ j, inverseBid n (b j))) ∧
      (∀ i, b i * (1 - marginal μ i) ^ (n - 1) = lam) := by
  classical
  have hnonempty : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  letI := hnonempty
  have hW : 0 < ∑ j, inverseBid n (b j) := Finset.sum_pos
    (fun j _ => inverseBid_pos n (hb j)) Finset.univ_nonempty
  obtain ⟨lam, hlam, hp, hroot⟩ := equilibrium_kernel n hn b hb c hc μ hμ
  have hcoord (i : ι) : 1 - marginal μ i = lam ^ rate n * inverseBid n (b i) := by
    rw [hp i]
    exact one_sub_demand_eq_inverseBid n hn (hb i) hlam (by simpa only [← hp i] using hactive i)
  have hsum : (∑ i, marginal μ i) = c := by simp_rw [hp]; exact hroot
  have he : ((Fintype.card ι : ℝ) - c) = lam ^ rate n * ∑ j, inverseBid n (b j) := by
    have hh := congrArg (fun f : ι → ℝ => ∑ i, f i) (funext hcoord)
    simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, hsum, ← Finset.mul_sum] using hh
  have hprice : lam ^ rate n = ((Fintype.card ι : ℝ) - c) / (∑ j, inverseBid n (b j)) :=
    (eq_div_iff hW.ne').mpr he.symm
  refine ⟨lam, hlam, hprice, ?_, ?_⟩
  · intro i
    have hh := hcoord i
    rw [hprice, div_mul_eq_mul_div] at hh
    linarith
  · intro i
    have hlt := (demand_pos_iff n hn (hb i) hlam.le).mp (by simpa only [← hp i] using hactive i)
    rw [hp i, demand_receipt n hn (hb i) hlam, min_eq_right hlt.le]

omit [DecidableEq ι] in

theorem inverseBid_share_le (n : ℕ) (hn : 2 ≤ n) (b : ι → ℝ)
    {a B : ℝ} (ha : 0 < a) (hb : ∀ i, b i ∈ Icc a B) (i : ι) :
    inverseBid n (b i) / (∑ j, inverseBid n (b j)) ≤
      inverseBid n a / ((Fintype.card ι : ℝ) * inverseBid n B) := by
  have hB : 0 < B := ha.trans_le ((hb i).1.trans (hb i).2)
  have hN : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
  have hden : 0 < (Fintype.card ι : ℝ) * inverseBid n B := mul_pos hN (inverseBid_pos n hB)
  have hs : (Fintype.card ι : ℝ) * inverseBid n B ≤ ∑ j, inverseBid n (b j) := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset ι))
      (fun j _ => inverseBid_antitone n hn (ha.trans_le (hb j).1) (hb j).2)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hh
  exact (div_le_div_of_nonneg_right (inverseBid_antitone n hn ha (hb i).1)
    (hden.trans_le hs).le).trans
      (div_le_div_of_nonneg_left (inverseBid_pos n ha).le hden hs)

end FCAppendix.Exclusive

namespace FCAppendix.Exclusive.Narrow
open Filter Topology Set

noncomputable def focalMarginal (r d W b : ℝ) : ℝ := 1 - d * b ^ (-r) / (W + b ^ (-r))
noncomputable def focalShare (r W b : ℝ) : ℝ := b ^ (-r) / (W + b ^ (-r))

theorem hasDerivAt_focalMarginal {r d W b : ℝ} (hb : 0 < b) (hW : 0 ≤ W) :
    HasDerivAt (focalMarginal r d W)
      (r * (1 - focalMarginal r d W b) / b * (1 - focalShare r W b)) b := by
  have hw : 0 < b ^ (-r) := Real.rpow_pos_of_pos hb _
  have hden : W + b ^ (-r) ≠ 0 := ne_of_gt (by linarith)
  have hpow : b ^ (-r - 1) = b ^ (-r) / b := by
    rw [Real.rpow_sub hb, Real.rpow_one]
  have hdw : HasDerivAt (fun x : ℝ => x ^ (-r)) (-r * (b ^ (-r) / b)) b := by
    convert Real.hasDerivAt_rpow_const (x := b) (p := -r) (Or.inl hb.ne') using 1
    rw [hpow]
  have hh := ((hdw.const_mul d).div ((hasDerivAt_const b W).add hdw) hden).const_sub 1
  change HasDerivAt (focalMarginal r d W) _ b at hh
  convert hh using 1
  dsimp only [focalMarginal, focalShare, Pi.add_apply]
  field_simp [hb.ne', hden]
  ring

theorem focalMarginal_derivative_pos {r d W b : ℝ}
    (hr : 0 < r) (hd : 0 < d) (hW : 0 < W) (hb : 0 < b) :
    0 < r * (1 - focalMarginal r d W b) / b * (1 - focalShare r W b) := by
  have hw : 0 < b ^ (-r) := Real.rpow_pos_of_pos hb _
  have hden : 0 < W + b ^ (-r) := add_pos hW hw
  have hq : 0 < 1 - focalMarginal r d W b := by
    dsimp only [focalMarginal]
    rw [sub_sub_cancel]
    exact div_pos (mul_pos hd hw) hden
  have hshare : focalShare r W b < 1 := by
    exact (div_lt_one hden).mpr (by linarith)
  exact mul_pos (div_pos (mul_pos hr hq) hb) (sub_pos.mpr hshare)

@[simp] theorem focalMarginal_zero_gap (r W b : ℝ) : focalMarginal r 0 W b = 1 := by
  simp [focalMarginal]

end FCAppendix.Exclusive.Narrow
