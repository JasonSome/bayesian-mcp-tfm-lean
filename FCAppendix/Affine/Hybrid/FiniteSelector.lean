import FCAppendix.Affine.Hybrid.Menu
import FCAppendix.Affine.Hybrid.Sampling

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def finiteMultiplier (xi : ℝ) (b : ι → ℝ) (D : Finset ι) (r : ℕ) : ℝ :=
  ((D.card : ℝ)-xi*r)/(∑ i ∈ D, (b i)⁻¹)

omit [Fintype ι] [DecidableEq ι] in
lemma reciprocal_sum_pos (b : ι → ℝ) (D : Finset ι)
    (hne : D.Nonempty) (hb : ∀ i ∈ D, 0 < b i) :
    0 < ∑ i ∈ D, (b i)⁻¹ := by
  exact Finset.sum_pos (fun i hi => inv_pos.mpr (hb i hi)) hne

omit [Fintype ι] [DecidableEq ι] in
lemma sum_exposure (xi : ℝ) (b : ι → ℝ) (D : Finset ι) (r : ℕ)
    (hxi : xi ≠ 0) (hD : (∑ i ∈ D, (b i)⁻¹) ≠ 0) :
    ∑ i ∈ D, exposure xi (finiteMultiplier xi b D r) (b i) = r := by
  unfold exposure
  rw [←Finset.sum_div,Finset.sum_sub_distrib]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
  have hmul : (∑ i ∈ D, finiteMultiplier xi b D r / b i) =
      finiteMultiplier xi b D r * (∑ i ∈ D, (b i)⁻¹) := by
    simp only [div_eq_mul_inv,Finset.mul_sum]
  rw [hmul]
  unfold finiteMultiplier
  field_simp [hD,hxi]
  ring

def ownerMixedMarginal (E D : Finset ι) (xi lam : ℝ) (b : ι → ℝ) (i : ι) : ℝ :=
  if i ∈ E then 1 else if i ∈ D then exposure xi lam (b i) else 0

lemma ownerMixedMarginal_sum (E D : Finset ι) (xi lam : ℝ) (b : ι → ℝ)
    (hd : Disjoint E D) :
    ∑ i, ownerMixedMarginal E D xi lam b i =
      (E.card : ℝ) + ∑ i ∈ D, exposure xi lam (b i) := by
  have hp (i : ι) : ownerMixedMarginal E D xi lam b i =
      (if i ∈ E then (1 : ℝ) else 0) +
      (if i ∈ D then exposure xi lam (b i) else 0) := by
    by_cases hE : i ∈ E <;> by_cases hD : i ∈ D
    · exact False.elim ((Finset.disjoint_left.mp hd) hE hD)
    · simp [ownerMixedMarginal, hE, hD]
    · simp [ownerMixedMarginal, hE, hD]
    · simp [ownerMixedMarginal, hE, hD]
  simp_rw [hp, Finset.sum_add_distrib]
  simp

structure GuardedData (ι : Type*) [Fintype ι] [DecidableEq ι] where
  xi : ℝ
  xi_pos : 0 < xi
  xi_lt_one : xi < 1
  bid : ι → ℝ
  bid_pos : ∀ i, 0 < bid i
  owner₁ : Finset ι
  owner₂ : Finset ι
  owners_disjoint : Disjoint owner₁ owner₂
  residual : ℕ
  mixed_nonempty : (Finset.univ \ (owner₁ ∪ owner₂)).Nonempty
  lower_guard : ∀ i,
    (1-xi)*bid i < finiteMultiplier xi bid (Finset.univ \ (owner₁ ∪ owner₂)) residual
  upper_guard : ∀ i,
    finiteMultiplier xi bid (Finset.univ \ (owner₁ ∪ owner₂)) residual < bid i

namespace GuardedData
variable (G : GuardedData ι)
def mixed : Finset ι := Finset.univ \ (G.owner₁ ∪ G.owner₂)
def multiplier : ℝ := finiteMultiplier G.xi G.bid G.mixed G.residual
def p₁ : ι → ℝ := ownerMixedMarginal G.owner₁ G.mixed G.xi G.multiplier G.bid
def p₂ : ι → ℝ := ownerMixedMarginal G.owner₂ G.mixed G.xi G.multiplier G.bid
def law₁ : FiniteLaw (Finset ι) := ExactCapacity.symmetricLottery G.p₁
def law₂ : FiniteLaw (Finset ι) := ExactCapacity.symmetricLottery G.p₂

def jointLaw : FiniteLaw (Finset ι × Finset ι) := G.law₁.prod G.law₂

def receipt₁ (i : ι) : ℝ := G.bid i * (1-G.xi*G.p₂ i)
def receipt₂ (i : ι) : ℝ := G.bid i * (1-G.xi*G.p₁ i)

lemma owner₁_disjoint_mixed : Disjoint G.owner₁ G.mixed := by
  apply Finset.disjoint_left.mpr
  intro i hi hD
  simp only [mixed, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_union, not_or] at hD
  exact hD.1 hi
lemma owner₂_disjoint_mixed : Disjoint G.owner₂ G.mixed := by
  apply Finset.disjoint_left.mpr
  intro i hi hD
  simp only [mixed, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_union, not_or] at hD
  exact hD.2 hi
lemma mixed_iff (i : ι) : i ∈ G.mixed ↔ i ∉ G.owner₁ ∧ i ∉ G.owner₂ := by
  simp [mixed]

lemma multiplier_pos : 0 < G.multiplier := by
  obtain ⟨i, hi⟩ := G.mixed_nonempty
  have hp : 0 < (1-G.xi)*G.bid i :=
    mul_pos (sub_pos.mpr G.xi_lt_one) (G.bid_pos i)
  exact hp.trans (G.lower_guard i)

lemma exposure_interior (i : ι) :
    exposure G.xi G.multiplier (G.bid i) ∈ Set.Ioo (0 : ℝ) 1 :=
  exposure_mem_Ioo G.xi_pos (G.bid_pos i) (G.lower_guard i) (G.upper_guard i)

lemma marginal_bounds₁ (i : ι) : 0 ≤ G.p₁ i ∧ G.p₁ i ≤ 1 := by
  unfold p₁ ownerMixedMarginal
  split_ifs
  · norm_num
  · exact ⟨(G.exposure_interior i).1.le, (G.exposure_interior i).2.le⟩
  · norm_num
lemma marginal_bounds₂ (i : ι) : 0 ≤ G.p₂ i ∧ G.p₂ i ≤ 1 := by
  unfold p₂ ownerMixedMarginal
  split_ifs
  · norm_num
  · exact ⟨(G.exposure_interior i).1.le, (G.exposure_interior i).2.le⟩
  · norm_num

lemma exposure_sum : ∑ i ∈ G.mixed, exposure G.xi G.multiplier (G.bid i) = G.residual := by
  exact sum_exposure G.xi G.bid G.mixed G.residual G.xi_pos.ne'
    (reciprocal_sum_pos G.bid G.mixed G.mixed_nonempty (fun i _ => G.bid_pos i)).ne'

lemma p₁_sum : ∑ i, G.p₁ i = (G.owner₁.card+G.residual : ℕ) := by
  rw [p₁, ownerMixedMarginal_sum _ _ _ _ _ G.owner₁_disjoint_mixed, G.exposure_sum]
  norm_cast
lemma p₂_sum : ∑ i, G.p₂ i = (G.owner₂.card+G.residual : ℕ) := by
  rw [p₂, ownerMixedMarginal_sum _ _ _ _ _ G.owner₂_disjoint_mixed, G.exposure_sum]
  norm_cast

lemma law₁_implements : ExactCapacity.Implements G.p₁
    (G.owner₁.card+G.residual) G.law₁ :=
  ExactCapacity.symmetricLottery_implements G.p₁ _
    (fun i => (G.marginal_bounds₁ i).1) (fun i => (G.marginal_bounds₁ i).2) G.p₁_sum
lemma law₂_implements : ExactCapacity.Implements G.p₂
    (G.owner₂.card+G.residual) G.law₂ :=
  ExactCapacity.symmetricLottery_implements G.p₂ _
    (fun i => (G.marginal_bounds₂ i).1) (fun i => (G.marginal_bounds₂ i).2) G.p₂_sum

lemma support_mem_of_marginal_one (μ : FiniteLaw (Finset ι))
    (i : ι) (hi : μ.prob (fun S => i ∈ S) = 1)
    (S : Finset ι) (hS : μ.mass S ≠ 0) : i ∈ S := by
  by_contra hnot
  have hp : 0 < μ.prob (fun T => i ∉ T) := by
    rw [FiniteLaw.prob_eq_expect]
    unfold FiniteLaw.expect
    have hpos : 0 < μ.mass S := lt_of_le_of_ne (μ.nonneg S) hS.symm
    have hx := Finset.single_le_sum
      (f := fun T => μ.mass T * (if i ∉ T then (1 : ℝ) else 0))
      (fun T _ => mul_nonneg (μ.nonneg T) (by split_ifs <;> norm_num))
      (Finset.mem_univ S)
    have hx' : μ.mass S ≤ ∑ T, μ.mass T * (if i ∉ T then (1 : ℝ) else 0) := by
      simpa only [if_pos hnot,mul_one] using hx
    exact hpos.trans_le hx'
  rw [FiniteLaw.prob_compl, hi] at hp
  linarith

lemma support_mem_of_nonzero_marginal (μ : FiniteLaw (Finset ι))
    (i : ι) (hi : μ.prob (fun S => i ∈ S) = 0)
    (S : Finset ι) (hS : μ.mass S ≠ 0) : i ∉ S := by
  intro his
  have hp := FiniteLaw.marginal_pos_of_support_mem μ S hS i his
  rw [hi] at hp
  exact lt_irrefl _ hp

lemma law₁_support (S : Finset ι) (hS : G.law₁.mass S ≠ 0) :
    S.card = G.owner₁.card+G.residual ∧ G.owner₁ ⊆ S ∧ Disjoint S G.owner₂ := by
  refine ⟨G.law₁_implements.1 S hS, ?_, ?_⟩
  · intro i hi
    apply support_mem_of_marginal_one G.law₁ i _ S hS
    rw [G.law₁_implements.2]
    simp [p₁, ownerMixedMarginal, hi]
  · apply Finset.disjoint_left.mpr
    intro i his hi₂
    have hi₁ : i ∉ G.owner₁ := fun h => (Finset.disjoint_left.mp G.owners_disjoint) h hi₂
    have hiD : i ∉ G.mixed := fun h => (G.mixed_iff i).mp h |>.2 hi₂
    apply support_mem_of_nonzero_marginal G.law₁ i _ S hS his
    rw [G.law₁_implements.2]
    simp [p₁, ownerMixedMarginal, hi₁, hiD]

lemma law₂_support (S : Finset ι) (hS : G.law₂.mass S ≠ 0) :
    S.card = G.owner₂.card+G.residual ∧ G.owner₂ ⊆ S ∧ Disjoint S G.owner₁ := by
  refine ⟨G.law₂_implements.1 S hS, ?_, ?_⟩
  · intro i hi
    apply support_mem_of_marginal_one G.law₂ i _ S hS
    rw [G.law₂_implements.2]
    simp [p₂, ownerMixedMarginal, hi]
  · apply Finset.disjoint_left.mpr
    intro i his hi₁
    have hi₂ : i ∉ G.owner₂ := fun h => (Finset.disjoint_left.mp G.owners_disjoint) hi₁ h
    have hiD : i ∉ G.mixed := fun h => (G.mixed_iff i).mp h |>.1 hi₁
    apply support_mem_of_nonzero_marginal G.law₂ i _ S hS his
    rw [G.law₂_implements.2]
    simp [p₂, ownerMixedMarginal, hi₂, hiD]

lemma receipt₁_owner (i : ι) (hi : i ∈ G.owner₁) : G.receipt₁ i = G.bid i := by
  have hn : i ∉ G.owner₂ := fun h => (Finset.disjoint_left.mp G.owners_disjoint) hi h
  have hD : i ∉ G.mixed := fun h => (G.mixed_iff i).mp h |>.1 hi
  simp [receipt₁, p₂, ownerMixedMarginal, hn, hD]
lemma receipt₁_other (i : ι) (hi : i ∈ G.owner₂) :
    G.receipt₁ i = (1-G.xi)*G.bid i := by
  simp [receipt₁, p₂, ownerMixedMarginal, hi]
  ring
lemma receipt₁_mixed (i : ι) (hi : i ∈ G.mixed) : G.receipt₁ i = G.multiplier := by
  have hn := (G.mixed_iff i).mp hi
  simp only [receipt₁, p₂, ownerMixedMarginal, if_neg hn.2, if_pos hi]
  exact mixed_receipt _ _ _ G.xi_pos.ne' (G.bid_pos i).ne'

lemma receipt₂_owner (i : ι) (hi : i ∈ G.owner₂) : G.receipt₂ i = G.bid i := by
  have hn : i ∉ G.owner₁ := fun h => (Finset.disjoint_left.mp G.owners_disjoint) h hi
  have hD : i ∉ G.mixed := fun h => (G.mixed_iff i).mp h |>.2 hi
  simp [receipt₂, p₁, ownerMixedMarginal, hn, hD]
lemma receipt₂_other (i : ι) (hi : i ∈ G.owner₁) :
    G.receipt₂ i = (1-G.xi)*G.bid i := by
  simp [receipt₂, p₁, ownerMixedMarginal, hi]
  ring
lemma receipt₂_mixed (i : ι) (hi : i ∈ G.mixed) : G.receipt₂ i = G.multiplier := by
  have hn := (G.mixed_iff i).mp hi
  simp only [receipt₂, p₁, ownerMixedMarginal, if_neg hn.1, if_pos hi]
  exact mixed_receipt _ _ _ G.xi_pos.ne' (G.bid_pos i).ne'

end GuardedData

omit [Fintype ι] in

lemma threshold_optimal (w : ι → ℝ) (S T : Finset ι) (lam : ℝ)
    (hlam : 0 ≤ lam) (hcard : T.card ≤ S.card)
    (hS : ∀ i ∈ S, lam ≤ w i) (hnot : ∀ i ∉ S, w i ≤ lam) :
    ∑ i ∈ T, w i ≤ ∑ i ∈ S, w i := by
  have hdrop : (T \ S).card ≤ (S \ T).card := by
    have ha := Finset.card_sdiff_add_card_inter T S
    have hb := Finset.card_sdiff_add_card_inter S T
    rw [Finset.inter_comm S T] at hb
    omega
  have ha : (∑ i ∈ T \ S, w i) ≤ ((T \ S).card : ℝ)*lam := by
    calc
      _ ≤ ∑ _i ∈ T \ S, lam := Finset.sum_le_sum (fun i hi => hnot i (Finset.mem_sdiff.mp hi).2)
      _ = _ := by simp
  have hb : ((S \ T).card : ℝ)*lam ≤ ∑ i ∈ S \ T, w i := by
    calc
      _ = ∑ _i ∈ S \ T, lam := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i hi => hS i (Finset.mem_sdiff.mp hi).1)
  have hc : ((T \ S).card : ℝ)*lam ≤ ((S \ T).card : ℝ)*lam :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hdrop) hlam
  have hsplitS : (∑ i ∈ S \ T, w i)+(∑ i ∈ S ∩ T, w i) = ∑ i ∈ S, w i :=
    (add_comm _ _).trans (Finset.sum_inter_add_sum_sdiff S T w)
  have hsplitT : (∑ i ∈ T \ S, w i)+(∑ i ∈ S ∩ T, w i) = ∑ i ∈ T, w i := by
    simpa only [Finset.inter_comm,add_comm] using Finset.sum_inter_add_sum_sdiff T S w
  linarith

namespace GuardedData
variable (G : GuardedData ι)

theorem law₁_support_best_response (S : Finset ι) (hS : G.law₁.mass S ≠ 0)
    (T : Finset ι) (hT : T.card ≤ G.owner₁.card+G.residual) :
    ∑ i ∈ T, G.receipt₁ i ≤ ∑ i ∈ S, G.receipt₁ i := by
  obtain ⟨hcard, howns, hdisj⟩ := G.law₁_support S hS
  apply threshold_optimal G.receipt₁ S T G.multiplier G.multiplier_pos.le (by omega)
  · intro i hi
    by_cases h₁ : i ∈ G.owner₁
    · rw [G.receipt₁_owner i h₁]; exact (G.upper_guard i).le
    · have h₂ : i ∉ G.owner₂ := fun h => (Finset.disjoint_left.mp hdisj) hi h
      rw [G.receipt₁_mixed i ((G.mixed_iff i).mpr ⟨h₁,h₂⟩)]
  · intro i hi
    have h₁ : i ∉ G.owner₁ := fun h => hi (howns h)
    by_cases h₂ : i ∈ G.owner₂
    · rw [G.receipt₁_other i h₂]; exact (G.lower_guard i).le
    · rw [G.receipt₁_mixed i ((G.mixed_iff i).mpr ⟨h₁,h₂⟩)]

theorem law₂_support_best_response (S : Finset ι) (hS : G.law₂.mass S ≠ 0)
    (T : Finset ι) (hT : T.card ≤ G.owner₂.card+G.residual) :
    ∑ i ∈ T, G.receipt₂ i ≤ ∑ i ∈ S, G.receipt₂ i := by
  obtain ⟨hcard, howns, hdisj⟩ := G.law₂_support S hS
  apply threshold_optimal G.receipt₂ S T G.multiplier G.multiplier_pos.le (by omega)
  · intro i hi
    by_cases h₂ : i ∈ G.owner₂
    · rw [G.receipt₂_owner i h₂]; exact (G.upper_guard i).le
    · have h₁ : i ∉ G.owner₁ := fun h => (Finset.disjoint_left.mp hdisj) hi h
      rw [G.receipt₂_mixed i ((G.mixed_iff i).mpr ⟨h₁,h₂⟩)]
  · intro i hi
    have h₂ : i ∉ G.owner₂ := fun h => hi (howns h)
    by_cases h₁ : i ∈ G.owner₁
    · rw [G.receipt₂_other i h₁]; exact (G.lower_guard i).le
    · rw [G.receipt₂_mixed i ((G.mixed_iff i).mpr ⟨h₁,h₂⟩)]

end GuardedData
end FCAppendix.Affine.Hybrid
