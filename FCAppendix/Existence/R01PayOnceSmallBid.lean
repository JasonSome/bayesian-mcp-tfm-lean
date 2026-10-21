import FCAppendix.Existence.R01PayOnceFloor
import Mathlib.MeasureTheory.Measure.Portmanteau

noncomputable section
namespace FCAppendix.Existence.PayOnceBounded
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped BigOperators
open FCAppendix.Existence.Distributional
attribute [local instance] Classical.propDecidable

theorem raise_payoff_bound (w b B s s' a : ℝ)
    (hwa : a ≤ w) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hs0 : 0 ≤ s) (hss' : s ≤ s') (hs'1 : s' ≤ 1) :
    a * (s' - s) - B ≤ (w - B) * s' - (w - b) * s := by
  have h₁ := mul_nonneg (sub_nonneg.mpr hwa) (sub_nonneg.mpr hss')
  have h₂ := mul_nonneg hb hs0
  have h₃ := mul_nonneg hB (sub_nonneg.mpr hs'1)
  nlinarith

def smallClass {ε W : ℝ} (a t : ℝ) (z : Value W × FloorAction ε W) : Prop :=
  a ≤ z.1.1 ∧ present z.2 = true ∧ bid z.2 ≤ t

theorem measurableSet_smallClass {ε W : ℝ} (a t : ℝ) :
    MeasurableSet {z : Value W × FloorAction ε W | smallClass a t z} := by
  exact (measurableSet_le measurable_const
    (measurable_subtype_coe.comp measurable_fst)).inter
    ((measurableSet_eq_fun (continuous_present.measurable.comp measurable_snd) measurable_const).inter
      (measurableSet_le (continuous_bid.measurable.comp measurable_snd) measurable_const))

def classGain {ε W : ℝ} (m n c : ℕ) (a t : ℝ) (B : Icc ε W)
    (x : Fin m → Value W × FloorAction ε W) (i : Fin m) : ℝ :=
  if smallClass a t (x i) then
    ((x i).1.1 - B.1) * success n c
      (Function.update (fun j => (x j).2) i (.inr B)) i -
      ((x i).1.1 - bid (x i).2) * success n c (fun j => (x j).2) i
  else 0

theorem classGain_lower {ε W : ℝ} (m n c : ℕ) (hn : 2 ≤ n) (hε : 0 < ε)
    (a t : ℝ) (B : Icc ε W) (htB : t ≤ B.1)
    (x : Fin m → Value W × FloorAction ε W) (i : Fin m) :
    -(B.1 * (if smallClass a t (x i) then 1 else 0)) ≤ classGain m n c a t B x i := by
  classical
  by_cases hC : smallClass a t (x i)
  · have hact := hC.2.1
    rcases ha : (x i).2 with _ | b
    · simp [ha, present] at hact
    · have hbb : b.1 ≤ B.1 := (by simpa [ha, bid] using hC.2.2 : b.1 ≤ t).trans htB
      have hmono := marginal_mono_own n c hn hε (fun j => (x j).2) i b B hbb
      have hupdate : Function.update (fun j => (x j).2) i (.inr b) = (fun j => (x j).2) := by
        simp [ha]
      rw [hupdate] at hmono
      have hs := success_bounds n c hn hε (fun j => (x j).2) i
      have hs' := success_bounds n c hn hε
        (Function.update (fun j => (x j).2) i (.inr B)) i
      have hm := success_mono_scalar n
        ((marginal_spec n c hn hε (fun j => (x j).2)).1 i) hmono
        ((marginal_spec n c hn hε
          (Function.update (fun j => (x j).2) i (.inr B))).2.1 i)
      have h := raise_payoff_bound (x i).1.1 b.1 B.1
        (success n c (fun j => (x j).2) i)
        (success n c (Function.update (fun j => (x j).2) i (.inr B)) i)
        0 (x i).1.2.1 (hε.le.trans b.2.1) (hε.le.trans B.2.1) hs.1 hm hs'.2
      simpa [classGain, hC, ha, bid] using h
  · simp [classGain, hC]

theorem raised_success_one {ε W : ℝ} (m n c : ℕ) (hn : 2 ≤ n) (hc : 1 ≤ c)
    (hε : 0 < ε) (a t : ℝ) (ht : 0 < t) (B : Icc ε W) (hB : B.1 = 2 * n * t)
    (x : Fin m → Value W × FloorAction ε W) (hC : ∀ i, smallClass a t (x i)) (i : Fin m) :
    success n c (Function.update (fun j => (x j).2) i (.inr B)) i = 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm := marginal_saturates n c hn hc hε
    (Function.update (fun j => (x j).2) i (.inr B)) i (by simp [present])
    (fun j hj _ => by
      rw [Function.update_of_ne hj, Function.update_self]
      have hb := (hC j).2.2
      change bid (x j).2 < B.1 / n
      rw [hB]
      have he : (2 * (n : ℝ) * t) / n = 2 * t := by field_simp
      rw [he]
      linarith)
  simp [success, hm, PayOnce.success, Nat.ne_of_gt (show 0 < n by omega)]

theorem sum_classGain_lower {ε W : ℝ} (m n c : ℕ)
    (hm : 0 < m) (hn : 2 ≤ n) (hc1 : 1 ≤ c) (hcm : c < m) (hε : 0 < ε)
    (a t : ℝ) (ha : 0 ≤ a) (ht : 0 < t) (B : Icc ε W) (hB : B.1 = 2 * n * t)
    (x : Fin m → Value W × FloorAction ε W) :
    (a * m * (1 - PayOnce.success n ((c : ℝ) / m))) *
        (if ∀ i, smallClass a t (x i) then 1 else 0) -
      B.1 * (∑ i : Fin m, if smallClass a t (x i) then 1 else 0) ≤
        ∑ i : Fin m, classGain m n c a t B x i := by
  classical
  have htB : t ≤ B.1 := by
    rw [hB]
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  by_cases hC : ∀ i, smallClass a t (x i)
  · have hp := marginal_spec n c hn hε (fun j => (x j).2)
    have hact : activeSet (fun j => (x j).2) = Finset.univ := by
      ext i
      simp [activeSet, (hC i).2.1]
    have hsum : ∑ i : Fin m, marginal n c (fun j => (x j).2) i = (c : ℝ) := by
      simpa [hact, Nat.min_eq_left hcm.le] using hp.2.2
    have hJ := success_sum_le n m c hm _ hp.1 hp.2.1 hsum
    have hpoint : ∀ i : Fin m,
        a * (1 - success n c (fun j => (x j).2) i) - B.1 ≤ classGain m n c a t B x i := by
      intro i
      have hs := success_bounds n c hn hε (fun j => (x j).2) i
      have hb := bid_pos_of_present hε (x i).2 (hC i).2.1
      have h := raise_payoff_bound (x i).1.1 (bid (x i).2) B.1
        (success n c (fun j => (x j).2) i) 1 a
        (hC i).1 hb.le (hε.le.trans B.2.1) hs.1 hs.2 le_rfl
      simpa [classGain, hC i, raised_success_one m n c hn hc1 hε a t ht B hB x hC i] using h
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
    simp only [Finset.sum_sub_distrib, mul_sub, mul_one, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
    rw [← Finset.mul_sum] at hh
    have hJ' := mul_le_mul_of_nonneg_left hJ ha
    simp only [if_pos hC, mul_one]
    have hcnt : (∑ i : Fin m, if smallClass a t (x i) then (1 : ℝ) else 0) = m := by
      simp [hC]
    rw [hcnt]
    dsimp [success] at hh
    nlinarith
  · have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      classGain_lower m n c hn hε a t B htB x i)
    simpa only [if_neg hC,mul_zero,zero_sub,Finset.sum_neg_distrib,← Finset.mul_sum] using hh

theorem source_small_bid_estimate {ε W : ℝ} (m n c : ℕ)
    (hm : 0 < m) (hn : 2 ≤ n) (hc1 : 1 ≤ c) (hcm : c < m) (hε : 0 < ε)
    (a t : ℝ) (ha : 0 ≤ a) (ht : 0 < t) (B : Icc ε W) (hB : B.1 = 2 * n * t)
    (π : ProbabilityMeasure (Value W × FloorAction ε W))
    (hint : Integrable (fun x => ∑ i : Fin m, classGain m n c a t B x i)
      (rowLaw m π : Measure (Fin m → Value W × FloorAction ε W)))
    (hIC : (∫ x, ∑ i : Fin m, classGain m n c a t B x i
      ∂(rowLaw m π : Measure (Fin m → Value W × FloorAction ε W))) ≤ 0) :
    let q := (π : Measure (Value W × FloorAction ε W)).real {z | smallClass a t z}
    a * q ^ m * (1 - PayOnce.success n ((c : ℝ) / m)) ≤ 2 * n * t * q := by
  classical
  let C : Set (Value W × FloorAction ε W) := {z | smallClass a t z}
  let ν : Measure (Fin m → Value W × FloorAction ε W) := rowLaw m π
  let q := (π : Measure (Value W × FloorAction ε W)).real C
  have hC : MeasurableSet C := measurableSet_smallClass a t
  have hAll : MeasurableSet {x : Fin m → Value W × FloorAction ε W | ∀ i, x i ∈ C} :=
    by
      convert MeasurableSet.iInter (fun i => hC.preimage (measurable_pi_apply i)) using 1
      · ext x
        simp only [mem_iInter,mem_preimage,mem_setOf_eq]
      · infer_instance
  have hiAll : Integrable (fun x : Fin m → Value W × FloorAction ε W =>
      if ∀ i, x i ∈ C then (1 : ℝ) else 0) ν :=
    by
      convert (integrable_const (1 : ℝ)).indicator (μ := ν) hAll using 1 <;>
        first | rfl | (funext x; simp only [Set.indicator,mem_setOf_eq])
  have hiCount : Integrable (fun x : Fin m → Value W × FloorAction ε W =>
      ∑ i : Fin m, if x i ∈ C then (1 : ℝ) else 0) ν := by
    apply integrable_finsetSum
    intro i _
    convert (integrable_const (1 : ℝ)).indicator (μ := ν) (hC.preimage (measurable_pi_apply i)) using 1
    rfl
  have hle := integral_mono
    ((hiAll.const_mul (a * m * (1 - PayOnce.success n ((c : ℝ) / m)))).sub
      (hiCount.const_mul B.1)) hint
    (sum_classGain_lower m n c hm hn hc1 hcm hε a t ha ht B hB)
  have heAll : (∫ x : Fin m → Value W × FloorAction ε W,
      if ∀ i, x i ∈ C then (1 : ℝ) else 0 ∂ν) = q ^ m := by
    calc
      _ = ν.real {x | ∀ i, x i ∈ C} := by
        convert integral_indicator_one (μ := ν) hAll using 1
        congr 1
        funext x
        simp only [Set.indicator,mem_setOf_eq,Pi.one_apply]
      _ = q^m := by
        change ((rowLaw m π : Measure (Fin m → Value W × FloorAction ε W)) {x | ∀ i, x i ∈ C}).toReal = q^m
        rw [rowLaw_all m π C hC,ENNReal.toReal_pow]
        rfl
  simp only [Pi.sub_apply] at hle
  rw [integral_sub (hiAll.const_mul _) (hiCount.const_mul _), integral_const_mul,
    integral_const_mul, heAll] at hle
  have heCount : (∫ x, ∑ i : Fin m, if x i ∈ C then (1:ℝ) else 0 ∂ν)=(m:ℝ)*q := by
    convert integral_row_class_count m π C hC using 1
    rfl
  rw [heCount,hB] at hle
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  dsimp only at hIC ⊢
  change a * q ^ m * (1 - PayOnce.success n ((c : ℝ) / m)) ≤ 2 * n * t * q
  apply le_of_mul_le_mul_left (a := (m : ℝ)) _ hmR
  nlinarith

theorem small_bid_bound_divide (m : ℕ) (hm : 1 ≤ m) (a gap n t q : ℝ)
    (ha : 0 < a) (hgap : 0 < gap) (hq : 0 < q)
    (h : a * q ^ m * gap ≤ 2 * n * t * q) :
    q ^ (m - 1) ≤ (2 * n * t) / (a * gap) := by
  have hp : q ^ m = q ^ (m - 1) * q := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hp] at h
  have hh : (a * gap * q ^ (m - 1)) * q ≤ (2 * n * t) * q := by nlinarith [h]
  have hd := le_of_mul_le_mul_right hh hq
  apply (le_div_iff₀ (mul_pos ha hgap)).mpr
  nlinarith
end FCAppendix.Existence.PayOnceBounded
