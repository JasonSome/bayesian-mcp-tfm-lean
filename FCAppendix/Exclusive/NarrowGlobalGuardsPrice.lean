import FCAppendix.Exclusive.CanonicalPolicy
import FCAppendix.Exclusive.LowTypeDeterrence

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Global
open MeasureTheory Set
open scoped BigOperators

variable {ι : Type*} [Fintype ι]
attribute [local instance] Classical.propDecidable

lemma activeDemand_bounds (n : ℕ) (b t : ℝ) (ht : 0 ≤ t) :
    0 ≤ activeDemand n b t ∧ activeDemand n b t ≤ 1 := by
  unfold activeDemand
  split_ifs with hb
  · exact ⟨demand_nonneg _ _ _, demand_le_one n hb ht⟩
  · exact ⟨le_refl 0,zero_le_one⟩

lemma canonicalPrice_le_of_totalDemand_le (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (hc : 0 < c)
    (b : ι → ℝ) (t : ℝ) (ht : 0 ≤ t) (hD : totalDemand n b t ≤ c) :
    canonicalPrice n hn c b ≤ t := by
  by_cases hover : c < positiveCount b
  · obtain ⟨hp,hr⟩ := canonicalPrice_overloaded n hn c b hover
    apply le_of_not_gt
    intro hlt
    have hmon : totalDemand n b (canonicalPrice n hn c b) ≤ totalDemand n b t := by
      simp only [totalDemand_eq_positive]
      exact Finset.sum_le_sum fun i _ => demand_antitone n hn i.property ht hlt.le
    have hpos : 0 < ∑ i : PositiveIndex b, demand n (b i.val) t := by
      rw [← totalDemand_eq_positive]
      rw [hr] at hmon
      exact (Nat.cast_pos.mpr hc).trans_le hmon
    have hstrict := sum_demand_strict n hn (fun i : PositiveIndex b => b i.val)
      (fun i => i.property) ht hlt hpos
    rw [← totalDemand_eq_positive,← totalDemand_eq_positive,hr] at hstrict
    exact (not_lt_of_ge hD) hstrict
  · simpa only [canonicalPrice,dif_neg hover] using ht

lemma le_canonicalPrice_of_le_totalDemand (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (hc : 0 < c)
    (b : ι → ℝ) (t : ℝ) (hD : (c:ℝ) ≤ totalDemand n b t) :
    t ≤ canonicalPrice n hn c b := by
  apply le_of_not_gt
  intro hlt
  exact (not_lt_of_ge hD) ((canonicalPrice_lt_iff n hn c hc b t).mp hlt).2

def focalBidVector (b : ℝ) (B : ι → ℝ) : Option ι → ℝ
  | none => b
  | some i => B i

lemma totalDemand_focalBidVector (n : ℕ) (b : ℝ) (B : ι → ℝ) (hB : ∀ i, 0 < B i) (t : ℝ) :
    totalDemand n (focalBidVector b B) t = activeDemand n b t + ∑ i, demand n (B i) t := by
  classical
  simp [totalDemand,Fintype.sum_option,focalBidVector,activeDemand,hB]

lemma positiveCount_focalBidVector (b : ℝ) (B : ι → ℝ) (hB : ∀ i, 0 < B i) :
    Fintype.card ι ≤ positiveCount (focalBidVector b B) := by
  apply Fintype.card_le_of_injective (fun i : ι =>
    (⟨some i,hB i⟩ : PositiveIndex (focalBidVector b B)))
  intro i j h
  exact Option.some_injective _ (congrArg Subtype.val h)

theorem canonical_focal_price_bracket (n c : ℕ) (hn : 2 ≤ n) (hc : 0 < c)
    (hN : c < Fintype.card ι) (B : ι → ℝ) (a upper : ℝ)
    (ha : 0 < a) (hB : ∀ i, B i ∈ Icc a upper) (b : ℝ) :
    let N : ℝ := Fintype.card ι
    canonicalPrice n hn c (focalBidVector b B) ∈
      Icc (a*((N-c)/N)^(n-1)) (upper*((N-c+1)/N)^(n-1)) := by
  have hN0 : (0:ℝ) < Fintype.card ι := Nat.cast_pos.mpr (by omega)
  have hcR : (1:ℝ) ≤ c := Nat.one_le_cast.mpr hc
  have hNc : (c:ℝ) < Fintype.card ι := Nat.cast_lt.mpr hN
  have hBpos : ∀ i, 0 < B i := fun i => ha.trans_le (hB i).1
  letI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hu : 0 < upper := ha.trans_le ((hB (Classical.arbitrary ι)).1.trans (hB _).2)
  let qlo : ℝ := ((Fintype.card ι:ℝ)-c)/(Fintype.card ι:ℝ)
  let qhi : ℝ := ((Fintype.card ι:ℝ)-c+1)/(Fintype.card ι:ℝ)
  have hql0 : 0 < qlo := div_pos (sub_pos.mpr hNc) hN0
  have hql1 : qlo ≤ 1 := (div_le_one hN0).mpr (by linarith)
  have hqh0 : 0 < qhi := div_pos (by linarith) hN0
  have hqh1 : qhi ≤ 1 := (div_le_one hN0).mpr (by linarith)
  let lo := a*qlo^(n-1)
  let hi := upper*qhi^(n-1)
  have hlo : 0 < lo := mul_pos ha (pow_pos hql0 _)
  have hhi : 0 < hi := mul_pos hu (pow_pos hqh0 _)
  have hdlo : (Fintype.card ι:ℝ)*demand n a lo = c := by
    rw [LowType.demand_at_reference_failure n hn ha hql0 hql1]
    dsimp [qlo]
    field_simp
    ring
  have hdhi : (Fintype.card ι:ℝ)*demand n upper hi = (c:ℝ)-1 := by
    rw [LowType.demand_at_reference_failure n hn hu hqh0 hqh1]
    dsimp [qhi]
    field_simp
    ring
  have hslo : (Fintype.card ι:ℝ)*demand n a lo ≤ ∑ i, demand n (B i) lo := by
    have hh := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => demand_mono_bid n hn ha (hB i).1 hlo.le)
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hh
  have hshi : (∑ i, demand n (B i) hi) ≤ (Fintype.card ι:ℝ)*demand n upper hi := by
    have hh := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => demand_mono_bid n hn (hBpos i) (hB i).2 hhi.le)
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hh
  change lo ≤ canonicalPrice n hn c (focalBidVector b B) ∧
    canonicalPrice n hn c (focalBidVector b B) ≤ hi
  constructor
  · apply le_canonicalPrice_of_le_totalDemand n hn c hc
    rw [totalDemand_focalBidVector n b B hBpos lo]
    linarith [(activeDemand_bounds n b lo hlo.le).1]
  · apply canonicalPrice_le_of_totalDemand_le n hn c hc _ hi hhi.le
    rw [totalDemand_focalBidVector n b B hBpos hi]
    linarith [(activeDemand_bounds n b hi hhi.le).2]

theorem canonicalPrice_eq_of_totalDemand_eq
    {κ : Type*} [Fintype κ] (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (hc : 0 < c)
    (b : ι → ℝ) (B : κ → ℝ)
    (hD : ∀ t, totalDemand n b t = totalDemand n B t) :
    canonicalPrice n hn c b = canonicalPrice n hn c B := by
  have he (t : ℝ) : canonicalPrice n hn c b < t ↔ canonicalPrice n hn c B < t := by
    rw [canonicalPrice_lt_iff n hn c hc,canonicalPrice_lt_iff n hn c hc,hD]
  apply le_antisymm
  · apply le_of_not_gt
    intro hlt
    exact (lt_irrefl _) ((he _).mpr hlt)
  · apply le_of_not_gt
    intro hlt
    exact (lt_irrefl _) ((he _).mp hlt)

abbrev PositiveRival {m : ℕ} (B : Fin m → ℝ) (i : Fin m) :=
  {j : Fin m // j ≠ i ∧ 0 < B j}

lemma totalDemand_eq_focal_positiveRivals {m : ℕ} (n : ℕ) (B : Fin m → ℝ)
    (i : Fin m) (t : ℝ) :
    totalDemand n B t = activeDemand n (B i) t +
      ∑ j : PositiveRival B i, demand n (B j.val) t := by
  classical
  have hs : (∑ j : PositiveRival B i, demand n (B j.val) t) =
      ∑ j ∈ Finset.univ.erase i, activeDemand n (B j) t := by
    have hh := Finset.sum_subtype_eq_sum_filter (s := Finset.univ)
      (p := fun j => j ≠ i ∧ 0 < B j) (fun j => demand n (B j) t)
    have hf : Finset.univ.filter (fun j => j ≠ i ∧ 0 < B j) =
        (Finset.univ.erase i).filter (fun j => 0 < B j) := by
      ext j
      simp [and_comm]
    simp only [activeDemand]
    rw [← Finset.sum_filter]
    simpa [hf] using hh
  rw [hs]
  exact (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm.trans (by ring)

theorem canonical_native_price_bracket {m : ℕ} (n c : ℕ) (hn : 2 ≤ n)
    (hc : 0 < c) (B : Fin m → ℝ) (i : Fin m) (a upper : ℝ)
    (ha : 0 < a)
    (hB : ∀ j, j ≠ i → B j = 0 ∨ B j ∈ Icc a upper)
    (hN : c < Fintype.card (PositiveRival B i)) :
    let N : ℝ := Fintype.card (PositiveRival B i)
    canonicalPrice n hn c B ∈
      Icc (a*((N-c)/N)^(n-1)) (upper*((N-c+1)/N)^(n-1)) := by
  let R : PositiveRival B i → ℝ := fun j => B j.val
  have hR : ∀ j, R j ∈ Icc a upper := by
    intro j
    rcases hB j.val j.property.1 with hz | hp
    · exact False.elim (by simpa [hz] using j.property.2)
    · exact hp
  have hD : ∀ t, totalDemand n B t =
      totalDemand n (focalBidVector (B i) R) t := by
    intro t
    rw [totalDemand_eq_focal_positiveRivals,
      totalDemand_focalBidVector n (B i) R (fun j => j.property.2)]
  rw [canonicalPrice_eq_of_totalDemand_eq n hn c hc B _ hD]
  exact canonical_focal_price_bracket n c hn hc hN R a upper ha hR (B i)

end FCAppendix.Exclusive.Narrow.Global
