import FCAppendix.Affine.Tail04.TypicalLottery
import FCAppendix.Affine.Tail04.FocalResponse
import FCAppendix.Finite.ReceiptOrder

noncomputable section
namespace FCAppendix.Affine.Tail04.FocalCapacity
open MeasureTheory Set
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem optimal_of_threshold (c : ℕ) (r : ι → ℝ) (S : Finset ι) (τ : ℝ)
    (hcard : S.card = c) (hτ : 0 ≤ τ)
    (hselected : ∀ i ∈ S, τ ≤ r i)
    (homitted : ∀ i ∉ S, r i ≤ τ) : Finite.Optimal c r S := by
  classical
  refine ⟨hcard.le, ?_⟩
  intro T hT
  let g : ι → ℝ := fun i => max (r i-τ) 0
  have hsum : (∑ i, g i) = ∑ i ∈ S, (r i-τ) := by
    calc
      _ = ∑ i, if i ∈ S then r i-τ else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ S
        · simp only [g, if_pos hi, max_eq_left (sub_nonneg.mpr (hselected i hi))]
        · simp only [g, if_neg hi, max_eq_right (sub_nonpos.mpr (homitted i hi))]
      _ = _ := by simp
  have hconst (V : Finset ι) :
      (∑ i ∈ V, r i) = (V.card:ℝ)*τ + ∑ i ∈ V, (r i-τ) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  have hbound : (∑ i ∈ T, (r i-τ)) ≤ ∑ i, g i := by
    calc
      _ ≤ ∑ i ∈ T, g i := Finset.sum_le_sum (fun i _ => le_max_left _ _)
      _ ≤ ∑ i, g i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => le_max_right _ _)
  rw [hconst T, hconst S, hcard]
  rw [hsum] at hbound
  have hcards : (T.card:ℝ)*τ ≤ (c:ℝ)*τ :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hT) hτ
  linarith

theorem scalar_support (p a : ℝ) (hp : p ∈ Icc (0:ℝ) 1)
    (hopt : FocalResponse.ScalarOptimal p a) :
    (p ≠ 0 → 0 ≤ a) ∧ (p ≠ 1 → a ≤ 0) := by
  constructor
  · intro hn
    have hp0 : 0 < p := lt_of_le_of_ne hp.1 hn.symm
    have hh := hopt 0 (by norm_num)
    by_contra ha
    have hh' := mul_neg_of_pos_of_neg hp0 (lt_of_not_ge ha)
    norm_num only [zero_mul] at hh
    linarith
  · intro hn
    have hp1 : p < 1 := lt_of_le_of_ne hp.2 hn
    have hh := hopt 1 (by norm_num)
    by_contra ha
    have hh' := mul_pos (sub_pos.mpr hp1) (lt_of_not_ge ha)
    norm_num only [one_mul] at hh
    nlinarith

theorem support_optimal (p : ι → ℝ) (c : ℕ) (K : FiniteLaw (Finset ι))
    (hK : ExactCapacity.Implements p c K) (r : ι → ℝ) (τ : ℝ) (hτ : 0 ≤ τ)
    (hlo : ∀ i, p i ≠ 0 → τ ≤ r i)
    (hhi : ∀ i, p i ≠ 1 → r i ≤ τ)
    (S : Finset ι) (hS : K.mass S ≠ 0) : Finite.Optimal c r S := by
  apply optimal_of_threshold c r S τ (hK.1 S hS) hτ
  · intro i hi
    have hp := FiniteLaw.marginal_pos_of_support_mem K S hS i hi
    rw [hK.2 i] at hp
    exact hlo i hp.ne'
  · intro i hi
    have hp := prob_pos_of_support_event K (fun V => i ∉ V) S hS hi
    rw [FiniteLaw.prob_compl, hK.2 i] at hp
    apply hhi i
    intro he
    rw [he] at hp
    linarith

def multiplier (ξ : ℝ) (c : ℕ) (fixed I : Finset ι) (b : ι → ℝ) (p : ℝ) : ℝ :=
  ((I.card:ℝ)-ξ*((c:ℝ)-fixed.card-p))/mixedReciprocalSum I b

def marginal (ξ : ℝ) (c : ℕ) (fixed I : Finset ι) (b : ι → ℝ)
    (focal : ι) (p : ℝ) (i : ι) : ℝ :=
  if i ∈ fixed then 1 else if i = focal then p
  else if i ∈ I then (1-multiplier ξ c fixed I b p/b i)/ξ else 0

def lottery (ξ : ℝ) (c : ℕ) (fixed I : Finset ι) (b : ι → ℝ)
    (focal : ι) (p : ℝ) : FiniteLaw (Finset ι) :=
  ExactCapacity.symmetricLottery (marginal ξ c fixed I b focal p)

omit [Fintype ι] [DecidableEq ι] in
theorem multiplier_shift (ξ : ℝ) (c : ℕ) (fixed I : Finset ι)
    (b : ι → ℝ) (p : ℝ) :
    multiplier ξ c fixed I b p = multiplier ξ c fixed I b 0 +
      ξ*p/mixedReciprocalSum I b := by
  unfold multiplier
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem nonfocal_sum (ξ : ℝ) (hξ : 0 < ξ) (c : ℕ)
    (fixed I : Finset ι) (b : ι → ℝ) (p : ℝ)
    (hW : 0 < mixedReciprocalSum I b) :
    (∑ i ∈ I, (1-multiplier ξ c fixed I b p/b i)/ξ) =
      (c:ℝ)-fixed.card-p := by
  have hsum : (∑ i ∈ I, multiplier ξ c fixed I b p/b i) =
      multiplier ξ c fixed I b p*mixedReciprocalSum I b := by
    simp only [mixedReciprocalSum, div_eq_mul_inv, one_mul, Finset.mul_sum]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, hsum]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  unfold multiplier
  field_simp [hξ.ne', hW.ne']
  ; ring

theorem marginal_sum (ξ : ℝ) (hξ : 0 < ξ) (c : ℕ)
    (fixed I : Finset ι) (b : ι → ℝ) (focal : ι) (p : ℝ)
    (hdis : Disjoint fixed I) (hf : focal ∉ fixed) (hi : focal ∉ I)
    (hW : 0 < mixedReciprocalSum I b) :
    (∑ i, marginal ξ c fixed I b focal p i) = c := by
  have he (i : ι) : marginal ξ c fixed I b focal p i =
      (if i ∈ fixed then 1 else 0) + (if i = focal then p else 0) +
        (if i ∈ I then (1-multiplier ξ c fixed I b p/b i)/ξ else 0) := by
    by_cases hif : i ∈ fixed
    · have hii : i ∉ I := fun h => (Finset.disjoint_left.mp hdis) hif h
      have hne : i ≠ focal := fun h => hf (h ▸ hif)
      simp [marginal, hif, hii, hne]
    · by_cases heq : i = focal
      · subst i
        simp [marginal, hf, hi]
      · simp [marginal, hif, heq]
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
    nsmul_eq_mul, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [nonfocal_sum ξ hξ c fixed I b p hW]
  ring

theorem lottery_implements (ξ : ℝ) (hξ : 0 < ξ) (c : ℕ)
    (fixed I : Finset ι) (b : ι → ℝ) (focal : ι) (p : ℝ)
    (hp : p ∈ Icc (0:ℝ) 1)
    (hdis : Disjoint fixed I) (hf : focal ∉ fixed) (hi : focal ∉ I)
    (hW : 0 < mixedReciprocalSum I b)
    (hb : ∀ i ∈ I, 0 < b i)
    (hΛ : ∀ i ∈ I, (1-ξ)*b i ≤ multiplier ξ c fixed I b p ∧
      multiplier ξ c fixed I b p ≤ b i) :
    ExactCapacity.Implements (marginal ξ c fixed I b focal p) c
      (lottery ξ c fixed I b focal p) := by
  have hbounds (i : ι) : marginal ξ c fixed I b focal p i ∈ Icc (0:ℝ) 1 := by
    unfold marginal
    split_ifs with hfix heq hmix
    · norm_num
    · exact hp
    · have hlo := (le_div_iff₀ (hb i hmix)).2 (hΛ i hmix).1
      have hhi := (div_le_one (hb i hmix)).2 (hΛ i hmix).2
      constructor
      · exact div_nonneg (by linarith) hξ.le
      · apply (div_le_one hξ).2
        linarith
    · norm_num
  apply ExactCapacity.symmetricLottery_implements
  · exact fun i => (hbounds i).1
  · exact fun i => (hbounds i).2
  · exact marginal_sum ξ hξ c fixed I b focal p hdis hf hi hW

theorem insertion_receipt_optimal (ξ : ℝ) (hξ : 0 < ξ) (c : ℕ)
    (fixed I : Finset ι) (b : ι → ℝ) (focal : ι) (p : ℝ)
    (hp : p ∈ Icc (0:ℝ) 1)
    (hdis : Disjoint fixed I) (hf : focal ∉ fixed) (hi : focal ∉ I)
    (hW : 0 < mixedReciprocalSum I b)
    (hb : ∀ i ∈ I, 0 < b i)
    (hΛ : ∀ i ∈ I, (1-ξ)*b i ≤ multiplier ξ c fixed I b p ∧
      multiplier ξ c fixed I b p ≤ b i)
    (r : ι → ℝ) (τ : ℝ) (hτ : 0 ≤ τ)
    (hrfixed : ∀ i ∈ fixed, τ ≤ r i)
    (hrmixed : ∀ i ∈ I, r i = τ)
    (hrexcluded : ∀ i, i ∉ fixed → i ≠ focal → i ∉ I → r i ≤ τ)
    (hrfocal : FocalResponse.ScalarOptimal p (r focal-τ))
    (S : Finset ι) (hS : (lottery ξ c fixed I b focal p).mass S ≠ 0) :
    Finite.Optimal c r S := by
  have hK := lottery_implements ξ hξ c fixed I b focal p hp hdis hf hi hW hb hΛ
  have hscalar := scalar_support p (r focal-τ) hp hrfocal
  apply support_optimal _ c _ hK r τ hτ ?_ ?_ S hS
  · intro i hpi
    by_cases hfix : i ∈ fixed
    · exact hrfixed i hfix
    by_cases heq : i = focal
    · subst i
      have hp0 : p ≠ 0 := by simpa only [marginal, if_neg hf, if_pos rfl, ite_true] using hpi
      exact sub_nonneg.mp (hscalar.1 hp0)
    by_cases hmix : i ∈ I
    · exact (hrmixed i hmix).ge
    · simp only [marginal, if_neg hfix, if_neg heq, if_neg hmix] at hpi
      exact (hpi rfl).elim
  · intro i hpi
    by_cases hfix : i ∈ fixed
    · simp only [marginal, if_pos hfix] at hpi
      exact (hpi rfl).elim
    by_cases heq : i = focal
    · subst i
      have hp1 : p ≠ 1 := by simpa only [marginal, if_neg hf, if_pos rfl, ite_true] using hpi
      exact sub_nonpos.mp (hscalar.2 hp1)
    by_cases hmix : i ∈ I
    · exact (hrmixed i hmix).le
    · exact hrexcluded i hfix heq hmix

theorem crossed_focal_advantage (ξ b W L p : ℝ) :
    b*(1-ξ*p)-(L+ξ*p/W) = b-L-ξ*(b+1/W)*p := by ring

theorem measurable_lottery_mass (ξ : ℝ) (c : ℕ) (fixed I : Finset ι)
    (focal : ι) (S : Finset ι) :
    Measurable (fun x : (ι → ℝ) × ℝ => (lottery ξ c fixed I x.1 focal x.2).mass S) := by
  apply (ExactCapacity.measurable_symmetricLottery_mass S).comp
  apply measurable_pi_lambda
  intro i
  unfold marginal multiplier mixedReciprocalSum
  split_ifs <;> fun_prop

set_option maxHeartbeats 800000 in
theorem exists_insertion_sampler (ξ : ℝ) (c : ℕ) (fixed I : Finset ι) (focal : ι) :
    ∃ f : ((ι → ℝ) × ℝ) → unitInterval → Finset ι,
      Measurable (Function.uncurry f) ∧
      (∀ x z, 0 < (lottery ξ c fixed I x.1 focal x.2).mass (f x z)) ∧
      ∀ x, volume.map (f x) =
        FiniteLaw.probabilityMeasure (lottery ξ c fixed I x.1 focal x.2) := by
  obtain ⟨f,hf,hpos,hlaw⟩ := Hybrid.exists_support_sampler
    (fun x : (ι → ℝ) × ℝ => lottery ξ c fixed I x.1 focal x.2)
    (measurable_lottery_mass ξ c fixed I focal)
  exact ⟨f,hf,hpos,hlaw⟩

end FCAppendix.Affine.Tail04.FocalCapacity
