import FCAppendix.Affine.LowBody.ResidualOutcomes
import FCAppendix.Affine.LowBody.CategoricalRateGuards

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory Set Classical
open scoped BigOperators

def hitCount {Ω : Type*} (E : Ω→Prop) {N : ℕ} (ω : Fin N→Ω) : ℕ :=
  ∑i,if E (ω i) then 1 else 0

theorem hitCount_cons {Ω : Type*} (E : Ω→Prop) {N : ℕ} (t : Ω) (ω : Fin N→Ω) :
    hitCount E (Fin.cons t ω)=(if E t then 1 else 0)+hitCount E ω := by
  unfold hitCount
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ]

theorem expect_hitCount_binomial {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (E : Ω→Prop) (N : ℕ) (φ : ℕ→ℝ) :
    (CommonList.iid μ N).expect (fun ω=>φ (hitCount E ω))=
      (IndependentCounts.binomial N (μ.prob E) (μ.prob_nonneg E) (μ.prob_le_one E)).expect
        (fun r=>φ r.val) := by
  induction N generalizing φ with
  | zero =>
    rw [CommonList.expect_iid_zero]
    simp [IndependentCounts.binomial,IndependentCounts.independentCount,hitCount]
  | succ N ih =>
    rw [CommonList.expect_iid_succ,IndependentCounts.expect_binomial_succ]
    simp only [hitCount_cons,IndependentCounts.val_add_false,IndependentCounts.val_add_true]
    set β:=IndependentCounts.binomial N (μ.prob E) (μ.prob_nonneg E) (μ.prob_le_one E)
    have hh : ∀t : Ω,
        (CommonList.iid μ N).expect (fun ω=>φ ((if E t then 1 else 0)+hitCount E ω))=
          (if E t then 1 else 0)*β.expect (fun r=>φ (1+r.val))+
            (1-(if E t then 1 else 0))*β.expect (fun r=>φ r.val) := by
      intro t
      rw [ih (fun r=>φ ((if E t then 1 else 0)+r))]
      by_cases ht : E t <;> simp [ht]
    rw [μ.expect_congr hh,μ.expect_add,μ.expect_mul_const,μ.expect_mul_const,
      μ.expect_sub,μ.expect_const]
    rw [←μ.prob_eq_expect E]
    ring

theorem localUnderflow_zero_iff {N : ℕ} (c : ℕ) (kind : Fin N→Fin 4) :
    LocalUnderflow c 0 kind↔hitCount (fun k : Fin 4=>k≠3) kind<c := by
  have he : classCount 0 (patternRow kind)+classCount 1 (patternRow kind)+
      classCount 2 (patternRow kind)=hitCount (fun k : Fin 4=>k≠3) kind := by
    unfold classCount hitCount patternRow
    rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only
    generalize hk : kind i=k
    fin_cases k <;> norm_num [Fin.ext_iff]
  change classCount 0 (patternRow kind)+classCount 1 (patternRow kind)+
    classCount 2 (patternRow kind)<c↔_<c
  rw [←he]

theorem categoryLaw_arrival_mass (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h)
    (hsum : s+a+h=1) (G : Measure ℝ) [IsProbabilityMeasure G] :
    (categoryLaw s a h hs ha hh hsum G).prob (fun k : Fin 4=>k≠3)=1-h/2 := by
  rw [FiniteLaw.prob_eq_expect,categoryLaw_expect]
  norm_num [Fin.ext_iff]
  linarith

theorem localUnderflow_probability (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h)
    (hsum : s+a+h=1) (G : Measure ℝ) [IsProbabilityMeasure G]
    (N c : ℕ) (hc : 0<c) :
    (CommonList.iid (categoryLaw s a h hs ha hh hsum G) N).prob (LocalUnderflow c 0)=
      (IndependentCounts.binomial N (1-h/2)
        (by have hp:=(categoryLaw s a h hs ha hh hsum G).prob_nonneg (fun k : Fin 4=>k≠3)
            rwa [categoryLaw_arrival_mass] at hp)
        (by have hp:=(categoryLaw s a h hs ha hh hsum G).prob_le_one (fun k : Fin 4=>k≠3)
            rwa [categoryLaw_arrival_mass] at hp)).prob (fun r=>r.val≤c-1) := by
  rw [FiniteLaw.prob_eq_expect]
  have he : (fun kind : Fin N→Fin 4=>if LocalUnderflow c 0 kind then (1:ℝ) else 0)=
      (fun kind=>if hitCount (fun k : Fin 4=>k≠3) kind≤c-1 then (1:ℝ) else 0) := by
    funext kind
    rw [localUnderflow_zero_iff]
    have hh : hitCount (fun k : Fin 4=>k≠3) kind<c ↔
        hitCount (fun k : Fin 4=>k≠3) kind≤c-1:=by omega
    rw [hh]
    split_ifs <;> rfl
  rw [he]
  have ht:=expect_hitCount_binomial (categoryLaw s a h hs ha hh hsum G)
    (fun k : Fin 4=>k≠3) N (fun r=>if r≤c-1 then (1:ℝ) else 0)
  simp only [categoryLaw_arrival_mass] at ht
  rw [FiniteLaw.prob_eq_expect]
  exact ht

end FCAppendix.Affine.LowBody
