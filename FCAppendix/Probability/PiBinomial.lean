import FCAppendix.Probability.CountPushforward
import FCAppendix.Probability.IndependentCounts
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi

namespace FCAppendix

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace PiBinomial

noncomputable def pmf (N : ℕ) (p : ℝ) (r : ℕ) : ℝ :=
  (N.choose r : ℝ) * p ^ r * (1 - p) ^ (N - r)

theorem pmf_zero_zero (p : ℝ) : pmf 0 p 0 = 1 := by simp [pmf]

theorem pmf_zero_succ (p : ℝ) (r : ℕ) : pmf 0 p (r + 1) = 0 := by simp [pmf]

theorem pmf_succ_zero (N : ℕ) (p : ℝ) : pmf (N + 1) p 0 = (1 - p) * pmf N p 0 := by
  simp [pmf, pow_succ]
  ring

theorem pmf_succ_succ (N r : ℕ) (p : ℝ) :
    pmf (N + 1) p (r + 1) = (1 - p) * pmf N p (r + 1) + p * pmf N p r := by
  unfold pmf
  rcases lt_or_ge N r with hNr | hrN
  · have h1 : N.choose (r + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h2 : N.choose r = 0 := Nat.choose_eq_zero_of_lt hNr
    have h3 : (N + 1).choose (r + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [h1, h2, h3]
  · rw [Nat.choose_succ_succ', Nat.cast_add]
    rcases Nat.eq_or_lt_of_le hrN with hEq | hlt
    · subst hEq
      simp [Nat.choose_succ_self]
      ring
    · have e1 : N + 1 - (r + 1) = N - r := by omega
      have e2 : N - r = (N - (r + 1)) + 1 := by omega
      rw [e1, e2, pow_succ, pow_succ]
      ring

theorem binomial_mass (N : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (r : Fin (N + 1)) :
    (IndependentCounts.binomial N p hp0 hp1).mass r = pmf N p r.val := by
  classical
  induction N with
  | zero =>
    rcases r with ⟨r, hr⟩
    obtain rfl : r = 0 := by omega
    simp [IndependentCounts.binomial, IndependentCounts.independentCount,
      FiniteLaw.dirac, pmf]
  | succ N ih =>
    have hm := IndependentCounts.expect_binomial_succ N p hp0 hp1
      (fun s => if s = r then (1 : ℝ) else 0)
    rw [FiniteLaw.expect_singleton] at hm
    rw [hm]
    rcases r with ⟨r, hr⟩
    cases r with
    | zero =>
      have hf : ∀ s : Fin (N + 1),
          (if IndependentCounts.addCount N false s = (⟨0, hr⟩ : Fin (N + 2)) then (1 : ℝ)
            else 0) = if s = (0 : Fin (N + 1)) then 1 else 0 := by
        intro s
        by_cases hs : s = 0
        · subst hs
          simp [IndependentCounts.addCount]
        · have hv : s.val ≠ 0 := fun h => hs (Fin.ext h)
          rw [if_neg hs, if_neg]
          intro h
          apply hv
          have := congrArg Fin.val h
          simpa [IndependentCounts.addCount] using this
      have ht : ∀ s : Fin (N + 1),
          (if IndependentCounts.addCount N true s = (⟨0, hr⟩ : Fin (N + 2)) then (1 : ℝ)
            else 0) = 0 := by
        intro s
        rw [if_neg]
        intro h
        have := congrArg Fin.val h
        simp [IndependentCounts.addCount] at this
      simp_rw [hf, ht, FiniteLaw.expect_singleton, FiniteLaw.expect_zero, ih]
      simp only [Fin.val_zero, pmf_succ_zero]
      ring
    | succ r =>
      have hf : ∀ s : Fin (N + 1),
          (if IndependentCounts.addCount N false s = (⟨r + 1, hr⟩ : Fin (N + 2)) then (1 : ℝ)
            else 0) = if s.val = r + 1 then 1 else 0 := by
        intro s
        congr 1
        apply propext
        constructor
        · intro h
          have := congrArg Fin.val h
          simpa [IndependentCounts.addCount] using this
        · intro h
          apply Fin.ext
          simp [IndependentCounts.addCount, h]
      have ht : ∀ s : Fin (N + 1),
          (if IndependentCounts.addCount N true s = (⟨r + 1, hr⟩ : Fin (N + 2)) then (1 : ℝ)
            else 0) = if s.val = r then 1 else 0 := by
        intro s
        congr 1
        apply propext
        constructor
        · intro h
          have := congrArg Fin.val h
          simp [IndependentCounts.addCount] at this
          omega
        · intro h
          apply Fin.ext
          simp [IndependentCounts.addCount, h]
          omega
      simp_rw [hf, ht]
      have hsum : ∀ q : ℕ, (IndependentCounts.binomial N p hp0 hp1).expect
          (fun s => if s.val = q then (1 : ℝ) else 0) = pmf N p q := by
        intro q
        by_cases hq : q < N + 1
        · have he : (fun s : Fin (N + 1) => if s.val = q then (1 : ℝ) else 0) =
              fun s => if s = (⟨q, hq⟩ : Fin (N + 1)) then 1 else 0 := by
            funext s
            congr 1
            apply propext
            exact ⟨fun h => Fin.ext h, fun h => by simp [h]⟩
          rw [he, FiniteLaw.expect_singleton, ih]
        · have he : (fun s : Fin (N + 1) => if s.val = q then (1 : ℝ) else 0) =
              fun _ => 0 := by
            funext s
            rw [if_neg]
            omega
          rw [he, FiniteLaw.expect_zero]
          unfold pmf
          rw [Nat.choose_eq_zero_of_lt (by omega)]
          simp
      rw [hsum, hsum, pmf_succ_succ]

open Classical in

noncomputable def count {ι α : Type*} (E : Set α) (s : Finset ι) (ω : ι → α) : ℕ := by
  classical
  exact (s.filter (fun l => ω l ∈ E)).card

section Counts

open Classical

theorem count_le {ι α : Type*} (E : Set α) (s : Finset ι) (ω : ι → α) :
    count E s ω ≤ s.card := by
  classical
  unfold count
  exact Finset.card_filter_le _ _

theorem count_eq_sum {ι α : Type*} (E : Set α) (s : Finset ι) (ω : ι → α) :
    count E s ω = ∑ l ∈ s, (if ω l ∈ E then 1 else 0) := by
  classical
  unfold count
  rw [Finset.card_filter]

variable {ι α : Type*} [Fintype ι] [MeasurableSpace α]

omit [Fintype ι] in
theorem measurable_indicatorNat (E : Set α) (hE : MeasurableSet E) (l : ι) :
    Measurable (fun ω : ι → α => if ω l ∈ E then (1 : ℕ) else 0) := by
  classical
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (measurable_pi_apply l) hE

omit [Fintype ι] in
theorem measurable_count (E : Set α) (hE : MeasurableSet E) (s : Finset ι) :
    Measurable (count E s) := by
  classical
  have h : count E s = fun ω => ∑ l ∈ s, (if ω l ∈ E then (1 : ℕ) else 0) := by
    funext ω
    exact count_eq_sum E s ω
  rw [h]
  exact Finset.measurable_sum s (fun l _ => measurable_indicatorNat E hE l)

theorem measureReal_count_eq (μ : Measure α) [IsProbabilityMeasure μ]
    (E : Set α) (hE : MeasurableSet E) (s : Finset ι) (r : ℕ) :
    (Measure.pi (fun _ : ι => μ)).real {ω | count E s ω = r} =
      pmf s.card (μ.real E) r := by
  classical
  set P := Measure.pi (fun _ : ι => μ)
  have hind : iIndepFun (fun (l : ι) (ω : ι → α) => if ω l ∈ E then (1 : ℕ) else 0) P := by
    have := iIndepFun_pi (μ := fun _ : ι => μ)
      (X := fun (_ : ι) (x : α) => if x ∈ E then (1 : ℕ) else 0)
      (fun _ => (Measurable.ite hE measurable_const measurable_const).aemeasurable)
    simpa using this
  have hmeas : ∀ l, Measurable (fun ω : ι → α => if ω l ∈ E then (1 : ℕ) else 0) :=
    fun l => measurable_indicatorNat E hE l
  induction s using Finset.induction_on generalizing r with
  | empty =>
    cases r with
    | zero => simp [count, pmf, P]
    | succ r => simp [count, pmf, P]
  | @insert a s ha ih =>
    have hcount : ∀ ω, count E (insert a s) ω =
        count E s ω + (if ω a ∈ E then 1 else 0) := by
      intro ω
      rw [count_eq_sum, count_eq_sum, Finset.sum_insert ha, add_comm]
    have hindep : IndepFun (fun ω => count E s ω)
        (fun ω : ι → α => if ω a ∈ E then (1 : ℕ) else 0) P := by
      have h := hind.indepFun_finsetSum_of_notMem hmeas ha
      have he : (∑ j ∈ s, fun (ω : ι → α) => if ω j ∈ E then (1 : ℕ) else 0) =
          fun ω => count E s ω := by
        funext ω
        rw [count_eq_sum, Finset.sum_apply]
      rw [he] at h
      exact h
    have hpa : P.real {ω | ω a ∈ E} = μ.real E := by
      have hset : {ω : ι → α | ω a ∈ E} = (fun ω => ω a) ⁻¹' E := rfl
      rw [hset, Measure.real, Measure.real, ← Measure.map_apply (measurable_pi_apply a) hE,
        (measurePreserving_eval (fun _ : ι => μ) a).map_eq]
    have hmeasA0 : MeasurableSet {ω : ι → α | ω a ∈ E} := (measurable_pi_apply a) hE
    have hpa' : P.real {ω | ω a ∉ E} = 1 - μ.real E := by
      have hset : {ω : ι → α | ω a ∉ E} = {ω | ω a ∈ E}ᶜ := rfl
      rw [hset, probReal_compl_eq_one_sub hmeasA0, hpa]
    have hjoint : ∀ (q : ℕ) (e : ℕ), P.real ({ω | count E s ω = q} ∩
        {ω | (if ω a ∈ E then (1 : ℕ) else 0) = e}) =
        P.real {ω | count E s ω = q} *
          P.real {ω | (if ω a ∈ E then (1 : ℕ) else 0) = e} := by
      intro q e
      have h := hindep.measure_inter_preimage_eq_mul {q} {e}
        (measurableSet_singleton q) (measurableSet_singleton e)
      simp only [Measure.real]
      have h1 : (fun ω => count E s ω) ⁻¹' {q} = {ω | count E s ω = q} := rfl
      have h2 : (fun ω : ι → α => if ω a ∈ E then (1 : ℕ) else 0) ⁻¹' {e} =
          {ω | (if ω a ∈ E then (1 : ℕ) else 0) = e} := rfl
      rw [h1, h2] at h
      rw [h, ENNReal.toReal_mul]
    have hone : {ω : ι → α | (if ω a ∈ E then (1 : ℕ) else 0) = 1} = {ω | ω a ∈ E} := by
      ext ω
      by_cases h : ω a ∈ E <;> simp [h]
    have hzero : {ω : ι → α | (if ω a ∈ E then (1 : ℕ) else 0) = 0} = {ω | ω a ∉ E} := by
      ext ω
      by_cases h : ω a ∈ E <;> simp [h]
    have hmeasCount : ∀ q, MeasurableSet {ω : ι → α | count E s ω = q} :=
      fun q => (measurable_count E hE s) (measurableSet_singleton q)
    have hmeasA : MeasurableSet {ω : ι → α | ω a ∈ E} := (measurable_pi_apply a) hE
    rw [Finset.card_insert_of_notMem ha]
    cases r with
    | zero =>
      have hset : {ω | count E (insert a s) ω = 0} =
          {ω | count E s ω = 0} ∩ {ω | (if ω a ∈ E then (1 : ℕ) else 0) = 0} := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, hcount]
        omega
      rw [hset, hjoint, hzero, hpa', ih, pmf_succ_zero]
      ring
    | succ r =>
      have hset : {ω | count E (insert a s) ω = r + 1} =
          ({ω | count E s ω = r + 1} ∩ {ω | (if ω a ∈ E then (1 : ℕ) else 0) = 0}) ∪
          ({ω | count E s ω = r} ∩ {ω | (if ω a ∈ E then (1 : ℕ) else 0) = 1}) := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_union, hcount]
        by_cases h : ω a ∈ E <;> simp [h]
      have hdisj : Disjoint
          ({ω | count E s ω = r + 1} ∩ {ω | (if ω a ∈ E then (1 : ℕ) else 0) = 0})
          ({ω | count E s ω = r} ∩ {ω | (if ω a ∈ E then (1 : ℕ) else 0) = 1}) := by
        rw [Set.disjoint_left]
        intro ω h1 h2
        have := h1.1.symm.trans h2.1
        omega
      rw [hset, measureReal_union hdisj
        ((hmeasCount r).inter (by rw [hone]; exact hmeasA)),
        hjoint, hjoint, hzero, hone, hpa, hpa', ih, ih, pmf_succ_succ]
      ring

end Counts

end PiBinomial
end FCAppendix
