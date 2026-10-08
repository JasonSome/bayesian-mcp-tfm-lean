import FCAppendix.Probability.PiBinomial
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Independence.Integration

noncomputable section

namespace FCAppendix.PiBinomial

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable def tiltMass (N : ℕ) (a z : ℝ) (r : ℕ) : ℝ :=
  (N.choose r : ℝ) * a ^ r * z ^ (N - r)

theorem tiltMass_zero_zero (a z : ℝ) : tiltMass 0 a z 0 = 1 := by simp [tiltMass]

theorem tiltMass_zero_succ (a z : ℝ) (r : ℕ) : tiltMass 0 a z (r + 1) = 0 := by
  simp [tiltMass]

theorem tiltMass_succ_zero (N : ℕ) (a z : ℝ) :
    tiltMass (N + 1) a z 0 = z * tiltMass N a z 0 := by
  simp [tiltMass, pow_succ]
  ring

theorem tiltMass_succ_succ (N r : ℕ) (a z : ℝ) :
    tiltMass (N + 1) a z (r + 1) = z * tiltMass N a z (r + 1) + a * tiltMass N a z r := by
  unfold tiltMass
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

variable {ι α : Type*} [MeasurableSpace α]

theorem integral_tilt_count [Fintype ι] (μ : Measure α) [IsProbabilityMeasure μ]
    (E B : Set α) (hE : MeasurableSet E) (hB : MeasurableSet B) (hEB : Disjoint E B)
    (t : ℝ) (ht : 0 ≤ t) (s : Finset ι) (r : ℕ) :
    ∫ ω, (if count E s ω = r then Real.exp (-t * count B s ω) else 0)
      ∂(Measure.pi fun _ : ι => μ) =
      tiltMass s.card (μ.real E) (μ.real (Eᶜ \ B) + μ.real B * Real.exp (-t)) r := by
  classical
  set P := Measure.pi (fun _ : ι => μ) with hP
  set z := μ.real (Eᶜ \ B) + μ.real B * Real.exp (-t) with hz
  let X : ι → (ι → α) → ℕ × ℕ := fun l ω =>
    ((if ω l ∈ E then 1 else 0 : ℕ), (if ω l ∈ B then 1 else 0 : ℕ))
  have hXm : ∀ l, Measurable (X l) := by
    intro l
    have h1 : Measurable (fun ω : ι → α => (if ω l ∈ E then 1 else 0 : ℕ)) :=
      Measurable.ite ((measurable_pi_apply l) hE) measurable_const measurable_const
    have h2 : Measurable (fun ω : ι → α => (if ω l ∈ B then 1 else 0 : ℕ)) :=
      Measurable.ite ((measurable_pi_apply l) hB) measurable_const measurable_const
    exact h1.prodMk h2
  have hind : iIndepFun X P := by
    have h := iIndepFun_pi (μ := fun _ : ι => μ)
      (X := fun (_ : ι) (x : α) => ((if x ∈ E then 1 else 0 : ℕ), (if x ∈ B then 1 else 0 : ℕ)))
      (fun _ => ((Measurable.ite hE measurable_const measurable_const).prodMk
          (Measurable.ite hB measurable_const measurable_const)).aemeasurable)
    exact h
  have hU (s : Finset ι) : (∑ l ∈ s, X l) = fun ω => (count E s ω, count B s ω) := by
    funext ω
    rw [Finset.sum_apply]
    ext
    · simp only [Prod.fst_sum, count_eq_sum, X]
    · simp only [Prod.snd_sum, count_eq_sum, X]
  have hEint : ∫ ω, (if ω ∈ E then (1 : ℝ) else 0) ∂μ = μ.real E := by
    have hh := integral_indicator_one (μ := μ) hE
    rw [← hh]
    congr 1
  have hzint : ∫ ω, (if ω ∈ E then (0 : ℝ) else Real.exp (-t * (if ω ∈ B then 1 else 0)))
      ∂μ = z := by
    have hfun : (fun ω : α => if ω ∈ E then (0 : ℝ) else
        Real.exp (-t * (if ω ∈ B then 1 else 0))) =
        fun ω => (Eᶜ \ B).indicator (fun _ => (1 : ℝ)) ω +
          B.indicator (fun _ => Real.exp (-t)) ω := by
      funext ω
      by_cases h1 : ω ∈ E
      · have h2 : ω ∉ B := Set.disjoint_left.mp hEB h1
        simp [Set.indicator, h1, h2]
      · by_cases h2 : ω ∈ B <;> simp [Set.indicator, h1, h2]
    rw [hfun, integral_add ((integrable_const (1 : ℝ)).indicator (hE.compl.diff hB))
      ((integrable_const _).indicator hB), integral_indicator_const _ (hE.compl.diff hB),
      integral_indicator_const _ hB]
    simp [hz, smul_eq_mul, mul_comm]
  induction s using Finset.induction_on generalizing r with
  | empty =>
    cases r with
    | zero => simp [count, tiltMass, P]
    | succ r => simp [count, tiltMass]
  | @insert a s ha ih =>
    have hindep : IndepFun (fun ω => (count E s ω, count B s ω)) (X a) P := by
      have h := hind.indepFun_finsetSum_of_notMem hXm ha
      rwa [hU s] at h
    let f1 : ℕ × ℕ → ℝ := fun u => if u.1 + 1 = r then Real.exp (-t * u.2) else 0
    let g1 : ℕ × ℕ → ℝ := fun v => if v.1 = 1 then 1 else 0
    let f0 : ℕ × ℕ → ℝ := fun u => if u.1 = r then Real.exp (-t * u.2) else 0
    let g0 : ℕ × ℕ → ℝ := fun v => if v.1 = 0 then Real.exp (-t * v.2) else 0
    have hpt : (fun ω : ι → α => if count E (insert a s) ω = r then
        Real.exp (-t * count B (insert a s) ω) else 0) =
        fun ω => f1 (count E s ω, count B s ω) * g1 (X a ω) +
          f0 (count E s ω, count B s ω) * g0 (X a ω) := by
      funext ω
      have hcE : count E (insert a s) ω = count E s ω + (if ω a ∈ E then 1 else 0) := by
        rw [count_eq_sum, count_eq_sum, Finset.sum_insert ha, add_comm]
      have hcB : count B (insert a s) ω = count B s ω + (if ω a ∈ B then 1 else 0) := by
        rw [count_eq_sum, count_eq_sum, Finset.sum_insert ha, add_comm]
      rw [hcE, hcB]
      by_cases h1 : ω a ∈ E
      · have h2 : ω a ∉ B := Set.disjoint_left.mp hEB h1
        simp [f1, g1, f0, g0, X, h1, h2]
      · by_cases h2 : ω a ∈ B
        · simp only [f1, g1, f0, g0, X, h1, h2, if_true, if_false, add_zero, Nat.cast_add,
            Nat.cast_one]
          simp only [zero_ne_one, if_false, mul_zero, zero_add]
          split_ifs <;> simp [mul_add, Real.exp_add]
        · simp [f1, g1, f0, g0, X, h1, h2]
    have hUm : Measurable (fun ω : ι → α => (count E s ω, count B s ω)) :=
      (measurable_count E hE s).prodMk (measurable_count B hB s)
    have hexp1 (x : ℕ) : |Real.exp (-t * x)| ≤ 1 := by
      rw [abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.mpr
      have : (0 : ℝ) ≤ t * x := mul_nonneg ht (Nat.cast_nonneg x)
      linarith
    have hf1 : ∀ u, |f1 u| ≤ 1 := fun u => by
      simp only [f1]; split_ifs
      · exact hexp1 _
      · simp
    have hf0 : ∀ u, |f0 u| ≤ 1 := fun u => by
      simp only [f0]; split_ifs
      · exact hexp1 _
      · simp
    have hg1 : ∀ u, |g1 u| ≤ 1 := fun u => by simp only [g1]; split_ifs <;> simp
    have hg0 : ∀ u, |g0 u| ≤ 1 := fun u => by
      simp only [g0]; split_ifs
      · exact hexp1 _
      · simp
    have hprod (f g : ℕ × ℕ → ℝ) : ∫ ω, f (count E s ω, count B s ω) * g (X a ω) ∂P =
        (∫ ω, f (count E s ω, count B s ω) ∂P) * ∫ ω, g (X a ω) ∂P :=
      hindep.integral_fun_comp_mul_comp hUm.aemeasurable (hXm a).aemeasurable
        (measurable_of_countable f).aestronglyMeasurable
        (measurable_of_countable g).aestronglyMeasurable
    have hint1 : Integrable (fun ω => f1 (count E s ω, count B s ω) * g1 (X a ω)) P := by
      refine Integrable.of_bound (C := 1) ?_ (Filter.Eventually.of_forall fun ω => ?_)
      · exact (((measurable_of_countable f1).comp hUm).mul
          ((measurable_of_countable g1).comp (hXm a))).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_one₀ (hf1 _) (abs_nonneg _) (hg1 _)
    have hint0 : Integrable (fun ω => f0 (count E s ω, count B s ω) * g0 (X a ω)) P := by
      refine Integrable.of_bound (C := 1) ?_ (Filter.Eventually.of_forall fun ω => ?_)
      · exact (((measurable_of_countable f0).comp hUm).mul
          ((measurable_of_countable g0).comp (hXm a))).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_one₀ (hf0 _) (abs_nonneg _) (hg0 _)
    have hG1 : ∫ ω, g1 (X a ω) ∂P = μ.real E := by
      have he : (fun ω : ι → α => g1 (X a ω)) =
          fun ω => (fun x : α => if x ∈ E then (1 : ℝ) else 0) (ω a) := by
        funext ω
        by_cases h : ω a ∈ E <;> simp [g1, X, h]
      rw [he, hP]
      exact (integral_comp_eval (μ := fun _ : ι => μ) (i := a)
        (f := fun x : α => if x ∈ E then (1 : ℝ) else 0)
        ((Measurable.ite hE measurable_const measurable_const).aestronglyMeasurable)).trans hEint
    have hG0 : ∫ ω, g0 (X a ω) ∂P = z := by
      have he : (fun ω : ι → α => g0 (X a ω)) =
          fun ω => (fun x : α => if x ∈ E then (0 : ℝ) else
            Real.exp (-t * (if x ∈ B then 1 else 0))) (ω a) := by
        funext ω
        by_cases h1 : ω a ∈ E
        · simp [g0, X, h1]
        · by_cases h2 : ω a ∈ B <;> simp [g0, X, h1, h2]
      have hm : Measurable (fun x : α => if x ∈ E then (0 : ℝ) else
          Real.exp (-t * (if x ∈ B then 1 else 0))) :=
        Measurable.ite hE measurable_const (Measurable.exp (measurable_const.mul
          (Measurable.ite hB measurable_const measurable_const)))
      rw [he, hP]
      exact (integral_comp_eval (μ := fun _ : ι => μ) (i := a) hm.aestronglyMeasurable).trans hzint
    have hF0 : ∫ ω, f0 (count E s ω, count B s ω) ∂P = tiltMass s.card (μ.real E) z r := by
      rw [← ih r]
    rw [hpt, integral_add hint1 hint0, hprod, hprod, hF0, hG1, hG0,
      Finset.card_insert_of_notMem ha]
    cases r with
    | zero =>
      have hF1 : ∫ ω, f1 (count E s ω, count B s ω) ∂P = 0 := by simp [f1]
      rw [hF1, tiltMass_succ_zero]
      ring
    | succ r' =>
      have hF1 : ∫ ω, f1 (count E s ω, count B s ω) ∂P = tiltMass s.card (μ.real E) z r' := by
        rw [← ih r']
        congr 1
        funext ω
        simp [f1]
      rw [hF1, tiltMass_succ_succ]
      ring

theorem pi_pair_lower_tail_le [Fintype ι] (μ : Measure α) [IsProbabilityMeasure μ]
    (E B : Set α) (hE : MeasurableSet E) (hB : MeasurableSet B) (hEB : Disjoint E B)
    (t : ℝ) (ht : 0 ≤ t) (s : Finset ι) (c : ℕ) (hα : μ.real E < 1) :
    (Measure.pi fun _ : ι => μ).real {ω | count E s ω < c ∧ count B s ω < c} ≤
      Real.exp (t * (c - 1 : ℕ)) *
        (1 - μ.real B / (1 - μ.real E) * (1 - Real.exp (-t))) ^ (s.card - (c - 1)) *
        ∑ r ∈ Finset.range c, pmf s.card (μ.real E) r := by
  classical
  set P := Measure.pi (fun _ : ι => μ) with hP
  set a := μ.real E with ha
  set β := μ.real B with hβ
  set z := μ.real (Eᶜ \ B) + β * Real.exp (-t) with hz
  set q := 1 - β / (1 - a) * (1 - Real.exp (-t)) with hq
  have ha0 : 0 ≤ a := measureReal_nonneg
  have h1a : 0 < 1 - a := sub_pos.mpr hα
  have hBsub : B ⊆ Eᶜ := fun x hx hxE => Set.disjoint_left.mp hEB hxE hx
  have hβle : β ≤ 1 - a := by
    have h := measureReal_mono (μ := μ) hBsub
    rwa [probReal_compl_eq_one_sub hE] at h
  have hexp0 : 0 ≤ 1 - Real.exp (-t) := by
    have : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have hexp1 : 1 - Real.exp (-t) ≤ 1 := by linarith [Real.exp_pos (-t)]
  have hratio0 : 0 ≤ β / (1 - a) := div_nonneg measureReal_nonneg h1a.le
  have hratio1 : β / (1 - a) ≤ 1 := (div_le_one h1a).mpr hβle
  have hq0 : 0 ≤ q := by
    have := mul_le_one₀ hratio1 hexp0 hexp1
    linarith
  have hq1 : q ≤ 1 := by
    have := mul_nonneg hratio0 hexp0
    linarith
  have hzq : z = (1 - a) * q := by
    have hd : μ.real (Eᶜ \ B) = 1 - a - β := by
      rw [measureReal_sdiff hBsub hB, probReal_compl_eq_one_sub hE]
    rw [hz, hq, hd]
    field_simp [h1a.ne']; ring
  let Ψ : ℕ → (ι → α) → ℝ := fun r ω =>
    if count E s ω = r then Real.exp (-t * count B s ω) else 0
  have hΨm (r : ℕ) : Measurable (Ψ r) := by
    have hm := (measurable_count E hE s).prodMk (measurable_count B hB s)
    exact (measurable_of_countable (fun u : ℕ × ℕ =>
      if u.1 = r then Real.exp (-t * u.2) else 0)).comp hm
  have hΨb (r : ℕ) (ω : ι → α) : 0 ≤ Ψ r ω ∧ Ψ r ω ≤ 1 := by
    simp only [Ψ]
    split_ifs
    · refine ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr ?_⟩
      have : (0 : ℝ) ≤ t * count B s ω := mul_nonneg ht (Nat.cast_nonneg _)
      linarith
    · simp
  have hΨi (r : ℕ) : Integrable (Ψ r) P :=
    Integrable.of_bound (C := 1) (hΨm r).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hΨb r ω).1]
        exact (hΨb r ω).2)
  let S : Set (ι → α) := {ω | count E s ω < c ∧ count B s ω < c}
  have hSm : MeasurableSet S :=
    ((measurable_count E hE s) (measurableSet_Iio (a := c))).inter
      ((measurable_count B hB s) (measurableSet_Iio (a := c)))
  have hpoint (ω : ι → α) : S.indicator (fun _ => (1 : ℝ)) ω ≤
      Real.exp (t * (c - 1 : ℕ)) * ∑ r ∈ Finset.range c, Ψ r ω := by
    have hsum0 : 0 ≤ ∑ r ∈ Finset.range c, Ψ r ω :=
      Finset.sum_nonneg fun r _ => (hΨb r ω).1
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
      have hmem : count E s ω ∈ Finset.range c := Finset.mem_range.mpr hω.1
      have hsum : ∑ r ∈ Finset.range c, Ψ r ω = Real.exp (-t * count B s ω) := by
        rw [Finset.sum_eq_single_of_mem _ hmem]
        · simp [Ψ]
        · intro r _ hr
          simp [Ψ, Ne.symm hr]
      rw [hsum, ← Real.exp_add]
      apply Real.one_le_exp
      have hc2 : count B s ω < c := hω.2
      have hB' : (count B s ω : ℝ) ≤ (c - 1 : ℕ) := by
        exact_mod_cast (show count B s ω ≤ c - 1 by omega)
      nlinarith
    · rw [Set.indicator_of_notMem hω]
      exact mul_nonneg (Real.exp_pos _).le hsum0
  have hint : P.real S ≤ Real.exp (t * (c - 1 : ℕ)) *
      ∑ r ∈ Finset.range c, tiltMass s.card a z r := by
    rw [← integral_indicator_one hSm]
    have hR : Integrable (fun ω => Real.exp (t * (c - 1 : ℕ)) *
        ∑ r ∈ Finset.range c, Ψ r ω) P :=
      (integrable_finsetSum _ fun r _ => hΨi r).const_mul _
    have hle := integral_mono ((integrable_const (1 : ℝ)).indicator hSm) hR hpoint
    refine hle.trans (le_of_eq ?_)
    rw [integral_const_mul, integral_finsetSum _ fun r _ => hΨi r]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    exact integral_tilt_count μ E B hE hB hEB t ht s r
  refine hint.trans ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  have hr' : r ≤ c - 1 := by have := Finset.mem_range.mp hr; omega
  unfold tiltMass pmf
  rw [hzq, mul_pow]
  have hpow : q ^ (s.card - r) ≤ q ^ (s.card - (c - 1)) :=
    pow_le_pow_of_le_one hq0 hq1 (by omega)
  have hnn : 0 ≤ (s.card.choose r : ℝ) * a ^ r * (1 - a) ^ (s.card - r) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ha0 _)) (pow_nonneg h1a.le _)
  have := mul_le_mul_of_nonneg_left hpow hnn
  linarith

theorem pi_pair_lower_tail_le_exp [Fintype ι] (μ : Measure α) [IsProbabilityMeasure μ]
    (E B : Set α) (hE : MeasurableSet E) (hB : MeasurableSet B) (hEB : Disjoint E B)
    (t : ℝ) (ht : 0 ≤ t) (s : Finset ι) (c : ℕ) (hα : μ.real E < 1) :
    (Measure.pi fun _ : ι => μ).real {ω | count E s ω < c ∧ count B s ω < c} ≤
      Real.exp (t * (c - 1 : ℕ) - (s.card - (c - 1) : ℕ) *
        (μ.real B / (1 - μ.real E)) * (1 - Real.exp (-t))) *
        ∑ r ∈ Finset.range c, pmf s.card (μ.real E) r := by
  have h := pi_pair_lower_tail_le μ E B hE hB hEB t ht s c hα
  refine h.trans ?_
  have hsum : 0 ≤ ∑ r ∈ Finset.range c, pmf s.card (μ.real E) r := by
    apply Finset.sum_nonneg
    intro r _
    unfold pmf
    have ha0 : 0 ≤ μ.real E := measureReal_nonneg
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ha0 _))
      (pow_nonneg (sub_pos.mpr hα).le _)
  apply mul_le_mul_of_nonneg_right _ hsum
  set x := μ.real B / (1 - μ.real E) * (1 - Real.exp (-t)) with hx
  have hq0 : 0 ≤ 1 - x := by
    have h1a : 0 < 1 - μ.real E := sub_pos.mpr hα
    have hBsub : B ⊆ Eᶜ := fun y hy hyE => Set.disjoint_left.mp hEB hyE hy
    have hβle : μ.real B ≤ 1 - μ.real E := by
      have h := measureReal_mono (μ := μ) hBsub
      rwa [probReal_compl_eq_one_sub hE] at h
    have hr1 : μ.real B / (1 - μ.real E) ≤ 1 := (div_le_one h1a).mpr hβle
    have he0 : 0 ≤ 1 - Real.exp (-t) := by
      have : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      linarith
    have he1 : 1 - Real.exp (-t) ≤ 1 := by linarith [Real.exp_pos (-t)]
    have := mul_le_one₀ hr1 he0 he1
    linarith
  have hle : (1 - x) ^ (s.card - (c - 1)) ≤ Real.exp (-x) ^ (s.card - (c - 1)) :=
    pow_le_pow_left₀ hq0 (by linarith [Real.add_one_le_exp (-x)]) _
  rw [← Real.exp_nat_mul] at hle
  have he : t * (c - 1 : ℕ) - (s.card - (c - 1) : ℕ) *
      (μ.real B / (1 - μ.real E)) * (1 - Real.exp (-t)) =
      t * (c - 1 : ℕ) + (s.card - (c - 1) : ℕ) * -x := by
    rw [hx]
    ring
  rw [he, Real.exp_add]
  exact mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le

end FCAppendix.PiBinomial
