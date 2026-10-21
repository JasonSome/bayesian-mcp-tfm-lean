import FCAppendix.Probability.EmpiricalMean
import FCAppendix.Probability.EmpiricalConcentration
import FCAppendix.Probability.FinitePushforward
import FCAppendix.Probability.IndependentCounts
import FCAppendix.Affine.Hybrid.NativeSeed

noncomputable section
namespace FCAppendix.Affine.Tail04.Empirical
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open scoped BigOperators

def flag (p u : unitInterval) : Bool := if u≤ p then true else false

theorem measurable_flag : Measurable (Function.uncurry flag) := by
  exact Measurable.ite (measurableSet_le measurable_snd measurable_fst)
    measurable_const measurable_const

theorem measurable_flag_fixed (p : unitInterval) : Measurable (flag p) :=
  measurable_flag.comp (measurable_const.prodMk measurable_id)

theorem uniform_flag_law (p : unitInterval) :
    FiniteLaw.ofMeasure (volume : Measure unitInterval) (flag p)
      (measurable_flag_fixed p) =
      IndependentCounts.bernoulli (p:ℝ) (unitInterval.nonneg p) (unitInterval.le_one p) := by
  let K := FiniteLaw.ofMeasure (volume : Measure unitInterval) (flag p)
    (measurable_flag_fixed p)
  have ht : K.mass true=(p:ℝ) := by
    rw [FiniteLaw.ofMeasure_mass]
    have he : {u : unitInterval | flag p u=true}=Iic p := by
      ext u
      by_cases hu : u≤ p <;> simp [flag,hu]
    rw [he,unitInterval.volume_Iic,ENNReal.toReal_ofReal (unitInterval.nonneg p)]
  have hs := K.total
  have hsum : ∑ b : Bool,K.mass b=K.mass false+K.mass true := by
    rw [Fintype.sum_bool]
    ring
  rw [hsum] at hs
  apply FiniteLaw.ext
  intro b
  cases b
  · change K.mass false=1-(p:ℝ)
    linarith
  · exact ht

theorem integral_flag_weight (p : unitInterval) (x : ℝ) :
    (∫ u : unitInterval, if flag p u then x else 0)=(p:ℝ)*x := by
  have hh := FiniteLaw.expect_ofMeasure (volume : Measure unitInterval) (flag p)
    (measurable_flag_fixed p) (fun b => if b then x else 0)
  rw [uniform_flag_law,IndependentCounts.expect_bernoulli] at hh
  simpa only [Bool.false_eq_true,ite_false,Bool.true_eq,ite_true,mul_zero,zero_add]
    using hh.symm

section MarkedPopulation
variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ]
variable (p : X→ unitInterval) (hp : Measurable p)
variable (h : X→ℝ) (hh : Measurable h) (hb : ∀ x,h x∈Icc 0 1)

def markedStatistic (p : X→ unitInterval) (h : X→ℝ) (z : X×unitInterval) : ℝ :=
  if flag (p z.1) z.2 then h z.1 else 0

include hp hh in
theorem measurable_markedStatistic : Measurable (markedStatistic p h) := by
  have hs : MeasurableSet {z : X×unitInterval | flag (p z.1) z.2=true} :=
    measurableSet_eq_fun
      (measurable_flag.comp ((hp.comp measurable_fst).prodMk measurable_snd))
      measurable_const
  exact Measurable.ite hs (hh.comp measurable_fst) measurable_const

include hb in
omit [MeasurableSpace X] in
theorem markedStatistic_bounds (z : X×unitInterval) : markedStatistic p h z∈Icc 0 1 := by
  unfold markedStatistic
  split_ifs
  · exact hb z.1
  · norm_num

include hp hh hb in
theorem integrable_markedStatistic :
    Integrable (markedStatistic p h) (μ.prod (volume : Measure unitInterval)) := by
  apply Integrable.of_bound (measurable_markedStatistic p hp h hh).aestronglyMeasurable 1
  exact Eventually.of_forall (fun z => by
    rw [Real.norm_eq_abs,abs_of_nonneg (markedStatistic_bounds p h hb z).1]
    exact (markedStatistic_bounds p h hb z).2)

include μ hp hh hb in
theorem integral_markedStatistic :
    (∫ z,markedStatistic p h z ∂μ.prod (volume : Measure unitInterval)) =
      ∫ x,(p x:ℝ)*h x ∂μ := by
  rw [integral_prod _ (integrable_markedStatistic μ p hp h hh hb)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => integral_flag_weight (p x) (h x))

include hp hh hb in
theorem marked_empirical_L1 (N : ℕ) (hN : 0< N) :
    (∫ z : Fin N→ X×unitInterval,
      |(∑ i,markedStatistic p h (z i))/(N:ℝ)-∫ x,(p x:ℝ)*h x ∂μ|
      ∂Measure.pi (fun _ : Fin N=> μ.prod (volume : Measure unitInterval))) ≤
      1/Real.sqrt N := by
  have hh' : AEStronglyMeasurable (markedStatistic p h) (μ.prod (volume : Measure unitInterval)) :=
    (measurable_markedStatistic p hp h hh).aestronglyMeasurable
  have hb' : ∀ᵐ z∂μ.prod (volume : Measure unitInterval),
      |markedStatistic p h z|≤1 := Eventually.of_forall (fun z => by
    rw [abs_of_nonneg (markedStatistic_bounds p h hb z).1]
    exact (markedStatistic_bounds p h hb z).2)
  simpa only [integral_markedStatistic μ p hp h hh hb] using
    Probability.iid_empiricalMean_L1_le (μ.prod (volume : Measure unitInterval))
      hh' 1 (by norm_num) hb' N hN

include hp hh hb in
theorem marked_empirical_tail (N : ℕ) (hN : 0< N) {ε : ℝ} (hε : 0≤ ε) :
    (Measure.pi (fun _ : Fin N=> μ.prod (volume : Measure unitInterval))).real
      {z | ε ≤ |(∑ i,markedStatistic p h (z i))/(N:ℝ)-∫ x,(p x:ℝ)*h x ∂μ|} ≤
      2*Real.exp (-2*(N:ℝ)*ε^2) := by
  have hh' : AEMeasurable (markedStatistic p h) (μ.prod (volume : Measure unitInterval)) :=
    (measurable_markedStatistic p hp h hh).aemeasurable
  have hb' : ∀ᵐ x ∂μ.prod (volume : Measure unitInterval),markedStatistic p h x∈Icc 0 1 :=
    Eventually.of_forall (markedStatistic_bounds p h hb)
  simpa only [integral_markedStatistic μ p hp h hh hb] using
    Probability.iid_empiricalMean_two_sided_le
      (μ.prod (volume : Measure unitInterval)) hh' hb' N hN hε

end MarkedPopulation

section EndogenousEdit
variable {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]

theorem edited_mean_L1 (old edited : Ω→ℝ) (hold : Integrable old ν)
    (hedit : Integrable edited ν) (a d E : ℝ)
    (hd : ∀ᵐ x∂ν,|edited x-old x|≤ d)
    (hE : (∫ x,|old x-a| ∂ν)≤ E) :
    (∫ x,|edited x-a| ∂ν)≤ E+d := by
  have hcmp : ∀ᵐ x∂ν,|edited x-a|≤|old x-a|+d := by
    filter_upwards [hd] with x hx
    have hh := abs_sub_le (edited x) (old x) a
    linarith
  calc
    _ ≤ ∫ x,|old x-a|+d ∂ν := integral_mono_ae
      (hedit.sub (integrable_const a)).abs
      ((hold.sub (integrable_const a)).abs.add (integrable_const d)) hcmp
    _ = (∫ x,|old x-a| ∂ν)+d := by
      have hh : (∫ x,|old x-a|+d ∂ν)=(∫ x,|old x-a| ∂ν)+(∫ _ : Ω,d ∂ν) :=
        integral_add (hold.sub (integrable_const a)).abs (integrable_const d)
      rw [hh]
      simp
    _ ≤ E+d := add_le_add_left hE d

omit [MeasurableSpace Ω] in
theorem edited_mean_bad_subset (old edited : Ω→ℝ) (a d ε : ℝ)
    (hd : ∀ x,|edited x-old x|≤ d) (hsmall : d≤ ε/2) :
    {x | ε≤|edited x-a|} ⊆ {x | ε/2≤|old x-a|} := by
  intro x hx
  have hh := abs_sub_le (edited x) (old x) a
  have h := hd x
  dsimp only [mem_setOf_eq] at hx ⊢
  linarith

theorem prefix_mean_error {N k : ℕ} (hN : 0< N)
    (oldMean prefixSum : ℝ) (hmean : oldMean∈Icc 0 1)
    (hprefix : prefixSum∈Icc 0 (k:ℝ)) :
    |((N:ℝ)*oldMean+prefixSum)/((N:ℝ)+k)-oldMean|≤(k:ℝ)/((N:ℝ)+k) := by
  have hN0 : (0:ℝ)< N := Nat.cast_pos.mpr hN
  have hd : 0<(N:ℝ)+k := by positivity
  have he : ((N:ℝ)*oldMean+prefixSum)/((N:ℝ)+k)-oldMean =
      (prefixSum-(k:ℝ)*oldMean)/((N:ℝ)+k) := by
    field_simp [hd.ne']
    ring
  rw [he,abs_div,abs_of_pos hd]
  apply div_le_div_of_nonneg_right _ hd.le
  apply abs_le.mpr
  constructor <;> nlinarith [show (0:ℝ)≤k by exact_mod_cast Nat.zero_le k, hmean.1,hmean.2,hprefix.1,hprefix.2]

end EndogenousEdit
end FCAppendix.Affine.Tail04.Empirical
