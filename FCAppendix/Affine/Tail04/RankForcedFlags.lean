import FCAppendix.Affine.Tail04.FlagAtomPrimitives
import FCAppendix.Affine.Hybrid.OwnerLaw

noncomputable section
namespace FCAppendix.Affine.Tail04
open MeasureTheory Set
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def forceExclusive (target : ι) (flags : ι → Bool) : ι → Bool :=
  Function.update flags target false

def flaggedMixedSet (flags : ι → Bool) : Finset ι :=
  Finset.univ.filter (fun i => flags i = true)

omit [Fintype ι] in
@[simp] theorem forceExclusive_target (target : ι) (flags : ι → Bool) :
    forceExclusive target flags target = false := by simp [forceExclusive]

omit [Fintype ι] in
theorem forceExclusive_other (target i : ι) (hi : i ≠ target) (flags : ι → Bool) :
    forceExclusive target flags i = flags i := by simp [forceExclusive, hi]

theorem flaggedMixedSet_forceExclusive (target : ι) (flags : ι → Bool) :
    flaggedMixedSet (forceExclusive target flags) = (flaggedMixedSet flags).erase target := by
  ext i
  by_cases hi : i = target
  · subst i
    simp [flaggedMixedSet, forceExclusive]
  · simp [flaggedMixedSet, forceExclusive, hi]

theorem forced_target_not_mixed (target : ι) (flags : ι → Bool) :
    target ∉ flaggedMixedSet (forceExclusive target flags) := by
  rw [flaggedMixedSet_forceExclusive]
  exact Finset.notMem_erase _ _

def rankForcedFlagLaw [Nonempty ι] (b p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    FiniteLaw (ι × (ι → Bool)) :=
  ((Hybrid.rankLaw b).prod (independentFlagLaw p hp0 hp1)).map
    (fun z => (z.1, forceExclusive z.1 z.2))

theorem rankForcedFlagLaw_expect [Nonempty ι] (b p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (f : ι × (ι → Bool) → ℝ) :
    (rankForcedFlagLaw b p hp0 hp1).expect f =
      (Hybrid.rankLaw b).expect (fun target =>
        (independentFlagLaw p hp0 hp1).expect
          (fun flags => f (target, forceExclusive target flags))) := by
  rw [rankForcedFlagLaw, FiniteLaw.expect_map, FiniteLaw.expect_prod]

theorem rankForcedFlagLaw_target_expect [Nonempty ι] (b p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (f : ι → ℝ) :
    (rankForcedFlagLaw b p hp0 hp1).expect (fun z => f z.1) =
      (Hybrid.rankLaw b).expect f := by
  rw [rankForcedFlagLaw_expect]
  simp only [FiniteLaw.expect_const]

theorem rankForcedFlagLaw_target_bound [Nonempty ι] (b p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (i : ι) :
    (rankForcedFlagLaw b p hp0 hp1).prob (fun z => z.1 = i) ≤
      2 / (Fintype.card ι : ℝ) := by
  rw [FiniteLaw.prob_eq_expect]
  calc
    _ = (Hybrid.rankLaw b).expect (fun x => if x=i then 1 else 0) :=
      rankForcedFlagLaw_target_expect b p hp0 hp1 (fun x => if x=i then 1 else 0)
    _ = (Hybrid.rankLaw b).mass i := FiniteLaw.expect_singleton _ _
    _ ≤ _ := Hybrid.rankLaw_mass_le b i

theorem rankForcedFlagLaw_target_exclusive [Nonempty ι] (b p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    (rankForcedFlagLaw b p hp0 hp1).prob (fun z => z.2 z.1 = false) = 1 := by
  rw [FiniteLaw.prob_eq_expect, rankForcedFlagLaw_expect]
  simp only [forceExclusive_target, if_true, FiniteLaw.expect_const]

theorem measurable_independentFlagLaw_mass {X : Type*} [MeasurableSpace X]
    (p : X → ι → ℝ) (hp0 : ∀ x i, 0 ≤ p x i) (hp1 : ∀ x i, p x i ≤ 1)
    (hp : ∀ i, Measurable (fun x => p x i)) (flags : ι → Bool) :
    Measurable (fun x => (independentFlagLaw (p x) (hp0 x) (hp1 x)).mass flags) := by
  apply Finset.measurable_prod
  intro i _
  cases hflag : flags i
  · change Measurable (fun a : X => 1-p a i)
    exact measurable_const.sub (hp i)
  · simpa only [IndependentCounts.bernoulli, hflag, if_true] using hp i

theorem measurable_rankForcedFlagLaw_mass [Nonempty ι]
    (p : (ι → ℝ) → ι → ℝ) (hp0 : ∀ b i, 0 ≤ p b i) (hp1 : ∀ b i, p b i ≤ 1)
    (hp : ∀ i, Measurable (fun b => p b i)) (out : ι × (ι → Bool)) :
    Measurable (fun b => (rankForcedFlagLaw b (p b) (hp0 b) (hp1 b)).mass out) := by
  classical
  simp only [rankForcedFlagLaw, FiniteLaw.map, FiniteLaw.prod]
  apply Finset.measurable_sum
  intro z _
  by_cases hz : (z.1, forceExclusive z.1 z.2) = out
  · simp only [if_pos hz]
    exact (Hybrid.measurable_rankLaw_mass z.1).mul
      (measurable_independentFlagLaw_mass p hp0 hp1 hp z.2)
  · simp only [if_neg hz]
    exact measurable_const

theorem exists_rankForcedFlag_sampler [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [StandardBorelSpace ι]
    (p : (ι → ℝ) → ι → ℝ) (hp0 : ∀ b i, 0 ≤ p b i) (hp1 : ∀ b i, p b i ≤ 1)
    (hp : ∀ i, Measurable (fun b => p b i)) :
    ∃ f : (ι → ℝ) → unitInterval → ι × (ι → Bool),
      Measurable (Function.uncurry f) ∧
      (∀ b u, 0 < (rankForcedFlagLaw b (p b) (hp0 b) (hp1 b)).mass (f b u)) ∧
      ∀ b, volume.map (f b) =
        FiniteLaw.probabilityMeasure (rankForcedFlagLaw b (p b) (hp0 b) (hp1 b)) :=
  Hybrid.exists_support_sampler (fun b => rankForcedFlagLaw b (p b) (hp0 b) (hp1 b))
    (measurable_rankForcedFlagLaw_mass p hp0 hp1 hp)

end FCAppendix.Affine.Tail04
