import FCAppendix.Affine.Tail04.RankForcedFlags

noncomputable section
namespace FCAppendix.Affine.Tail04
open MeasureTheory
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def forcedExclusiveSet (target : ι) (flags : ι → Bool) : Finset ι :=
  Finset.univ \ flaggedMixedSet (forceExclusive target flags)

theorem target_mem_forcedExclusiveSet (target : ι) (flags : ι → Bool) :
    target ∈ forcedExclusiveSet target flags := by
  simp only [forcedExclusiveSet, Finset.mem_sdiff, Finset.mem_univ, true_and]
  exact forced_target_not_mixed target flags

theorem forcedExclusiveSet_nonempty (target : ι) (flags : ι → Bool) :
    (forcedExclusiveSet target flags).Nonempty :=
  ⟨target, target_mem_forcedExclusiveSet target flags⟩

def integerOwnerPlanLaw [Nonempty ι] (b p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (K : ι × (ι → Bool) → ℕ) :
    FiniteLaw ((ι × (ι → Bool)) × (Finset ι × Finset ι)) :=
  FiniteLaw.finiteMix ((Hybrid.rankLaw b).prod (independentFlagLaw p hp0 hp1))
    (fun z => (Hybrid.ownerDivision (forcedExclusiveSet z.1 z.2) (K z)).map
      (fun AB => (z, AB)))

theorem integerOwnerPlanLaw_expect [Nonempty ι] (b p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (K : ι × (ι → Bool) → ℕ)
    (f : (ι × (ι → Bool)) × (Finset ι × Finset ι) → ℝ) :
    (integerOwnerPlanLaw b p hp0 hp1 K).expect f =
      (Hybrid.rankLaw b).expect (fun target =>
        (independentFlagLaw p hp0 hp1).expect (fun flags =>
          (Hybrid.ownerDivision (forcedExclusiveSet target flags) (K (target, flags))).expect
            (fun AB => f ((target, flags), AB)))) := by
  rw [integerOwnerPlanLaw, FiniteLaw.expect_finiteMix, FiniteLaw.expect_prod]
  apply FiniteLaw.expect_congr
  intro target
  apply FiniteLaw.expect_congr
  intro flags
  exact FiniteLaw.expect_map _ _ _

private theorem map_positive_preimage {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (mu : FiniteLaw Ω) (f : Ω → Ξ) (x : Ξ) (hx : (mu.map f).mass x ≠ 0) :
    ∃ y, mu.mass y ≠ 0 ∧ f y = x := by
  classical
  by_contra hn
  apply hx
  unfold FiniteLaw.map
  apply Finset.sum_eq_zero
  intro y _
  split_ifs with he
  · by_contra hy
    exact hn ⟨y, hy, he⟩
  · rfl

theorem integerOwnerPlanLaw_support [Nonempty ι] (b p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (K : ι × (ι → Bool) → ℕ)
    (hK : ∀ z, K z ≤ (forcedExclusiveSet z.1 z.2).card)
    (z : ι × (ι → Bool)) (A B : Finset ι)
    (hmass : (integerOwnerPlanLaw b p hp0 hp1 K).mass (z, (A, B)) ≠ 0) :
    A.card = K z ∧ B.card = (forcedExclusiveSet z.1 z.2).card - K z ∧
      Disjoint A B ∧ A ∪ B = forcedExclusiveSet z.1 z.2 ∧
      Disjoint (A ∪ B) (flaggedMixedSet (forceExclusive z.1 z.2)) := by
  obtain ⟨z', _, hpair⟩ := Hybrid.finiteMix_support
    ((Hybrid.rankLaw b).prod (independentFlagLaw p hp0 hp1))
    (fun z' => (Hybrid.ownerDivision (forcedExclusiveSet z'.1 z'.2) (K z')).map
      (fun AB => (z', AB))) (z, (A, B)) hmass
  obtain ⟨AB, hAB, heq⟩ := map_positive_preimage
    (Hybrid.ownerDivision (forcedExclusiveSet z'.1 z'.2) (K z'))
    (fun AB => (z', AB)) (z, (A, B)) hpair
  have hz : z' = z := congrArg Prod.fst heq
  have hABeq : AB = (A, B) := congrArg Prod.snd heq
  subst z'
  subst AB
  obtain ⟨hsub, hA, hB, hdis, hcover⟩ := Hybrid.ownerDivision_support
    (forcedExclusiveSet_nonempty z.1 z.2) (hK z) A B hAB
  refine ⟨hA, ?_, hdis, hcover, ?_⟩
  · rw [hB, Finset.card_sdiff_of_subset hsub, hA]
  · rw [hcover]
    exact Finset.sdiff_disjoint

theorem measurable_integerOwnerPlanLaw_mass [Nonempty ι]
    (p : (ι → ℝ) → ι → ℝ) (hp0 : ∀ b i, 0 ≤ p b i) (hp1 : ∀ b i, p b i ≤ 1)
    (hp : ∀ i, Measurable (fun b => p b i))
    (K : (ι → ℝ) → ι × (ι → Bool) → ℕ)
    (hK : ∀ z, Measurable (fun b => K b z))
    (out : (ι × (ι → Bool)) × (Finset ι × Finset ι)) :
    Measurable (fun b => (integerOwnerPlanLaw b (p b) (hp0 b) (hp1 b) (K b)).mass out) := by
  classical
  unfold integerOwnerPlanLaw FiniteLaw.finiteMix FiniteLaw.expect
  apply Finset.measurable_sum
  intro z _
  apply Measurable.mul
  · exact (Hybrid.measurable_rankLaw_mass z.1).mul
      (measurable_independentFlagLaw_mass p hp0 hp1 hp z.2)
  · have hg : Measurable (fun k : ℕ =>
        ((Hybrid.ownerDivision (forcedExclusiveSet z.1 z.2) k).map
          (fun AB => (z, AB))).mass out) := measurable_of_countable _
    exact hg.comp (hK z)

theorem exists_integerOwnerPlan_sampler [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [StandardBorelSpace ι]
    (p : (ι → ℝ) → ι → ℝ) (hp0 : ∀ b i, 0 ≤ p b i) (hp1 : ∀ b i, p b i ≤ 1)
    (hp : ∀ i, Measurable (fun b => p b i))
    (K : (ι → ℝ) → ι × (ι → Bool) → ℕ)
    (hK : ∀ z, Measurable (fun b => K b z)) :
    ∃ f : (ι → ℝ) → unitInterval → (ι × (ι → Bool)) × (Finset ι × Finset ι),
      Measurable (Function.uncurry f) ∧
      (∀ b u, 0 < (integerOwnerPlanLaw b (p b) (hp0 b) (hp1 b) (K b)).mass (f b u)) ∧
      ∀ b, volume.map (f b) =
        FiniteLaw.probabilityMeasure (integerOwnerPlanLaw b (p b) (hp0 b) (hp1 b) (K b)) :=
  Hybrid.exists_support_sampler
    (fun b => integerOwnerPlanLaw b (p b) (hp0 b) (hp1 b) (K b))
    (measurable_integerOwnerPlanLaw_mass p hp0 hp1 hp K hK)

end FCAppendix.Affine.Tail04
