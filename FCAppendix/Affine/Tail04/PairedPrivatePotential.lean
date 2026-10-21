import FCAppendix.Affine.Tail04.EqualPrivateFrontier

noncomputable section
namespace FCAppendix.Affine.Tail04.PairedPrivatePotential
open TopologicalSpace
open MeasureTheory ProbabilityTheory Set Classical
open scoped BigOperators
open EqualPrivateFrontier

variable {ι T0 T1 A0 A1 : Type*} [Fintype ι]
  [TopologicalSpace T0] [MeasurableSpace T0] [CompactSpace T0] [PolishSpace T0] [BorelSpace T0]
  [TopologicalSpace T1] [MeasurableSpace T1] [CompactSpace T1] [PolishSpace T1] [BorelSpace T1]
  [TopologicalSpace A0] [MeasurableSpace A0] [CompactSpace A0] [MetrizableSpace A0]
    [BorelSpace A0] [Nonempty A0] [StandardBorelSpace A0]
  [TopologicalSpace A1] [MeasurableSpace A1] [CompactSpace A1] [MetrizableSpace A1]
    [BorelSpace A1] [Nonempty A1] [StandardBorelSpace A1]

variable (x0 : ι → C(T0×A0,ℝ)) (x1 : ι → C(T1×A1,ℝ))
  (r0 : C(T0×A0,ℝ)) (r1 : C(T1×A1,ℝ)) (b : ι → ℝ) (ξ : ℝ)

variable (μ0 : Measure T0) [IsProbabilityMeasure μ0]
  (μ1 : Measure T1) [IsProbabilityMeasure μ1]

def pairPotential (π : Plan (A:=A0) μ0 × Plan (A:=A1) μ1) : ℝ :=
  (∑ i,b i*(marginal x0 π.1 i+marginal x1 π.2 i-
    ξ*marginal x0 π.1 i*marginal x1 π.2 i))+mean π.1 r0+mean π.2 r1

omit [PolishSpace T0] [PolishSpace T1] [Nonempty A0] [StandardBorelSpace A0] [Nonempty A1] [StandardBorelSpace A1] [IsProbabilityMeasure μ0] [IsProbabilityMeasure μ1] in
lemma continuous_pairPotential : Continuous (pairPotential x0 x1 r0 r1 b ξ μ0 μ1) := by
  apply Continuous.add
  · apply Continuous.add
    · apply continuous_finsetSum
      intro i _
      have h0 : Continuous (fun π : Plan (A:=A0) μ0 × Plan (A:=A1) μ1 => mean π.1 (x0 i)) :=
        (continuous_mean μ0 (x0 i)).comp continuous_fst
      have h1 : Continuous (fun π : Plan (A:=A0) μ0 × Plan (A:=A1) μ1 => mean π.2 (x1 i)) :=
        (continuous_mean μ1 (x1 i)).comp continuous_snd
      exact continuous_const.mul ((h0.add h1).sub ((continuous_const.mul h0).mul h1))
    · exact (continuous_mean μ0 r0).comp continuous_fst
  · exact (continuous_mean μ1 r1).comp continuous_snd

include A0 A1 x0 x1 r0 r1 b ξ μ0 μ1 in
omit [PolishSpace T0] [CompactSpace T1] [PolishSpace T1] [BorelSpace T1] [Nonempty A0] [StandardBorelSpace A0] [CompactSpace A1] [MetrizableSpace A1] [BorelSpace A1] [Nonempty A1] [StandardBorelSpace A1] [IsProbabilityMeasure μ0] [IsProbabilityMeasure μ1] in
lemma difference_zero (π0 τ0 : Plan (A:=A0) μ0) (π1 : Plan (A:=A1) μ1) :
    pairPotential x0 x1 r0 r1 b ξ μ0 μ1 (τ0,π1)-
      pairPotential x0 x1 r0 r1 b ξ μ0 μ1 (π0,π1)=
      mean τ0 (score x0 r0 b (marginal x1 π1) ξ)-
        mean π0 (score x0 r0 b (marginal x1 π1) ξ) := by
  rw [mean_score,mean_score]
  unfold pairPotential
  have hs : (∑ i,b i*(marginal x0 τ0 i+marginal x1 π1 i-
      ξ*marginal x0 τ0 i*marginal x1 π1 i))-
      (∑ i,b i*(marginal x0 π0 i+marginal x1 π1 i-
        ξ*marginal x0 π0 i*marginal x1 π1 i))=
      (∑ i,b i*(1-ξ*marginal x1 π1 i)*marginal x0 τ0 i)-
      (∑ i,b i*(1-ξ*marginal x1 π1 i)*marginal x0 π0 i) := by
    rw [←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  linarith

include A0 A1 x0 x1 r0 r1 b ξ μ0 μ1 in
omit [CompactSpace T0] [PolishSpace T0] [BorelSpace T0] [PolishSpace T1] [CompactSpace A0] [MetrizableSpace A0] [BorelSpace A0] [Nonempty A0] [StandardBorelSpace A0] [Nonempty A1] [StandardBorelSpace A1] [IsProbabilityMeasure μ0] [IsProbabilityMeasure μ1] in
lemma difference_one (π0 : Plan (A:=A0) μ0) (π1 τ1 : Plan (A:=A1) μ1) :
    pairPotential x0 x1 r0 r1 b ξ μ0 μ1 (π0,τ1)-
      pairPotential x0 x1 r0 r1 b ξ μ0 μ1 (π0,π1)=
      mean τ1 (score x1 r1 b (marginal x0 π0) ξ)-
        mean π1 (score x1 r1 b (marginal x0 π0) ξ) := by
  rw [mean_score,mean_score]
  unfold pairPotential
  have hs : (∑ i,b i*(marginal x0 π0 i+marginal x1 τ1 i-
      ξ*marginal x0 π0 i*marginal x1 τ1 i))-
      (∑ i,b i*(marginal x0 π0 i+marginal x1 π1 i-
        ξ*marginal x0 π0 i*marginal x1 π1 i))=
      (∑ i,b i*(1-ξ*marginal x0 π0 i)*marginal x1 τ1 i)-
      (∑ i,b i*(1-ξ*marginal x0 π0 i)*marginal x1 π1 i) := by
    rw [←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  linarith

include A0 A1 x0 x1 r0 r1 b ξ μ0 μ1 in
omit [StandardBorelSpace A0] [StandardBorelSpace A1] in
theorem exists_paired_plans :
    ∃ (π0 : Plan (A:=A0) μ0) (π1 : Plan (A:=A1) μ1),
      Existence.Distributional.IntegralOptimal π0
        (score x0 r0 b (marginal x1 π1) ξ) ∧
      Existence.Distributional.IntegralOptimal π1
        (score x1 r1 b (marginal x0 π0) ξ) ∧
      Existence.Distributional.AllActionOptimal π0
        (score x0 r0 b (marginal x1 π1) ξ) ∧
      Existence.Distributional.AllActionOptimal π1
        (score x1 r1 b (marginal x0 π0) ξ) := by
  obtain ⟨π,hπ,hmax⟩ := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty : (Set.univ : Set (Plan (A:=A0) μ0 × Plan (A:=A1) μ1)).Nonempty)
    (continuous_pairPotential x0 x1 r0 r1 b ξ μ0 μ1).continuousOn
  have h0 : Existence.Distributional.IntegralOptimal π.1
      (score x0 r0 b (marginal x1 π.2) ξ) := by
    intro τ
    have hmax0 : pairPotential x0 x1 r0 r1 b ξ μ0 μ1 (τ,π.2) ≤
        pairPotential x0 x1 r0 r1 b ξ μ0 μ1 π := hmax (Set.mem_univ (τ,π.2))
    have h := sub_nonpos.mpr hmax0
    rw [difference_zero] at h
    exact sub_nonpos.mp h
  have h1 : Existence.Distributional.IntegralOptimal π.2
      (score x1 r1 b (marginal x0 π.1) ξ) := by
    intro τ
    have hmax1 : pairPotential x0 x1 r0 r1 b ξ μ0 μ1 (π.1,τ) ≤
        pairPotential x0 x1 r0 r1 b ξ μ0 μ1 π := hmax (Set.mem_univ (π.1,τ))
    have h := sub_nonpos.mpr hmax1
    rw [difference_one] at h
    exact sub_nonpos.mp h
  exact ⟨π.1,π.2,h0,h1,
    Existence.Distributional.allAction_of_integralOptimal μ0 π.1 _
      (score x0 r0 b (marginal x1 π.2) ξ).continuous h0,
    Existence.Distributional.allAction_of_integralOptimal μ1 π.2 _
      (score x1 r1 b (marginal x0 π.1) ξ).continuous h1⟩

end FCAppendix.Affine.Tail04.PairedPrivatePotential
