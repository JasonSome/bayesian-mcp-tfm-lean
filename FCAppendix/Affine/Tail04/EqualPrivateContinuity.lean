import FCAppendix.Affine.Tail04.EqualPrivateFrontier

noncomputable section
namespace FCAppendix.Affine.Tail04.EqualPrivateContinuity
open TopologicalSpace
open MeasureTheory ProbabilityTheory Set Classical
open scoped BigOperators
open EqualPrivateFrontier

variable {ι T A : Type*} [Fintype ι]
  [TopologicalSpace T] [MeasurableSpace T] [CompactSpace T]
  [PolishSpace T] [BorelSpace T]
  [TopologicalSpace A] [MeasurableSpace A] [CompactSpace A]
  [MetrizableSpace A] [BorelSpace A] [Nonempty A] [StandardBorelSpace A]
  [Fintype A]

abbrev Joint := ProbabilityMeasure (T × A)

def ambientMean (π : Joint (T := T) (A := A)) (f : C(T × A, ℝ)) : ℝ :=
  ∫ z, f z ∂(π : Measure (T × A))

def ambientMarginal (x : ι → C(T × A, ℝ)) (π : Joint (T := T) (A := A)) : ι → ℝ :=
  fun i => ambientMean π (x i)

omit [Fintype ι] [PolishSpace T] [Nonempty A] [StandardBorelSpace A] in
lemma continuous_ambientMarginal (x : ι → C(T × A, ℝ)) :
    Continuous (ambientMarginal x) :=
  continuous_pi fun i => ProbabilityMeasure.continuous_integral_continuousMap (x i)

def firstMarginal (π : Joint (T := T) (A := A)) : ProbabilityMeasure T :=
  π.map measurable_fst.aemeasurable

omit [CompactSpace T] [PolishSpace T] [CompactSpace A] [Nonempty A] [StandardBorelSpace A] in
lemma continuous_firstMarginal :
    Continuous (firstMarginal : Joint (T := T) (A := A) → ProbabilityMeasure T) :=
  ProbabilityMeasure.continuous_map continuous_fst

abbrev Environment := (ι → ℝ) × Joint (T := T) (A := A)

def utility (x : ι → C(T × A, ℝ)) (r : C(T × A, ℝ)) (ξ : ℝ)
    (p : Environment (ι := ι) (T := T) (A := A)) (z : T × A) : ℝ :=
  score x r p.1 (ambientMarginal x p.2) ξ z

omit [PolishSpace T] [Nonempty A] [StandardBorelSpace A] in
lemma continuous_utility (x : ι → C(T × A, ℝ)) (r : C(T × A, ℝ)) (ξ : ℝ) :
    Continuous (fun p : Environment (ι := ι) (T := T) (A := A) × (T × A) =>
      utility x r ξ p.1 p.2) := by
  unfold utility score
  simp only [ContinuousMap.add_apply,ContinuousMap.sum_apply,
    ContinuousMap.smul_apply,smul_eq_mul]
  apply (r.continuous.comp continuous_snd).add
  apply continuous_finsetSum
  intro i _
  exact (((continuous_apply i).comp (continuous_fst.comp continuous_fst)).mul
    (continuous_const.sub (continuous_const.mul
      ((continuous_apply i).comp ((continuous_ambientMarginal x).comp
        (continuous_snd.comp continuous_fst)))))).mul
    ((x i).continuous.comp continuous_snd)

def bestValue (x : ι → C(T × A, ℝ)) (r : C(T × A, ℝ)) (ξ : ℝ)
    (p : Environment (ι := ι) (T := T) (A := A)) (t : T) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a => utility x r ξ p (t,a))

omit [CompactSpace T] [PolishSpace T] [BorelSpace T] [CompactSpace A] [MetrizableSpace A] [BorelSpace A] [StandardBorelSpace A] in
lemma utility_le_bestValue (x : ι → C(T × A, ℝ)) (r : C(T × A, ℝ)) (ξ : ℝ)
    (p : Environment (ι := ι) (T := T) (A := A)) (z : T × A) :
    utility x r ξ p z ≤ bestValue x r ξ p z.1 :=
  Finset.le_sup' (fun a => utility x r ξ p (z.1,a)) (Finset.mem_univ z.2)

omit [PolishSpace T] [StandardBorelSpace A] in
lemma continuous_bestValue (x : ι → C(T × A, ℝ)) (r : C(T × A, ℝ)) (ξ : ℝ) :
    Continuous (fun p : Environment (ι := ι) (T := T) (A := A) × T =>
      bestValue x r ξ p.1 p.2) := by
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro a _
  exact (continuous_utility x r ξ).comp
    (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))

def regret (x : ι → C(T × A, ℝ)) (r : C(T × A, ℝ)) (ξ : ℝ)
    (p : Environment (ι := ι) (T := T) (A := A)) (z : T × A) : ℝ :=
  bestValue x r ξ p z.1-utility x r ξ p z

omit [CompactSpace T] [PolishSpace T] [BorelSpace T] [CompactSpace A] [MetrizableSpace A] [BorelSpace A] [StandardBorelSpace A] in
lemma regret_nonneg (x : ι → C(T × A, ℝ)) (r : C(T × A, ℝ)) (ξ : ℝ)
    (p : Environment (ι := ι) (T := T) (A := A)) (z : T × A) :
    0 ≤ regret x r ξ p z :=
  sub_nonneg.mpr (utility_le_bestValue x r ξ p z)

omit [PolishSpace T] [StandardBorelSpace A] in
lemma continuous_regret (x : ι → C(T × A, ℝ)) (r : C(T × A, ℝ)) (ξ : ℝ) :
    Continuous (fun p : Environment (ι := ι) (T := T) (A := A) × (T × A) =>
      regret x r ξ p.1 p.2) :=
  ((continuous_bestValue x r ξ).comp
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).sub
      (continuous_utility x r ξ)

def gap (x : ι → C(T × A, ℝ)) (r : C(T × A, ℝ)) (ξ : ℝ)
    (p : Environment (ι := ι) (T := T) (A := A)) : ℝ :=
  ∫ z, regret x r ξ p z ∂(p.2 : Measure (T × A))

omit [PolishSpace T] [StandardBorelSpace A] in
lemma continuous_gap (x : ι → C(T × A, ℝ)) (r : C(T × A, ℝ)) (ξ : ℝ) :
    Continuous (gap x r ξ) :=
  (Existence.Distributional.continuous_law_integral
    (fun p => regret x r ξ p.1 p.2) (continuous_regret x r ξ)).comp
      (continuous_id.prodMk continuous_snd)

omit [CompactSpace T] [PolishSpace T] [BorelSpace T] [CompactSpace A] [MetrizableSpace A] [BorelSpace A] [StandardBorelSpace A] in
lemma gap_eq_zero_of_allAction (x : ι → C(T × A, ℝ))
    (r : C(T × A, ℝ)) (b : ι → ℝ) (ξ : ℝ)
    (μ : Measure T) (π : Plan (A := A) μ)
    (hπ : Existence.Distributional.AllActionOptimal π
      (score x r b (marginal x π) ξ)) : gap x r ξ (b,π.1) = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [hπ] with z hz
  have hmax : bestValue x r ξ (b,π.1) z.1 ≤ utility x r ξ (b,π.1) z :=
    Finset.sup'_le Finset.univ_nonempty _ (fun a _ => hz a)
  exact sub_eq_zero.mpr (le_antisymm hmax (utility_le_bestValue x r ξ (b,π.1) z))

omit [CompactSpace T] [PolishSpace T] [TopologicalSpace A] [CompactSpace A] [MetrizableSpace A] [BorelSpace A] [Nonempty A] [StandardBorelSpace A] [Fintype A] in
lemma fixed_marginal_integral (μ : Measure T)
    (π τ : Plan (A := A) μ) (f : C(T,ℝ)) :
    (∫ z, f z.1 ∂(π.1 : Measure (T × A))) =
      ∫ z, f z.1 ∂(τ.1 : Measure (T × A)) := by
  have hp := integral_map measurable_fst.aemeasurable f.continuous.aestronglyMeasurable
    (μ := (π.1 : Measure (T × A)))
  have ht := integral_map measurable_fst.aemeasurable f.continuous.aestronglyMeasurable
    (μ := (τ.1 : Measure (T × A)))
  rw [π.2] at hp
  rw [τ.2] at ht
  exact hp.symm.trans ht

set_option maxHeartbeats 800000 in
omit [PolishSpace T] [StandardBorelSpace A] in
lemma integralOptimal_of_gap_eq_zero (x : ι → C(T × A, ℝ))
    (r : C(T × A, ℝ)) (b : ι → ℝ) (ξ : ℝ)
    (μ : Measure T) (π : Plan (A := A) μ)
    (hgap : gap x r ξ (b,π.1) = 0) :
    Existence.Distributional.IntegralOptimal π
      (score x r b (marginal x π) ξ) := by
  let B : Environment (ι := ι) (T := T) (A := A) × T → ℝ :=
    fun z => bestValue x r ξ z.1 z.2
  have hB : Continuous B := continuous_bestValue x r ξ
  have hmB : Continuous (fun t : T => ((b,π.1),t)) :=
    continuous_const.prodMk continuous_id
  have hvmax := hB.comp hmB
  let vmax : C(T,ℝ) := ⟨bestValue x r ξ (b,π.1), hvmax⟩
  let high : C(T × A,ℝ) := ⟨fun z => vmax z.1,vmax.continuous.comp continuous_fst⟩
  let u : C(T × A,ℝ) := score x r b (marginal x π) ξ
  have he : mean π high = mean π u := by
    change (∫ z, high z-u z ∂(π.1 : Measure (T × A))) = 0 at hgap
    rw [integral_sub (integrable_test π high) (integrable_test π u)] at hgap
    exact sub_eq_zero.mp hgap
  intro τ
  have hbound : mean τ u ≤ mean τ high :=
    integral_mono (integrable_test τ u) (integrable_test τ high)
      (fun z => utility_le_bestValue x r ξ (b,π.1) z)
  have hm : mean τ high = mean π high := fixed_marginal_integral μ τ π vmax
  exact hbound.trans_eq (hm.trans he)

theorem continuous_unique_compact_factor {P K Z : Type*}
    [TopologicalSpace P] [TopologicalSpace K] [CompactSpace K] [TopologicalSpace Z]
    (G : Set (P × K)) (hG : IsClosed G) (value : K → Z) (hv : Continuous value)
    (f : P → Z) (hne : ∀ p, ∃ k, (p,k) ∈ G)
    (hunique : ∀ p k, (p,k) ∈ G → value k = f p) : Continuous f := by
  apply continuous_iff_isClosed.mpr
  intro C hC
  let S : Set (P × K) := G ∩ (fun p => value p.2) ⁻¹' C
  have hS : IsClosed S := hG.inter (hC.preimage (hv.comp continuous_snd))
  have he : f ⁻¹' C = Prod.fst '' S := by
    ext p
    constructor
    · intro hp
      obtain ⟨k,hk⟩ := hne p
      have hvk : value k ∈ C := by rw [hunique p k hk];exact hp
      exact ⟨(p,k),⟨hk,hvk⟩,rfl⟩
    · rintro ⟨⟨p',k⟩,⟨hk,hCk⟩,heq⟩
      change p' = p at heq
      subst p'
      change value k∈C at hCk
      change f p∈C
      rwa [hunique p k hk] at hCk
  rw [he]
  exact isClosedMap_fst_of_compactSpace S hS

abbrev Parameter (ι T : Type*) [TopologicalSpace T] [MeasurableSpace T]
    (lo hi : ℝ) := (ι → Icc lo hi) × ProbabilityMeasure T

def parameterBids {lo hi : ℝ} (p : Parameter ι T lo hi) : ι → ℝ := fun i => (p.1 i).1

def chosenPlan (x : ι → C(T × A, ℝ)) (r : C(T × A, ℝ)) (ξ : ℝ)
    {lo hi : ℝ} (p : Parameter ι T lo hi) :
    Plan (A := A) (p.2 : Measure T) :=
  (exists_equal_private_continuation (p.2 : Measure T) x r (parameterBids p) ξ).choose

def chosenMarginal (x : ι → C(T × A, ℝ)) (r : C(T × A, ℝ)) (ξ : ℝ)
    {lo hi : ℝ} (p : Parameter ι T lo hi) : ι → ℝ :=
  marginal x (chosenPlan x r ξ p)

lemma chosenPlan_gap (x : ι → C(T × A, ℝ)) (r : C(T × A, ℝ)) (ξ : ℝ)
    {lo hi : ℝ} (p : Parameter ι T lo hi) :
    gap x r ξ (parameterBids p,(chosenPlan x r ξ p).1) = 0 := by
  have hs := (exists_equal_private_continuation (p.2 : Measure T)
    x r (parameterBids p) ξ).choose_spec
  obtain ⟨σ,hσ,hdis,hmax,hopt,hall,hlocal⟩ := hs
  exact gap_eq_zero_of_allAction x r (parameterBids p) ξ _ _ hall

theorem continuous_chosenMarginal (x : ι → C(T × A, ℝ)) (r : C(T × A, ℝ))
    (ξ lo hi : ℝ) (hξ : 0 < ξ) (hlo : 0 < lo) :
    Continuous (chosenMarginal (T := T) (A := A) x r ξ
      (lo := lo) (hi := hi)) := by
  let P := Parameter ι T lo hi
  let G : Set (P × Joint (T := T) (A := A)) :=
    {z | firstMarginal z.2 = z.1.2 ∧ gap x r ξ (parameterBids z.1,z.2) = 0}
  have hb : Continuous (parameterBids : P → ι → ℝ) :=
    continuous_pi fun i => continuous_subtype_val.comp
      ((continuous_apply i).comp continuous_fst)
  have hG : IsClosed G :=
    (isClosed_eq (continuous_firstMarginal.comp continuous_snd)
      (continuous_snd.comp continuous_fst)).inter
    (isClosed_eq ((continuous_gap x r ξ).comp
      ((hb.comp continuous_fst).prodMk continuous_snd)) continuous_const)
  have hne : ∀ p : P, ∃ π : Joint (T := T) (A := A), (p,π) ∈ G := by
    intro p
    refine ⟨(chosenPlan x r ξ p).1,?_,chosenPlan_gap x r ξ p⟩
    apply ProbabilityMeasure.toMeasure_injective
    exact (chosenPlan x r ξ p).2
  have huniq : ∀ p π, (p,π) ∈ G →
      ambientMarginal x π = chosenMarginal x r ξ p := by
    intro p π hπ
    have hfst : (π : Measure (T × A)).map Prod.fst = (p.2 : Measure T) :=
      congrArg (fun μ : ProbabilityMeasure T => (μ : Measure T)) hπ.1
    let τ : Plan (A := A) (p.2 : Measure T) := ⟨π,hfst⟩
    let χ := chosenPlan x r ξ p
    have hτ := integralOptimal_of_gap_eq_zero x r (parameterBids p) ξ
      (p.2 : Measure T) τ hπ.2
    have hχ := integralOptimal_of_gap_eq_zero x r (parameterBids p) ξ
      (p.2 : Measure T) χ (chosenPlan_gap x r ξ p)
    exact marginal_unique (p.2 : Measure T) x r (parameterBids p) ξ hξ
      (fun i => hlo.trans_le (p.1 i).2.1) τ χ hτ hχ
  exact continuous_unique_compact_factor G hG (ambientMarginal x)
    (continuous_ambientMarginal x) (chosenMarginal x r ξ) hne huniq

theorem continuous_unique_compact_response {P K Z : Type*}
    [TopologicalSpace P] [TopologicalSpace K] [CompactSpace K] [TopologicalSpace Z]
    (G : Set (P × K)) (hG : IsClosed G) (value : P × K → Z) (hv : Continuous value)
    (f : P → Z) (hne : ∀ p, ∃ k, (p,k) ∈ G)
    (hunique : ∀ p k, (p,k) ∈ G → value (p,k) = f p) : Continuous f := by
  apply continuous_iff_isClosed.mpr
  intro C hC
  let S : Set (P × K) := G ∩ value ⁻¹' C
  have hS : IsClosed S := hG.inter (hC.preimage hv)
  have he : f ⁻¹' C = Prod.fst '' S := by
    ext p
    constructor
    · intro hp
      obtain ⟨k,hk⟩ := hne p
      have hvk : value (p,k) ∈ C := by rw [hunique p k hk];exact hp
      exact ⟨(p,k),⟨hk,hvk⟩,rfl⟩
    · rintro ⟨⟨p',k⟩,⟨hk,hCk⟩,heq⟩
      change p'=p at heq
      subst p'
      change value (p,k)∈C at hCk
      change f p∈C
      rwa [hunique p k hk] at hCk
  rw [he]
  exact isClosedMap_fst_of_compactSpace S hS

end FCAppendix.Affine.Tail04.EqualPrivateContinuity
