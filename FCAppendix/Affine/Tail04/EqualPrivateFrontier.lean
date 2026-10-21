import FCAppendix.Existence.R01Distributional

noncomputable section
namespace FCAppendix.Affine.Tail04.EqualPrivateFrontier
open TopologicalSpace

open MeasureTheory ProbabilityTheory Set Classical
open scoped BigOperators ENNReal

variable {ι T A : Type*} [Fintype ι]
  [TopologicalSpace T] [MeasurableSpace T] [CompactSpace T]
  [PolishSpace T] [BorelSpace T]
  [TopologicalSpace A] [MeasurableSpace A] [CompactSpace A]
  [MetrizableSpace A] [BorelSpace A] [Nonempty A]

abbrev Plan (μ : Measure T) := Existence.Distributional.Law (A := A) μ

def mean {μ : Measure T} (π : Plan (A := A) μ) (f : C(T × A, ℝ)) : ℝ :=
  ∫ x, f x ∂(π.1 : Measure (T × A))

omit [PolishSpace T] [Nonempty A] in
lemma integrable_test {μ : Measure T} (π : Plan (A := A) μ)
    (f : C(T × A, ℝ)) : Integrable (fun x => f x) (π.1 : Measure (T × A)) := by
  refine ⟨f.continuous.aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := ‖f‖) ?_⟩
  exact ae_of_all _ fun x => f.norm_coe_le_norm x

omit [PolishSpace T] [Nonempty A] in
lemma continuous_mean (μ : Measure T) (f : C(T × A, ℝ)) :
    Continuous (fun π : Plan (A := A) μ => mean π f) :=
  (ProbabilityMeasure.continuous_integral_continuousMap f).comp continuous_subtype_val

omit [PolishSpace T] [Nonempty A] in
lemma mean_add {μ : Measure T} (π : Plan (A := A) μ)
    (f g : C(T × A, ℝ)) : mean π (f + g) = mean π f + mean π g := by
  exact integral_add (integrable_test π f) (integrable_test π g)

omit [CompactSpace T] [PolishSpace T] [BorelSpace T] [CompactSpace A] [MetrizableSpace A] [BorelSpace A] [Nonempty A] in
lemma mean_smul {μ : Measure T} (π : Plan (A := A) μ)
    (a : ℝ) (f : C(T × A, ℝ)) : mean π (a • f) = a * mean π f := by
  exact integral_const_mul a _

omit [Fintype ι] [PolishSpace T] [Nonempty A] in
lemma mean_sum {μ : Measure T} (π : Plan (A := A) μ)
    (s : Finset ι) (f : ι → C(T × A, ℝ)) :
    mean π (∑ i ∈ s, f i) = ∑ i ∈ s, mean π (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mean]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, mean_add, ih]

def marginal {μ : Measure T} (x : ι → C(T × A, ℝ))
    (π : Plan (A := A) μ) : ι → ℝ := fun i => mean π (x i)

def potential {μ : Measure T} (x : ι → C(T × A, ℝ))
    (privateReceipt : C(T × A, ℝ)) (b : ι → ℝ) (ξ : ℝ)
    (π : Plan (A := A) μ) : ℝ :=
  (∑ i, b i * (marginal x π i - ξ * marginal x π i ^ 2 / 2)) +
    mean π privateReceipt

def score (x : ι → C(T × A, ℝ)) (privateReceipt : C(T × A, ℝ))
    (b q : ι → ℝ) (ξ : ℝ) : C(T × A, ℝ) :=
  privateReceipt + ∑ i, (b i * (1 - ξ * q i)) • x i

omit [PolishSpace T] [Nonempty A] in
lemma mean_score {μ : Measure T} (π : Plan (A := A) μ)
    (x : ι → C(T × A, ℝ)) (privateReceipt : C(T × A, ℝ))
    (b q : ι → ℝ) (ξ : ℝ) :
    mean π (score x privateReceipt b q ξ) =
      mean π privateReceipt + ∑ i, b i * (1 - ξ * q i) * marginal x π i := by
  rw [score, mean_add, mean_sum]
  simp only [mean_smul, marginal]

omit [PolishSpace T] [Nonempty A] in
lemma continuous_potential (μ : Measure T) (x : ι → C(T × A, ℝ))
    (privateReceipt : C(T × A, ℝ)) (b : ι → ℝ) (ξ : ℝ) :
    Continuous (potential (μ := μ) x privateReceipt b ξ) := by
  exact (continuous_finsetSum _ fun i _ =>
    continuous_const.mul ((continuous_mean μ (x i)).sub
      ((continuous_const.mul ((continuous_mean μ (x i)).pow 2)).div_const 2))).add
        (continuous_mean μ privateReceipt)

variable (μ : Measure T) [IsProbabilityMeasure μ]

def mix (π τ : Plan (A := A) μ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Plan (A := A) μ :=
  (Existence.Distributional.law_mix μ π τ (ENNReal.ofReal (1-t)) (ENNReal.ofReal t)
    (by rw [← ENNReal.ofReal_add (by linarith) ht0]; norm_num)).choose

omit [TopologicalSpace T] [CompactSpace T] [PolishSpace T] [BorelSpace T] [TopologicalSpace A] [CompactSpace A] [MetrizableSpace A] [BorelSpace A] [Nonempty A] in
lemma mix_measure (π τ : Plan (A := A) μ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((mix μ π τ t ht0 ht1).1 : Measure (T × A)) =
      ENNReal.ofReal (1-t) • (π.1 : Measure (T × A)) +
        ENNReal.ofReal t • (τ.1 : Measure (T × A)) :=
  (Existence.Distributional.law_mix μ π τ (ENNReal.ofReal (1-t)) (ENNReal.ofReal t)
    (by rw [← ENNReal.ofReal_add (by linarith) ht0]; norm_num)).choose_spec

omit [PolishSpace T] [Nonempty A] in
lemma mean_mix (π τ : Plan (A := A) μ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (f : C(T × A, ℝ)) :
    mean (mix μ π τ t ht0 ht1) f = (1-t) * mean π f + t * mean τ f := by
  unfold mean
  rw [mix_measure, integral_add_measure
    ((integrable_test π f).smul_measure (by simp))
    ((integrable_test τ f).smul_measure (by simp)),
    integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal (by linarith : 0 ≤ 1-t), ENNReal.toReal_ofReal ht0]
  simp only [smul_eq_mul]

omit [PolishSpace T] [Nonempty A] in
lemma potential_mix_sub (x : ι → C(T × A, ℝ))
    (privateReceipt : C(T × A, ℝ)) (b : ι → ℝ) (ξ : ℝ)
    (π τ : Plan (A := A) μ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    potential x privateReceipt b ξ (mix μ π τ t ht0 ht1) -
      potential x privateReceipt b ξ π =
    t * (mean τ (score x privateReceipt b (marginal x π) ξ) -
      mean π (score x privateReceipt b (marginal x π) ξ)) -
    t^2 * (ξ / 2 * ∑ i, b i * (marginal x τ i - marginal x π i)^2) := by
  have hmain :
      (∑ i, b i * (marginal x (mix μ π τ t ht0 ht1) i -
        ξ * marginal x (mix μ π τ t ht0 ht1) i ^ 2 / 2)) -
        (∑ i, b i * (marginal x π i - ξ * marginal x π i ^ 2 / 2)) =
      (∑ i, (t * (b i * (1-ξ*marginal x π i) *
        (marginal x τ i-marginal x π i)) -
        t^2 * (ξ/2 * b i * (marginal x τ i-marginal x π i)^2))) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [marginal, mean_mix]
    ring
  unfold potential
  rw [add_sub_add_comm, hmain, mean_mix, mean_score, mean_score]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum,
    mul_assoc]
  simp_rw [mul_sub, sub_mul, Finset.sum_sub_distrib]
  ring

lemma first_variation_nonpos (a d : ℝ)
    (h : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t*a-t^2*d ≤ 0) : a ≤ 0 := by
  by_contra hn
  have ha : 0 < a := lt_of_not_ge hn
  let D := a + |d| + 1
  have hD : 0 < D := by dsimp [D]; positivity
  let t := a / D
  have ht : 0 < t := div_pos ha hD
  have ht1 : t ≤ 1 := (div_le_one hD).mpr (by dsimp [D]; linarith [abs_nonneg d])
  have hh := h t ht.le ht1
  have hcancel : a ≤ t*d := (mul_le_mul_iff_right₀ ht).mp (by nlinarith [hh])
  have hdD : d < D := by dsimp [D]; linarith [le_abs_self d]
  have htd : t*d < t*D := mul_lt_mul_of_pos_left hdD ht
  have he : t*D = a := div_mul_cancel₀ a hD.ne'
  rw [he] at htd
  exact (not_lt_of_ge hcancel) htd

omit [PolishSpace T] [Nonempty A] in
theorem integralOptimal_of_potential_max (x : ι → C(T × A, ℝ))
    (privateReceipt : C(T × A, ℝ)) (b : ι → ℝ) (ξ : ℝ)
    (π : Plan (A := A) μ)
    (hπ : ∀ τ : Plan (A:=A) μ, potential x privateReceipt b ξ τ ≤ potential x privateReceipt b ξ π) :
    Existence.Distributional.IntegralOptimal π
      (score x privateReceipt b (marginal x π) ξ) := by
  intro τ
  apply sub_nonpos.mp
  apply first_variation_nonpos _ (ξ/2 * ∑ i, b i * (marginal x τ i-marginal x π i)^2)
  intro t ht0 ht1
  have hm := sub_nonpos.mpr (hπ (mix μ π τ t ht0 ht1))
  rwa [potential_mix_sub] at hm

theorem exists_equal_private_continuation [StandardBorelSpace A]
    (x : ι → C(T × A, ℝ)) (privateReceipt : C(T × A, ℝ))
    (b : ι → ℝ) (ξ : ℝ) :
    ∃ (π : Plan (A := A) μ) (σ : Kernel T A),
      IsMarkovKernel σ ∧
      μ ⊗ₘ σ = (π.1 : Measure (T × A)) ∧
      (∀ τ : Plan (A:=A) μ, potential x privateReceipt b ξ τ ≤ potential x privateReceipt b ξ π) ∧
      Existence.Distributional.IntegralOptimal π
        (score x privateReceipt b (marginal x π) ξ) ∧
      Existence.Distributional.AllActionOptimal π
        (score x privateReceipt b (marginal x π) ξ) ∧
      (∀ᵐ t ∂μ, ∀ᵐ a ∂σ t, ∀ a' : A,
        score x privateReceipt b (marginal x π) ξ (t,a') ≤
          score x privateReceipt b (marginal x π) ξ (t,a)) := by
  obtain ⟨π, _, hmax⟩ := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty : (Set.univ : Set (Plan (A := A) μ)).Nonempty)
      (continuous_potential μ x privateReceipt b ξ).continuousOn
  have hp : ∀ τ : Plan (A:=A) μ, potential x privateReceipt b ξ τ ≤ potential x privateReceipt b ξ π :=
    fun τ => hmax (Set.mem_univ τ)
  have hopt := integralOptimal_of_potential_max μ x privateReceipt b ξ π hp
  have hall := Existence.Distributional.allAction_of_integralOptimal μ π
    (score x privateReceipt b (marginal x π) ξ)
      (score x privateReceipt b (marginal x π) ξ).continuous hopt
  obtain ⟨σ,hσ,hdis,hlocal⟩ := Existence.Distributional.disintegrate_allAction μ π
    (score x privateReceipt b (marginal x π) ξ)
      (score x privateReceipt b (marginal x π) ξ).continuous hall
  exact ⟨π,σ,hσ,hdis,hp,hopt,hall,hlocal⟩

def MeanFiber (x : ι → C(T × A, ℝ)) (q : ι → ℝ) : Set (Plan (A := A) μ) :=
  {π | marginal x π = q}

omit [Fintype ι] [IsProbabilityMeasure μ] [PolishSpace T] [Nonempty A] in
lemma isClosed_meanFiber (x : ι → C(T × A, ℝ)) (q : ι → ℝ) :
    IsClosed (MeanFiber μ x q) :=
  isClosed_eq (continuous_pi fun i => continuous_mean μ (x i)) continuous_const

omit [Fintype ι] [Nonempty A] in
lemma isCompact_meanFiber (x : ι → C(T × A, ℝ)) (q : ι → ℝ) :
    IsCompact (MeanFiber μ x q) := (isClosed_meanFiber μ x q).isCompact

def MeanFeasible (x : ι → C(T × A, ℝ)) (q : ι → ℝ) : Prop :=
  (MeanFiber μ x q).Nonempty

omit [Fintype ι] [Nonempty A] in
theorem exists_frontier_plan (x : ι → C(T × A, ℝ))
    (privateReceipt : C(T × A, ℝ)) (q : ι → ℝ) (hq : MeanFeasible μ x q) :
    ∃ π : Plan (A := A) μ, marginal x π = q ∧
      ∀ τ : Plan (A := A) μ, marginal x τ = q → mean τ privateReceipt ≤ mean π privateReceipt := by
  obtain ⟨π,hπ,hmax⟩ := (isCompact_meanFiber μ x q).exists_isMaxOn hq
    (continuous_mean μ privateReceipt).continuousOn
  exact ⟨π,hπ,fun τ hτ => hmax hτ⟩

def frontierPlan (x : ι → C(T × A, ℝ)) (privateReceipt : C(T × A, ℝ))
    (q : ι → ℝ) (hq : MeanFeasible μ x q) : Plan (A := A) μ :=
  (exists_frontier_plan μ x privateReceipt q hq).choose

omit [Fintype ι] [Nonempty A] in
lemma frontierPlan_spec (x : ι → C(T × A, ℝ)) (privateReceipt : C(T × A, ℝ))
    (q : ι → ℝ) (hq : MeanFeasible μ x q) :
    marginal x (frontierPlan μ x privateReceipt q hq) = q ∧
      ∀ τ : Plan (A := A) μ, marginal x τ = q →
        mean τ privateReceipt ≤ mean (frontierPlan μ x privateReceipt q hq) privateReceipt :=
  (exists_frontier_plan μ x privateReceipt q hq).choose_spec

def frontier (x : ι → C(T × A, ℝ)) (privateReceipt : C(T × A, ℝ))
    (q : ι → ℝ) : ℝ :=
  if hq : MeanFeasible μ x q then mean (frontierPlan μ x privateReceipt q hq) privateReceipt
  else 0

omit [Fintype ι] [Nonempty A] in
lemma frontier_dominates (x : ι → C(T × A, ℝ))
    (privateReceipt : C(T × A, ℝ)) (π : Plan (A := A) μ) :
    mean π privateReceipt ≤ frontier μ x privateReceipt (marginal x π) := by
  have hq : MeanFeasible μ x (marginal x π) := ⟨π,rfl⟩
  rw [frontier, dif_pos hq]
  exact (frontierPlan_spec μ x privateReceipt _ hq).2 π rfl

omit [Fintype ι] [Nonempty A] in
theorem frontier_concave (x : ι → C(T × A, ℝ))
    (privateReceipt : C(T × A, ℝ)) (q r : ι → ℝ)
    (hq : MeanFeasible μ x q) (hr : MeanFeasible μ x r)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    MeanFeasible μ x (fun i => (1-t)*q i+t*r i) ∧
    (1-t)*frontier μ x privateReceipt q+t*frontier μ x privateReceipt r ≤
      frontier μ x privateReceipt (fun i => (1-t)*q i+t*r i) := by
  let π := frontierPlan μ x privateReceipt q hq
  let τ := frontierPlan μ x privateReceipt r hr
  have hπ := frontierPlan_spec μ x privateReceipt q hq
  have hτ := frontierPlan_spec μ x privateReceipt r hr
  have hmix : marginal x (mix μ π τ t ht0 ht1) = fun i => (1-t)*q i+t*r i := by
    funext i
    change mean (mix μ π τ t ht0 ht1) (x i) = _
    rw [mean_mix]
    change (1-t)*marginal x π i+t*marginal x τ i = _
    rw [hπ.1,hτ.1]
  refine ⟨⟨mix μ π τ t ht0 ht1,hmix⟩,?_⟩
  have hh := frontier_dominates μ x privateReceipt (mix μ π τ t ht0 ht1)
  rw [hmix, mean_mix] at hh
  simpa only [frontier, dif_pos hq, dif_pos hr, π, τ] using hh

omit [PolishSpace T] [Nonempty A] [IsProbabilityMeasure μ] in
theorem marginal_unique (x : ι → C(T × A, ℝ))
    (privateReceipt : C(T × A, ℝ)) (b : ι → ℝ) (ξ : ℝ)
    (hξ : 0 < ξ) (hb : ∀ i, 0 < b i)
    (π τ : Plan (A := A) μ)
    (hπ : Existence.Distributional.IntegralOptimal π
      (score x privateReceipt b (marginal x π) ξ))
    (hτ : Existence.Distributional.IntegralOptimal τ
      (score x privateReceipt b (marginal x τ) ξ)) :
    marginal x π = marginal x τ := by
  have h₁ := hπ τ
  have h₂ := hτ π
  change mean τ _ ≤ mean π _ at h₁
  change mean π _ ≤ mean τ _ at h₂
  rw [mean_score,mean_score] at h₁ h₂
  have hid :
      ((∑ i, b i*(1-ξ*marginal x π i)*marginal x π i) -
        (∑ i, b i*(1-ξ*marginal x π i)*marginal x τ i)) +
      ((∑ i, b i*(1-ξ*marginal x τ i)*marginal x τ i) -
        (∑ i, b i*(1-ξ*marginal x τ i)*marginal x π i)) =
      -ξ * ∑ i, b i*(marginal x π i-marginal x τ i)^2 := by
    rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hn : 0 ≤ ∑ i, b i*(marginal x π i-marginal x τ i)^2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hb i).le (sq_nonneg _)
  have he : (∑ i, b i*(marginal x π i-marginal x τ i)^2) = 0 := by
    nlinarith [hid]
  funext i
  have hi : b i*(marginal x π i-marginal x τ i)^2 ≤
      ∑ j, b j*(marginal x π j-marginal x τ j)^2 :=
    Finset.single_le_sum (fun j _ => mul_nonneg (hb j).le (sq_nonneg (marginal x π j-marginal x τ j)))
      (Finset.mem_univ i)
  rw [he] at hi
  have hzero : b i*(marginal x π i-marginal x τ i)^2=0 :=
    le_antisymm hi (mul_nonneg (hb i).le (sq_nonneg _))
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hzero).resolve_left (hb i).ne'))

omit [Fintype ι] [PolishSpace T] [Nonempty A] [IsProbabilityMeasure μ] in
lemma marginal_mem_Icc (x : ι → C(T × A, ℝ))
    (hx : ∀ i z, 0 ≤ x i z ∧ x i z ≤ 1)
    (π : Plan (A := A) μ) (i : ι) : marginal x π i ∈ Icc (0:ℝ) 1 := by
  constructor
  · exact integral_nonneg fun z => (hx i z).1
  · have hh := integral_mono (integrable_test π (x i))
      (integrable_const (1:ℝ)) (fun z => (hx i z).2)
    simpa only [marginal,mean,integral_const,probReal_univ,one_smul] using hh

omit [IsProbabilityMeasure μ] [PolishSpace T] [Nonempty A] in
theorem response_energy (x : ι → C(T × A, ℝ))
    (privateReceipt : C(T × A, ℝ)) (b b' : ι → ℝ) (ξ : ℝ)
    (π τ : Plan (A := A) μ)
    (hπ : Existence.Distributional.IntegralOptimal π
      (score x privateReceipt b (marginal x π) ξ))
    (hτ : Existence.Distributional.IntegralOptimal τ
      (score x privateReceipt b' (marginal x τ) ξ)) :
    ξ * ∑ i, b i*(marginal x π i-marginal x τ i)^2 ≤
      ∑ i, (b i-b' i)*(1-ξ*marginal x τ i)*(marginal x π i-marginal x τ i) := by
  have h₁ := hπ τ
  have h₂ := hτ π
  change mean τ _ ≤ mean π _ at h₁
  change mean π _ ≤ mean τ _ at h₂
  rw [mean_score,mean_score] at h₁ h₂
  have he :
      ((∑ i, b i*(1-ξ*marginal x π i)*marginal x π i) -
        (∑ i, b i*(1-ξ*marginal x π i)*marginal x τ i)) +
      ((∑ i, b' i*(1-ξ*marginal x τ i)*marginal x τ i) -
        (∑ i, b' i*(1-ξ*marginal x τ i)*marginal x π i)) =
      -ξ * ∑ i, b i*(marginal x π i-marginal x τ i)^2 +
        ∑ i, (b i-b' i)*(1-ξ*marginal x τ i)*(marginal x π i-marginal x τ i) := by
    rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  linarith

omit [PolishSpace T] [Nonempty A] [IsProbabilityMeasure μ] in
theorem own_bid_lipschitz (x : ι → C(T × A, ℝ))
    (privateReceipt : C(T × A, ℝ)) (b b' : ι → ℝ) (ξ : ℝ)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hb : ∀ j, 1 ≤ b j)
    (hx : ∀ j z, 0 ≤ x j z ∧ x j z ≤ 1)
    (i : ι) (hother : ∀ j, j ≠ i → b' j = b j)
    (π τ : Plan (A := A) μ)
    (hπ : Existence.Distributional.IntegralOptimal π
      (score x privateReceipt b (marginal x π) ξ))
    (hτ : Existence.Distributional.IntegralOptimal τ
      (score x privateReceipt b' (marginal x τ) ξ)) :
    |marginal x π i-marginal x τ i| ≤ |b i-b' i| / ξ := by
  classical
  have henergy := response_energy μ x privateReceipt b b' ξ π τ hπ hτ
  have hcorr : (∑ j, (b j-b' j)*(1-ξ*marginal x τ j)*
      (marginal x π j-marginal x τ j)) =
      (b i-b' i)*(1-ξ*marginal x τ i)*(marginal x π i-marginal x τ i) := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [hother j hji]
      ring
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  rw [hcorr] at henergy
  have hs : b i*(marginal x π i-marginal x τ i)^2 ≤
      ∑ j, b j*(marginal x π j-marginal x τ j)^2 :=
    Finset.single_le_sum (fun j _ => mul_nonneg (by linarith only [hb j] : 0 ≤ b j) (sq_nonneg (marginal x π j-marginal x τ j)))
      (Finset.mem_univ i)
  have hsq : (marginal x π i-marginal x τ i)^2 ≤
      b i*(marginal x π i-marginal x τ i)^2 := by
    calc
      _ = 1*(marginal x π i-marginal x τ i)^2 := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (hb i) (sq_nonneg _)
  have hr := marginal_mem_Icc μ x hx τ i
  have hf0 : 0 ≤ 1-ξ*marginal x τ i := by nlinarith only [hr.2,hξ.le,hξ1]
  have hf1 : 1-ξ*marginal x τ i ≤ 1 := by nlinarith only [hr.1,hξ.le]
  have hreceipt :
      (b i-b' i)*(1-ξ*marginal x τ i)*(marginal x π i-marginal x τ i) ≤
      |b i-b' i| * |marginal x π i-marginal x τ i| := by
    calc
      _ ≤ |(b i-b' i)*(1-ξ*marginal x τ i)*(marginal x π i-marginal x τ i)| :=
        le_abs_self _
      _ = |b i-b' i| *(1-ξ*marginal x τ i)*|marginal x π i-marginal x τ i| := by
        rw [abs_mul,abs_mul,abs_of_nonneg hf0]
      _ ≤ |b i-b' i| *1*|marginal x π i-marginal x τ i| := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hf1 (abs_nonneg _)) (abs_nonneg _)
      _ = _ := by ring
  have he : ξ*(marginal x π i-marginal x τ i)^2 ≤
      |b i-b' i| * |marginal x π i-marginal x τ i| :=
    (mul_le_mul_of_nonneg_left (hsq.trans hs) hξ.le).trans
      (henergy.trans hreceipt)
  apply (le_div_iff₀ hξ).mpr
  by_cases hz : marginal x π i-marginal x τ i = 0
  · simp [hz]
  · have hpos := abs_pos.mpr hz
    have habs := sq_abs (marginal x π i-marginal x τ i)
    nlinarith [habs]

end FCAppendix.Affine.Tail04.EqualPrivateFrontier
