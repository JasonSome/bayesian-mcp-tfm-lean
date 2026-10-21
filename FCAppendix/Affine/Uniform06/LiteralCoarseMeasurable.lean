import FCAppendix.Affine.Uniform06.LiteralCoarsePath
import FCAppendix.Affine.WeightedSampler

noncomputable section
namespace FCAppendix.Affine.Uniform06.LiteralCoarseMeasurable

open MeasureTheory Set LowBody
open scoped BigOperators
open FCAppendix.Affine.ClippedResidual FCAppendix.Affine.WeightedSampling
open LiteralExperiment LiteralCoarsePath

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem measurable_oneDraw_mass (w : Ω → Weights ι)
    (hw : ∀ j,Measurable (fun ω => (w ω).1 j)) (S : Finset ι) (j : ι) :
    Measurable (fun ω => (oneDraw (w ω) S).mass j) := by
  have hm : Measurable w := (measurable_pi_lambda _ hw).subtype_mk
  exact (FCAppendix.Affine.WeightedSampling.measurable_oneDraw_mass S j).comp hm

theorem measurable_path_mass (w : Ω → Weights ι)
    (hw : ∀ j,Measurable (fun ω => (w ω).1 j))
    (n : ℕ) (S : Finset ι) (path : Path ι n) :
    Measurable (fun ω => (pathLaw (w ω) n S).mass path) := by
  have hm : Measurable w := (measurable_pi_lambda _ hw).subtype_mk
  exact (FCAppendix.Affine.WeightedSampling.measurable_pathLaw_mass n S path).comp hm

omit [Fintype ι] [Nonempty ι] in
theorem measurable_weights (ξ : ℝ) (g : GuardData) (T : PureTemplate ι)
    (B : Ω → ι → ℝ) (hB : ∀ j,Measurable (fun ω => B ω j)) :
    ∀ j, Measurable (fun ω => (weights ξ g T (B ω)).1 j) := by
  intro j
  by_cases hj : j ∈ T.support
  · simp only [weights,if_pos hj]
    unfold FiniteGuards.eligibility FiniteGuards.clip01 exposure
    fun_prop
  · simpa only [weights,if_neg hj] using
      (measurable_const : Measurable (fun _ : Ω => (0 : ℝ)))

omit [Nonempty ι] in
theorem measurable_complement {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (T : PureTemplate ι) (B : Ω → ι → ℝ)
    (hB : ∀ j,Measurable (fun ω => B ω j)) (E : Finset ι) (j : ι) :
    Measurable (fun ω => complementMarginal ξ T (B ω) E j) := by
  have hm : Measurable (fun ω => maskedBids T (B ω) E) := by
    apply measurable_pi_lambda
    intro k
    by_cases hk : k ∈ T.support \ E
    · simpa only [maskedBids,if_pos hk] using hB k
    · simpa only [maskedBids,if_neg hk] using
        (measurable_const : Measurable (fun _ : Ω => (0 : ℝ)))
  exact (measurable_pi_apply j).comp
    ((EqualCapacity.measurable_positiveMarginal ξ (small T) hξ hξ1).comp hm)

omit [Nonempty ι] in
theorem measurable_guard (ξ : ℝ) (g : GuardData) (T : PureTemplate ι)
    (B : Ω → ι → ℝ) (hB : ∀ j,Measurable (fun ω => B ω j)) :
    Measurable (fun ω => guardAlpha ξ g T (B ω)) := by
  classical
  have hD (z : ℝ) : Measurable (fun ω => LiteralExperiment.demand ξ T (B ω) z) := by
    unfold LiteralExperiment.demand
    apply Finset.measurable_sum
    intro k _
    unfold exposure
    fun_prop
  have hW : Measurable (fun ω => totalWeight (weights ξ g T (B ω))) := by
    unfold totalWeight
    exact Finset.measurable_sum _ (fun j _ => measurable_weights ξ g T B hB j)
  have hP : Measurable (fun ω => ∑ j ∈ T.support,
      PrefixRoot.psi g.rejectionScale g.rejectionRoot (B ω j)) := by
    apply Finset.measurable_sum
    intro k _
    unfold PrefixRoot.psi
    fun_prop
  have hs : ∀ k,Measurable (fun ω => slackVector ξ g T (B ω) k) := by
    intro k
    fin_cases k
    · exact ((hD _).sub_const _).sub_const _
    · exact measurable_const.sub (hD _)
    · exact hW.sub_const _
    · exact (hP.sub_const _).sub_const _
    · exact measurable_const
  have hseed : MeasurableSet {ω | seeded g T (B ω)} := by
    have he : {ω | seeded g T (B ω)}=⋃ j : ι,
        {ω | j ∈ T.support ∧ B ω j ≤ g.seedCutoff} := by
      ext ω
      simp only [seeded,mem_setOf_eq,mem_iUnion]
    rw [he]
    apply MeasurableSet.iUnion
    intro j
    by_cases hj : j ∈ T.support
    · simpa only [hj,true_and] using measurableSet_le (hB j) measurable_const
    · simpa only [hj,false_and,setOf_false] using MeasurableSet.empty
  unfold guardAlpha FiniteGuards.alpha
  apply Measurable.ite hseed _ measurable_const
  apply Finset.measurable_prod
  intro k _
  unfold FiniteGuards.ramp FiniteGuards.clip01
  fun_prop

theorem measurable_path_moment {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (g : GuardData) (T : PureTemplate ι) (B : Ω → ι → ℝ)
    (hB : ∀ j,Measurable (fun ω => B ω j)) (j : ι) (k : ℕ) :
    Measurable (fun ω => (pathLaw (weights ξ g T (B ω)) (imbalance T) ∅).expect
      (fun path => (complementMarginal ξ T (B ω) (finalSet (imbalance T) ∅ path) j)^k)) := by
  unfold FCAppendix.FiniteLaw.expect
  apply Finset.measurable_sum
  intro path _
  exact (measurable_path_mass (fun ω => weights ξ g T (B ω))
    (measurable_weights ξ g T B hB) (imbalance T) ∅ path).mul
      ((measurable_complement hξ hξ1 T B hB _ j).pow_const k)

theorem measurable_numeric_moments {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (g : GuardData) (T : PureTemplate ι) (B : Ω → ι → ℝ)
    (hB : ∀ j,Measurable (fun ω => B ω j)) (j : ι)
    (hε : 0 < g.margin) (hM : 0 < g.population) (hr : 0 < g.requiredDemand)
    (hb : ∀ ω,B ω j ≤ g.multiplier) :
    Measurable (fun ω => numericMarginal ξ g T (B ω) j) ∧
      Measurable (fun ω => numericDuplicate ξ g T (B ω) j) := by
  have hα : Measurable (fun ω => branchWeight ξ g T (B ω)) := by
    by_cases he : T.residual₀=T.residual₁
    · simpa only [branchWeight,if_pos he] using
        (measurable_const : Measurable (fun _ : Ω => (1 : ℝ)))
    · simpa only [branchWeight,if_neg he] using measurable_guard ξ g T B hB
  have he := fun ω => numeric_path_moments hξ hξ1 g T (B ω) j hε hM hr (hb ω)
  constructor
  · have hm := hα.mul (measurable_path_moment hξ hξ1 g T B hB j 1)
    convert! hm using 1
    funext ω
    simpa only [pow_one,Pi.mul_apply] using! (he ω).1
  · have hm := hα.mul (measurable_path_moment hξ hξ1 g T B hB j 2)
    convert! hm using 1
    funext ω
    simpa only [Pi.mul_apply] using! (he ω).2

theorem measurable_raw_rowBids (N : ℕ) (b : ℝ) (k : Fin (N+1)) :
    Measurable (fun ω : Fin N → RowRival => rowBids b ω k) := by
  refine Fin.cases ?_ (fun j => ?_) k
  · exact measurable_const
  · change Measurable (fun ω : Fin N → RowRival => if (ω j).1=0 then (ω j).2 else 0)
    exact Measurable.ite
      (measurableSet_eq_fun (measurable_fst.comp (measurable_pi_apply j)) measurable_const)
      (measurable_snd.comp (measurable_pi_apply j)) measurable_const

theorem measurable_pattern_choice {N : ℕ}
    (f : (Fin N → Fin 4) → (Fin N → RowRival) → ℝ)
    (hf : ∀ kind,Measurable (f kind)) :
    Measurable (fun ω => f (fun j => (ω j).1) ω) := by
  classical
  have hk : Measurable (fun ω : Fin N → RowRival => fun j => (ω j).1) :=
    measurable_pi_lambda _ (fun j => measurable_fst.comp (measurable_pi_apply j))
  have he : (fun ω => f (fun j => (ω j).1) ω)=fun ω =>
      ∑ kind : Fin N → Fin 4,if (fun j => (ω j).1)=kind then f kind ω else 0 := by
    funext ω
    symm
    rw [Finset.sum_eq_single (fun j => (ω j).1)]
    · simp
    · intro kind _ hn
      simp only [if_neg (Ne.symm hn)]
    · simp
  rw [he]
  apply Finset.measurable_sum
  intro kind _
  exact Measurable.ite (measurableSet_eq_fun hk measurable_const) (hf kind) measurable_const

theorem measurable_original_moments {N : ℕ} {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (g : GuardData) (countMargin : (Fin N → Fin 4) → ℝ) (b : ℝ)
    (hε : 0 < g.margin) (hM : 0 < g.population) (hr : 0 < g.requiredDemand)
    (hb : b ≤ g.multiplier) :
    Measurable (originalRowMarginal ξ c g countMargin b) ∧
      Measurable (originalRowDuplicate ξ c g countMargin b) := by
  have hh (kind : Fin N → Fin 4) := measurable_numeric_moments hξ hξ1
    {g with countMargin := countMargin kind} (patternTemplate c kind) (rowBids b)
      (measurable_raw_rowBids N b) 0 hε hM hr
      (fun ω => by simpa only [rowBids,Fin.cons_zero] using hb)
  exact ⟨measurable_pattern_choice _ (fun kind => (hh kind).1),
    measurable_pattern_choice _ (fun kind => (hh kind).2)⟩

end FCAppendix.Affine.Uniform06.LiteralCoarseMeasurable
