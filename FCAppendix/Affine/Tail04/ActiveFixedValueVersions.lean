import FCAppendix.Affine.Tail04.ParametricMenuCount
import FCAppendix.Affine.Tail04.PartialFixedValueVersions

noncomputable section
namespace FCAppendix.Affine.Tail04.ActiveFixedValueVersions
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Game Bayes
open OriginalValues OriginalPopulation SourceMenuIdentity ConditionalVersions

variable (P : ValueParameters) (ξ U : ℝ) (hU : 1≤ U)

def error (e v : ℝ) : ℝ := (max 0 v+2*Central.B ξ)*e

lemma error_nonneg (hξ : 0< ξ) {e : ℝ} (he : 0≤ e) (v : ℝ) :
    0≤ error ξ e v := by
  have hB : 0< Central.B ξ := by unfold Central.B;linarith
  exact mul_nonneg (by linarith [le_max_left (0:ℝ) v]) he

lemma continuous_error (e : ℝ) : Continuous (error ξ e) := by
  unfold error
  fun_prop

def graph (lam : ℝ×ℝ) (e : ℝ) : Set (ℝ×Icc (1:ℝ) U) :=
  {x | ∀y : Icc (1:ℝ) U,menuUtility P ξ lam.1 lam.2 x.1 y≤
    menuUtility P ξ lam.1 lam.2 x.1 x.2+2*error ξ e x.1}

lemma isClosed_graph (lam : ℝ×ℝ) (e : ℝ) : IsClosed (graph P ξ U lam e) := by
  have hc : Continuous (fun x : ℝ×Icc (1:ℝ) U=> menuUtility P ξ lam.1 lam.2 x.1 x.2) :=
    (CompactMenuChoice.continuous_utility P ξ U).comp
      ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)
  have he : graph P ξ U lam e=⋂y : Icc (1:ℝ) U,
      {x | menuUtility P ξ lam.1 lam.2 x.1 y≤
        menuUtility P ξ lam.1 lam.2 x.1 x.2+2*error ξ e x.1} := by
    ext x;simp only [graph,mem_setOf_eq,mem_iInter]
  rw [he]
  exact isClosed_iInter fun y=> isClosed_le
    (hc.comp (continuous_fst.prodMk continuous_const))
    (hc.add (continuous_const.mul ((continuous_error ξ e).comp continuous_fst)))

def condition (vL vU : ℝ) (lam : ℝ×ℝ) (e : ℝ) (x : ℝ×JointAction 2) : Prop :=
  x.1∈Icc vL vU → x.2.routeCount=2 ∧ x.2.bid∈Icc (1:ℝ) U ∧
    (x.1,clipToBand 1 U hU x.2.bid)∈graph P ξ U lam e

lemma measurableSet_condition (vL vU : ℝ) (lam : ℝ×ℝ) (e : ℝ) :
    MeasurableSet {x | condition P ξ U hU vL vU lam e x} := by
  have hp : Measurable (fun x : ℝ×JointAction 2=>(x.1,clipToBand 1 U hU x.2.bid)) :=
    measurable_fst.prodMk ((measurable_clipToBand 1 U hU).comp
      ((measurable_bid 2).comp measurable_snd))
  have he : {x | condition P ξ U hU vL vU lam e x}=
      (Prod.fst ⁻¹' Icc vL vU)ᶜ∪
        ({x : ℝ×JointAction 2 | x.2.routeCount=2}∩
          {x : ℝ×JointAction 2 | x.2.bid∈Icc (1:ℝ) U}∩
            (fun x : ℝ×JointAction 2=>(x.1,clipToBand 1 U hU x.2.bid)) ⁻¹' graph P ξ U lam e) := by
    ext x;simp [condition,imp_iff_not_or,and_assoc]
  rw [he]
  exact (measurableSet_Icc.preimage measurable_fst).compl.union
    (((measurableSet_eq_fun ((measurable_routeCount 2).comp measurable_snd) measurable_const).inter
      (measurableSet_Icc.preimage ((measurable_bid 2).comp measurable_snd))).inter
        ((isClosed_graph P ξ U lam e).measurableSet.preimage hp))

lemma condition_iff (vL vU : ℝ) (lam : ℝ×ℝ) (e : ℝ) (x : ℝ×JointAction 2) :
    condition P ξ U hU vL vU lam e x ↔
      (x.1∈Icc vL vU→ x.2.routeCount=2 ∧ x.2.bid∈Icc (1:ℝ) U ∧
        ∀y : Icc (1:ℝ) U,menuUtility P ξ lam.1 lam.2 x.1 y≤
          menuUtility P ξ lam.1 lam.2 x.1 x.2.bid+2*error ξ e x.1) := by
  constructor <;> intro hh hv
  · obtain ⟨hk,hb,hr⟩:=hh hv
    exact ⟨hk,hb,by simpa only [graph,mem_setOf_eq,clipToBand_eq 1 U hU hb] using hr⟩
  · obtain ⟨hk,hb,hr⟩:=hh hv
    exact ⟨hk,hb,by simpa only [graph,mem_setOf_eq,clipToBand_eq 1 U hU hb] using hr⟩

def reference (lam : ℝ×ℝ) (v : ℝ) : JointAction 2 :=
  bandAction (by norm_num) 2 le_rfl (CompactMenuChoice.choice P ξ U hU (lam,v))

lemma measurable_reference (lam : ℝ×ℝ) : Measurable (reference P ξ U hU lam) :=
  (measurable_bandAction _ _ _).comp ((CompactMenuChoice.measurable_choice P ξ U hU).comp
    (measurable_const.prodMk measurable_id))

variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def strategy (Γ : FiniteGame m 2 c Seed) (vL vU : ℝ) (lam : ℝ×ℝ) (e : ℝ) :
    Kernel ℝ (JointAction 2) :=
  repair Γ.σ (measurableSet_condition P ξ U hU vL vU lam e)
    (reference P ξ U hU lam) (measurable_reference P ξ U hU lam)

instance strategy_markov (Γ : FiniteGame m 2 c Seed) (vL vU : ℝ) (lam : ℝ×ℝ) (e : ℝ) :
    IsMarkovKernel (strategy P ξ U hU Γ vL vU lam e) := by unfold strategy;infer_instance

def game (Γ : FiniteGame m 2 c Seed) (vL vU : ℝ) (lam : ℝ×ℝ) (e : ℝ) :
    FiniteGame m 2 c Seed := withStrategy Γ (strategy P ξ U hU Γ vL vU lam e)

theorem fixed_value_support (hξ : 0< ξ) (Γ : FiniteGame m 2 c Seed)
    (vL vU : ℝ) (lam : ℝ×ℝ) (e : ℝ) (he : 0≤ e) (v : ℝ) (hv : v∈Icc vL vU) :
    ∀ᵐa ∂strategy P ξ U hU Γ vL vU lam e v,
      a.routeCount=2 ∧ a.bid∈Icc (1:ℝ) U ∧
        ∀y : Icc (1:ℝ) U,menuUtility P ξ lam.1 lam.2 v y≤
          menuUtility P ξ lam.1 lam.2 v a.bid+2*error ξ e v := by
  filter_upwards [repair_fixed_value_support Γ.σ
    (measurableSet_condition P ξ U hU vL vU lam e)
    (reference P ξ U hU lam) (measurable_reference P ξ U hU lam) v] with a ha
  rcases ha with ha | rfl
  · exact (condition_iff P ξ U hU vL vU lam e (v,a)).mp ha hv
  · refine ⟨rfl,(CompactMenuChoice.choice P ξ U hU (lam,v)).2,?_⟩
    intro y
    have hm:=CompactMenuChoice.choice_max P ξ U hU (lam,v) y
    have hn:=error_nonneg ξ hξ he v
    change _≤ menuUtility P ξ lam.1 lam.2 v (CompactMenuChoice.choice P ξ U hU (lam,v))+_
    linarith

theorem outside (Γ : FiniteGame m 2 c Seed) (vL vU : ℝ) (lam : ℝ×ℝ) (e : ℝ)
    (v : ℝ) (hv : v∉Icc vL vU) : strategy P ξ U hU Γ vL vU lam e v=Γ.σ v := by
  apply repair_apply_good
  change Γ.σ v {a | ¬condition P ξ U hU vL vU lam e (v,a)}=0
  have he : {a | ¬condition P ξ U hU vL vU lam e (v,a)}=∅ := by
    ext a;simp [condition,hv]
  rw [he,measure_empty]

variable (Γ : FiniteGame m 2 c Seed) (vL vU : ℝ) (lam : ℝ×ℝ) (e : ℝ)
  (hs : ∀ᵐx ∂Γ.F⊗ₘΓ.σ,condition P ξ U hU vL vU lam e x)

include hs in
lemma strategy_ae_eq : strategy P ξ U hU Γ vL vU lam e=ᵐ[Γ.F] Γ.σ :=
  repair_ae_eq Γ.F Γ.σ (measurableSet_condition P ξ U hU vL vU lam e)
    (reference P ξ U hU lam) (measurable_reference P ξ U hU lam)
    (Measure.ae_ae_of_ae_compProd hs)

include hs in
lemma joint_eq :
    (game P ξ U hU Γ vL vU lam e).F⊗ₘ(game P ξ U hU Γ vL vU lam e).σ=Γ.F⊗ₘΓ.σ :=
  withStrategy_joint Γ _ (strategy_ae_eq P ξ U hU Γ vL vU lam e hs)

include hs in
lemma problem_eq (i : Fin m) : problem (game P ξ U hU Γ vL vU lam e) i=problem Γ i :=
  withStrategy_problem Γ _ (strategy_ae_eq P ξ U hU Γ vL vU lam e hs) i

include hs in
theorem conditional_eq_outside (hm : 0< m) (v : ℝ) (hv : v∉Icc vL vU) :
    conditionalTypeCountLaw (game P ξ U hU Γ vL vU lam e) hm v=
      conditionalTypeCountLaw Γ hm v := by
  apply FiniteLaw.ext
  intro r
  rw [←FiniteLaw.expect_singleton,←FiniteLaw.expect_singleton,
    conditionalTypeCountLaw_expect,conditionalTypeCountLaw_expect]
  simp_rw [problem_eq P ξ U hU Γ vL vU lam e hs,
    show (game P ξ U hU Γ vL vU lam e).σ v=Γ.σ v from outside P ξ U hU Γ vL vU lam e v hv]

end FCAppendix.Affine.Tail04.ActiveFixedValueVersions
