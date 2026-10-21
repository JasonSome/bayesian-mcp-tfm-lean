import FCAppendix.Game.PosteriorFeasible
import FCAppendix.Affine.Uniform07Finishing.Native.StrictTags

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.StrictNative
open MeasureTheory ProbabilityTheory Bayes Game Set Filter

def otherProposer (j : Fin 2) : Fin 2 := if j=0 then 1 else 0

@[simp] lemma otherProposer_ne (j : Fin 2) : otherProposer j≠j := by
  fin_cases j <;> simp [otherProposer]
@[simp] lemma ne_otherProposer (j : Fin 2) : j≠otherProposer j := Ne.symm (otherProposer_ne j)
@[simp] lemma otherProposer_other (j : Fin 2) : otherProposer (otherProposer j)=j := by
  fin_cases j <;> simp [otherProposer]

def routeTo (j : Fin 2) : Equiv.Perm (Fin 2) := Equiv.swap 0 j

lemma firstK_routeTo (j : Fin 2) : firstK (routeTo j) 1={j} := by
  ext l
  fin_cases j <;> fin_cases l <;> simp [firstK,routeTo]

lemma firstK_full_two (τ : Equiv.Perm (Fin 2)) : firstK τ 2=Finset.univ := by
  ext j
  simp only [mem_firstK,Finset.mem_univ,iff_true]
  exact (τ j).isLt

def classifiedAction (U R : ℝ) : Option ℝ → JointAction 2
  | none=>⟨max R 0,le_max_right _ _,1,by omega⟩
  | some b=>⟨max b 0,le_max_right _ _,if b< U then 2 else 1,by split_ifs <;> omega⟩

def classifiedOrdering (j : Fin 2) : Option ℝ → Equiv.Perm (Fin 2)
  | none=>routeTo (otherProposer j)
  | some _=>routeTo j

lemma measurable_classifiedAction (U R : ℝ) : Measurable (classifiedAction U R) := by
  apply Measurable.of_comap_le
  rw [instMeasurableSpaceJointAction,MeasurableSpace.comap_comp]
  apply Measurable.comap_le
  intro S hS
  change MeasurableSet ((fun b : ℝ=>(max b 0,if b< U then (2:ℕ) else 1)) ⁻¹' S)
  exact (((measurable_id.max measurable_const).prodMk
    (Measurable.ite measurableSet_Iio measurable_const measurable_const))) hS

lemma measurable_classifiedOrdering (j : Fin 2) : Measurable (classifiedOrdering j) := by
  intro S _
  change MeasurableSet ((fun _ : ℝ=>routeTo j) ⁻¹' S)
  exact measurable_const (MeasurableSet.of_discrete)

def classifiedProfile (m : ℕ) (U R : ℝ) (j : Fin 2) (L : LocalList m) : UserProfile m 2 :=
  fun i=>((0,classifiedAction U R (L i)),classifiedOrdering j (L i))

lemma measurable_classifiedProfile (m : ℕ) (U R : ℝ) (j : Fin 2) :
    Measurable (classifiedProfile m U R j) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_const.prodMk
    ((measurable_classifiedAction U R).comp (measurable_pi_apply i))).prodMk
      ((measurable_classifiedOrdering j).comp (measurable_pi_apply i))

lemma observe_classifiedProfile {m : ℕ} (U R : ℝ) (j : Fin 2) (L : LocalList m)
    (hL : NonnegativeList L) : observe (drawsRealization (classifiedProfile m U R j L)) j=L := by
  funext i
  cases hentry : L i with
  | none=>simp [observe,drawsRealization,classifiedProfile,classifiedAction,classifiedOrdering,hentry,
      firstK_routeTo]
  | some b=>
    have hb : 0≤ b := by simpa only [NonnegativeList,hentry,entryBid] using hL i
    by_cases hbU : b< U
    · simp [observe,drawsRealization,classifiedProfile,classifiedAction,classifiedOrdering,hentry,hbU,
        firstK_full_two,max_eq_left hb]
    · simp [observe,drawsRealization,classifiedProfile,classifiedAction,classifiedOrdering,hentry,hbU,
        firstK_routeTo,max_eq_left hb]

def classifiedProfiles (m : ℕ) (U : ℝ) : Set (UserProfile m 2) :=
  {d | ∀ i,((d i).1.2.bid< U ∧ (d i).1.2.routeCount=2) ∨
    (U≤(d i).1.2.bid ∧ (d i).1.2.routeCount=1)}

lemma measurableSet_classifiedProfiles (m : ℕ) (U : ℝ) :
    MeasurableSet (classifiedProfiles m U) := by
  simp only [classifiedProfiles,setOf_forall]
  apply MeasurableSet.iInter
  intro i
  have ha : Measurable (fun d : UserProfile m 2=>(d i).1.2) :=
    (measurable_pi_apply i).fst.snd
  have hb := (measurable_bid 2).comp ha
  have hr := (measurable_routeCount 2).comp ha
  exact ((measurableSet_lt hb measurable_const).inter
    (measurableSet_eq_fun hr measurable_const)).union
      ((measurableSet_le measurable_const hb).inter
        (measurableSet_eq_fun hr measurable_const))

lemma classifiedProfile_mem {m : ℕ} {U R : ℝ} (hU : 0≤ U) (hR : U≤ R)
    (j : Fin 2) (L : LocalList m) (hL : NonnegativeList L) :
    classifiedProfile m U R j L∈classifiedProfiles m U := by
  intro i
  cases hentry : L i with
  | none=>
    right
    simpa only [classifiedProfile,classifiedAction,hentry,max_eq_left (hU.trans hR)] using
      (And.intro hR rfl : U≤ R ∧ (1:ℕ)=1)
  | some b=>
    have hb : 0≤ b := by simpa only [NonnegativeList,hentry,entryBid] using hL i
    by_cases hbU : b< U
    · left
      simp [classifiedProfile,classifiedAction,hentry,hbU,max_eq_left hb]
    · right
      simp [classifiedProfile,classifiedAction,hentry,hbU,max_eq_left hb,le_of_not_gt hbU]

def classifiedFallback (m : ℕ) (U R : ℝ) (j : Fin 2) : Kernel (LocalList m) (UserProfile m 2) :=
  Kernel.deterministic (classifiedProfile m U R j) (measurable_classifiedProfile m U R j)

instance (m : ℕ) (U R : ℝ) (j : Fin 2) : IsMarkovKernel (classifiedFallback m U R j) := by
  unfold classifiedFallback
  infer_instance

lemma classifiedFallback_feasible {m : ℕ} (U R : ℝ) (j : Fin 2) (L : LocalList m)
    (hL : FeasibleObservedList j L) :
    ∀ᵐd ∂classifiedFallback m U R j L,observe (drawsRealization d) j=L := by
  rw [classifiedFallback,Kernel.deterministic_apply]
  apply (ae_dirac_iff (measurableSet_eq_lists (measurable_observe_draws j) measurable_const)).mpr
  exact observe_classifiedProfile U R j L ((feasibleObservedList_iff_nonnegative j L).mp hL)

def classifiedPosterior {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) {U R : ℝ} (hfull : ∀ᵐd ∂userProfileLaw Γ,d∈classifiedProfiles m U) :
    PosteriorSystem Γ :=
  posteriorWithFallback Γ (measurableSet_classifiedProfiles m U) hfull
    (classifiedFallback m U R) (classifiedFallback_feasible U R)

theorem classifiedPosterior_support {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) {U R : ℝ} (hU : 0≤ U) (hR : U≤ R)
    (hfull : ∀ᵐd ∂userProfileLaw Γ,d∈classifiedProfiles m U)
    (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L) :
    ∀ᵐd ∂(classifiedPosterior Γ (R:=R) hfull).posterior j L,
      observe (drawsRealization d) j=L ∧ d∈classifiedProfiles m U := by
  classical
  change ∀ᵐd ∂posteriorWithFallbackKernel Γ (measurableSet_classifiedProfiles m U)
    (classifiedFallback m U R) j L,_
  by_cases hgood : L∈goodPosteriorLists Γ (classifiedProfiles m U) j
  · simp only [posteriorWithFallbackKernel,Kernel.piecewise_apply,if_pos hgood]
    exact ae_iff.mpr hgood
  · simp only [posteriorWithFallbackKernel,Kernel.piecewise_apply,if_neg hgood,
      classifiedFallback,Kernel.deterministic_apply]
    apply (ae_dirac_iff ((measurableSet_eq_lists (measurable_observe_draws j) measurable_const).inter
      (measurableSet_classifiedProfiles m U))).mpr
    have hnonneg := (feasibleObservedList_iff_nonnegative j L).mp hL
    exact ⟨observe_classifiedProfile U R j L hnonneg,classifiedProfile_mem hU hR j L hnonneg⟩

end FCAppendix.Affine.Uniform07Finishing.StrictNative
