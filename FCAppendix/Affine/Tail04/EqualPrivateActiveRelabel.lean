import FCAppendix.Affine.Tail04.EqualPrivateCountPayoff
import FCAppendix.Affine.Tail04.SortedAllNoise

noncomputable section
namespace FCAppendix.Affine.Tail04.EqualPrivateActiveRelabel
open MeasureTheory ProbabilityTheory Set Classical
open EqualPrivateSignal EqualPrivateFrontier EqualPrivateContinuity
open scoped BigOperators

local instance (N H : ℕ) : TopologicalSpace (Finset (Target N H)) := ⊥
local instance (N H : ℕ) : DiscreteTopology (Finset (Target N H)) := ⟨rfl⟩
local instance (N H : ℕ) : MeasurableSpace (Finset (Target N H)) := ⊤
local instance (N H : ℕ) : BorelSpace (Finset (Target N H)) := ⟨borel_eq_top_of_discrete.symm⟩

def targetEquiv (H : ℕ) {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    Target N H ≃ Target N H := Equiv.sumCongr σ (Equiv.refl _)

@[simp] lemma targetEquiv_inl (H : ℕ) {N : ℕ} (σ : Equiv.Perm (Fin N)) (i : Fin N) :
    targetEquiv H σ (Sum.inl i)=Sum.inl (σ i) := rfl

@[simp] lemma targetEquiv_inr (H : ℕ) {N : ℕ} (σ : Equiv.Perm (Fin N)) (j : Fin H) :
    targetEquiv H σ (Sum.inr j)=Sum.inr j := rfl

lemma mem_map_active {N H : ℕ} (σ : Equiv.Perm (Fin N))
    (S : Finset (Target N H)) (i : Fin N) :
    Sum.inl i∈S.map (targetEquiv H σ).toEmbedding ↔ Sum.inl (σ.symm i)∈S := by
  constructor
  · intro hi
    obtain ⟨j,hj,he⟩ := Finset.mem_map.mp hi
    have hji : j=Sum.inl (σ.symm i) := by
      apply (targetEquiv H σ).injective
      simpa using he
    simpa only [hji] using hj
  · intro hi
    exact Finset.mem_map.mpr ⟨Sum.inl (σ.symm i),hi,by simp⟩

lemma mem_map_private {N H : ℕ} (σ : Equiv.Perm (Fin N))
    (S : Finset (Target N H)) (j : Fin H) :
    Sum.inr j∈S.map (targetEquiv H σ).toEmbedding ↔ Sum.inr j∈S := by
  constructor
  · intro hj
    obtain ⟨k,hk,he⟩ := Finset.mem_map.mp hj
    have hkj : k=Sum.inr j := by
      apply (targetEquiv H σ).injective
      simpa using he
    simpa only [hkj] using hk
  · intro hj
    exact Finset.mem_map.mpr ⟨Sum.inr j,hj,rfl⟩

def relabelAction {N H c : ℕ} (σ : Equiv.Perm (Fin N)) (a : Action N H c) : Action N H c :=
  fun z => ⟨(a z).1.map (targetEquiv H σ).toEmbedding,
    ⟨by simpa using (a z).2.1,fun j hj => (a z).2.2 j ((mem_map_private σ (a z).1 j).mp hj)⟩⟩

def relabelJoint {N H c : ℕ} {R Rp : ℝ} (σ : Equiv.Perm (Fin N)) :
    Signal H R Rp×Action N H c → Signal H R Rp×Action N H c :=
  fun z => (z.1,relabelAction σ z.2)

lemma continuous_relabelJoint {N H c : ℕ} {R Rp : ℝ} (σ : Equiv.Perm (Fin N)) :
    Continuous (relabelJoint (H:=H) (c:=c) (R:=R) (Rp:=Rp) σ) :=
  continuous_fst.prodMk ((continuous_of_discreteTopology (f:=relabelAction σ)).comp continuous_snd)

@[simp] lemma selected_relabelAction {N H c : ℕ} {R Rp : ℝ}
    (σ : Equiv.Perm (Fin N)) (s : Signal H R Rp) (a : Action N H c) :
    selected s (relabelAction σ a)=(selected s a).map (targetEquiv H σ).toEmbedding := rfl

lemma activeIndicator_relabel {N H c : ℕ} {R Rp : ℝ}
    (σ : Equiv.Perm (Fin N)) (i : Fin N) (z : Signal H R Rp×Action N H c) :
    activeIndicator N H c R Rp i (relabelJoint σ z)=
      activeIndicator N H c R Rp (σ.symm i) z := by
  simp only [activeIndicator,ContinuousMap.coe_mk,relabelJoint,selected_relabelAction,mem_map_active]

lemma privateReceipt_relabel {N H c : ℕ} {R Rp : ℝ}
    (σ : Equiv.Perm (Fin N)) (z : Signal H R Rp×Action N H c) :
    privateReceipt N H c R Rp (relabelJoint σ z)=privateReceipt N H c R Rp z := by
  simp only [privateReceipt,ContinuousMap.coe_mk,relabelJoint,selected_relabelAction,mem_map_private]

def relabelPlan {N H c : ℕ} {R Rp : ℝ} {μ : Measure (Signal H R Rp)}
    (σ : Equiv.Perm (Fin N)) (π : Plan (A:=Action N H c) μ) : Plan (A:=Action N H c) μ :=
  ⟨π.1.map (continuous_relabelJoint σ).measurable.aemeasurable,by
    change (((π.1:Measure (Signal H R Rp×Action N H c)).map (relabelJoint σ)).map Prod.fst)=μ
    rw [Measure.map_map measurable_fst (continuous_relabelJoint σ).measurable]
    exact π.2⟩

lemma marginal_relabelPlan {N H c : ℕ} {R Rp : ℝ} {μ : Measure (Signal H R Rp)}
    (σ : Equiv.Perm (Fin N)) (π : Plan (A:=Action N H c) μ) (i : Fin N) :
    marginal (activeIndicator N H c R Rp) (relabelPlan σ π) i=
      marginal (activeIndicator N H c R Rp) π (σ.symm i) := by
  change (∫ z,activeIndicator N H c R Rp i z
      ∂((π.1:Measure _).map (relabelJoint σ)))=_
  rw [integral_map (continuous_relabelJoint σ).measurable.aemeasurable
    (activeIndicator N H c R Rp i).continuous.aestronglyMeasurable]
  simp only [activeIndicator_relabel,marginal,mean]

lemma privateMean_relabelPlan {N H c : ℕ} {R Rp : ℝ} {μ : Measure (Signal H R Rp)}
    (σ : Equiv.Perm (Fin N)) (π : Plan (A:=Action N H c) μ) :
    mean (relabelPlan σ π) (privateReceipt N H c R Rp)=mean π (privateReceipt N H c R Rp) := by
  change (∫ z,privateReceipt N H c R Rp z
      ∂((π.1:Measure _).map (relabelJoint σ)))=_
  rw [integral_map (continuous_relabelJoint σ).measurable.aemeasurable
    (privateReceipt N H c R Rp).continuous.aestronglyMeasurable]
  simp only [privateReceipt_relabel,mean]

lemma potential_relabelPlan {N H c : ℕ} {R Rp : ℝ} {μ : Measure (Signal H R Rp)}
    (σ : Equiv.Perm (Fin N)) (π : Plan (A:=Action N H c) μ) (b : Fin N → ℝ) (ξ : ℝ) :
    potential (activeIndicator N H c R Rp) (privateReceipt N H c R Rp) b ξ (relabelPlan σ π)=
      potential (activeIndicator N H c R Rp) (privateReceipt N H c R Rp)
        (fun j => b (σ j)) ξ π := by
  simp only [potential,marginal_relabelPlan,privateMean_relabelPlan]
  congr 1
  exact (Equiv.sum_comp σ (fun j => b j*(marginal (activeIndicator N H c R Rp) π (σ.symm j)-
    ξ*marginal (activeIndicator N H c R Rp) π (σ.symm j)^2/2))).symm.trans
      (by simp only [Equiv.symm_apply_apply])

theorem relabelPlan_max {N H c : ℕ} {R Rp : ℝ} {μ : Measure (Signal H R Rp)}
    (σ : Equiv.Perm (Fin N)) (π : Plan (A:=Action N H c) μ) (b : Fin N → ℝ) (ξ : ℝ)
    (hmax : ∀ τ : Plan (A:=Action N H c) μ,potential (activeIndicator N H c R Rp) (privateReceipt N H c R Rp) b ξ τ≤
      potential (activeIndicator N H c R Rp) (privateReceipt N H c R Rp) b ξ π) :
    ∀ τ : Plan (A:=Action N H c) μ,potential (activeIndicator N H c R Rp) (privateReceipt N H c R Rp)
        (fun j => b (σ.symm j)) ξ τ≤
      potential (activeIndicator N H c R Rp) (privateReceipt N H c R Rp)
        (fun j => b (σ.symm j)) ξ (relabelPlan σ π) := by
  intro τ
  have h := hmax (relabelPlan σ.symm τ)
  rw [potential_relabelPlan] at h
  simpa only [potential_relabelPlan,Equiv.symm_apply_apply] using h

def relabelParameters {N H : ℕ} {R Rp lo hi : ℝ} (σ : Equiv.Perm (Fin N))
    (p : PolicyParameters N H R Rp lo hi) : PolicyParameters N H R Rp lo hi :=
  (fun j => p.1 (σ.symm j),p.2)

theorem policyMean_relabel {N H c : ℕ} {R Rp ξ lo hi : ℝ}
    (hξ : 0< ξ) (hlo : 0< lo) (σ : Equiv.Perm (Fin N))
    (p : PolicyParameters N H R Rp lo hi) (i : Fin N) :
    policyMean N H c R Rp ξ lo hi (relabelParameters σ p) i=
      policyMean N H c R Rp ξ lo hi p (σ.symm i) := by
  let x := activeIndicator N H c R Rp
  let r := privateReceipt N H c R Rp
  let μ := WeakProbability.toMeasure p.2
  let b := EqualPrivateMeasurable.bids p
  let π := chosenPlan x r ξ (EqualPrivateMeasurable.forget p)
  let p' := relabelParameters σ p
  let τ := chosenPlan x r ξ (EqualPrivateMeasurable.forget p')
  have hmax : ∀ χ : Plan (A:=Action N H c) μ,potential x r b ξ χ≤ potential x r b ξ π := by
    obtain ⟨κ,hκ,hdis,hm,hopt,hall,hlocal⟩ :=
      (exists_equal_private_continuation μ x r b ξ).choose_spec
    exact hm
  have hopt : Existence.Distributional.IntegralOptimal (relabelPlan σ π)
      (score x r (fun j => b (σ.symm j)) (marginal x (relabelPlan σ π)) ξ) :=
    integralOptimal_of_potential_max μ x r _ ξ _ (relabelPlan_max σ π b ξ hmax)
  have ht : Existence.Distributional.IntegralOptimal τ
      (score x r (fun j => b (σ.symm j)) (marginal x τ) ξ) :=
    integralOptimal_of_gap_eq_zero x r _ ξ μ τ
      (chosenPlan_gap x r ξ (EqualPrivateMeasurable.forget p'))
  have hu := congrFun (marginal_unique μ x r (fun j => b (σ.symm j)) ξ hξ
    (fun j => hlo.trans_le (p.1 (σ.symm j)).2.1) τ (relabelPlan σ π) ht hopt) i
  rw [marginal_relabelPlan] at hu
  change EqualPrivateMeasurable.q x r ξ lo hi p' i=
    EqualPrivateMeasurable.q x r ξ lo hi p (σ.symm i)
  rw [EqualPrivateMeasurable.q_eq_chosenMarginal x r ξ lo hi hξ hlo p',
    EqualPrivateMeasurable.q_eq_chosenMarginal x r ξ lo hi hξ hlo p]
  exact hu

theorem policyMean_tied {N H c : ℕ} {R Rp ξ lo hi : ℝ}
    (hξ : 0< ξ) (hlo : 0< lo) (p : PolicyParameters N H R Rp lo hi)
    (i j : Fin N) (hij : (p.1 i:ℝ)=(p.1 j:ℝ)) :
    policyMean N H c R Rp ξ lo hi p i=policyMean N H c R Rp ξ lo hi p j := by
  have hp : relabelParameters (Equiv.swap i j) p=p := by
    apply Prod.ext
    · funext k
      by_cases hki : k=i
      · subst k
        apply Subtype.ext
        simpa [relabelParameters] using hij.symm
      · by_cases hkj : k=j
        · subst k
          apply Subtype.ext
          simpa [relabelParameters] using hij
        · simp [relabelParameters,Equiv.swap_apply_of_ne_of_ne hki hkj]
    · rfl
  have h := policyMean_relabel (c:=c) hξ hlo (Equiv.swap i j) p i
  simpa only [hp,Equiv.symm_swap,Equiv.swap_apply_left] using h

theorem countLaw_relabel {N H c : ℕ} {R Rp ξ lo hi : ℝ}
    (hξ : 0< ξ) (hlo : 0< lo) (σ : Equiv.Perm (Fin N))
    (p : PolicyParameters N H R Rp lo hi) (i : Fin N) :
    EqualPrivateCountPayoff.countLaw N H c R Rp ξ lo hi (relabelParameters σ p) i=
      EqualPrivateCountPayoff.countLaw N H c R Rp ξ lo hi p (σ.symm i) := by
  unfold EqualPrivateCountPayoff.countLaw
  simp only [policyMean_relabel hξ hlo σ p i]

theorem countLaw_sorted {N H c : ℕ} {R Rp ξ B : ℝ}
    (hξ : 0< ξ) (b : Fin N → Icc (1:ℝ) B)
    (μ : WeakProbability.Law (Signal H R Rp)) (i : Fin N) :
    EqualPrivateCountPayoff.countLaw N H c R Rp ξ 1 B
      (SortedAllNoise.sortedBox b,μ) (SortedAllNoise.focalRank (fun j => (b j:ℝ)) i)=
      EqualPrivateCountPayoff.countLaw N H c R Rp ξ 1 B (b,μ) i := by
  let σ := PrivateRowSorting.permutation (fun j => (b j:ℝ))
  have hp : (SortedAllNoise.sortedBox b,μ)=relabelParameters σ.symm (b,μ) := rfl
  rw [hp,countLaw_relabel hξ (by norm_num)]
  change EqualPrivateCountPayoff.countLaw N H c R Rp ξ 1 B (b,μ) (σ (σ.symm i))=_
  rw [Equiv.apply_symm_apply]

end FCAppendix.Affine.Tail04.EqualPrivateActiveRelabel
