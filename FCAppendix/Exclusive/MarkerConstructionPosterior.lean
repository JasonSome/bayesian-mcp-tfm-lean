import FCAppendix.Exclusive.MarkerConstructionPolicy
import FCAppendix.Game.PosteriorFeasible

namespace FCAppendix.Exclusive.Marker

open MeasureTheory ProbabilityTheory Game Bayes Set
open scoped BigOperators

variable {m n c : ℕ}

theorem measurable_world {Ω : Type*} [MeasurableSpace Ω]
    (P : Finset (Fin m)) (b : Ω → Fin m → ℝ)
    (hb : ∀ ω i, i ∈ P → 0 ≤ b ω i) (hmeas : ∀ i, Measurable (fun ω => b ω i))
    (M : Markers P n) (roles : Equiv.Perm (Fin n)) :
    Measurable (fun ω => world P (b ω) (hb ω) M roles) := by
  classical
  apply measurable_pi_iff.mpr
  intro i
  by_cases hi : i ∈ P
  · have ha : Measurable (fun ω => (⟨b ω i,hb ω i hi,n,le_rfl⟩ : JointAction n)) := by
      apply measurable_comap_iff.mpr
      exact (hmeas i).prodMk measurable_const
    simpa only [world,dif_pos hi] using (measurable_const.prodMk ha).prodMk measurable_const
  · by_cases hm : ∃ l, M.identity l=i
    · simp only [world,dif_neg hi,dif_pos hm]
      exact measurable_const
    · simp only [world,dif_neg hi,dif_neg hm]
      exact measurable_const

def CompletionCode (P Z : Finset (Fin m)) (n : ℕ) : Prop :=
  Disjoint P Z ∧ Z.card<n ∧ n-1 ≤ m-P.card

theorem positives_disjoint_zeros (ℓ : LocalList m) : Disjoint (positives ℓ) (zeros ℓ) := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hp hz
  have hpos := (Finset.mem_filter.mp hp).2
  have he := (Finset.mem_filter.mp hz).2
  simp [he] at hpos

noncomputable def templateWorld (j : Fin n)
    (P Z : Finset (Fin m)) (ℓ : LocalList m) : UserProfile m n := by
  classical
  exact if h : CompletionCode P Z n then
    let M := Classical.choose (exists_markers_extending P Z h.1 h.2.1 h.2.2)
    let roles := Equiv.swap j (⟨Z.card,h.2.1⟩ : Fin n)
    world P (fun i => max ((ℓ i).getD 0) 0) (fun _ _ => le_max_right _ _) M roles
  else completedProfile m n ℓ

theorem measurable_templateWorld (j : Fin n) (P Z : Finset (Fin m)) :
    Measurable (templateWorld j P Z) := by
  classical
  change Measurable (fun ℓ => templateWorld j P Z ℓ)
  by_cases h : CompletionCode P Z n
  · simp only [templateWorld,dif_pos h]
    exact measurable_world P (fun (ℓ : LocalList m) i => max ((ℓ i).getD 0) 0)
      (fun _ _ _ => le_max_right _ _)
      (fun i => (measurable_option_getD.comp (measurable_pi_apply i)).max measurable_const) _ _
  · simpa only [templateWorld,dif_neg h] using measurable_completedProfile m n

noncomputable def markerWorld (j : Fin n) (ℓ : LocalList m) : UserProfile m n :=
  templateWorld j (positives ℓ) (zeros ℓ) ℓ

theorem measurable_markerWorld (j : Fin n) : Measurable (markerWorld (m := m) j) := by
  have hm : Measurable (fun z : (Finset (Fin m) × Finset (Fin m)) × LocalList m =>
      templateWorld j z.1.1 z.1.2 z.2) :=
    measurable_from_prod_countable_right (fun z => measurable_templateWorld j z.1 z.2)
  exact hm.comp ((measurable_positives.prodMk measurable_zeros).prodMk measurable_id)

theorem completionCode_of_eligible (cutoff : ℝ) (ℓ : LocalList m)
    (hroom : n-1 ≤ m-n*c) (hℓ : Eligible cutoff ℓ n c) :
    CompletionCode (positives ℓ) (zeros ℓ) n := by
  refine ⟨positives_disjoint_zeros ℓ,hℓ.2.2,?_⟩
  exact hroom.trans (Nat.sub_le_sub_left hℓ.1 _)

theorem list_decomposition (ℓ : LocalList m) (hℓ : NonnegativeList ℓ) :
    ∀ i, ℓ i=if i ∈ positives ℓ then some (max ((ℓ i).getD 0) 0)
      else if i ∈ zeros ℓ then some 0 else none := by
  classical
  intro i
  cases he : ℓ i with
  | none => simp [positives,zeros,he]
  | some b =>
    have hb : 0 ≤ b := by simpa only [he,entryBid] using hℓ i
    by_cases hb0 : b=0
    · simp [positives,zeros,he,hb0]
    · have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      simp [positives,he,hbp,max_eq_left hb]

theorem observe_markerWorld (j : Fin n) (cutoff : ℝ) (ℓ : LocalList m)
    (hroom : n-1 ≤ m-n*c) (helig : Eligible cutoff ℓ n c)
    (hℓ : NonnegativeList ℓ) :
    observe (drawsRealization (markerWorld j ℓ)) j=ℓ := by
  classical
  let P := positives ℓ
  let Z := zeros ℓ
  have hcode : CompletionCode P Z n := completionCode_of_eligible cutoff ℓ hroom helig
  let M := Classical.choose (exists_markers_extending P Z hcode.1 hcode.2.1 hcode.2.2)
  let r : Fin n := ⟨Z.card,hcode.2.1⟩
  have hM : ∀ i, (∃ l : Fin (n-1), M.identity l=i ∧ l.val<Z.card) ↔ i ∈ Z :=
    Classical.choose_spec (exists_markers_extending P Z hcode.1 hcode.2.1 hcode.2.2)
  have hlist : roleList P (fun i => max ((ℓ i).getD 0) 0) M r=ℓ := by
    funext i
    rw [list_decomposition ℓ hℓ i]
    change roleList P (fun i => max ((ℓ i).getD 0) 0) M r i=
      if i ∈ P then some (max ((ℓ i).getD 0) 0) else if i ∈ Z then some 0 else none
    by_cases hi : i ∈ P
    · simp [roleList,hi,P]
    · simp only [roleList,hi,if_false]
      have hm : (∃ l : Fin (n-1), M.identity l=i ∧ l.val<r.val) ↔ i ∈ Z := hM i
      simp only [hm]
  change observe (drawsRealization (templateWorld j P Z ℓ)) j=ℓ
  simp only [templateWorld,dif_pos hcode]
  rw [observe_world,Equiv.swap_apply_left]
  exact hlist

noncomputable def fallbackKernel (j : Fin n) (cutoff : ℝ) :
    Kernel (LocalList m) (UserProfile m n) := by
  classical
  exact Kernel.piecewise (measurableSet_eligible (n := n) (c := c) cutoff)
    (Kernel.deterministic (markerWorld j) (measurable_markerWorld j)) (broadcastFallback m n)

instance (j : Fin n) (cutoff : ℝ) :
    IsMarkovKernel (fallbackKernel (m := m) (c := c) j cutoff) := by
  unfold fallbackKernel
  infer_instance

theorem fallbackKernel_at_eligible (j : Fin n) (cutoff : ℝ) (ℓ : LocalList m)
    (hℓ : Eligible cutoff ℓ n c) :
    fallbackKernel (c := c) j cutoff ℓ=Measure.dirac (markerWorld j ℓ) := by
  simp only [fallbackKernel,Kernel.piecewise_apply,Set.mem_setOf_eq,if_pos hℓ,Kernel.deterministic_apply]

theorem fallbackKernel_feasible (j : Fin n) (cutoff : ℝ) (hroom : n-1 ≤ m-n*c)
    (ℓ : LocalList m) (hℓ : FeasibleObservedList j ℓ) :
    ∀ᵐ d ∂fallbackKernel (c := c) j cutoff ℓ, observe (drawsRealization d) j=ℓ := by
  classical
  by_cases he : Eligible cutoff ℓ n c
  · rw [fallbackKernel_at_eligible j cutoff ℓ he]
    apply (ae_dirac_iff (measurableSet_eq_lists (measurable_observe_draws j) measurable_const)).mpr
    exact observe_markerWorld j cutoff ℓ hroom he ((feasibleObservedList_iff_nonnegative j ℓ).mp hℓ)
  · simpa only [fallbackKernel,Kernel.piecewise_apply,Set.mem_setOf_eq,if_neg he] using
      broadcastFallback_feasible j ℓ hℓ

end FCAppendix.Exclusive.Marker
