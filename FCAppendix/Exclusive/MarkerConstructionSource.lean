import FCAppendix.Exclusive.MarkerConstructionSorted
import FCAppendix.Exclusive.MarkerConstructionPosterior

namespace FCAppendix.Exclusive.Marker

open MeasureTheory ProbabilityTheory Game Bayes Set
open scoped BigOperators

variable {m n c : ℕ}

noncomputable def sourceFallbackKernel (hm : 0 < m) (j : Fin n) (cutoff : ℝ) :
    Kernel (LocalList m) (UserProfile m n) := by
  classical
  exact Kernel.piecewise (measurableSet_sourceEligible (n := n) (c := c) hm cutoff)
    (Kernel.deterministic (markerWorld j) (measurable_markerWorld j)) (broadcastFallback m n)

instance (hm : 0 < m) (j : Fin n) (cutoff : ℝ) :
    IsMarkovKernel (sourceFallbackKernel (c := c) hm j cutoff) := by
  unfold sourceFallbackKernel
  infer_instance

theorem sourceFallbackKernel_at_eligible (hm : 0 < m) (j : Fin n) (cutoff : ℝ)
    (ℓ : LocalList m) (he : SourceEligible hm cutoff ℓ n c) :
    sourceFallbackKernel (c := c) hm j cutoff ℓ=Measure.dirac (markerWorld j ℓ) := by
  simp only [sourceFallbackKernel,Kernel.piecewise_apply,Set.mem_setOf_eq,
    if_pos he,Kernel.deterministic_apply]

theorem sourceFallbackKernel_feasible (hm : 0 < m) (j : Fin n) (cutoff : ℝ)
    (hroom : n-1 ≤ m-n*c) (ℓ : LocalList m) (hℓ : FeasibleObservedList j ℓ) :
    ∀ᵐ d ∂sourceFallbackKernel (c := c) hm j cutoff ℓ, observe (drawsRealization d) j=ℓ := by
  classical
  by_cases he : SourceEligible hm cutoff ℓ n c
  · rw [sourceFallbackKernel_at_eligible hm j cutoff ℓ he]
    apply (ae_dirac_iff (measurableSet_eq_lists (measurable_observe_draws j) measurable_const)).mpr
    exact observe_markerWorld j cutoff ℓ hroom he.1 ((feasibleObservedList_iff_nonnegative j ℓ).mp hℓ)
  · simpa only [sourceFallbackKernel,Kernel.piecewise_apply,Set.mem_setOf_eq,if_neg he] using
      broadcastFallback_feasible j ℓ hℓ

theorem source_marker_optimal {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ)
    (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c) (cutoff : ℝ)
    (fallback : LocalPolicy m c Seed)
    (hpolicy : ∀ j ℓ s, (Γ.policy j ℓ s).val=(sourceContinuation hm hn hc cutoff fallback ℓ s).val)
    (hroom : n-1 ≤ m-n*c) (j : Fin n) (ℓ : LocalList m)
    (helig : SourceEligible hm cutoff ℓ n c) (hℓ : FeasibleObservedList j ℓ)
    (hpost : B.posterior j ℓ=Measure.dirac (markerWorld j ℓ)) (s : Seed) :
    Finite.Optimal c (exclusiveReceipts (posteriorCountBelief Γ B j ℓ) ℓ) (Γ.policy j ℓ s).val := by
  classical
  let P := positives ℓ
  let Z := zeros ℓ
  let b := fun i => max ((ℓ i).getD 0) 0
  have hb : ∀ i ∈ P, 0 < b i := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2.trans_le (le_max_left _ _)
  have hb_eq : ∀ i ∈ P, b i=(ℓ i).getD 0 := by
    intro i hi
    exact max_eq_left (Finset.mem_filter.mp hi).2.le
  have hdist : Set.InjOn b P := by
    have hd := ((sourceEligible_iff hm cutoff ℓ).mp helig).2
    intro i hi l hl he
    apply hd hi hl
    change (ℓ i).getD 0=(ℓ l).getD 0
    rw [← hb_eq i hi,← hb_eq l hl]
    exact he
  have hcode : CompletionCode P Z n := completionCode_of_eligible cutoff ℓ hroom helig.1
  let M := Classical.choose (exists_markers_extending P Z hcode.1 hcode.2.1 hcode.2.2)
  let roles := Equiv.swap j (⟨Z.card,hcode.2.1⟩ : Fin n)
  have hw : markerWorld j ℓ=world P b (fun i hi => (hb i hi).le) M roles := by
    change templateWorld j P Z ℓ=_
    unfold templateWorld
    rw [dif_pos hcode]
  let target := targetOfSingleton (lows cutoff ℓ) helig.1.2.1
  have hlow : lows cutoff ℓ={target} := singleton_target _ helig.1.2.1
  have htarget_low : target ∈ lows cutoff ℓ := by rw [hlow]; simp
  have htarget : target ∈ P := lows_subset_positives cutoff ℓ htarget_low
  have hsmall : b target<cutoff := by
    rw [hb_eq target htarget]
    exact (Finset.mem_filter.mp htarget_low).2.2
  have hhigh : ∀ i ∈ P, i≠target → cutoff ≤ b i := by
    intro i hi hine
    by_contra hnot
    have hilow : i ∈ lows cutoff ℓ := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2,?_⟩
      rw [← hb_eq i hi]
      exact lt_of_not_ge hnot
    have heq : i=target := by simpa only [hlow,Finset.mem_singleton] using hilow
    exact hine heq
  have hP : P.card≤n*c := helig.1.1
  obtain ⟨Q,hQ⟩ := exists_sorted_partition hm hn hc P hP target htarget b hdist
  have hselect : ∀ l z, (Γ.policy l (roleList P b M (roles l)) z).val=Q.block (roles l) := by
    intro l z
    rw [hpolicy,sourceContinuation_roleList hm hn hc cutoff fallback P hP b hb hdist M
      (roles l) target htarget hsmall hhigh z,← hQ]
  have hlist : roleList P b M (roles j)=ℓ := by
    have hh := observe_markerWorld j cutoff ℓ hroom helig.1
      ((feasibleObservedList_iff_nonnegative j ℓ).mp hℓ)
    rw [hw,observe_world] at hh
    exact hh
  have hp : B.posterior j (roleList P b M (roles j))=
      Measure.dirac (world P b (fun i hi => (hb i hi).le) M roles) := by
    rw [hlist,hpost,hw]
  have hopt := optimal_at_world Γ B P Q b hb M roles hselect j hp s
  have hpol := congrArg (fun L => (Γ.policy j L s).val) hlist
  rw [hpol] at hopt
  simpa only [hlist] using hopt

theorem marker_not_goodPosteriorList {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m n c Seed) (Q : Set (UserProfile m n)) (cutoff : ℝ)
    (hQ : ∀ d ∈ Q, ∀ i, (d i).1.2.routeCount=0 ∨ cutoff ≤ (d i).1.2.bid)
    (j : Fin n) (ℓ : LocalList m) (hlow : (lows cutoff ℓ).Nonempty) :
    ℓ ∉ goodPosteriorLists Γ Q j := by
  classical
  obtain ⟨i,hi⟩ := hlow
  have hlow0 : 0<(ℓ i).getD 0 := (Finset.mem_filter.mp hi).2.1
  have hlowt : (ℓ i).getD 0<cutoff := (Finset.mem_filter.mp hi).2.2
  have hno : ∀ d : UserProfile m n, ¬(observe (drawsRealization d) j=ℓ ∧ d ∈ Q) := by
    intro d hd
    have hentry := congrArg (fun L : LocalList m => (L i).getD 0) hd.1
    by_cases hr : j ∈ firstK (d i).2 (d i).1.2.routeCount
    · simp only [observe,drawsRealization,if_pos hr,Option.getD_some] at hentry
      rcases hQ d hd.2 i with hz | hh
      · rw [hz,mem_firstK] at hr
        omega
      · linarith
    · simp only [observe,drawsRealization,if_neg hr,Option.getD_none] at hentry
      linarith
  have he : {d : UserProfile m n | ¬(observe (drawsRealization d) j=ℓ ∧ d ∈ Q)}=univ := by
    ext d
    simp only [mem_setOf_eq,mem_univ,iff_true]
    exact hno d
  intro hgood
  change regularUserPosterior Γ j ℓ {d | ¬(observe (drawsRealization d) j=ℓ ∧ d ∈ Q)}=0 at hgood
  rw [he,measure_univ] at hgood
  exact one_ne_zero hgood

theorem constructed_posterior_at_marker {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m n c Seed) (hm : 0 < m) (cutoff : ℝ) (hroom : n-1 ≤ m-n*c)
    (Q : Set (UserProfile m n)) (hQmeas : MeasurableSet Q)
    (hQfull : ∀ᵐ d ∂userProfileLaw Γ, d ∈ Q)
    (hQ : ∀ d ∈ Q, ∀ i, (d i).1.2.routeCount=0 ∨ cutoff ≤ (d i).1.2.bid)
    (j : Fin n) (ℓ : LocalList m) (helig : SourceEligible hm cutoff ℓ n c) :
    (posteriorWithFallback Γ hQmeas hQfull (fun j => sourceFallbackKernel (c := c) hm j cutoff)
      (fun j L hL => sourceFallbackKernel_feasible hm j cutoff hroom L hL)).posterior j ℓ=
        Measure.dirac (markerWorld j ℓ) := by
  classical
  have hlow : (lows cutoff ℓ).Nonempty := Finset.card_pos.mp (by rw [helig.1.2.1]; omega)
  have hnot := marker_not_goodPosteriorList Γ Q cutoff hQ j ℓ hlow
  change posteriorWithFallbackKernel Γ hQmeas (fun j => sourceFallbackKernel (c := c) hm j cutoff) j ℓ=_
  simp only [posteriorWithFallbackKernel,Kernel.piecewise_apply,if_neg hnot]
  exact sourceFallbackKernel_at_eligible hm j cutoff ℓ helig

theorem constructed_marker_optimal {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m n c Seed) (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c)
    (cutoff : ℝ) (fallback : LocalPolicy m c Seed)
    (hpolicy : ∀ j ℓ s, (Γ.policy j ℓ s).val=(sourceContinuation hm hn hc cutoff fallback ℓ s).val)
    (hroom : n-1 ≤ m-n*c)
    (Q : Set (UserProfile m n)) (hQmeas : MeasurableSet Q)
    (hQfull : ∀ᵐ d ∂userProfileLaw Γ, d ∈ Q)
    (hQ : ∀ d ∈ Q, ∀ i, (d i).1.2.routeCount=0 ∨ cutoff ≤ (d i).1.2.bid)
    (j : Fin n) (ℓ : LocalList m) (helig : SourceEligible hm cutoff ℓ n c)
    (hℓ : FeasibleObservedList j ℓ) (s : Seed) :
    let B := posteriorWithFallback Γ hQmeas hQfull (fun j => sourceFallbackKernel (c := c) hm j cutoff)
      (fun j L hL => sourceFallbackKernel_feasible hm j cutoff hroom L hL)
    Finite.Optimal c (exclusiveReceipts (posteriorCountBelief Γ B j ℓ) ℓ) (Γ.policy j ℓ s).val := by
  apply source_marker_optimal Γ _ hm hn hc cutoff fallback hpolicy hroom j ℓ helig hℓ _ s
  exact constructed_posterior_at_marker Γ hm cutoff hroom Q hQmeas hQfull hQ j ℓ helig

end FCAppendix.Exclusive.Marker
