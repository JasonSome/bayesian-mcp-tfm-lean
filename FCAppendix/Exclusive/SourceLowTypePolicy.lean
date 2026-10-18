import FCAppendix.Exclusive.SourceLowTypeCount

noncomputable section
namespace FCAppendix.Bayes.ExclusiveSource

open MeasureTheory ProbabilityTheory Game Exclusive ExclusiveNarrow Set
open scoped BigOperators

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def HighRivals (cutoff : ℝ) (i : Fin m) (d : UserProfile m n) : Prop :=
  ∀ j, j ≠ i → (d j).1.2.routeCount = 0 ∨
    ((d j).1.2.routeCount = n ∧ cutoff ≤ (d j).1.2.bid)

theorem focalList_no_low (cutoff : ℝ) (i : Fin m) (d : UserProfile m n)
    (hd : HighRivals cutoff i d) {b : ℝ} (hb : cutoff ≤ b) :
    Marker.lows cutoff (focalList i b d) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  have hh := (Finset.mem_filter.mp hj).2
  by_cases hji : j = i
  · simp only [focalList,hji,if_true,Option.getD_some] at hh
    exact (not_lt_of_ge hb) hh.2
  · rcases hd j hji with hz | ⟨hr,hfloor⟩
    · simp [focalList,hji,hz] at hh
    · by_cases hn0 : n = 0
      · simp [focalList,hji,hr,hn0] at hh
      · simp only [focalList,if_neg hji,hr,if_neg hn0,Option.getD_some] at hh
        exact (not_lt_of_ge hfloor) hh.2

theorem observe_update_recipient_eq_focalList (cutoff : ℝ) (i : Fin m)
    (d : UserProfile m n) (hd : HighRivals cutoff i d) (x : ℝ × JointAction n)
    (τ : Equiv.Perm (Fin n)) (j : Fin n)
    (hj : j ∈ (drawsRealization (Function.update d i (x,τ))).recipients i) :
    observe (drawsRealization (Function.update d i (x,τ))) j = focalList i x.2.bid d := by
  classical
  have hj' : j ∈ firstK τ x.2.routeCount := by simpa [drawsRealization] using hj
  funext l
  by_cases hli : l = i
  · subst l
    simp [observe,drawsRealization,focalList,hj']
  · rcases hd l hli with hz | ⟨hr,_⟩
    · simp [observe,drawsRealization,focalList,hli,mem_firstK,hz]
    · have hn0 : n ≠ 0 := by have := j.isLt; omega
      simp [observe,drawsRealization,focalList,hli,mem_firstK,hr,hn0]

theorem measurable_focalList (i : Fin m) (b : ℝ) :
    Measurable (focalList (n := n) i b) := by
  classical
  apply measurable_pi_lambda
  intro j
  by_cases hji : j = i
  · simp only [focalList,hji,if_true]
    exact measurable_const
  · simp only [focalList,if_neg hji]
    have ha : Measurable (fun d : UserProfile m n => (d j).1.2) :=
      measurable_snd.comp (measurable_fst.comp (measurable_pi_apply j))
    exact Measurable.ite
      (measurableSet_eq_fun ((measurable_routeCount n).comp ha) measurable_const)
      measurable_const (measurable_some.comp ((measurable_bid n).comp ha))

def focalMarginal (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (i : Fin m) (b : ℝ)
    (d : UserProfile m n) : ℝ :=
  canonicalListMarginal n hn c (focalList i b d) i

theorem measurable_focalMarginal (hn : 2 ≤ n) (hc : 0 < c) (i : Fin m) (b : ℝ) :
    Measurable (focalMarginal n hn c i b) :=
  (measurable_pi_apply i).comp
    ((measurable_canonicalListMarginal m n hn c hc).comp (measurable_focalList i b))

theorem focalMarginal_bounds (hn : 2 ≤ n) (i : Fin m) (b : ℝ) (d : UserProfile m n) :
    0 ≤ focalMarginal n hn c i b d ∧ focalMarginal n hn c i b d ≤ 1 :=
  canonicalMarginal_bounds n hn c (listBids (focalList i b d)) i

theorem source_symmetric_canonical (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c) (cutoff : ℝ)
    (fallback : LocalPolicy m c Seed)
    (hfallback : Measurable (fun p : LocalList m × Seed => (fallback p.1 p.2).val))
    (hcanonical : ∀ ℓ, FiniteLaw.ofMeasure Γ.seedLaw (fun s => (fallback ℓ s).val)
      (hfallback.comp (measurable_const.prodMk measurable_id)) =
        canonicalLottery n hn c (listBids ℓ))
    (hpolicy : ∀ j ℓ s, (Γ.policy j ℓ s).val =
      (Marker.sourceContinuation hm hn hc cutoff fallback ℓ s).val)
    (ℓ : LocalList m) (hℓ : Marker.lows cutoff ℓ = ∅) :
    SymmetricAtList Γ ℓ (canonicalLottery n hn c (listBids ℓ)) := by
  intro j
  have he : (fun s => (Γ.policy j ℓ s).val) = fun s => (fallback ℓ s).val := by
    funext s
    rw [hpolicy,Marker.sourceContinuation_fallback_of_no_low hm hn hc cutoff fallback ℓ hℓ]
  unfold seedLottery
  convert hcanonical ℓ using 1
  congr 1

theorem source_profile_test_large_bid (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c) (cutoff : ℝ)
    (fallback : LocalPolicy m c Seed)
    (hfallback : Measurable (fun p : LocalList m × Seed => (fallback p.1 p.2).val))
    (hcanonical : ∀ ℓ, FiniteLaw.ofMeasure Γ.seedLaw (fun s => (fallback ℓ s).val)
      (hfallback.comp (measurable_const.prodMk measurable_id)) =
        canonicalLottery n hn c (listBids ℓ))
    (hpolicy : ∀ j ℓ s, (Γ.policy j ℓ s).val =
      (Marker.sourceContinuation hm hn hc cutoff fallback ℓ s).val)
    (i : Fin m) (d : UserProfile m n) (hd : HighRivals cutoff i d)
    (x : ℝ × JointAction n) (hb : cutoff ≤ x.2.bid) (τ : Equiv.Perm (Fin n))
    (f : ℕ → ℝ) :
    (profileCountLaw Γ (Function.update d i (x,τ)) i).expect (fun r => f r.val) =
      Exclusive.Narrow.binomialPolynomial x.2.routeCount f
        (focalMarginal n hn c i x.2.bid d) := by
  have hs := source_symmetric_canonical Γ hm hn hc cutoff fallback hfallback hcanonical
    hpolicy (focalList i x.2.bid d) (focalList_no_low cutoff i d hd hb)
  have he := profile_test_of_recipient_common_list Γ (Function.update d i (x,τ)) i
    (focalList i x.2.bid d)
    (observe_update_recipient_eq_focalList cutoff i d hd x τ)
    (canonicalLottery n hn c (listBids (focalList i x.2.bid d))) hs f
  simpa only [drawsRealization,Function.update_self,card_firstK τ x.2.routeCount x.2.routeCount_le,
    canonicalLottery_marginal,focalMarginal,canonicalListMarginal] using he

end FCAppendix.Bayes.ExclusiveSource
