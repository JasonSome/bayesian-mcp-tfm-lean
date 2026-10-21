import FCAppendix.Game.PosteriorFeasible
import FCAppendix.Finite.ReceiptBoundsAE

noncomputable section
namespace FCAppendix.Bayes.SingletonConstruction
open MeasureTheory ProbabilityTheory Game Set Filter
open scoped BigOperators

def singletonAction (n : ℕ) (hn : 0 < n) : Option ℝ → JointAction n
  | none => Interim.abstain n
  | some b => ⟨max b 0, le_max_right _ _, 1, hn⟩

theorem measurable_singletonAction (n : ℕ) (hn : 0 < n) :
    Measurable (singletonAction n hn) := by
  apply Measurable.of_comap_le
  rw [instMeasurableSpaceJointAction, MeasurableSpace.comap_comp]
  change MeasurableSpace.comap
    (fun o : Option ℝ => ((singletonAction n hn o).bid,
      (singletonAction n hn o).routeCount)) inferInstance ≤ _
  apply Measurable.comap_le
  intro s hs
  change MeasurableSet ((fun b : ℝ => (max b 0, (1 : ℕ))) ⁻¹' s)
  exact ((measurable_id.max measurable_const).prodMk measurable_const) hs

def completedSingletonProfile (m n : ℕ) (hn : 0 < n) (j : Fin n)
    (L : LocalList m) : UserProfile m n :=
  fun i => ((0, singletonAction n hn (L i)), Equiv.swap ⟨0, hn⟩ j)

theorem measurable_completedSingletonProfile (m n : ℕ) (hn : 0 < n) (j : Fin n) :
    Measurable (completedSingletonProfile m n hn j) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (measurable_const.prodMk
    ((measurable_singletonAction n hn).comp (measurable_pi_apply i))).prodMk measurable_const

def singletonProfiles (m n : ℕ) : Set (UserProfile m n) :=
  {d | ∀ i, (d i).1.2.routeCount ≤ 1}

theorem measurableSet_singletonProfiles (m n : ℕ) :
    MeasurableSet (singletonProfiles m n) := by
  simp only [singletonProfiles, setOf_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_le
    ((measurable_routeCount n).comp
      (measurable_snd.comp (measurable_fst.comp (measurable_pi_apply i)))) measurable_const

theorem completedSingletonProfile_support (m n : ℕ) (hn : 0 < n) (j : Fin n)
    (L : LocalList m) : completedSingletonProfile m n hn j L ∈ singletonProfiles m n := by
  intro i
  cases he : L i <;>
    simp [completedSingletonProfile, singletonAction, Interim.abstain, he]

theorem observe_completedSingletonProfile {m n : ℕ} (hn : 0 < n) (j : Fin n)
    (L : LocalList m) (hL : NonnegativeList L) :
    observe (drawsRealization (completedSingletonProfile m n hn j L)) j = L := by
  funext i
  cases he : L i with
  | none => simp [observe, drawsRealization, completedSingletonProfile, singletonAction,
      he, Interim.abstain, mem_firstK]
  | some b =>
    have hb : 0 ≤ b := by simpa only [he, entryBid] using hL i
    simp [observe, drawsRealization, completedSingletonProfile, singletonAction,
      he, mem_firstK, max_eq_left hb]

def singletonFallback (m n : ℕ) (hn : 0 < n) (j : Fin n) :
    Kernel (LocalList m) (UserProfile m n) :=
  Kernel.deterministic (completedSingletonProfile m n hn j)
    (measurable_completedSingletonProfile m n hn j)

instance (m n : ℕ) (hn : 0 < n) (j : Fin n) :
    IsMarkovKernel (singletonFallback m n hn j) := by
  unfold singletonFallback
  infer_instance

theorem singletonFallback_feasible {m n : ℕ} (hn : 0 < n) (j : Fin n)
    (L : LocalList m) (hL : FeasibleObservedList j L) :
    ∀ᵐ d ∂singletonFallback m n hn j L, observe (drawsRealization d) j = L := by
  rw [singletonFallback, Kernel.deterministic_apply]
  apply (ae_dirac_iff (measurableSet_eq_lists (measurable_observe_draws j) measurable_const)).mpr
  exact observe_completedSingletonProfile hn j L
    ((feasibleObservedList_iff_nonnegative j L).mp hL)

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def singletonPosterior (Γ : FiniteGame m n c Seed) (hn : 0 < n)
    (hroute : ∀ᵐ d ∂userProfileLaw Γ, d ∈ singletonProfiles m n) : PosteriorSystem Γ :=
  posteriorWithFallback Γ (measurableSet_singletonProfiles m n) hroute
    (singletonFallback m n hn) (singletonFallback_feasible hn)

theorem singletonPosterior_support (Γ : FiniteGame m n c Seed) (hn : 0 < n)
    (hroute : ∀ᵐ d ∂userProfileLaw Γ, d ∈ singletonProfiles m n)
    (j : Fin n) (L : LocalList m) :
    ∀ᵐ d ∂(singletonPosterior Γ hn hroute).posterior j L,
      d ∈ singletonProfiles m n := by
  classical
  change ∀ᵐ d ∂posteriorWithFallbackKernel Γ (measurableSet_singletonProfiles m n)
    (singletonFallback m n hn) j L, _
  by_cases hg : L ∈ goodPosteriorLists Γ (singletonProfiles m n) j
  · simp only [posteriorWithFallbackKernel, Kernel.piecewise_apply, if_pos hg]
    exact (ae_iff.mpr hg).mono fun _ hd => hd.2
  · simp only [posteriorWithFallbackKernel, Kernel.piecewise_apply, if_neg hg,
      singletonFallback, Kernel.deterministic_apply, ae_dirac_eq]
    exact completedSingletonProfile_support m n hn j L

theorem otherCount_zero_of_singleton (Γ : FiniteGame m n c Seed)
    (d : UserProfile m n) (hd : d ∈ singletonProfiles m n)
    (j : Fin n) (L : LocalList m) (hobs : observe (drawsRealization d) j = L)
    (i : Fin m) (b : ℝ) (hi : L i = some b) (s : Fin n → Seed) :
    (otherInclusionCount Γ j i (d, s)).val = 0 := by
  classical
  let x := drawsRealization d
  have hj : j ∈ x.recipients i := by
    by_contra hnot
    have h := congrFun hobs i
    simp [x, observe, hnot, hi] at h
  have hcard : (x.recipients i).card ≤ 1 := by
    rw [x.chosen_size]
    exact hd i
  rw [otherInclusionCount_eq_sum]
  apply Finset.sum_eq_zero
  intro l hl
  have hlj : l ≠ j := Finset.ne_of_mem_erase hl
  have hnot : i ∉ allocation x Γ.policy s l := by
    intro hinc
    have ha : l ∈ accepted x Γ.policy s i := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinc⟩
    have hr := accepted_subset_recipients x Γ.policy s i ha
    exact hlj ((Finset.card_le_one.mp hcard) l hr j hj)
  exact if_neg hnot

theorem singletonPosterior_receipt (Γ : FiniteGame m n c Seed) (hn : 0 < n)
    (hroute : ∀ᵐ d ∂userProfileLaw Γ, d ∈ singletonProfiles m n)
    (j : Fin n) (L : LocalList m) (hL : FeasibleObservedList j L)
    (i : Fin m) (b : ℝ) (hi : L i = some b) :
    Finite.conditionalReceipt Γ.A
      (posteriorCountBelief Γ (singletonPosterior Γ hn hroute) j L i) b = b := by
  let B := singletonPosterior Γ hn hroute
  have hz : ∀ᵐ ω ∂posteriorBackground Γ B j L,
      (otherInclusionCount Γ j i ω).val = 0 := by
    unfold posteriorBackground
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
      ((measurable_of_countable (fun r : Fin n => r.val)).comp
        (measurable_otherInclusionCount Γ j i)) measurable_const)).mpr
    filter_upwards [B.feasible j L hL, singletonPosterior_support Γ hn hroute j L]
      with d hd hs
    exact ae_of_all _ fun s => otherCount_zero_of_singleton Γ d hs j L hd i b hi s
  rw [posterior_receipt_eq_integral]
  have he : (fun ω : Background m n Seed =>
      b * Γ.A.charge ((otherInclusionCount Γ j i ω).val + 1) /
        (((otherInclusionCount Γ j i ω).val : ℝ) + 1)) =ᵐ[posteriorBackground Γ B j L]
      fun _ => b := by
    filter_upwards [hz] with ω hω
    simp only [hω, zero_add, Nat.cast_zero, zero_add, div_one, Γ.A.one hn, mul_one]
  rw [integral_congr_ae he]
  simp

theorem singletonPosterior_receipts (Γ : FiniteGame m n c Seed) (hn : 0 < n)
    (hroute : ∀ᵐ d ∂userProfileLaw Γ, d ∈ singletonProfiles m n)
    (j : Fin n) (L : LocalList m) (hL : FeasibleObservedList j L) :
    beliefReceipts Γ.A (posteriorCountBelief Γ (singletonPosterior Γ hn hroute) j L) L =
      fun i => entryBid (L i) := by
  funext i
  cases hi : L i with
  | none => simp [beliefReceipts, hi, entryBid]
  | some b =>
    simpa only [beliefReceipts, hi, entryBid] using
      singletonPosterior_receipt Γ hn hroute j L hL i b hi

end FCAppendix.Bayes.SingletonConstruction
