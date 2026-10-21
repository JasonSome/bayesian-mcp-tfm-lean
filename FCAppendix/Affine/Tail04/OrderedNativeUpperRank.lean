import FCAppendix.Affine.Tail04.NativeTailUpperRank
import FCAppendix.Affine.Tail04.OrderedNativePolicy

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedNativeUpperRank
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open LocalCoordinates SortedCoordinates NativeLocalPolicy NativeTailUpperRank
open OriginalValues OriginalPopulation
open scoped BigOperators

variable {m c : ℕ} (K : Data m c)

variable (Γ : FiniteGame m 2 c Seed) (P : ValueParameters) (t : ℝ)

lemma source_present_on_menu (i : Fin m) (ω : Background m 2 Seed)
    (hband : ∀ k,k≠i→ sourceBands P K.E t (ω.1 k).1)
    (j : Fin 2) (y : ℝ) (hy : K.E.H≤ y) :
    K.offCommon (presentList ω i y j)=∅ := by
  apply (K.offCommon_eq_empty_iff _).mpr
  intro k hk
  by_cases hki : k=i
  · subst k
    simp only [presentList_self,upper_tag K y hy] at hk
    contradiction
  · have he : presentList ω i y j k=NativePrivatePosterior.observedEntry j (ω.1 k) :=
      presentList_other ω i k hki y j
    rw [he] at hk ⊢
    exact NativeObservationPair.source_active_box K.E P t (ω.1 k) (hband k hki) j hk

theorem native_upper_accepts_iff_rank
    (hpolicy : ∀ j L,NonnegativeList L→∀ u,Γ.policy j L u=OrderedNativePolicy.policy K j L u)
    (hband : ∀ᵐ x ∂userLaw Γ,sourceBands P K.E t x.1)
    (hatom : ∀ (j : Fin 2) (y : ℝ),K.E.H≤ y→
      userLaw Γ {x | j∈firstK x.2 x.1.2.routeCount ∧ x.1.2.bid=y}=0)
    (i : Fin m) (j : Fin 2) (y : ℝ) (hy : K.E.H≤ y) :
    ∀ᵐ ω ∂backgroundLaw Γ,
      Accepts Γ i y j ω ↔ rivals i (aboveAt j y) ω< c := by
  have hsingle := measure_eq_zero_iff_ae_notMem.mp (hatom j y hy)
  have hall : ∀ᵐ d ∂userProfileLaw Γ,∀ k,
      sourceBands P K.E t (d k).1 ∧
        ¬(j∈firstK (d k).2 (d k).1.2.routeCount ∧ (d k).1.2.bid=y) :=
    ae_all_iff.mpr (fun k=>(measurePreserving_eval (fun _ : Fin m=> userLaw Γ) k).quasiMeasurePreserving.ae (hband.and hsingle))
  have hback := (measurePreserving_fst (μ:=userProfileLaw Γ)
    (ν:=Measure.pi fun _ : Fin 2 => Γ.seedLaw)).quasiMeasurePreserving.ae hall
  filter_upwards [hback] with ω hω
  let L := presentList ω i y j
  have hy0 : 0≤ y := ((by norm_num : (0:ℝ)≤1).trans K.E.one_le_U).trans
    (K.E.U_lt_H.le.trans hy)
  have hL : NonnegativeList L := by
    intro k
    cases he : L k with
    | none => exact le_rfl
    | some b => exact presentList_bid_nonneg ω i y hy0 j k b he
  have hn : ∀ k,k≠i→ L k≠some y := fun k hk he=>
    (hω k).2 (presentList_other_some ω i k hk y j y he)
  have hm := source_present_on_menu K P t i ω (fun k _=>(hω k).1) j y hy
  have hs := completed_local_upper_rank K (OrderedNativePolicy.role K.E j L) L hm (ω.2 j) i y hy
    (presentList_self ω i y j) hn
  have heq : (Finset.univ.filter fun k=> y< entryBid (L k))=
      (Finset.univ.erase i).filter fun k=> ω.1 k∈aboveAt j y := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,and_true,
      aboveAt,mem_setOf_eq]
    by_cases hk : k=i
    · subst k
      simp only [L,presentList_self,entryBid,lt_self_iff_false,ne_eq,not_true_eq_false,false_and]
    · rw [show L k=if j∈firstK (ω.1 k).2 (ω.1 k).1.2.routeCount
          then some (ω.1 k).1.2.bid else none from presentList_other ω i k hk y j]
      by_cases hj : j∈firstK (ω.1 k).2 (ω.1 k).1.2.routeCount
      · simp [hj,entryBid,hk]
      · simp [hj,entryBid,not_lt.mpr hy0]
  rw [heq] at hs
  change i∈(Γ.policy j L (ω.2 j)).val ↔ _
  rw [hpolicy j L hL (ω.2 j)]
  simpa only [OrderedNativePolicy.policy,rivals_eq_card] using hs

end FCAppendix.Affine.Tail04.OrderedNativeUpperRank
