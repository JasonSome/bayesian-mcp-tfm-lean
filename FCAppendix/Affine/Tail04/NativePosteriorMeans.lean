import FCAppendix.Affine.Tail04.NativePosteriorIntegration

noncomputable section
namespace FCAppendix.Affine.Tail04.NativePosteriorMeans
open MeasureTheory ProbabilityTheory Set Classical Filter Game Bayes
open LocalCoordinates SortedCoordinates NativeLocalPolicy NativeObservationPair
open NativePolicyFactor NativePosteriorIntegration OriginalValues OriginalPopulation
open OriginalPrivateSource NativePrivatePosterior Existence.Distributional Hybrid

variable {m c : ℕ} (D : Data m c) (P : ValueParameters) (hd : D.E.d=P.d0)
    (t : ℝ) (ht : P.M≤ t)
local instance : IsProbabilityMeasure (P.originalMovingActiveLaw t ht) :=
  P.originalMovingActiveLaw_probability t ht
variable (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
    (πP : Law (A:=Icc D.E.R D.E.Rp) P.originalPartialLaw)
    (πA : Law (A:=Icc (1:ℝ) D.E.U) (P.originalMovingActiveLaw t ht))
    (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)
    (hfloor : ∀ v,t< v → D.E.H≤ upperBid v)
    (hrows : ∀ H : Fin (m+1),D.originalPrivateRow H=
      originalPrivateRow D.E P hd t ht πL πP πA upperBid hupperBid hfloor H.val)
    (Γ : FiniteGame m 2 c Seed)
    (hjoint : Γ.F ⊗ₘ Γ.σ=(originalJoint P t ht D.E.R D.E.Rp D.E.U
      (D.E.d_nonneg.trans D.E.d_lt_R.le) πL πP πA upperBid hupperBid : Measure _))
    (hseed : Γ.seedLaw=seedLaw)
    (hpolicy : ∀ j,Γ.policy j=D.completedPolicy j)
    (B : PosteriorSystem Γ)

include P hd t ht πL πP πA upperBid hupperBid hfloor hrows hjoint hseed hpolicy in
theorem original_means (j : Fin 2) :
    ∀ᵐ L ∂observedListLaw Γ j,
      NonnegativeList L ∧ D.offCommon L=∅ ∧
      (∀ i,D.E.localTag (L i)=2 → posteriorOtherMean Γ B j L i=0) ∧
      (∀ i,D.E.localTag (L i)=0 → posteriorOtherMean Γ B j L i=
        NativeExactLow.acceptance D.ξ D.xi_pos D.xi_lt_one c (otherProposer j)
          (Observable.Regions.lowContext D.E j L) i) ∧
      (∀ i (hi : i∈ids D.E 1 L),posteriorOtherMean Γ B j L i=
        D.oppositeActiveMean j L (rankFin (ids D.E 1 L) (bidVector L) ⟨i,hi⟩)) := by
  filter_upwards [original_native_private_posterior_all D.E P hd t ht πL πP πA
      upperBid hupperBid hfloor Γ hjoint B j,
    posterior_original_sourceBands D.E P hd t ht πL πP πA
      upperBid hupperBid hfloor Γ hjoint B j,B.ae_observation Γ j]
    with L hrow hsource hobs
  have hgood : ∀ᵐ d ∂B.posterior j L,
      (∀ i,sourceBands P D.E t (d i).1) ∧ observe (drawsRealization d) j=L :=
    hsource.and hobs
  obtain ⟨d0,hs0,ho0⟩ := hgood.exists
  have hnonneg : NonnegativeList L :=
    (feasibleObservedList_iff_nonnegative j L).mp ⟨d0,ho0⟩
  have hmenu : D.offCommon L=∅ := by
    rw [←ho0]
    exact D.source_on_menu P t d0 hs0 j
  refine ⟨hnonneg,hmenu,?_,?_,?_⟩
  · intro i hi
    apply private_posterior_mean Γ B j L i
    filter_upwards [hgood] with d hd
    have hc := D.E.source_list_compatible P t d hd.1 j
    rw [hd.2] at hc
    exact (D.E.entry_private_other_absent (hc i)).mp hi
  · intro i hi
    apply low_posterior_mean Γ B hseed D j L i
    filter_upwards [hgood] with d hd
    have hc := D.E.source_list_compatible P t d hd.1 j
    rw [hd.2] at hc
    intro u
    rw [hpolicy (otherProposer j),D.completed_on_menu (otherProposer j) _
      (D.source_on_menu P t d hd.1 (otherProposer j)) u]
    exact (NativePolicyFactor.opposite_low_factor D) hc j i hi u
  · intro i hi
    letI : PolishSpace (Ici D.E.H) := isClosed_Ici.polishSpace
    letI : PolishSpace (Icc D.E.R D.E.Rp) := isClosed_Icc.polishSpace
    let S := ids D.E 3 L
    have hmask : ∀ k,L k=none ↔ k∈S := by
      intro k
      simp only [S,ids,Finset.mem_filter,Finset.mem_univ,true_and,D.E.localTag_absent]
    have hlaw : (B.posterior j L).map
        (fun d : UserProfile m 2 => privateRow D.E S
          (observe (drawsRealization d) (otherProposer j)))=
        ((D.originalPrivateRow (D.finiteCount S) : Measure (EqualPrivateUpper.Row (D.finiteCount S).val D.E.R D.E.Rp D.E.H))) := by
      erw [hrows]
      convert! hrow S hmask using 1
    have hmrow : Measurable (fun d : UserProfile m 2 => privateRow D.E S
        (observe (drawsRealization d) (otherProposer j))) :=
      (measurable_privateRow D.E S).comp (measurable_observe_draws (otherProposer j))
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    · rw [(NativePolicyFactor.oppositeActiveMean_zero D),Data.zeroMean]
      apply sampler_posterior_mean Γ B hseed 0 L i
        (D.oneSampler (ids D.E 1 L).card (D.finiteCount (ids D.E 2 L)) (D.finiteCount S))
        (D.oneSampler_measurable _ _ _)
        (D.parameter (ids D.E 1 L) (D.finiteCount (ids D.E 2 L)) (D.finiteCount S) L)
        _ hmrow _ hlaw (Sum.inl (rankFin (ids D.E 1 L) (bidVector L) ⟨i,hi⟩))
      filter_upwards [hgood] with d hd
      have hc := D.E.source_list_compatible P t d hd.1 0
      rw [hd.2] at hc
      intro u
      rw [hpolicy (otherProposer 0),D.completed_on_menu (otherProposer 0) _
        (D.source_on_menu P t d hd.1 (otherProposer 0)) u]
      simpa only [S,otherProposer,ite_true] using (NativePolicyFactor.opposite_one_factor D) hc i hi u
    · rw [(NativePolicyFactor.oppositeActiveMean_one D),Data.oneMean]
      apply sampler_posterior_mean Γ B hseed 1 L i
        (D.zeroSampler (ids D.E 1 L).card (D.finiteCount S) (D.finiteCount (ids D.E 2 L)))
        (D.zeroSampler_measurable _ _ _)
        (D.parameter (ids D.E 1 L) (D.finiteCount S) (D.finiteCount (ids D.E 2 L)) L)
        _ hmrow _ hlaw (Sum.inl (rankFin (ids D.E 1 L) (bidVector L) ⟨i,hi⟩))
      filter_upwards [hgood] with d hd
      have hc := D.E.source_list_compatible P t d hd.1 1
      rw [hd.2] at hc
      intro u
      rw [hpolicy (otherProposer 1),D.completed_on_menu (otherProposer 1) _
        (D.source_on_menu P t d hd.1 (otherProposer 1)) u]
      simpa only [S,otherProposer,if_neg (by decide : (1:Fin 2)≠0)] using
        (NativePolicyFactor.opposite_zero_factor D) hc i hi u

end FCAppendix.Affine.Tail04.NativePosteriorMeans
