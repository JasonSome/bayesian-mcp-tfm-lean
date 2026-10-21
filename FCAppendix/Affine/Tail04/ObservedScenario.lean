import FCAppendix.Affine.Tail04.PublicScenario
import FCAppendix.Affine.Tail04.OriginalPopulationSupport

noncomputable section
namespace FCAppendix.Affine.Tail04.ObservedScenario
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Hybrid NativeFlag PublicScenario OriginalValues OriginalPopulation

variable (E : Observable.Regions)

lemma coarseTag_low_iff (u : UserDraw 2) : E.coarseTag u=0 ↔ u.1.2.bid≤ E.d := by
  have hupper : (Hybrid.upperRow u.2).1≠(0:Fin 4) := by
    unfold Hybrid.upperRow
    split <;> norm_num [Fin.ext_iff]
  by_cases hl : u.1.2.bid≤ E.d
  · simp [Observable.Regions.coarseTag,Observable.Regions.collapse,hl]
  · by_cases hp : u.1.2.bid∈E.privateBids <;>
      simp [Observable.Regions.coarseTag,Observable.Regions.collapse,hl,hp,hupper]

theorem observed_low_list {m : ℕ} (d : UserProfile m 2) (k : Fin m → Fin 4)
    (hk : ∀ i,E.coarseTag (d i)=k i)
    (hroute : ∀ i,(d i).1.2.bid≤ E.d → (d i).1.2.routeCount=2) (j : Fin 2) :
    E.roleList 0 (observe (drawsRealization d) j)=
      fun i => if k i=0 then some (d i).1.2.bid else none := by
  funext i
  have htag : k i=0 ↔ (d i).1.2.bid≤ E.d := by rw [← hk i];exact coarseTag_low_iff E (d i)
  by_cases hl : (d i).1.2.bid≤ E.d
  · have hr := hroute i hl
    simp [Observable.Regions.roleList,Observable.Regions.localTag,
      observe,drawsRealization,hr,Hybrid.firstK_full_two,hl,htag.mpr hl]
  · have hk0 : k i≠0 := fun h => hl (htag.mp h)
    by_cases hj : j∈firstK (d i).2 (d i).1.2.routeCount
    · by_cases hp : (d i).1.2.bid∈E.privateBids <;>
        simp [Observable.Regions.roleList,Observable.Regions.localTag,
          observe,drawsRealization,hj,hl,hp,hk0]
    · simp [Observable.Regions.roleList,Observable.Regions.localTag,
        observe,drawsRealization,hj,hk0]

lemma observed_seed {m n : ℕ} (μL : Measure ℝ) (d : UserProfile m 2)
    (k : Fin m → Fin 4) (hk : ∀ i,E.coarseTag (d i)=k i)
    (hroute : ∀ i,(d i).1.2.bid≤ E.d → (d i).1.2.routeCount=2)
    (e : Fin (n+1) ≃ {i : Fin m // k i=0}) (j : Fin 2) :
    Hybrid.seedOnList μL (E.roleList 0 (observe (drawsRealization d) j))=
      some (Hybrid.conditionalMinimumSeed μL n (fun l => (d (e l)).1.2.bid)) := by
  exact Hybrid.seedOnList_enumeration μL (fun i => k i=0) e
    (fun i => (d i).1.2.bid) _ (fun i => congrFun (observed_low_list E d k hk hroute j) i)

theorem sourceBands_low_broadcast (P : ValueParameters) (t : ℝ)
    (x : ℝ × JointAction 2) (hx : OriginalPopulation.sourceBands P E t x) :
    x.2.bid≤ E.d → x.2.routeCount=2 := by
  intro hl
  rcases hx with hx | hx | hx | hx
  · exact hx.2.2
  · exact False.elim ((not_lt.mpr hl) (E.private_above_low (Or.inl hx.2.1)))
  · exact hx.2.2
  · exact False.elim ((not_lt.mpr hl) (E.private_above_low (Or.inr hx.2.1)))

section Native
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
variable (Γ : FiniteGame m 2 c Seed)

lemma ae_profile_low_broadcast
    (h : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.bid≤ E.d → x.2.routeCount=2) :
    ∀ᵐ d ∂userProfileLaw Γ, ∀ i,(d i).1.2.bid≤ E.d → (d i).1.2.routeCount=2 := by
  have hu : ∀ᵐ x ∂userLaw Γ, x.1.2.bid≤ E.d → x.1.2.routeCount=2 :=
    (Measure.quasiMeasurePreserving_fst (μ:=Γ.F ⊗ₘ Γ.σ) (ν:=permLaw 2)).ae h
  exact ae_all_iff.mpr (fun i =>
    (measurePreserving_eval (fun _ : Fin m=>userLaw Γ) i).quasiMeasurePreserving.ae hu)

lemma ae_cond_background_low_broadcast (k : Fin m → Fin 4)
    (h : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.bid≤ E.d → x.2.routeCount=2) :
    ∀ᵐ x ∂ProbabilityTheory.cond (backgroundLaw Γ) (categoryFiber E.coarseTag k ×ˢ univ),
      ∀ i,(x.1 i).1.2.bid≤ E.d → (x.1 i).1.2.routeCount=2 := by
  have hb : ∀ᵐ x ∂backgroundLaw Γ,
      ∀ i,(x.1 i).1.2.bid≤ E.d → (x.1 i).1.2.routeCount=2 :=
    (Measure.quasiMeasurePreserving_fst (μ:=userProfileLaw Γ)
      (ν:=Measure.pi (fun _ : Fin 2=>Γ.seedLaw))).ae (ae_profile_low_broadcast E Γ h)
  unfold ProbabilityTheory.cond
  exact Measure.ae_smul_measure (ae_restrict_of_ae hb) _

theorem localChoice_native_joint (P : PublicScenario.Data)
    (k : Fin m → Fin 4)
    (hmass : ∀ i,(userLaw Γ) (E.coarseTag ⁻¹' {k i})≠0)
    (n : ℕ) (e : Fin (n+1) ≃ {i : Fin m // k i=0})
    (hLowBid : ∀ b,nativeLowBidLaw Γ E {b}=0)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.bid≤ E.d → x.2.routeCount=2)
    (N : ℕ)
    (C : NonlowData (Seed:=Seed) k → TypicalGuard.BidBox N E.U × (ℕ × ℕ))
    (hC : Measurable C) (j : Fin 2) :
    (ProbabilityTheory.cond (backgroundLaw Γ) (categoryFiber E.coarseTag k ×ˢ univ)).map
      (fun x => let z := seedAndNonlow Γ E k n e x
        (z.2,PublicScenario.localChoice E P (nativeLowBidLaw Γ E) N
          (E.roleList 0 (observe (drawsRealization x.1) j),C z.2))) =
      ((nonlowLaw Γ E k).prod (volume : Measure unitInterval)).map
        (fun z => (z.1,PublicScenario.draw P N
          (TypicalGuard.bids (C z.1).1,(C z.1).2) z.2)) := by
  letI (i : {i : Fin m // k i ≠ 0}) :
      IsProbabilityMeasure (ProbabilityTheory.cond (userLaw Γ) (E.coarseTag ⁻¹' {k i})) :=
    cond_isProbabilityMeasure (hmass i)
  letI : IsProbabilityMeasure (nonlowLaw Γ E k) := by
    unfold nonlowLaw
    infer_instance
  let μ := ProbabilityTheory.cond (backgroundLaw Γ) (categoryFiber E.coarseTag k ×ˢ univ)
  let f : NonlowData (Seed:=Seed) k × unitInterval →
      NonlowData (Seed:=Seed) k × (JoinedHighPolicy.Scenario N × unitInterval) :=
    fun z => (z.1,PublicScenario.draw P N
      (TypicalGuard.bids (C z.1).1,(C z.1).2) z.2)
  have hf : Measurable f :=
    measurable_fst.prodMk ((PublicScenario.measurable_draw P N).comp
      ((((TypicalGuard.continuous_bids.measurable.comp hC.fst).prodMk hC.snd).comp
        measurable_fst).prodMk measurable_snd))
  have hswap : ((volume : Measure unitInterval).prod (nonlowLaw Γ E k)).map Prod.swap=
      (nonlowLaw Γ E k).prod (volume : Measure unitInterval) :=
    (Measure.measurePreserving_swap (μ := (volume : Measure unitInterval))
      (ν := nonlowLaw Γ E k)).map_eq
  have hshape : ∀ᵐ x ∂μ, ∀ i,E.coarseTag (x.1 i)=k i := by
    have hc : ∀ᵐ x ∂μ,x∈categoryFiber E.coarseTag k ×ˢ univ := by
      unfold μ ProbabilityTheory.cond
      apply Measure.ae_smul_measure
      exact ae_restrict_mem ((measurableSet_categoryFiber E.coarseTag E.measurable_coarseTag k).prod
        MeasurableSet.univ)
    exact hc.mono (fun _ hx i => hx.1 i (mem_univ i))
  have hr := ae_cond_background_low_broadcast E Γ k hroute
  calc
    _ = μ.map (f ∘ Prod.swap ∘ seedAndNonlow Γ E k n e) := by
      apply Measure.map_congr
      filter_upwards [hshape,hr] with x hx hrx
      dsimp only [Function.comp_def,f,Prod.swap]
      apply Prod.ext
      · rfl
      · exact PublicScenario.localChoice_of_seed E P (nativeLowBidLaw Γ E) N
          _ (C (seedAndNonlow Γ E k n e x).2).1
          (C (seedAndNonlow Γ E k n e x).2).2 _
          (observed_seed E _ x.1 k hx hrx e j)
    _ = ((μ.map (seedAndNonlow Γ E k n e)).map Prod.swap).map f := by
      rw [Measure.map_map hf measurable_swap,
        Measure.map_map (hf.comp measurable_swap) (measurable_seedAndNonlow Γ E k n e)]
      rfl
    _ = _ := by
      rw [native_seedAndNonlow_law Γ E k hmass n e hLowBid,hswap]

end Native
end FCAppendix.Affine.Tail04.ObservedScenario
