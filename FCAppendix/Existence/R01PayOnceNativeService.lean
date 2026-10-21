import FCAppendix.Existence.R01PayOnceNativePayoff
import FCAppendix.PayOnce.GeneralParticipation

noncomputable section
namespace FCAppendix.Bayes.PayOnceConstruction
open MeasureTheory ProbabilityTheory Game Set Filter
open Existence.PayOnceBounded
variable {N k c : ℕ} (hn : 2≤k+1) (F : Measure ℝ) [IsProbabilityMeasure F]
    {W : ℝ} (κ : Kernel ℝ (FloorAction 0 W)) [IsMarkovKernel κ]
    (g : ℝ) (hg : 0≤g)
local notation "Gamma"=>mixedGame (N+1) (k+1) c hn F κ (Schedule.once (k+1)) g hg

theorem mixedGame_positive_full_support
    (hsupport : ∀ᵐv ∂F,∀ᵐa ∂κ v,
      (v≤g ↔ present a=false) ∧ (present a=true→0<bid a)) :
    ∀ᵐx ∂((Gamma).F ⊗ₘ (Gamma).σ),
      (Gamma).g<x.1→0<x.2.bid ∧ x.2.routeCount=k+1 := by
  apply Measure.ae_compProd_of_ae_ae
  · change MeasurableSet {x : ℝ×JointAction (k+1) | g<x.1→0<x.2.bid ∧ x.2.routeCount=k+1}
    have hv : MeasurableSet {x : ℝ×JointAction (k+1) | g<x.1}:=
      measurableSet_lt measurable_const measurable_fst
    have hb : MeasurableSet {x : ℝ×JointAction (k+1) | 0<x.2.bid}:=
      measurableSet_lt measurable_const ((measurable_bid (k+1)).comp measurable_snd)
    have hr : MeasurableSet {x : ℝ×JointAction (k+1) | x.2.routeCount=k+1}:=
      measurableSet_eq_fun ((measurable_routeCount (k+1)).comp measurable_snd) measurable_const
    simpa only [imp_iff_not_or,setOf_or,setOf_and,compl_setOf] using hv.compl.union (hb.inter hr)
  · filter_upwards [hsupport] with v hv
    change ∀ᵐa ∂(κ.map (nativeAction (k+1))) v,g<v→0<a.bid ∧ a.routeCount=k+1
    rw [Kernel.map_apply _ (measurable_nativeAction (k+1) W)]
    apply (ae_map_iff (measurable_nativeAction (k+1) W).aemeasurable ?_).mpr
    · filter_upwards [hv] with a ha hvpos
      have hpres : present a=true := by
        cases hp : present a
        · exact False.elim (not_le_of_gt hvpos (ha.1.mpr hp))
        · rfl
      have hb:=ha.2 hpres
      cases a with
      | inl u=>simp [present] at hpres
      | inr b=>exact ⟨hb,rfl⟩
    · by_cases hvpos : g<v
      · simpa only [hvpos,true_implies,setOf_and] using
          (measurableSet_lt measurable_const (measurable_bid (k+1))).inter
            (measurableSet_eq_fun (measurable_routeCount (k+1)) measurable_const)
      · simpa only [hvpos,false_implies,setOf_true] using (MeasurableSet.univ (α:=JointAction (k+1)))

theorem mixedGame_positive_service (hc : 1≤c) (hcm : c≤N+1)
    (hsupport : ∀ᵐv ∂F,∀ᵐa ∂κ v,
      (v≤g ↔ present a=false) ∧ (present a=true→0<bid a)) (i : Fin (N+1)) :
    ∀ᵐx ∂((Gamma).F ⊗ₘ (Gamma).σ),g<x.1→0<((problem Gamma i).outcome x.2).success := by
  have hroute : ∀ᵐx ∂((Gamma).F ⊗ₘ (Gamma).σ),
      0<x.2.bid→0<x.2.routeCount→x.2.routeCount=k+1 := by
    filter_upwards [mixedGame_ae_shape (m:=N+1) (c:=c) hn F κ (Schedule.once (k+1)) g hg] with x hx hb _
    rcases hx with hz|hr
    · rw [hz.2] at hb; exact False.elim (lt_irrefl _ hb)
    · exact hr
  exact ae_positive_success_from_full_positive_profiles Gamma (by omega) (by omega) hcm rfl
    (mixedPosterior (m:=N+1) (c:=c) hn F κ (Schedule.once (k+1)) g hg)
    (mixedGame_proposer_optimal hn F κ (Schedule.once (k+1)) g hg)
    (mixedGame_symmetric hn F κ (Schedule.once (k+1)) g hg) hroute
    (mixedGame_positive_full_support hn F κ g hg hsupport) i

theorem mixedGame_positiveQ_ae (hc : 1≤c) (hcm : c≤N+1)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W))
    (hbid : realBidLaw Gamma=(π : Measure (Value W × FloorAction 0 W)).map (fun z=>bid z.2))
    (hsupport : ∀ᵐv ∂F,∀ᵐa ∂κ v,
      (v≤g ↔ present a=false) ∧ (present a=true→0<bid a)) :
    ∀ᵐv ∂F,∀ᵐa ∂κ v,g<v→0<positiveQ N (k+1) c π a := by
  have hs:=Measure.ae_ae_of_ae_compProd
    (mixedGame_positive_service hn F κ g hg hc hcm hsupport (0 : Fin (N+1)))
  filter_upwards [hs] with v hv
  have hmap : ∀ᵐa ∂(κ v).map (nativeAction (k+1)),
      g<v→0<((problem Gamma 0).outcome a).success := by
    simpa only [mixedGame,Kernel.map_apply _ (measurable_nativeAction (k+1) W)] using hv
  have hp:=ae_of_ae_map (measurable_nativeAction (k+1) W).aemeasurable hmap
  filter_upwards [hp] with a ha hvpos
  rw [←mixedGame_native_success hn F κ g hg π hbid 0 a]
  exact ha hvpos

end FCAppendix.Bayes.PayOnceConstruction
