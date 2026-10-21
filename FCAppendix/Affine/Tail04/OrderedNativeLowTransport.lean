import FCAppendix.Affine.Tail04.OrderedNativeSourceAllFeasible
import FCAppendix.Affine.Tail04.NativeLowSourceIC
import FCAppendix.Affine.Tail04.GlobalLowerRoutes

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedNativeLowTransport
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Hybrid NativeLocalPolicy NativeMenuReports LocalCoordinates
open OriginalValues OriginalPopulation Existence.Distributional
open scoped BigOperators

variable {m c : ℕ} (D : NativeLocalPolicy.Data m c)
    (Γ : FiniteGame m 2 c NativeLocalPolicy.Seed)

def orderedGame : FiniteGame m 2 c NativeLocalPolicy.Seed :=
  { Γ with policy := OrderedNativePolicy.policy D
           policy_measurable := OrderedNativePolicy.policy_measurable D }

@[simp] lemma userProfileLaw_orderedGame :
    userProfileLaw (orderedGame D Γ)=userProfileLaw Γ := rfl

@[simp] lemma sampleLaw_orderedGame :
    sampleLaw (orderedGame D Γ)=sampleLaw Γ := rfl

lemma low_membership (j : Fin 2) (L : LocalList m)
    (hmenu : D.offCommon L=∅) (u : NativeLocalPolicy.Seed)
    (i : Fin m) (hi : D.E.localTag (L i)=0) :
    (i∈(OrderedNativePolicy.policy D j L u).val) ↔
      i∈(D.completedPolicy j L u).val := by
  unfold OrderedNativePolicy.policy
  rw [D.completed_on_menu _ L hmenu u,D.completed_on_menu j L hmenu u,
    D.policy_low_iff _ L u i hi,D.policy_low_iff j L u i hi,
    OrderedNativePolicy.lowSelect_label_independent D.E D.ξ D.xi_pos D.xi_lt_one
      (OrderedNativePolicy.role D.E j L) j L u.2]

lemma onMenu_present_low (i : Fin m) (b : ℝ) (hb : b≤D.E.d)
    (ω : Background m 2 NativeLocalPolicy.Seed)
    (hr : ∀l,l≠i→MenuAction D.E (ω.1 l).1.2) (j : Fin 2) :
    D.offCommon (presentList ω i b j)=∅ := by
  apply (D.offCommon_eq_empty_iff _).mpr
  intro l hl
  by_cases hli : l=i
  · subst l
    rw [presentList_self] at hl
    have hz : D.E.localTag (some b)=0 := by
      simp [Observable.Regions.localTag,hb]
    rw [hz] at hl
    exact (by decide : (0:Fin 4)≠1) hl |>.elim
  · rw [presentList_other ω i l hli b j] at hl ⊢
    exact menu_active_box D.E (ω.1 l) (hr l hli) j hl

variable (hpolicy : Γ.policy=D.completedPolicy)

include hpolicy in
lemma accepts_eq (i : Fin m) (b : ℝ) (hb : b≤D.E.d)
    (ω : Background m 2 NativeLocalPolicy.Seed)
    (hr : ∀l,l≠i→MenuAction D.E (ω.1 l).1.2) (j : Fin 2) :
    Accepts (orderedGame D Γ) i b j ω ↔ Accepts Γ i b j ω := by
  change (i∈(OrderedNativePolicy.policy D j (presentList ω i b j) (ω.2 j)).val) ↔ _
  unfold Accepts
  rw [hpolicy]
  apply low_membership D j _ (onMenu_present_low D i b hb ω hr j) (ω.2 j) i
  rw [presentList_self]
  simp [Observable.Regions.localTag,hb]

include hpolicy in

theorem focalCount_eq (i : Fin m) (a : JointAction 2) (hb : a.bid≤D.E.d)
    (ω : Sample m 2 NativeLocalPolicy.Seed)
    (hr : ∀l,l≠i→MenuAction D.E (ω.1.1 l).1.2) :
    focalCount (orderedGame D Γ) i a ω=focalCount Γ i a ω := by
  apply Fin.ext
  change inclusionCount (deviated i a ω) (orderedGame D Γ).policy ω.1.2 i=
    inclusionCount (deviated i a ω) Γ.policy ω.1.2 i
  rw [inclusionCount_eq_sum,inclusionCount_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [mem_allocation_deviated_iff,
    accepts_eq D Γ hpolicy i a.bid hb ω.1 hr j]

variable (hprofiles : ∀ᵐp ∂userProfileLaw Γ,∀l,MenuAction D.E (p l).1.2)

include hpolicy hprofiles in

theorem outcome_eq (i : Fin m) (a : JointAction 2) (hb : a.bid≤D.E.d) :
    (problem (orderedGame D Γ) i).outcome a=(problem Γ i).outcome a := by
  apply FiniteLaw.ext_expect
  intro f
  rw [problem_outcome,problem_outcome,CountLaw.expect_ofMeasure,CountLaw.expect_ofMeasure,
    sampleLaw_orderedGame]
  have hs : ∀ᵐω ∂sampleLaw Γ,∀l,MenuAction D.E (ω.1.1 l).1.2 := by
    have hp : ∀ᵐw ∂backgroundLaw Γ,∀l,MenuAction D.E (w.1 l).1.2 :=
      (measurePreserving_fst (μ:=userProfileLaw Γ)
        (ν:=Measure.pi (fun _ : Fin 2=>Γ.seedLaw))).quasiMeasurePreserving.ae hprofiles
    exact (measurePreserving_fst (μ:=backgroundLaw Γ)
      (ν:=permLaw 2)).quasiMeasurePreserving.ae hp
  apply integral_congr_ae
  filter_upwards [hs] with ω hω
  rw [focalCount_eq D Γ hpolicy i a hb ω (fun l _=>hω l)]

include hpolicy hprofiles in

theorem payoff_eq (i : Fin m) (v : ℝ) (a : JointAction 2) (hb : a.bid≤D.E.d) :
    (problem (orderedGame D Γ) i).payoff v a=(problem Γ i).payoff v a := by
  rw [payoff_eq_profile_seed_route_integral,payoff_eq_profile_seed_route_integral]
  change (∫p,∫s,∫tau,nativeRealizedPayoff (orderedGame D Γ) i v a ((p,s),tau)
    ∂permLaw 2 ∂Measure.pi (fun _ : Fin 2=>Γ.seedLaw) ∂userProfileLaw Γ)=_
  apply integral_congr_ae
  filter_upwards [hprofiles] with p hp
  apply integral_congr_ae
  refine ae_of_all _ fun s=>?_
  apply integral_congr_ae
  refine ae_of_all _ fun tau=>?_
  change userPayoff v a.bid Γ.g Γ.A.charge Γ.G.charge
      (focalCount (orderedGame D Γ) i a ((p,s),tau)).val=
    userPayoff v a.bid Γ.g Γ.A.charge Γ.G.charge (focalCount Γ i a ((p,s),tau)).val
  rw [focalCount_eq D Γ hpolicy i a hb ((p,s),tau) (fun l _=>hp l)]

include hpolicy hprofiles in

theorem bestResponse (i : Fin m) (v : ℝ) (hv : v≤D.E.d)
    (a : JointAction 2) (ha : a.bid≤D.E.d)
    (hbest : (problem Γ i).BestResponse v a) :
    (problem (orderedGame D Γ) i).BestResponse v a := by
  apply GlobalLower.low_bestResponse_of_restricted (problem (orderedGame D Γ) i)
    D.E.d v D.E.d_nonneg hv a
  intro b hb
  rw [payoff_eq D Γ hpolicy hprofiles i v b hb,
    payoff_eq D Γ hpolicy hprofiles i v a ha]
  exact hbest b

end FCAppendix.Affine.Tail04.OrderedNativeLowTransport
