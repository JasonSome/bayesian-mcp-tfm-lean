import FCAppendix.Affine.Tail04.NativeLowRowPayoff
import FCAppendix.Affine.Hybrid.NativeLowBounds

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeLowIntegration
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Hybrid LowBody NativeContinuation NativeLowCoordinates NativeLowSelector
open scoped BigOperators

variable {N c : ℕ}

def rowProfile (E : Observable.Regions) (i : Fin (N+1))
    (p : UserProfile (N+1) 2) : Fin N→ RowRival :=
  fun r=> E.collapse ((p (i.succAbove r)).1.2,(p (i.succAbove r)).2)

theorem measurable_rowProfile (E : Observable.Regions) (i : Fin (N+1)) :
    Measurable (rowProfile E i) :=
  measurable_pi_lambda _ (fun r=> E.measurable_collapse.comp
    (((measurable_pi_apply (i.succAbove r)).fst.snd).prodMk
      (measurable_pi_apply (i.succAbove r)).snd))

@[simp] theorem rivalRow_eq_rowProfile (E : Observable.Regions) (i : Fin (N+1))
    (ω : Background (N+1) 2 NativeLocalPolicy.Seed) :
    rivalRow E i ω=rowProfile E i ω.1 := rfl

theorem rowProfile_low_bounds (E : Observable.Regions) (i : Fin (N+1))
    (p : UserProfile (N+1) 2) (r : Fin N)
    (hr : (rowProfile E i p r).1=0) :
    (rowProfile E i p r).2∈Icc (0:ℝ) E.d := by
  have ht : E.coarseTag (p (i.succAbove r))=0 := hr
  have hb := (ObservedScenario.coarseTag_low_iff E _).mp ht
  change (E.collapse ((p (i.succAbove r)).1.2,(p (i.succAbove r)).2)).2∈_
  rw [collapse_low_bid E _ ht]
  exact ⟨(p (i.succAbove r)).1.2.bid_nonneg,hb⟩

def lowSeeds (s : Fin 2→ NativeLocalPolicy.Seed) : Fin 2→ unitInterval :=
  fun j=>(s j).2

theorem lowSeeds_measurePreserving :
    MeasurePreserving lowSeeds (Measure.pi (fun _ : Fin 2=> NativeLocalPolicy.seedLaw))
      (Measure.pi (fun _ : Fin 2=>(volume : Measure unitInterval))) :=
  measurePreserving_pi (fun _ : Fin 2=> NativeLocalPolicy.seedLaw)
    (fun _ : Fin 2=>(volume : Measure unitInterval))
    (fun _=> measurePreserving_snd (μ:=(volume : Measure unitInterval))
      (ν:=(volume : Measure unitInterval)))

variable (D : NativeLocalPolicy.Data (N+1) c)
  (Γ : FiniteGame (N+1) 2 c NativeLocalPolicy.Seed)
  (hpolicy : Γ.policy=D.completedPolicy)
  (hseed : Γ.seedLaw=NativeLocalPolicy.seedLaw)
  (η : ℝ) (hη0 : 0≤ η) (hη1 : η≤1) (hcoef : (1-η)/2=D.ξ)
  (hA : Γ.A=Schedule.affine 2 η hη0 hη1) (hG : Γ.G=Schedule.once 2) (hg : Γ.g=0)

include hpolicy hseed η hη0 hη1 hcoef hA hG hg in
theorem native_seed_average (i : Fin (N+1)) (v : ℝ) (a : JointAction 2)
    (hk : a.routeCount=2) (hb : a.bid≤ D.E.d) (p : UserProfile (N+1) 2)
    (hr : ∀ r : Fin N,NativeMenuReports.MenuAction D.E (p (i.succAbove r)).1.2) :
    (∫s,nativeRealizedPayoff Γ i v a ((p,s),Equiv.refl (Fin 2))
      ∂Measure.pi (fun _ : Fin 2=> Γ.seedLaw))=
      NativeExactLow.seedAveragePayoff D.ξ D.xi_pos D.xi_lt_one c
        (rowContextAt i a.bid (rowProfile D.E i p)) i v := by
  let X:=rowContextAt i a.bid (rowProfile D.E i p)
  let f : (Fin 2→ unitInterval)→ℝ := fun s=> purePayoff (1-D.ξ) v
    (fun l=> entryBid (X.1 l))
    (NativeExactLow.select D.ξ D.xi_pos D.xi_lt_one c 0 X (s 0),
      NativeExactLow.select D.ξ D.xi_pos D.xi_lt_one c 1 X (s 1)) i
  have hm (j : Fin 2) : Measurable (fun s : Fin 2→ unitInterval=>
      NativeExactLow.select D.ξ D.xi_pos D.xi_lt_one c j X (s j)) :=
    (NativeExactLow.measurable_select D.ξ D.xi_pos D.xi_lt_one c j).comp
      (measurable_const.prodMk (measurable_pi_apply j))
  have hf : Measurable f :=
    (measurable_of_countable (fun Q : Finset (Fin (N+1))×Finset (Fin (N+1))=>
      purePayoff (1-D.ξ) v (fun l=> entryBid (X.1 l)) Q i)).comp
        ((hm 0).prodMk (hm 1))
  rw [hseed]
  calc
    _=∫s,f (lowSeeds s) ∂Measure.pi (fun _ : Fin 2=> NativeLocalPolicy.seedLaw) := by
      apply integral_congr_ae
      exact ae_of_all _ fun s=> low_realized_payoff D Γ hpolicy η hη0 hη1 hcoef
        hA hG hg i v a hk hb ((p,s),Equiv.refl (Fin 2)) hr
    _=∫s,f s ∂Measure.pi (fun _ : Fin 2=>(volume : Measure unitInterval)) := by
      rw [←lowSeeds_measurePreserving.map_eq]
      exact (integral_map lowSeeds_measurePreserving.measurable.aemeasurable
        hf.aestronglyMeasurable).symm
    _=NativeExactLow.seedAveragePayoff D.ξ D.xi_pos D.xi_lt_one c X i v := by
      have hbids : (fun l=>entryBid (X.1 l))=Existence.PayOnceBounded.listBids X.1 := by
        funext l
        cases h : X.1 l <;> simp [Existence.PayOnceBounded.listBids,entryBid,h]
      simp only [f,NativeExactLow.seedAveragePayoff,
        FCAppendix.AppendixRepair.GeneralLow.ExactLow.seedAveragePayoff,hbids]
      apply integral_congr_ae
      exact ae_of_all _ (fun s=> by
        change purePayoff (1-D.ξ) v _
          (NativeExactLow.select D.ξ D.xi_pos D.xi_lt_one c 0 X (s 0),
            NativeExactLow.select D.ξ D.xi_pos D.xi_lt_one c 1 X (s 1)) i = _
        rfl)

theorem integrable_seed_average (i : Fin (N+1)) (v : ℝ) (a : JointAction 2) :
    Integrable (fun p=>∫s,nativeRealizedPayoff Γ i v a ((p,s),Equiv.refl (Fin 2))
      ∂Measure.pi (fun _ : Fin 2=> Γ.seedLaw)) (userProfileLaw Γ) := by
  have hm : Measurable (fun ω : Background (N+1) 2 NativeLocalPolicy.Seed=>
      focalCount Γ i a (ω,Equiv.refl (Fin 2))) :=
    (measurable_focalCount Γ i a).comp (measurable_id.prodMk measurable_const)
  have hi := CountLaw.integrable_comp (backgroundLaw Γ)
    (fun ω : Background (N+1) 2 NativeLocalPolicy.Seed=> focalCount Γ i a (ω,Equiv.refl (Fin 2)))
    hm (fun r : Fin 3=> userPayoff v a.bid Γ.g Γ.A.charge Γ.G.charge r.val)
  exact hi.integral_prod_left

include hpolicy hseed η hη0 hη1 hcoef hA hG hg in
theorem zero_envelope
    (hprofiles : ∀ᵐp ∂userProfileLaw Γ,∀l,NativeMenuReports.MenuAction D.E (p l).1.2)
    (i : Fin (N+1)) (v : ℝ) (hv : 0≤ v) (a : JointAction 2)
    (hk : a.routeCount=2) (hzero : a.bid=0) (y : ℝ) (hy : 0< y) (hyd : y≤ D.E.d) :
    (problem Γ i).payoff v a≤
      (problem Γ i).payoff v (NativeLowIncentives.broadcast y hy.le)+2*y := by
  let ay:=NativeLowIncentives.broadcast y hy.le
  have hξh : D.ξ≤1/2 := by linarith
  have h0d : a.bid≤ D.E.d := by rw [hzero];exact D.E.d_nonneg
  rw [broadcast_payoff_eq_profile_seed_integral Γ i v a hk,
    broadcast_payoff_eq_profile_seed_integral Γ i v ay rfl]
  have hi0:=integrable_seed_average Γ i v a
  have hiy:=integrable_seed_average Γ i v ay
  have hadd:=integral_add hiy (integrable_const (2*y))
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at hadd
  rw [←hadd]
  apply integral_mono_ae hi0 (hiy.add (integrable_const (2*y)))
  filter_upwards [hprofiles] with p hp
  dsimp only [Pi.add_apply]
  rw [native_seed_average D Γ hpolicy hseed η hη0 hη1 hcoef hA hG hg
      i v a hk h0d p (fun r=> hp (i.succAbove r)),
    native_seed_average D Γ hpolicy hseed η hη0 hη1 hcoef hA hG hg
      i v ay rfl hyd p (fun r=> hp (i.succAbove r))]
  have hx : (rowContextAt i a.bid (rowProfile D.E i p)).1 i=some 0 := by
    rw [rowContextAt_focal,hzero]
  let X := rowContextAt i a.bid (rowProfile D.E i p)
  have he := NativeExactLow.Direct.zero_payoff_le_positive D.ξ D.xi_pos hξh
    X.1 (NativeContinuation.residual c 0 X) (NativeContinuation.residual c 1 X)
    i hx v hv y hy
  change NativeExactLow.seedAveragePayoff D.ξ D.xi_pos D.xi_lt_one c X i v ≤
    NativeExactLow.seedAveragePayoff D.ξ D.xi_pos D.xi_lt_one c
      (contextAtBid X i y) i v+2*y at he
  dsimp only [X] at he
  rw [←rowContextAt_change_bid] at he
  exact he

end FCAppendix.Affine.Tail04.NativeLowIntegration
