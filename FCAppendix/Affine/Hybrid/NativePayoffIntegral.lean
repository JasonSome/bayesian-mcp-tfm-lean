import FCAppendix.Affine.Hybrid.PopulationRows
import FCAppendix.Affine.LowBody.NoisyClusterIC

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Set Game Bayes

def nativeRealizedPayoff {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Gamma : FiniteGame m 2 c Seed) (i : Fin m) (v : ℝ) (a : JointAction 2)
    (omega : Sample m 2 Seed) : ℝ:=
  userPayoff v a.bid Gamma.g Gamma.A.charge Gamma.G.charge (focalCount Gamma i a omega).val

theorem integrable_nativeRealizedPayoff {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Gamma : FiniteGame m 2 c Seed) (i : Fin m) (v : ℝ) (a : JointAction 2) :
    Integrable (nativeRealizedPayoff Gamma i v a) (sampleLaw Gamma) :=
  CountLaw.integrable_comp (sampleLaw Gamma) (focalCount Gamma i a)
    (measurable_focalCount Gamma i a)
    (fun r : Fin 3=>userPayoff v a.bid Gamma.g Gamma.A.charge Gamma.G.charge r.val)

theorem payoff_eq_profile_seed_route_integral {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Gamma : FiniteGame m 2 c Seed) (i : Fin m) (v : ℝ) (a : JointAction 2) :
    (problem Gamma i).payoff v a=
      ∫profile,∫seed,∫tau,nativeRealizedPayoff Gamma i v a ((profile,seed),tau)
        ∂permLaw 2 ∂Measure.pi (fun _ : Fin 2=>Gamma.seedLaw) ∂userProfileLaw Gamma := by
  change ((problem Gamma i).outcome a).utility v a.bid Gamma.g Gamma.A Gamma.G=_
  rw [problem_outcome,CountLaw.utility,CountLaw.expect_ofMeasure]
  have hi:=integrable_nativeRealizedPayoff Gamma i v a
  change (∫omega,nativeRealizedPayoff Gamma i v a omega ∂sampleLaw Gamma)=_
  change (∫omega,nativeRealizedPayoff Gamma i v a omega
    ∂((userProfileLaw Gamma).prod (Measure.pi (fun _ : Fin 2=>Gamma.seedLaw))).prod (permLaw 2))=_
  change Integrable (nativeRealizedPayoff Gamma i v a)
    (((userProfileLaw Gamma).prod (Measure.pi (fun _ : Fin 2=>Gamma.seedLaw))).prod (permLaw 2)) at hi
  rw [integral_prod _ hi,integral_prod _ hi.integral_prod_left]

theorem nativeRealizedPayoff_broadcast_route_independent {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Gamma : FiniteGame m 2 c Seed) (i : Fin m) (v : ℝ) (a : JointAction 2)
    (hk : a.routeCount=2) (profile : UserProfile m 2) (seed : Fin 2→Seed)
    (tau sigma : Equiv.Perm (Fin 2)) :
    nativeRealizedPayoff Gamma i v a ((profile,seed),tau)=
      nativeRealizedPayoff Gamma i v a ((profile,seed),sigma) := by
  have hx : deviated i a ((profile,seed),tau)=deviated i a ((profile,seed),sigma) := by
    unfold deviated
    rw [hk,firstK_full_two,firstK_full_two]
  change userPayoff _ _ _ _ _ (boundedCount (deviated i a ((profile,seed),tau)) Gamma.policy seed i).val=_
  rw [hx]
  rfl

theorem broadcast_payoff_eq_profile_seed_integral {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Gamma : FiniteGame m 2 c Seed) (i : Fin m) (v : ℝ) (a : JointAction 2)
    (hk : a.routeCount=2) :
    (problem Gamma i).payoff v a=
      ∫profile,∫seed,nativeRealizedPayoff Gamma i v a ((profile,seed),Equiv.refl (Fin 2))
        ∂Measure.pi (fun _ : Fin 2=>Gamma.seedLaw) ∂userProfileLaw Gamma := by
  rw [payoff_eq_profile_seed_route_integral]
  apply integral_congr_ae
  apply ae_of_all
  intro profile
  apply integral_congr_ae
  apply ae_of_all
  intro seed
  have he : (fun tau=>nativeRealizedPayoff Gamma i v a ((profile,seed),tau))=
      fun _ : Equiv.Perm (Fin 2)=>nativeRealizedPayoff Gamma i v a ((profile,seed),Equiv.refl (Fin 2)) :=
    funext (fun tau=>nativeRealizedPayoff_broadcast_route_independent Gamma i v a hk profile seed tau _)
  dsimp only
  rw [he,integral_const,probReal_univ,smul_eq_mul,one_mul]

theorem broadcast_payoff_of_row_identity {N c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Gamma : FiniteGame (N+1) 2 c Seed) (i : Fin (N+1)) (v : ℝ) (a : JointAction 2)
    (hk : a.routeCount=2) {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (row : UserProfile (N+1) 2→(Fin N→LowBody.RowRival)) (hrow : Measurable row)
    (nu : Measure (Fin N→LowBody.RowRival))
    (hlaw : (userProfileLaw Gamma).map row=nu)
    (hidentity : ∀ᵐprofile ∂userProfileLaw Gamma,
      (∫seed,nativeRealizedPayoff Gamma i v a ((profile,seed),Equiv.refl (Fin 2))
        ∂Measure.pi (fun _ : Fin 2=>Gamma.seedLaw))=
        LowBody.literalRowPayoff ξ c v (a.bid,row profile)) :
    (problem Gamma i).payoff v a=∫r,LowBody.literalRowPayoff ξ c v (a.bid,r) ∂nu := by
  rw [broadcast_payoff_eq_profile_seed_integral Gamma i v a hk]
  calc
    _=∫profile,LowBody.literalRowPayoff ξ c v (a.bid,row profile) ∂userProfileLaw Gamma:=
      integral_congr_ae hidentity
    _=_:=by
      rw [←hlaw]
      exact (integral_map hrow.aemeasurable
        (((LowBody.measurable_literalRowPayoff hξ hξ1 c v).comp
          (measurable_const.prodMk measurable_id)).aestronglyMeasurable)).symm

end FCAppendix.Affine.Hybrid
