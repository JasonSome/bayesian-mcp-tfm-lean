import FCAppendix.Affine.UniformFinite.Early.Restricted
import FCAppendix.Affine.UniformFinite.Late.RemoveFloor
import FCAppendix.Affine.UniformFinite.Late.ExceptionalRoutes
import FCAppendix.Affine.UniformFinite.OriginalPopulationRows

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical
open Existence.Distributional

namespace Late

def extendedRawUtility (i : Row) (N : ℕ) (G : Uniform05.RestrictedLaw i) (v b : ℝ) : ℝ :=
  if Uniform05.cap i< b then Exceptional.rawUtility i N G v b else rawUtility i N G v b

theorem extendedRawUtility_on_path (i : Row) (N : ℕ) (G : Uniform05.RestrictedLaw i)
    (v b : ℝ) (hb : b≤ Uniform05.cap i) :
    extendedRawUtility i N G v b=rawUtility i N G v b := by
  simp only [extendedRawUtility,if_neg (not_lt_of_ge hb)]

theorem rawUtility_overbid (i : Row) (N : ℕ) (G : Uniform05.RestrictedLaw i)
    {v b : ℝ} (hv : 0≤ v) (hb : v< b) : rawUtility i N G v b≤0 := by
  apply (categoryRowLaw i N).expect_le_const
  intro kind
  apply integral_nonpos
  intro rivals
  apply (continuationLaw i G (focalRow kind) (focalBids i kind b rivals)).expect_le_const
  intro P
  simpa only [focalBids_zero,Pi.zero_apply] using
    pairPayoff_overbid (Uniform05.eta_range i).1.le hv hb (0 : Fin (N+1)) P

end Late

structure FiniteLowerConstruction (i : Row) (M : ℕ) (R : ℝ) where
  restricted : ExactRestrictedLaw i M
  upper_floor : Uniform05.cap i< R
  all_broadcast_IC : ∀ᵐp∂(restricted.pi.1 : Measure (Value i×unitInterval)),∀b : ℝ,
    0≤ b→ b< R→ Late.extendedRawUtility i (M-1) restricted.law p.1 b≤
      rawUtility i (M-1) restricted.law p.1 (baseBid i p)
  below_floor_routes : ∀ᵐp∂(restricted.pi.1 : Measure (Value i×unitInterval)),∀b : ℝ,
    0≤ b→ b< Uniform05.floorBid i p.1→
      (∀j : Fin 2,rawRouteUtility i (M-1) restricted.law j p.1 b<
        rawUtility i (M-1) restricted.law p.1 (baseBid i p)) ∧
      oneRouteRawUtility i (M-1) restricted.law p.1 b<
        rawUtility i (M-1) restricted.law p.1 (baseBid i p)
  above_cap_routes : ∀ᵐp∂(restricted.pi.1 : Measure (Value i×unitInterval)),∀b : ℝ,
    Uniform05.cap i< b→ b< R→
      (∀j : Fin 2,Late.Exceptional.rawRouteUtility i (M-1) restricted.law j p.1 b≤
        rawUtility i (M-1) restricted.law p.1 (baseBid i p)) ∧
      Late.Exceptional.oneRouteRawUtility i (M-1) restricted.law p.1 b≤
        rawUtility i (M-1) restricted.law p.1 (baseBid i p)

namespace FiniteLowerConstruction
variable {i : Row} {M : ℕ} {R : ℝ}

theorem common_conull_contract (F : FiniteLowerConstruction i M R) :
    ∀ᵐp∂(F.restricted.pi.1 : Measure (Value i×unitInterval)),
      0<(p.1:ℝ) ∧ 0<(baseBid i p:ℝ) ∧
      (baseBid i p:ℝ)≤ Uniform05.cap i-capSlack i ∧
      (1-Uniform05.chi)*(baseBid i p:ℝ)*Lprob i M/2≤(p.1:ℝ)-(baseBid i p:ℝ) ∧
      (∀b : ℝ,0≤ b→ b< R→ Late.extendedRawUtility i (M-1) F.restricted.law p.1 b≤
        rawUtility i (M-1) F.restricted.law p.1 (baseBid i p)) ∧
      (∀b : ℝ,0≤ b→ b< Uniform05.floorBid i p.1→∀j : Fin 2,
        rawRouteUtility i (M-1) F.restricted.law j p.1 b<
          rawUtility i (M-1) F.restricted.law p.1 (baseBid i p)) := by
  filter_upwards [F.restricted.common_conull_contract,F.all_broadcast_IC,F.below_floor_routes]
    with p hp hb hr
  exact ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,hb,fun b hb0 hbf=>(hr b hb0 hbf).1⟩

theorem conditional_all_broadcast_IC (F : FiniteLowerConstruction i M R) :
    ∀ᵐ(v : Value i)∂lowerMeasure i,∀ᵐq∂F.restricted.sigma v,∀b : ℝ,0≤ b→ b< R→
      Late.extendedRawUtility i (M-1) F.restricted.law v b≤
        rawUtility i (M-1) F.restricted.law v (baseBid i (v,q)) := by
  have h:=F.all_broadcast_IC
  have hdis : lowerMeasure i⊗ₘF.restricted.sigma=
      (F.restricted.pi.1 : Measure (Value i×unitInterval)) := F.restricted.disintegration
  rw [← hdis] at h
  exact Measure.ae_ae_of_ae_compProd h

def typeLaw (F : FiniteLowerConstruction i M R) (v : Value i) : CountLaw 2 :=
  typeCountLaw i (M-1) F.restricted.pi F.restricted.sigma v

theorem typeLaw_expect (F : FiniteLowerConstruction i M R) (v : Value i) (f : Fin 3→ℝ) :
    (F.typeLaw v).expect f=
      ∫q,(rawCountLaw i (M-1) F.restricted.law (baseBid i (v,q))).expect f ∂F.restricted.sigma v :=
  typeCountLaw_expect i (M-1) F.restricted.pi F.restricted.sigma v f

end FiniteLowerConstruction

theorem eventually_finite_lower_construction (i : Row) :
    ∀ᶠM : ℕ in atTop,∀R : ℝ,Uniform05.cap i< R→ Nonempty (FiniteLowerConstruction i M R) := by
  obtain ⟨Nfloor,hfloor⟩:=eventually_atTop.mp (Late.remove_floor i)
  obtain ⟨Ncap,hcap⟩:=eventually_atTop.mp (Late.remove_cap i)
  filter_upwards [eventually_exists_exact_restricted_law i,
    eventually_ge_atTop (max Nfloor Ncap+1)] with M hE hM
  intro R hR
  let E:=Classical.choice hE
  have hf:=hfloor (M-1) (by omega) E.pi E.IC
  have hc:=hcap (M-1) (by omega) E.pi E.IC
  have hnonneg:=Late.restricted_incumbent_nonnegative i (M-1) E.pi E.restricted_IC
  have hall : ∀ᵐp∂(E.pi.1 : Measure (Value i×unitInterval)),∀b : ℝ,0≤ b→ b< R→
      Late.extendedRawUtility i (M-1) E.law p.1 b≤ rawUtility i (M-1) E.law p.1 (baseBid i p) := by
    filter_upwards [E.restricted_IC,hf,hc,hnonneg] with p hp hfp hcp hn
    intro b hb0 _
    by_cases hbcap : Uniform05.cap i< b
    · rw [Late.extendedRawUtility,if_pos hbcap]
      exact (hcp b hbcap).1
    · rw [Late.extendedRawUtility,if_neg hbcap]
      by_cases hbf : b< Uniform05.floorBid i p.1
      · exact (hfp b hb0 hbf).1.le
      · by_cases hbv : b≤(p.1:ℝ)
        · exact hp b ⟨le_of_not_gt hbf,le_min hbv (le_of_not_gt hbcap)⟩
        · exact (Late.rawUtility_overbid i (M-1) E.law p.1.property.1 (lt_of_not_ge hbv)).trans hn
  refine ⟨⟨E,hR,hall,?_,?_⟩⟩
  · filter_upwards [hf] with p hp
    exact fun b hb hbf=>(hp b hb hbf).2
  · filter_upwards [hc] with p hp
    exact fun b hb _=>(hp b hb).2

theorem exists_finite_lower_family (i : Row) :
    ∃M0 : ℕ,∀M : ℕ,M0≤ M→∀R : ℝ,Uniform05.cap i< R→ Nonempty (FiniteLowerConstruction i M R) :=
  eventually_atTop.mp (eventually_finite_lower_construction i)

end FCAppendix.Affine.UniformFinite
