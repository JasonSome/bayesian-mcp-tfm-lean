import FCAppendix.AppendixRepair.Information
import FCAppendix.Affine.Hybrid.NativeLowStrictPrimitive
import FCAppendix.Affine.LowBody.ActualLowStrategy
import FCAppendix.Probability.FinitePushforward

noncomputable section
namespace FCAppendix.Appendix08
open MeasureTheory ProbabilityTheory Set Game Bayes Filter Topology
open Affine Affine.LowBody Affine.Hybrid
open Existence.Distributional

section Copy
variable {m c : ℕ} {Seed SeedRef : Type*}
  [MeasurableSpace Seed] [MeasurableSpace SeedRef]

structure LowCountReproduction (Gamma : FiniteGame m 2 c Seed)
    (Reference : FiniteGame m 2 c SeedRef) (d : ℝ) where
  relabel : Sample m 2 Seed → Sample m 2 SeedRef
  law : MeasurePreserving relabel (sampleLaw Gamma) (sampleLaw Reference)
  counts : ∀ i : Fin m, ∀ᵐω ∂sampleLaw Gamma,
    ∀ a : JointAction 2, a.bid ≤ d →
      focalCount Gamma i a ω = focalCount Reference i a (relabel ω)

structure LowAllocationReproduction (Gamma : FiniteGame m 2 c Seed)
    (Reference : FiniteGame m 2 c SeedRef) (d : ℝ) where
  relabel : Sample m 2 Seed → Sample m 2 SeedRef
  law : MeasurePreserving relabel (sampleLaw Gamma) (sampleLaw Reference)
  membership : ∀ i : Fin m, ∀ᵐω ∂sampleLaw Gamma,
    ∀ a : JointAction 2, a.bid ≤ d → ∀ j : Fin 2,
      (i ∈ allocation (deviated i a ω) Gamma.policy ω.1.2 j) ↔
      (i ∈ allocation (deviated i a (relabel ω)) Reference.policy (relabel ω).1.2 j)

def LowAllocationReproduction.toCounts
    {Gamma : FiniteGame m 2 c Seed} {Reference : FiniteGame m 2 c SeedRef} {d : ℝ}
    (C : LowAllocationReproduction Gamma Reference d) : LowCountReproduction Gamma Reference d where
  relabel := C.relabel
  law := C.law
  counts := by
    intro i
    filter_upwards [C.membership i] with ω hω
    intro a ha
    apply Fin.ext
    change inclusionCount (deviated i a ω) Gamma.policy ω.1.2 i =
      inclusionCount (deviated i a (C.relabel ω)) Reference.policy (C.relabel ω).1.2 i
    rw [inclusionCount_eq_sum, inclusionCount_eq_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [hω a ha j]

namespace LowCountReproduction
variable {Gamma : FiniteGame m 2 c Seed} {Reference : FiniteGame m 2 c SeedRef} {d : ℝ}

def refl (Gamma : FiniteGame m 2 c Seed) (d : ℝ) : LowCountReproduction Gamma Gamma d where
  relabel := id
  law := MeasurePreserving.id (sampleLaw Gamma)
  counts := fun _ => ae_of_all _ (fun _ _ _ => rfl)

theorem common_conull (C : LowCountReproduction Gamma Reference d) :
    ∀ᵐω ∂sampleLaw Gamma, ∀ i : Fin m, ∀ a : JointAction 2, a.bid ≤ d →
      focalCount Gamma i a ω = focalCount Reference i a (C.relabel ω) :=
  ae_all_iff.mpr C.counts

theorem outcome_eq (C : LowCountReproduction Gamma Reference d)
    (i : Fin m) (a : JointAction 2) (ha : a.bid ≤ d) :
    (problem Gamma i).outcome a = (problem Reference i).outcome a := by
  have hcount : focalCount Gamma i a =ᵐ[sampleLaw Gamma]
      focalCount Reference i a ∘ C.relabel := by
    filter_upwards [C.counts i] with ω hω
    exact hω a ha
  apply FiniteLaw.ext_expect
  intro f
  simp only [problem_outcome, CountLaw.expect_ofMeasure]
  calc
    _ = ∫ ω, f (focalCount Reference i a (C.relabel ω)) ∂sampleLaw Gamma := by
      apply integral_congr_ae
      filter_upwards [hcount] with ω hω
      exact congrArg f hω
    _ = ∫ ω, f (focalCount Reference i a ω) ∂(sampleLaw Gamma).map C.relabel :=
      (integral_map_of_stronglyMeasurable C.law.measurable
        (((measurable_of_countable f).comp (measurable_focalCount Reference i a)).stronglyMeasurable)).symm
    _ = _ := by rw [C.law.map_eq]

theorem payoff_eq (C : LowCountReproduction Gamma Reference d)
    (hA : Gamma.A = Reference.A) (hg : Gamma.g = 0) (hrg : Reference.g = 0)
    (i : Fin m) (v : ℝ) (a : JointAction 2) (ha : a.bid ≤ d) :
    (problem Gamma i).payoff v a = (problem Reference i).payoff v a := by
  change ((problem Gamma i).outcome a).utility v a.bid Gamma.g Gamma.A Gamma.G =
    ((problem Reference i).outcome a).utility v a.bid Reference.g Reference.A Reference.G
  rw [CountLaw.utility_eq, CountLaw.utility_eq, C.outcome_eq i a ha, hA, hg, hrg]
  simp only [zero_mul, sub_zero]

theorem fixed_value_mass_eq (C : LowCountReproduction Gamma Reference d)
    (sigma : Kernel ℝ (JointAction 2)) (i : Fin m) (v : ℝ)
    (hs : ∀ᵐa ∂sigma v, a.bid ≤ d) (k : Fin 3) :
    (∫ a, ((problem Gamma i).outcome a).mass k ∂sigma v) =
      ∫ a, ((problem Reference i).outcome a).mass k ∂sigma v := by
  apply integral_congr_ae
  filter_upwards [hs] with a ha
  rw [C.outcome_eq i a ha]

theorem best_response (C : LowCountReproduction Gamma Reference d)
    (hA : Gamma.A = Reference.A) (hg : Gamma.g = 0) (hrg : Reference.g = 0)
    (i : Fin m) (v : ℝ) (hv : v ≤ d) (a : JointAction 2) (ha : a.bid ≤ d)
    (hbest : (problem Reference i).BestResponse v a) :
    (problem Gamma i).BestResponse v a := by
  have hnonneg : 0 ≤ (problem Reference i).payoff v a := by
    simpa only [Interim.Problem.payoff_abstain] using hbest (Interim.abstain 2)
  intro a'
  by_cases had : a'.bid ≤ d
  · rw [C.payoff_eq hA hg hrg i v a' had, C.payoff_eq hA hg hrg i v a ha]
    exact hbest a'
  · have hvb : v ≤ a'.bid := hv.trans (le_of_lt (lt_of_not_ge had))
    have hnp := NativeLowIncentives.payoff_nonpos_of_value_le_bid Gamma hg i v a' hvb
    rw [C.payoff_eq hA hg hrg i v a ha]
    exact hnp.trans hnonneg

private def zeroSingleton : JointAction 2 := ⟨0, le_rfl, 1, by decide⟩

theorem strict_one_route (C : LowCountReproduction Gamma Reference d)
    (hA : Gamma.A = Reference.A) (hg : Gamma.g = 0) (hrg : Reference.g = 0)
    (i : Fin m) (v : ℝ) (hv0 : 0 ≤ v) (hvd : v ≤ d)
    (a : JointAction 2) (ha : a.bid ≤ d)
    (hstrict : ∀ a' : JointAction 2, a'.routeCount = 1 →
      (problem Reference i).payoff v a' < (problem Reference i).payoff v a) :
    ∀ a' : JointAction 2, a'.routeCount = 1 →
      (problem Gamma i).payoff v a' < (problem Gamma i).payoff v a := by
  have hz : 0 ≤ (problem Reference i).payoff v zeroSingleton := by
    change 0 ≤ ((problem Reference i).outcome zeroSingleton).utility
      v zeroSingleton.bid Reference.g Reference.A Reference.G
    rw [CountLaw.utility_eq, hrg]
    simp only [zeroSingleton, zero_mul, sub_zero]
    exact mul_nonneg hv0 ((problem Reference i).outcome zeroSingleton).success_nonneg
  have hpos : 0 < (problem Reference i).payoff v a :=
    hz.trans_lt (hstrict zeroSingleton rfl)
  intro a' hk
  by_cases had : a'.bid ≤ d
  · rw [C.payoff_eq hA hg hrg i v a' had, C.payoff_eq hA hg hrg i v a ha]
    exact hstrict a' hk
  · have hvb : v ≤ a'.bid := hvd.trans (le_of_lt (lt_of_not_ge had))
    have hnp := NativeLowIncentives.payoff_nonpos_of_value_le_bid Gamma hg i v a' hvb
    rw [C.payoff_eq hA hg hrg i v a ha]
    exact hnp.trans_lt hpos

end LowCountReproduction
end Copy

theorem exists_low_from_finite_guards {N : ℕ} {d ξ ell H : ℝ} (hd : 0 ≤ d)
    (hξ : 0 < ξ) (hξh : ξ ≤ 1/2) (c : ℕ) (hc : 0 < c)
    (s a h : ℝ) (hs : 0 < s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (hell : 0 < ell)
    (hellDef : ell = (CommonList.iid (categoryLaw s a h hs.le ha hh hsum Gref) (N+1)).prob
      (LocalUnderflow c 0))
    (hjoint : (CommonList.iid (categoryLaw s a h hs.le ha hh hsum Gref) (N+1)).prob
      (BothUnderflow c) ≤ ell/4)
    (hHe : (CommonList.iid (categoryLaw s a h hs.le ha hh hsum Gref) N).prob
      (BothUnderflow c) < H)
    (hboundary : ∀ (G : Measure ℝ) (_hG : IsProbabilityMeasure G) (u : ℝ),
      H ≤ PiBinomial.pmf N (higherBidProbability s a h G u) (c-1))
    (hcoefficient : 8*(1-2*ξ)*(N+1 : ℕ)*
      (CommonList.iid (categoryLaw s a h hs.le ha hh hsum Gref) N).prob (BothUnderflow c) /
      (ell*(H-(CommonList.iid (categoryLaw s a h hs.le ha hh hsum Gref) N).prob
        (BothUnderflow c))) < 1/2)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (hmu : ∀ᵐw ∂mu, 0 < w.1) :
    ∃ L : ActualAtomlessLowLimit (N+1) d ξ c
        (categoryLaw s a h hs.le ha hh hsum Gref) mu,
      ∀ᵐx ∂(L.joint.1 : Measure (LowValue d × LowValue d)), ∀ b : ℝ, 0 ≤ b →
        exactExpectedPayoff (N+1) d ξ c (categoryLaw s a h hs.le ha hh hsum Gref)
          (L.joint.1.map measurable_snd.aemeasurable) (x.1.1,b) ≤
        exactExpectedPayoff (N+1) d ξ c (categoryLaw s a h hs.le ha hh hsum Gref)
          (L.joint.1.map measurable_snd.aemeasurable) (x.1.1,x.2.1) := by
  obtain ⟨L⟩ := exists_actual_atomless_low_limit hd hξ hξh c hc s a h hs ha hh hsum
    Gref hell hellDef hjoint hHe hboundary hcoefficient mu hmu
  exact ⟨L, L.all_bid_IC hξ hξh⟩

theorem population_low_duplicate_bound {N c : ℕ} {d U eta : ℝ}
    (hd : 0 ≤ d) (hdU : d ≤ U)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A := LowValue d) mu)
    (PA PH : ProbabilityMeasure (ℝ × JointAction 2))
    (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (hactive : ∀ᵐx ∂(PA : Measure (ℝ × JointAction 2)),
      d < ((1+eta)/2)*x.2.bid ∧ x.2.bid ≤ U ∧ x.2.routeCount=2)
    (hupper : ∀ᵐx ∂(PH : Measure (ℝ × JointAction 2)), U < x.2.bid ∧ x.2.routeCount=1)
    (i : Fin (N+1)) (act : JointAction 2) (hk : act.routeCount=2) (hbd : act.bid ≤ d) :
    let P := populationLaw s a h hs ha hh hsum (lowJoint mu pi) PA PH
    let Gamma := PopulationGame.game (N+1) c P eta heta0 heta1 U
    ((problem Gamma i).outcome act).duplicates ≤
      (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob (BothUnderflow c) := by
  dsimp only
  let P := populationLaw s a h hs ha hh hsum (lowJoint mu pi) PA PH
  let Gamma := PopulationGame.game (N+1) c P eta heta0 heta1 U
  let row : UserProfile (N+1) 2 → Fin N → RowRival :=
    fun profile j => nativeRowRival Gamma d U (profile (i.succAbove j))
  have hrow : Measurable row := measurable_pi_lambda _ (fun j =>
    (measurable_nativeRowRival Gamma d U).comp (measurable_pi_apply (i.succAbove j)))
  have hkap : ((1+eta)/2) ≤ 1 := by linarith
  have hac : ∀ᵐx ∂(PA : Measure (ℝ × JointAction 2)),
      d < ((1+eta)/2)*x.2.bid ∧ d < x.2.bid ∧ x.2.bid ≤ U ∧ x.2.routeCount=2 := by
    filter_upwards [hactive] with x hx
    exact ⟨hx.1, hx.1.trans_le (by
      nlinarith [mul_nonneg (sub_nonneg.mpr hkap) x.2.bid_nonneg]), hx.2⟩
  have hp : ∀ᵐx ∂(P : Measure (ℝ × JointAction 2)), lowActionGuard d U ((1+eta)/2) x.2 :=
    population_lowActionGuard hdU s a h mu pi PA PH hac hupper
  have hprofiles := profile_lowActionGuard (N := N) (c := c) P heta0 heta1 hp
  have hphysical : (userLaw Gamma).map (nativeRowRival Gamma d U) =
      rivalLaw s a h (realLowBidLaw pi.1 : Measure ℝ) :=
    native_population_row hdU s a h hs ha hh hsum mu pi PA PH
      (hac.mono (fun _ hx => ⟨hx.2.1, hx.2.2.1⟩)) (hupper.mono (fun _ hx => hx.1))
      eta heta0 heta1
  have hlaw : (userProfileLaw Gamma).map row =
      Measure.pi (fun _ : Fin N => rivalLaw s a h (realLowBidLaw pi.1 : Measure ℝ)) :=
    deleted_rival_rows_law Gamma i (nativeRowRival Gamma d U)
      (measurable_nativeRowRival Gamma d U) _ hphysical
  have hb := native_duplicates_le_underflow_of_guard P heta0 heta1 hd hdU hprofiles
    i row hrow (fun _ => rfl) _ hlaw act hk hbd
  rw [rowBothUnderflow_probability s a h hs ha hh hsum (realLowBidLaw pi.1 : Measure ℝ) N c,
    categoryLaw_eq_low_law s a h hs ha hh hsum (realLowBidLaw pi.1 : Measure ℝ) Gref] at hb
  exact hb

theorem every_positive_low_value_strict_improvement
    {N c : ℕ} {d U eta : ℝ} {Seed : Type*} [MeasurableSpace Seed]
    (hd : 0 ≤ d) (hdU : d ≤ U)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (L : ActualAtomlessLowLimit N d ((1-eta)/2) c
      (categoryLaw s a h hs ha hh hsum Gref) mu)
    (PA PH : ProbabilityMeasure (ℝ × JointAction 2))
    (hactive : ∀ᵐx ∂(PA : Measure (ℝ × JointAction 2)),
      d < ((1+eta)/2)*x.2.bid ∧ x.2.bid ≤ U ∧ x.2.routeCount=2)
    (hupper : ∀ᵐx ∂(PH : Measure (ℝ × JointAction 2)), U < x.2.bid ∧ x.2.routeCount=1)
    (hell : 0 < (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob
      (LocalUnderflow c 0))
    (hsmall : (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob
      (BothUnderflow c) ≤
      (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob (LocalUnderflow c 0)/4)
    (Gamma : FiniteGame (N+1) 2 c Seed)
    (hA : Gamma.A = Schedule.affine 2 eta heta0 heta1.le) (hg : Gamma.g=0)
    (C : LowCountReproduction Gamma
      (PopulationGame.game (N+1) c
        (populationLaw s a h hs ha hh hsum (lowJoint mu L.joint) PA PH)
        eta heta0 heta1 U) d)
    (i : Fin (N+1)) (v : ℝ) (hv : 0 < v) (hvd : v ≤ d) :
    ∀ act : JointAction 2, act.routeCount=1 →
      ∃ raised : JointAction 2, raised.routeCount=2 ∧
        (problem Gamma i).payoff v act < (problem Gamma i).payoff v raised := by
  let xi := (1-eta)/2
  have hxi : 0 < xi := by dsimp [xi]; linarith
  have hxih : xi ≤ 1/2 := by dsimp [xi]; linarith
  let ell := (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob (LocalUnderflow c 0)
  let delta := (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob (BothUnderflow c)
  have hdelt : 0 ≤ delta := (CommonList.iid _ _).prob_nonneg _
  let ref := NativeLowIncentives.broadcast (v/2) (by linarith : 0 ≤ v/2)
  have hrefd : ref.bid ≤ d := by dsimp [ref, NativeLowIncentives.broadcast]; linarith
  letI := L.compact_atomless
  have href : (problem Gamma i).payoff v ref =
      exactExpectedPayoff N d xi c (categoryLaw s a h hs ha hh hsum Gref)
        (L.joint.1.map measurable_snd.aemeasurable) (v,v/2) := by
    rw [C.payoff_eq hA hg rfl i v ref hrefd]
    exact population_positive_broadcast_payoff hd hdU s a h hs ha hh hsum Gref mu L.joint
      PA PH heta0 heta1 hactive hupper i v ref rfl
      (by dsimp [ref, NativeLowIncentives.broadcast]; linarith) hrefd
  have hcompare : v*(ell-delta)/2 ≤ (problem Gamma i).payoff v ref := by
    rw [href]
    simpa only [ell, delta, div_mul_eq_mul_div] using
      exactExpectedPayoff_half_bid_lower (N := N) hxi hxih hv c
        (categoryLaw s a h hs ha hh hsum Gref) (L.joint.1.map measurable_snd.aemeasurable)
  have hgap : v*delta < (problem Gamma i).payoff v ref := by
    have hpos : 0 < v*(ell-3*delta) := mul_pos hv (by dsimp [ell, delta]; linarith)
    nlinarith
  intro act hk
  by_cases hbid : act.bid ≤ v
  · by_cases hu : (problem Gamma i).payoff v act ≤ v*delta
    · exact ⟨ref, rfl, hu.trans_lt hgap⟩
    · have hdup : ((problem Gamma i).outcome (addSecondRoute act)).duplicates ≤ delta := by
        rw [C.outcome_eq i (addSecondRoute act) (hbid.trans hvd)]
        exact population_low_duplicate_bound hd hdU s a h hs ha hh hsum Gref mu L.joint
          PA PH heta0 heta1 hactive hupper i (addSecondRoute act) rfl (hbid.trans hvd)
      have hgain := native_second_route_utility_lower Gamma heta0 heta1.le hA hg i act hk hbid hdup
      refine ⟨addSecondRoute act, rfl, ?_⟩
      linarith
  · have hnp := NativeLowIncentives.payoff_nonpos_of_value_le_bid Gamma hg i v act
      (le_of_lt (lt_of_not_ge hbid))
    exact ⟨ref, rfl, hnp.trans_lt ((mul_nonneg hv.le hdelt).trans_lt hgap)⟩

theorem native_low_copy {N c : ℕ} {d U eta : ℝ} {Seed : Type*} [MeasurableSpace Seed]
    (hd : 0 ≤ d) (hdU : d ≤ U)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (L : ActualAtomlessLowLimit N d ((1-eta)/2) c
      (categoryLaw s a h hs ha hh hsum Gref) mu)
    (PA PH : ProbabilityMeasure (ℝ × JointAction 2))
    (hactive : ∀ᵐx ∂(PA : Measure (ℝ × JointAction 2)),
      d < ((1+eta)/2)*x.2.bid ∧ x.2.bid ≤ U ∧ x.2.routeCount=2)
    (hupper : ∀ᵐx ∂(PH : Measure (ℝ × JointAction 2)), U < x.2.bid ∧ x.2.routeCount=1)
    (hell : 0 < (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob
      (LocalUnderflow c 0))
    (hsmall : (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob
      (BothUnderflow c) ≤
      (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob (LocalUnderflow c 0)/4)
    (Gamma : FiniteGame (N+1) 2 c Seed)
    (hA : Gamma.A = Schedule.affine 2 eta heta0 heta1.le) (hg : Gamma.g=0)
    (C : LowCountReproduction Gamma
      (PopulationGame.game (N+1) c
        (populationLaw s a h hs ha hh hsum (lowJoint mu L.joint) PA PH)
        eta heta0 heta1 U) d) :
    ∀ᵐx ∂(L.joint.1 : Measure (LowValue d × LowValue d)), ∀ i : Fin (N+1),
      (problem Gamma i).BestResponse x.1.1 (lowBroadcast x.2) ∧
      ∀ act : JointAction 2, act.routeCount=1 →
        (problem Gamma i).payoff x.1.1 act <
          (problem Gamma i).payoff x.1.1 (lowBroadcast x.2) := by
  apply ae_all_iff.mpr
  intro i
  have href := population_low_joint_strict_one_route hd hdU s a h hs ha hh hsum Gref mu
    heta0 heta1 L PA PH hactive hupper hell hsmall i
  filter_upwards [href] with x hx
  refine ⟨C.best_response hA hg rfl i x.1.1 x.1.property.2 (lowBroadcast x.2)
    x.2.property.2 hx.1, ?_⟩
  exact C.strict_one_route hA hg rfl i x.1.1 x.1.property.1 x.1.property.2
    (lowBroadcast x.2) x.2.property.2 hx.2

theorem low_IC_from_verified_strict_native_endpoint
    {N c : ℕ} {d U eta : ℝ} {Seed : Type*} [MeasurableSpace Seed]
    (hd : 0 ≤ d) (hdU : d ≤ U)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (L : ActualAtomlessLowLimit N d ((1-eta)/2) c
      (categoryLaw s a h hs ha hh hsum Gref) mu)
    (PA PH : ProbabilityMeasure (ℝ × JointAction 2))
    (hactive : ∀ᵐx ∂(PA : Measure (ℝ × JointAction 2)),
      d < ((1+eta)/2)*x.2.bid ∧ x.2.bid ≤ U ∧ x.2.routeCount=2)
    (hupper : ∀ᵐx ∂(PH : Measure (ℝ × JointAction 2)), U < x.2.bid ∧ x.2.routeCount=1)
    (hell : 0 < (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob
      (LocalUnderflow c 0))
    (hsmall : (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob
      (BothUnderflow c) ≤
      (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob (LocalUnderflow c 0)/4)
    (Gamma : FiniteGame (N+1) 2 c Seed)
    (hA : Gamma.A = Schedule.affine 2 eta heta0 heta1.le) (hg : Gamma.g=0)
    (C : LowCountReproduction Gamma
      (PopulationGame.game (N+1) c
        (populationLaw s a h hs ha hh hsum (lowJoint mu L.joint) PA PH)
        eta heta0 heta1 U) d) :
    ∀ᵐx ∂(lowJoint mu L.joint : Measure (ℝ × JointAction 2)), ∀ i : Fin (N+1),
      (problem Gamma i).BestResponse x.1 x.2 ∧
      ∀ act : JointAction 2, act.routeCount=1 →
        (problem Gamma i).payoff x.1 act < (problem Gamma i).payoff x.1 x.2 := by
  change ∀ᵐx ∂(L.joint.1 : Measure (LowValue d × LowValue d)).map
    (fun x => (x.1.1, lowBroadcast x.2)), _
  apply (measurableEmbedding_lowJointPoint d).ae_map_iff.mpr
  exact native_low_copy hd hdU s a h hs ha hh hsum Gref mu heta0 heta1 L PA PH
    hactive hupper hell hsmall Gamma hA hg C

theorem disintegrate_native_low {N c : ℕ} {d ξ : ℝ} {categories : FiniteLaw (Fin 4)}
    {mu : Measure (LowValue d)} [IsProbabilityMeasure mu]
    (L : ActualAtomlessLowLimit N d ξ c categories mu) (hξ : 0 < ξ) (hξh : ξ ≤ 1/2)
    {Seed : Type*} [MeasurableSpace Seed] (Gamma : FiniteGame (N+1) 2 c Seed)
    (hbest : ∀ᵐx ∂(L.joint.1 : Measure (LowValue d × LowValue d)), ∀ i : Fin (N+1),
      (problem Gamma i).BestResponse x.1.1 (lowBroadcast x.2) ∧
      ∀ act : JointAction 2, act.routeCount=1 →
        (problem Gamma i).payoff x.1.1 act <
          (problem Gamma i).payoff x.1.1 (lowBroadcast x.2)) :
    ∃ sigma : Kernel (LowValue d) (LowValue d), IsMarkovKernel sigma ∧
      mu ⊗ₘ sigma = (L.joint.1 : Measure (LowValue d × LowValue d)) ∧
      ∀ᵐw ∂mu, ∀ᵐb ∂sigma w, ∀ i : Fin (N+1),
        (problem Gamma i).BestResponse w.1 (lowBroadcast b) ∧
        ∀ act : JointAction 2, act.routeCount=1 →
          (problem Gamma i).payoff w.1 act < (problem Gamma i).payoff w.1 (lowBroadcast b) := by
  obtain ⟨sigma, hMarkov, hdis, _, _⟩ := L.exists_bid_kernel hξ hξh
  letI := hMarkov
  refine ⟨sigma, hMarkov, hdis, ?_⟩
  have hbest' : ∀ᵐx ∂mu ⊗ₘ sigma, ∀ i : Fin (N+1),
      (problem Gamma i).BestResponse x.1.1 (lowBroadcast x.2) ∧
      ∀ act : JointAction 2, act.routeCount=1 →
        (problem Gamma i).payoff x.1.1 act <
          (problem Gamma i).payoff x.1.1 (lowBroadcast x.2) := by
    simpa only [hdis] using hbest
  exact Measure.ae_ae_of_ae_compProd hbest'

theorem eventually_native_low_bounded (d U eta : ℝ) (hd : 0 ≤ d) (hdU : d ≤ U)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (s a h : ℝ) (hs : 0 < s) (ha : 0 ≤ a) (hh : 0 < h) (hsum : s+a+h=1)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (c : ℕ → ℕ) (rho : ℝ) (hrho : 0 < rho) (hrank : rho < a+h/2)
    (hc : Tendsto (fun m => (c m : ℝ)/(m : ℝ)) atTop (𝓝 rho))
    (hgap : 2*Ample.binaryKL rho (1-h/2) < jointRate s a h rho)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] (hmu : ∀ᵐw ∂mu, 0 < w.1)
    (PA PH : ProbabilityMeasure (ℝ × JointAction 2))
    (hactive : ∀ᵐx ∂(PA : Measure (ℝ × JointAction 2)),
      d < ((1+eta)/2)*x.2.bid ∧ x.2.bid ≤ U ∧ x.2.routeCount=2)
    (hupper : ∀ᵐx ∂(PH : Measure (ℝ × JointAction 2)), U < x.2.bid ∧ x.2.routeCount=1) :
    ∀ᶠm : ℕ in atTop,
      ∃ L : ActualAtomlessLowLimit (m-1) d ((1-eta)/2) (c m)
          (categoryLaw s a h hs.le ha hh.le hsum Gref) mu,
        let P := populationLaw s a h hs.le ha hh.le hsum (lowJoint mu L.joint) PA PH
        let Gamma := PopulationGame.game m (c m) P eta heta0 heta1 U
        2 < m ∧
        Gamma.F ⊗ₘ Gamma.σ = populationJoint s a h (lowJoint mu L.joint) PA PH ∧
        (∀ᵐx ∂(L.joint.1 : Measure (LowValue d × LowValue d)), 0 < x.2.1 ∧ x.2.1 ≤ x.1.1) ∧
        (∀ b : ℝ, (realLowBidLaw L.joint.1 : Measure ℝ) {b} = 0) ∧
        (∀ᵐx ∂(lowJoint mu L.joint : Measure (ℝ × JointAction 2)), ∀ i : Fin m,
          (problem Gamma i).BestResponse x.1 x.2 ∧
          ∀ act : JointAction 2, act.routeCount=1 →
            (problem Gamma i).payoff x.1 act < (problem Gamma i).payoff x.1 x.2) ∧
        ∀ i : Fin m, ∀ v : ℝ, 0 < v → v ≤ d → ∀ act : JointAction 2, act.routeCount=1 →
          ∃ raised : JointAction 2, raised.routeCount=2 ∧
            (problem Gamma i).payoff v act < (problem Gamma i).payoff v raised := by
  have hguards := eventually_primitive_source_guards s a h hs ha hh hsum Gref c rho eta
    hrho hrank heta0 hc hgap
  filter_upwards [eventually_exists_native_low_population_strict d U eta hd hdU heta0 heta1
    s a h hs ha hh hsum Gref c rho hrho hrank hc hgap mu hmu PA PH hactive hupper,
    hguards] with m hm hmG
  obtain ⟨L, hm2, hjoint, hpos, hatom, hbest⟩ := hm
  rcases hmG with ⟨_, _, hell, _, hsmall, _, _⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  refine ⟨L, hm2, hjoint, hpos, hatom, ae_all_iff.mpr hbest, ?_⟩
  intro i v hv hvd
  let Gamma := PopulationGame.game (k+1) (c (k+1))
    (populationLaw s a h hs.le ha hh.le hsum (lowJoint mu L.joint) PA PH) eta heta0 heta1 U
  exact every_positive_low_value_strict_improvement hd hdU s a h hs.le ha hh.le hsum Gref mu
    heta0 heta1 L PA PH hactive hupper hell hsmall Gamma rfl rfl
    (LowCountReproduction.refl Gamma d) i v hv hvd

end FCAppendix.Appendix08
