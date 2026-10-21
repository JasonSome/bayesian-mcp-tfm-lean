import FCAppendix.Affine.Hybrid.Native02.ClosedPosterior
import FCAppendix.Affine.Hybrid.UpperNativeAttainment

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Bayes Game Set Filter Classical
open Existence.RankEnvelope
open scoped BigOperators

section ExactTransport
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem sample_noGap_support (Γ : FiniteGame m 2 c Seed) (U R : ℝ)
    (hgap : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ, x.2.bid ≤ U ∨ R ≤ x.2.bid) :
    ∀ᵐ ω ∂sampleLaw Γ, ∀ k : Fin m,
      (ω.1.1 k).1.2.bid ≤ U ∨ R ≤ (ω.1.1 k).1.2.bid := by
  have hu : ∀ᵐ u ∂userLaw Γ, u.1.2.bid ≤ U ∨ R ≤ u.1.2.bid :=
    (measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ) (ν := permLaw 2)).quasiMeasurePreserving.ae hgap
  have hp : ∀ᵐ z ∂Measure.pi (fun _ : Fin m => userLaw Γ),
      ∀ k, (z k).1.2.bid ≤ U ∨ R ≤ (z k).1.2.bid :=
    ae_all_iff.mpr (fun k =>
      (measurePreserving_eval (fun _ : Fin m => userLaw Γ) k).quasiMeasurePreserving.ae hu)
  have hbg : ∀ᵐ ω ∂backgroundLaw Γ,
      ∀ k, (ω.1 k).1.2.bid ≤ U ∨ R ≤ (ω.1 k).1.2.bid :=
    (measurePreserving_fst (μ := Measure.pi (fun _ : Fin m => userLaw Γ))
      (ν := Measure.pi (fun _ : Fin 2 => Γ.seedLaw))).quasiMeasurePreserving.ae hp
  exact (measurePreserving_fst (μ := backgroundLaw Γ) (ν := permLaw 2)).quasiMeasurePreserving.ae hbg

theorem upper_focalCount_eq_old (C D : ContextPolicy m c Seed)
    (Γ : FiniteGame m 2 c Seed) {U R : ℝ} (hUR : U < R)
    (hgap : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ, x.2.bid ≤ U ∨ R ≤ x.2.bid)
    (i : Fin m) (act : JointAction 2) (hb : R ≤ act.bid) :
    focalCount (ClosedPolicy.nativeGame C Γ R) i act =ᵐ[sampleLaw Γ]
      focalCount (D.nativeGame Γ U) i act := by
  filter_upwards [sample_noGap_support Γ U R hgap] with ω hω
  have hx : ∀ k, ((deviated i act ω).action k).bid ≤ U ∨
      R ≤ ((deviated i act ω).action k).bid := by
    intro k
    by_cases hk : k = i
    · subst k
      right
      simpa only [deviated_bid_self] using hb
    · simpa only [deviated_bid_other i k hk] using hω k
  apply Fin.ext
  exact upper_inclusionCount_eq_old C D hUR (deviated i act ω) hx ω.1.2 ω.1.2 i
    (by simpa only [deviated_bid_self] using hb)

theorem upper_outcome_eq_old (C D : ContextPolicy m c Seed)
    (Γ : FiniteGame m 2 c Seed) {U R : ℝ} (hUR : U < R)
    (hgap : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ, x.2.bid ≤ U ∨ R ≤ x.2.bid)
    (i : Fin m) (act : JointAction 2) (hb : R ≤ act.bid) :
    (problem (ClosedPolicy.nativeGame C Γ R) i).outcome act =
      (problem (D.nativeGame Γ U) i).outcome act := by
  rw [problem_outcome, problem_outcome]
  exact CountLaw.ofMeasure_congr_ae (sampleLaw Γ) _ _
    (measurable_focalCount (ClosedPolicy.nativeGame C Γ R) i act)
    (measurable_focalCount (D.nativeGame Γ U) i act)
    (upper_focalCount_eq_old C D Γ hUR hgap i act hb)

theorem upper_payoff_eq_old (C D : ContextPolicy m c Seed)
    (Γ : FiniteGame m 2 c Seed) {U R : ℝ} (hUR : U < R)
    (hgap : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ, x.2.bid ≤ U ∨ R ≤ x.2.bid)
    (i : Fin m) (v : ℝ) (act : JointAction 2) (hb : R ≤ act.bid) :
    (problem (ClosedPolicy.nativeGame C Γ R) i).payoff v act =
      (problem (D.nativeGame Γ U) i).payoff v act := by
  change ((problem (ClosedPolicy.nativeGame C Γ R) i).outcome act).utility
      v act.bid Γ.g Γ.A Γ.G =
    ((problem (D.nativeGame Γ U) i).outcome act).utility v act.bid Γ.g Γ.A Γ.G
  rw [upper_outcome_eq_old C D Γ hUR hgap i act hb]

theorem upper_mean_eq_old (C D : ContextPolicy m c Seed)
    (Γ : FiniteGame m 2 c Seed) {U R : ℝ} (hUR : U < R) (hR : 0 ≤ R)
    (hgap : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ, x.2.bid ≤ U ∨ R ≤ x.2.bid)
    (i : Fin m) (y : ℝ) (hy : R ≤ y) :
    meanAcceptProb (ClosedPolicy.nativeGame C Γ R) i y =
      meanAcceptProb (D.nativeGame Γ U) i y := by
  let act : JointAction 2 := ⟨y, hR.trans hy, 1, by omega⟩
  have hh := congrArg CountLaw.load (upper_outcome_eq_old C D Γ hUR hgap i act hy)
  rw [load_eq_mean _ (by norm_num : 0 < 2), load_eq_mean _ (by norm_num : 0 < 2)] at hh
  simpa only [act, Nat.cast_one, one_mul] using hh

end ExactTransport

lemma population_noGap_support (s a h U R : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a)
    (hh : 0 ≤ h) (hsum : s+a+h = 1)
    (PL PA PH : ProbabilityMeasure (ℝ × JointAction 2))
    (hL : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)), x.2.bid ≤ U)
    (hA : ∀ᵐ x ∂(PA : Measure (ℝ × JointAction 2)), x.2.bid ≤ U)
    (hH : ∀ᵐ x ∂(PH : Measure (ℝ × JointAction 2)), R ≤ x.2.bid) :
    ∀ᵐ x ∂(populationLaw s a h hs ha hh hsum PL PA PH : Measure (ℝ × JointAction 2)),
      x.2.bid ≤ U ∨ R ≤ x.2.bid := by
  change ∀ᵐ x ∂populationJoint s a h PL PA PH, _
  rw [populationJoint, ae_add_measure_iff, ae_add_measure_iff]
  exact ⟨⟨Measure.ae_smul_measure (hL.mono (fun _ hx => Or.inl hx)) _,
    Measure.ae_smul_measure (hA.mono (fun _ hx => Or.inl hx)) _⟩,
    Measure.ae_smul_measure (hH.mono (fun _ hx => Or.inr hx)) _⟩

lemma physical_upper_floor_of_bidLaw (FH : ProbabilityMeasure ℝ)
    (PH : ProbabilityMeasure (ℝ × JointAction 2)) (b : ℝ → ℝ) (hb : Measurable b)
    (hbid : (PH : Measure (ℝ × JointAction 2)).map (fun x => x.2.bid) =
      (FH : Measure ℝ).map b) (R : ℝ)
    (hfloor : ∀ᵐ v ∂(FH : Measure ℝ), R ≤ b v) :
    ∀ᵐ x ∂(PH : Measure (ℝ × JointAction 2)), R ≤ x.2.bid := by
  have hm : Measurable (fun x : ℝ × JointAction 2 => x.2.bid) :=
    (measurable_bid 2).comp measurable_snd
  apply (ae_map_iff hm.aemeasurable measurableSet_Ici).mp
  rw [hbid]
  exact (ae_map_iff hb.aemeasurable measurableSet_Ici).mpr hfloor

section Population
variable (m c : ℕ) (U R s a h : ℝ)
    (C : ContextPolicy m c unitInterval)
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h = 1)
    (PL PA PH : ProbabilityMeasure (ℝ × JointAction 2))
    (hL : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)), x.2.bid ≤ U)
    (hA : ∀ᵐ x ∂(PA : Measure (ℝ × JointAction 2)), x.2.bid ≤ U)
    (hHfloor : ∀ᵐ x ∂(PH : Measure (ℝ × JointAction 2)), R ≤ x.2.bid)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1)
local notation "P" => populationLaw s a h hs ha hh hsum PL PA PH
local notation "Gamma" => PopulationGame.game m c P η hη0 hη1 U
local notation "Closed" => ClosedPolicy.nativeGame C Gamma R

include hL hA hHfloor in
lemma upper_population_outcome_eq_old (hUR : U < R)
    (i : Fin m) (act : JointAction 2) (hb : R ≤ act.bid) :
    (problem Closed i).outcome act = (problem Gamma i).outcome act := by
  let D := NativeContinuation.contextPolicy (m := m) ((1-η)/2)
    (by linarith : 0 < (1-η)/2) (by linarith : (1-η)/2 < 1) c
  have hgap : ∀ᵐ x ∂(Gamma).F ⊗ₘ (Gamma).σ, x.2.bid ≤ U ∨ R ≤ x.2.bid := by
    rw [PopulationGame.joint_law]
    exact population_noGap_support s a h U R hs ha hh hsum PL PA PH hL hA hHfloor
  exact upper_outcome_eq_old C D Gamma hUR hgap i act hb

include hL hA hHfloor in
lemma upper_population_payoff_eq_old (hUR : U < R)
    (i : Fin m) (v : ℝ) (act : JointAction 2) (hb : R ≤ act.bid) :
    (problem Closed i).payoff v act = (problem Gamma i).payoff v act := by
  change ((problem Closed i).outcome act).utility v act.bid (Gamma).g (Gamma).A (Gamma).G =
    ((problem Gamma i).outcome act).utility v act.bid (Gamma).g (Gamma).A (Gamma).G
  rw [upper_population_outcome_eq_old m c U R s a h C hs ha hh hsum PL PA PH
    hL hA hHfloor η hη0 hη1 hUR i act hb]

include hL hA hHfloor in
lemma upper_population_mean_eq_old (hUR : U < R) (hR : 0 ≤ R)
    (i : Fin m) (y : ℝ) (hy : R ≤ y) :
    meanAcceptProb Closed i y = meanAcceptProb Gamma i y := by
  let D := NativeContinuation.contextPolicy (m := m) ((1-η)/2)
    (by linarith : 0 < (1-η)/2) (by linarith : (1-η)/2 < 1) c
  have hgap : ∀ᵐ x ∂(Gamma).F ⊗ₘ (Gamma).σ, x.2.bid ≤ U ∨ R ≤ x.2.bid := by
    rw [PopulationGame.joint_law]
    exact population_noGap_support s a h U R hs ha hh hsum PL PA PH hL hA hHfloor
  exact upper_mean_eq_old C D Gamma hUR hR hgap i y hy

end Population

section Constructed
variable (m c : ℕ) (U s a h : ℝ) (hU : 0 ≤ U)
    (C : ContextPolicy m c unitInterval)
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hh1 : h ≤ 1) (hsum : s+a+h = 1)
    (PL PA PH : ProbabilityMeasure (ℝ × JointAction 2)) (FH : ProbabilityMeasure ℝ)
    [NullSingletonClass (FH : Measure ℝ)]
    (hL : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)), x.2.bid ≤ U)
    (hA : ∀ᵐ x ∂(PA : Measure (ℝ × JointAction 2)), x.2.bid ≤ U)
    (hH : ∀ᵐ x ∂(PH : Measure (ℝ × JointAction 2)), x.2.routeCount = 1)
    (hnull : ∀ y : ℝ, (PH : Measure (ℝ × JointAction 2)) {x | x.2.bid = y} = 0)
    (b : ℝ → ℝ)
    (hbid : (PH : Measure (ℝ × JointAction 2)).map (fun x => x.2.bid) = (FH : Measure ℝ).map b)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1)
local notation "P" => populationLaw s a h hs ha hh hsum PL PA PH
local notation "Gamma" => PopulationGame.game m c P η hη0 hη1 U
local notation "mu" => ENNReal.ofReal h • (FH : Measure ℝ)

local instance weightedUpperFinite : IsFiniteMeasure mu := by
  constructor
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  exact ENNReal.ofReal_lt_top

local instance weightedUpperAtomless : NullSingletonClass mu :=
  ⟨fun y => by simp only [Measure.smul_apply, smul_eq_mul, measure_singleton, mul_zero]⟩

include hh hh1 in
omit [NullSingletonClass (FH : Measure ℝ)] in
lemma constructed_rank_mass : (mu).real univ ≤ 1 :=
  weighted_upper_mass_le_one h hh hh1 FH

include hh hh1 in
omit [NullSingletonClass (FH : Measure ℝ)] in
lemma constructed_bid_floor (hm : 2 ≤ m) (hc : 1 ≤ c) (hcm : c < m)
    (t R : ℝ) (hRt : R < t)
    (hb : b = bid (rank mu (m-1) c 2) t R) (v : ℝ) (hv : t ≤ v) : R ≤ b v := by
  have hmEq : m-2+1 = m-1 := by omega
  have hmass : (mu).real univ ≤ 1 := weighted_upper_mass_le_one h hh hh1 FH
  have hqmono : Monotone (rank mu (m-1) c 2) := by
    have hn := rank_monotone mu (r := m-2) hc (by omega) (by norm_num : 2 ≤ (2 : ℕ)) hmass
    rwa [hmEq] at hn
  have hqpos : 0 < rank mu (m-1) c 2 t := rank_pos mu _ _ hc (by norm_num) hmass t
  rw [hb]
  exact floor_le_bid hqmono hRt.le hqpos hv

include hh hh1 hbid in
lemma constructed_physical_upper_floor (hm : 2 ≤ m) (hc : 1 ≤ c) (hcm : c < m)
    (t R : ℝ) (hRt : R < t)
    (hsupport : ∀ᵐ v ∂(FH : Measure ℝ), t ≤ v)
    (hb : b = bid (rank mu (m-1) c 2) t R) :
    ∀ᵐ x ∂(PH : Measure (ℝ × JointAction 2)), R ≤ x.2.bid := by
  have hmass : (mu).real univ ≤ 1 := weighted_upper_mass_le_one h hh hh1 FH
  have hqpos : ∀ x, 0 < rank mu (m-1) c 2 x :=
    fun x => rank_pos mu _ _ hc (by norm_num) hmass x
  have hbm : Measurable b := by
    rw [hb]
    exact (continuous_bid (continuous_rank mu _ _ _) (fun x => (hqpos x).ne') t R).measurable
  apply physical_upper_floor_of_bidLaw FH PH b hbm hbid R
  filter_upwards [hsupport] with v hv
  exact constructed_bid_floor m c h hh hh1 FH b hm hc hcm t R hRt hb v hv

include hU hh1 hL hA hH hnull hbid in

theorem closed_upper_constructed_attainment (hm : 2 ≤ m) (hc : 1 ≤ c) (hcm : c < m)
    (t R : ℝ) (hR : 0 < R) (hRt : R < t) (hUR : U < R)
    (hsupport : ∀ᵐ v ∂(FH : Measure ℝ), t ≤ v)
    (hb : b = bid (rank mu (m-1) c 2) t R)
    (i : Fin m) (v : ℝ) (hv : t ≤ v) :
    (problem (ClosedPolicy.nativeGame C Gamma R) i).payoff v (upperAction b v) =
      utility (rank mu (m-1) c 2) t R v := by
  have hf := constructed_physical_upper_floor m c h hh hh1 PH FH b hbid
    hm hc hcm t R hRt hsupport hb
  have hbv := constructed_bid_floor m c h hh hh1 FH b hm hc hcm t R hRt hb v hv
  have hact : R ≤ (upperAction b v).bid := by
    change R ≤ max (b v) 0
    exact hbv.trans (le_max_left _ _)
  rw [upper_population_payoff_eq_old m c U R s a h C hs ha hh hsum PL PA PH
    hL hA hf η hη0 hη1 hUR i v (upperAction b v) hact]
  exact native_upper_constructed_attainment m c U s a h hU hs ha hh hh1 hsum
    PL PA PH FH hL hA hH hnull b hbid η hη0 hη1 hm hc hcm t R hR hRt hUR hsupport hb i v hv

include hU hh1 hL hA hH hnull hbid in

theorem closed_upper_one_route_bound (hm : 2 ≤ m) (hc : 1 ≤ c) (hcm : c < m)
    (t R H : ℝ) (hR : 0 < R) (hRt : R < t) (hUR : U < R)
    (hsupport : ∀ᵐ v ∂(FH : Measure ℝ), v ∈ Icc t H)
    (hb : b = bid (rank mu (m-1) c 2) t R)
    (i : Fin m) (v : ℝ) (act : JointAction 2)
    (hk : act.routeCount = 1) (hact : R ≤ act.bid) :
    (problem (ClosedPolicy.nativeGame C Gamma R) i).payoff v act ≤
      utility (rank mu (m-1) c 2) t R v := by
  have hf := constructed_physical_upper_floor m c h hh hh1 PH FH b hbid
    hm hc hcm t R hRt (hsupport.mono (fun _ hv => hv.1)) hb
  rw [upper_population_payoff_eq_old m c U R s a h C hs ha hh hsum PL PA PH
    hL hA hf η hη0 hη1 hUR i v act hact]
  have hmEq : m-2+1 = m-1 := by omega
  have hmass : (mu).real univ ≤ 1 := weighted_upper_mass_le_one h hh hh1 FH
  have hsMu : ∀ᵐ x ∂mu, x ∈ Icc t H := Measure.ae_smul_measure hsupport _
  have HE := upper_envelope_bounded mu (m-2) c hc (by omega) hmass t R H hR hRt hsMu
  rw [hmEq, ← hb] at HE
  exact native_upper_one_route_bound m c U s a h hU hs ha hh hh1 hsum
    PL PA PH FH hL hA hH hnull b hbid η hη0 hη1 hm (by omega)
    (rank mu (m-1) c 2) (utility (rank mu (m-1) c 2) t R) t R
    (error (rank mu (m-1) c 2) t R) hUR HE i v act hk hact

include hU hh1 hL hA hH hnull hbid in

theorem closed_upper_mean_floor_lower (hm : 2 ≤ m) (hc : 1 ≤ c) (hcm : c < m)
    (t R : ℝ) (hRt : R < t) (hUR : U < R)
    (hsupport : ∀ᵐ v ∂(FH : Measure ℝ), t ≤ v)
    (hb : b = bid (rank mu (m-1) c 2) t R)
    (i : Fin m) (y : ℝ) (hy : R ≤ y) :
    rank mu (m-1) c 2 t ≤ meanAcceptProb (ClosedPolicy.nativeGame C Gamma R) i y := by
  have hf := constructed_physical_upper_floor m c h hh hh1 PH FH b hbid
    hm hc hcm t R hRt hsupport hb
  rw [upper_population_mean_eq_old m c U R s a h C hs ha hh hsum PL PA PH
    hL hA hf η hη0 hη1 hUR (hU.trans hUR.le) i y hy]
  exact native_upper_mean_floor_lower m c U s a h hU hs ha hh hh1 hsum
    PL PA PH FH hL hA hH hnull b hbid η hη0 hη1 hm hc hcm t R hRt hUR hsupport hb i y hy

include hU hh1 hL hA hH hnull hbid in

theorem closed_upper_hidden_constructed_excluded
    (hm : 2 ≤ m) (hc : 1 ≤ c) (hcm : c < m)
    (t R H : ℝ) (hR : 0 < R) (hRt : R < t) (hUR : U < R)
    (hsupport : ∀ᵐ v ∂(FH : Measure ℝ), v ∈ Icc t H)
    (hb : b = bid (rank mu (m-1) c 2) t R)
    (hguard : error (rank mu (m-1) c 2) t R <
      η*R*(1-2*(1-rank mu (m-1) c 2 t)))
    (i : Fin m) (v : ℝ) (hv : t ≤ v)
    (act : JointAction 2) (hk : act.routeCount = 2) (hact : R ≤ act.bid) :
    (problem (ClosedPolicy.nativeGame C Gamma R) i).payoff v act <
      utility (rank mu (m-1) c 2) t R v := by
  have hf := constructed_physical_upper_floor m c h hh hh1 PH FH b hbid
    hm hc hcm t R hRt (hsupport.mono (fun _ hv => hv.1)) hb
  rw [upper_population_payoff_eq_old m c U R s a h C hs ha hh hsum PL PA PH
    hL hA hf η hη0 hη1 hUR i v act hact]
  exact native_upper_hidden_constructed_excluded m c U s a h hU hs ha hh hh1 hsum
    PL PA PH FH hL hA hH hnull b hbid η hη0 hη1 hm hc hcm t R H hR hRt hUR
    hsupport hb hguard i v hv act hk hact

end Constructed
end FCAppendix.Affine.Hybrid.Native02
