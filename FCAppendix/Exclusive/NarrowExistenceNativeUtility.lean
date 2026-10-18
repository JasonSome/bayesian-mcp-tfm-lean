import FCAppendix.Exclusive.NarrowExistenceNativeStatistics
import FCAppendix.Exclusive.NarrowExistenceGameNormalization

noncomputable section
namespace FCAppendix.Bayes.ExclusiveConstruction
open MeasureTheory ProbabilityTheory Game Exclusive ExclusiveNarrow Set Filter
open Exclusive.Narrow.Finite Exclusive.Narrow.Existence
open scoped BigOperators

def actionProfilePayoff {m : ℕ} (d c : ℕ) (a : UserTariff) (G : Schedule (d+1))
    (g v b : ℝ) (acts : Fin m → JointAction (d+1)) : ℝ :=
  LowType.binomialPayoff a G (d+1) g v b
    (Exclusive.Narrow.focalMarginal (1/(d:ℝ)) ((1+actionRivalCount acts-c:ℕ):ℝ)
      (actionRivalWeight (d+1) acts) b)

theorem measurable_actionProfilePayoff {m : ℕ} (d c : ℕ) (a : UserTariff)
    (G : Schedule (d+1)) (g v b : ℝ) :
    Measurable (actionProfilePayoff (m := m) d c a G g v b) := by
  have hN : Measurable (fun acts : Fin m → JointAction (d+1) => ((1+actionRivalCount acts-c:ℕ):ℝ)) :=
    (measurable_of_countable (fun N : ℕ => ((1+N-c:ℕ):ℝ))).comp measurable_actionRivalCount
  have hp : Measurable (fun acts : Fin m → JointAction (d+1) =>
      Exclusive.Narrow.focalMarginal (1/(d:ℝ)) ((1+actionRivalCount acts-c:ℕ):ℝ)
        (actionRivalWeight (d+1) acts) b) :=
    measurable_const.sub ((hN.mul_const _).div ((measurable_actionRivalWeight (d+1)).add_const _))
  exact (LowType.continuous_binomialPayoff a G (d+1) g v b).measurable.comp hp

theorem canonical_profile_payoff_eq_actionProfilePayoff {m d c : ℕ}
    (P : Corridor (d+1) (m+1) c) (i : Fin (m+1)) (profile : UserProfile (m+1) (d+1))
    (hprofile : GoodProfile P profile) (a : UserTariff) (G : Schedule (d+1)) (g v b : ℝ)
    (hb : b ∈ Icc P.lower P.upper) :
    LowType.binomialPayoff a G (d+1) g v b
      (ExclusiveSource.focalMarginal (d+1) P.proposers c i b profile) =
        actionProfilePayoff d c a G g v b (fun j : Fin m => (profile (i.succAbove j)).1.2) := by
  rw [canonical_focalMarginal_eq_corridor P i profile hprofile hb,
    rivalCount_eq_actionRivalCount, rivalWeight_eq_actionRivalWeight]
  simp only [Corridor.allocation, rate, Nat.add_sub_cancel_right, actionProfilePayoff]

theorem actionProfilePayoff_flag_normalization {m : ℕ} {V : Type*}
    (d c : ℕ) (hd : 1 ≤ d) (a : UserTariff) (ha : a.Allowed) (G : Schedule (d+1))
    (p0 H baseRatio : ℝ) (hp0 : 0 ≤ p0) (hp1 : p0 < 1) (hH : 0 < H)
    (beta : V → ℝ) (v z : ℝ) (omega : RivalProfile m V) :
    let B := H*referenceBidScale d a p0
    actionProfilePayoff d c a G (H*baseRatio) (H*v) (B*Real.exp z)
      (fun j => flagAction (d+1) (fun w => B*Real.exp (beta w)) (omega j)) =
        B*finiteRowUtility d c a G p0 baseRatio beta v z omega := by
  have hB := mul_pos hH (referenceBidScale_pos d hd a ha p0 hp0 hp1)
  dsimp only
  unfold actionProfilePayoff
  rw [actionRivalCount_flag (by omega), actionRivalWeight_flag (by omega) _
    (fun _ => (mul_pos hB (Real.exp_pos _)).le)]
  change LowType.binomialPayoff a G (d+1) (H*baseRatio) (H*v)
    (H*referenceBidScale d a p0*Real.exp z)
    (Exclusive.Narrow.focalMarginal (1/(d:ℝ)) ((1+activeCount omega-c:ℕ):ℝ)
      (rawRivalInverseSum d (H*referenceBidScale d a p0) beta omega)
      (H*referenceBidScale d a p0*Real.exp z)) = _
  rw [LowType.binomialPayoff, ← Narrow.binomialPolynomial_once (d+1)]
  exact finiteRowUtility_normalization d c hd a ha G p0 H baseRatio hp0 hp1 hH beta v z omega

section Native
variable {m d c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {V : Type*} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]

theorem canonical_profile_integral_normalization
    (Gamma : FiniteGame (m+1) (d+1) c Seed) (P : Corridor (d+1) (m+1) c)
    (hplay : CorridorPlay Gamma P) (i : Fin (m+1))
    (a : UserTariff) (ha : a.Allowed) (p0 H baseRatio : ℝ)
    (hp0 : 0 ≤ p0) (hp1 : p0 < 1) (hH : 0 < H) (hcharge : Gamma.g = H*baseRatio)
    (h : unitInterval) (nu : Measure V) [IsProbabilityMeasure nu]
    (beta : V → ℝ) (hbeta : Continuous beta) (v z : ℝ)
    (hb : H*referenceBidScale d a p0*Real.exp z ∈ Icc P.lower P.upper)
    (hlaw : (userProfileLaw Gamma).map (fun profile j => (profile (i.succAbove j)).1.2) =
      (iidRivalLaw m h nu).map (fun omega j => flagAction (d+1)
        (fun w => H*referenceBidScale d a p0*Real.exp (beta w)) (omega j))) :
    (∫ profile, LowType.binomialPayoff a Gamma.G (d+1) Gamma.g (H*v)
      (H*referenceBidScale d a p0*Real.exp z)
      (ExclusiveSource.focalMarginal (d+1) P.proposers c i
        (H*referenceBidScale d a p0*Real.exp z) profile) ∂userProfileLaw Gamma) =
      (H*referenceBidScale d a p0)*finiteExpectedUtility (m := m) d c a Gamma.G
        p0 baseRatio h nu beta v z := by
  have hd : 1 ≤ d := by have := P.proposers; omega
  let B := H*referenceBidScale d a p0
  let test := actionProfilePayoff (m := m) d c a Gamma.G (H*baseRatio) (H*v) (B*Real.exp z)
  have htest : Measurable test := measurable_actionProfilePayoff d c a Gamma.G _ _ _
  have hproj : Measurable (fun profile : UserProfile (m+1) (d+1) =>
      fun j : Fin m => (profile (i.succAbove j)).1.2) :=
    measurable_pi_lambda _ (fun j => measurable_snd.comp (measurable_fst.comp (measurable_pi_apply _)))
  have hflag : Measurable (fun omega : RivalProfile m V => fun j => flagAction (d+1)
      (fun w => B*Real.exp (beta w)) (omega j)) :=
    measurable_pi_lambda _ (fun j =>
      (measurable_flagAction (d+1) (measurable_const.mul (Real.continuous_exp.comp hbeta).measurable)).comp
        (measurable_pi_apply j))
  calc
    _ = ∫ profile, test (fun j : Fin m => (profile (i.succAbove j)).1.2) ∂userProfileLaw Gamma := by
      apply integral_congr_ae
      filter_upwards [ae_goodProfile Gamma P hplay] with profile hprofile
      rw [hcharge]
      exact canonical_profile_payoff_eq_actionProfilePayoff P i profile hprofile a Gamma.G _ _ _ hb
    _ = ∫ acts, test acts ∂(userProfileLaw Gamma).map
        (fun profile j => (profile (i.succAbove j)).1.2) :=
      (integral_map hproj.aemeasurable htest.aestronglyMeasurable).symm
    _ = ∫ acts, test acts ∂(iidRivalLaw m h nu).map
        (fun omega j => flagAction (d+1) (fun w => B*Real.exp (beta w)) (omega j)) := by rw [hlaw]
    _ = ∫ omega, test (fun j => flagAction (d+1) (fun w => B*Real.exp (beta w)) (omega j)) ∂iidRivalLaw m h nu :=
      integral_map hflag.aemeasurable htest.aestronglyMeasurable
    _ = ∫ omega, B*finiteRowUtility d c a Gamma.G p0 baseRatio beta v z omega ∂iidRivalLaw m h nu := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (actionProfilePayoff_flag_normalization d c hd a ha Gamma.G
        p0 H baseRatio hp0 hp1 hH beta v z)
    _ = _ := integral_const_mul _ _

theorem source_full_payoff_normalization
    (Gamma : FiniteGame (m+1) (d+1) c Seed) (P : Corridor (d+1) (m+1) c)
    (hplay : CorridorPlay Gamma P) (cutoff : ℝ) (hcut : cutoff ≤ P.lower)
    (fallback : LocalPolicy (m+1) c Seed)
    (hfallback : Measurable (fun p : LocalList (m+1) × Seed => (fallback p.1 p.2).val))
    (hcanonical : ∀ L, FiniteLaw.ofMeasure Gamma.seedLaw (fun s => (fallback L s).val)
      (hfallback.comp (measurable_const.prodMk measurable_id)) =
        canonicalLottery (d+1) P.proposers c (listBids L))
    (hpolicy : ∀ j L s, (Gamma.policy j L s).val =
      (Marker.sourceContinuation P.population P.proposers P.capacity cutoff fallback L s).val)
    (i : Fin (m+1)) (a : UserTariff) (ha : a.Allowed) (p0 H baseRatio : ℝ)
    (hp0 : 0 ≤ p0) (hp1 : p0 < 1) (hH : 0 < H) (hcharge : Gamma.g = H*baseRatio)
    (h : unitInterval) (nu : Measure V) [IsProbabilityMeasure nu]
    (beta : V → ℝ) (hbeta : Continuous beta) (v z : ℝ)
    (hb : H*referenceBidScale d a p0*Real.exp z ∈ Icc P.lower P.upper)
    (hlaw : (userProfileLaw Gamma).map (fun profile j => (profile (i.succAbove j)).1.2) =
      (iidRivalLaw m h nu).map (fun omega j => flagAction (d+1)
        (fun w => H*referenceBidScale d a p0*Real.exp (beta w)) (omega j))) :
    let B := H*referenceBidScale d a p0
    let action : JointAction (d+1) :=
      ⟨B*Real.exp z,(P.lower_pos.trans_le hb.1).le,d+1,le_rfl⟩
    exclusiveTariffPayoff Gamma a i (H*v) action =
      B*finiteExpectedUtility (m := m) d c a Gamma.G p0 baseRatio h nu beta v z := by
  have hd : ∀ᵐ profile ∂userProfileLaw Gamma, ExclusiveSource.HighRivals cutoff i profile := by
    filter_upwards [ae_goodProfile Gamma P hplay] with profile hprofile
    intro j _
    rcases hprofile j with hz | ⟨hr,hbid⟩
    · exact Or.inl hz
    · exact Or.inr ⟨hr,hcut.trans hbid.1⟩
  dsimp only
  rw [ExclusiveSource.source_actual_payoff_large_bid Gamma P.population P.proposers P.capacity cutoff
    fallback hfallback hcanonical hpolicy a i hd _ _ (hcut.trans hb.1)]
  exact canonical_profile_integral_normalization Gamma P hplay i a ha p0 H baseRatio hp0 hp1 hH
    hcharge h nu beta hbeta v z hb hlaw

theorem full_payoff_normalization_of_continuation
    (Gamma : FiniteGame (m+1) (d+1) c Seed) (P : Corridor (d+1) (m+1) c)
    (hplay : CorridorPlay Gamma P) (Bpost : PosteriorSystem Gamma)
    (hcont : BroadcastCorridorContinuation Gamma Bpost P)
    (i : Fin (m+1)) (a : UserTariff) (ha : a.Allowed) (p0 H baseRatio : ℝ)
    (hp0 : 0 ≤ p0) (hp1 : p0 < 1) (hH : 0 < H) (hcharge : Gamma.g = H*baseRatio)
    (h : unitInterval) (nu : Measure V) [IsProbabilityMeasure nu]
    (beta : V → ℝ) (hbeta : Continuous beta) (v z : ℝ)
    (hb : H*referenceBidScale d a p0*Real.exp z ∈ Icc P.lower P.upper)
    (hlaw : (userProfileLaw Gamma).map (fun profile j => (profile (i.succAbove j)).1.2) =
      (iidRivalLaw m h nu).map (fun omega j => flagAction (d+1)
        (fun w => H*referenceBidScale d a p0*Real.exp (beta w)) (omega j))) :
    let B := H*referenceBidScale d a p0
    let action : JointAction (d+1) :=
      ⟨B*Real.exp z,(P.lower_pos.trans_le hb.1).le,d+1,le_rfl⟩
    exclusiveTariffPayoff Gamma a i (H*v) action =
      B*finiteExpectedUtility (m := m) d c a Gamma.G p0 baseRatio h nu beta v z := by
  dsimp only
  rw [ExclusiveSource.exclusiveTariffPayoff_eq_test,
    interim_moment_of_continuation Gamma P hplay Bpost hcont i
      (H*v, ⟨H*referenceBidScale d a p0*Real.exp z,(P.lower_pos.trans_le hb.1).le,d+1,le_rfl⟩)
      rfl hb]
  have he : (gameRow Gamma P hplay i).moment
      (ExclusiveSource.payoffTest a Gamma.G Gamma.g (H*v) (H*referenceBidScale d a p0*Real.exp z))
      (H*referenceBidScale d a p0*Real.exp z) =
      ∫ profile, LowType.binomialPayoff a Gamma.G (d+1) Gamma.g (H*v)
        (H*referenceBidScale d a p0*Real.exp z)
        (ExclusiveSource.focalMarginal (d+1) P.proposers c i
          (H*referenceBidScale d a p0*Real.exp z) profile) ∂userProfileLaw Gamma := by
    apply integral_congr_ae
    filter_upwards [ae_goodProfile Gamma P hplay] with profile hprofile
    rw [canonical_focalMarginal_eq_corridor P i profile hprofile hb]
    have hp := P.allocation_bounds (rival_bounds P i profile hprofile) hb
    exact ExclusiveSource.binomial_payoffTest a Gamma.G (d+1) Gamma.g (H*v)
      (H*referenceBidScale d a p0*Real.exp z) _ hp.1.le hp.2
  rw [he]
  exact canonical_profile_integral_normalization Gamma P hplay i a ha p0 H baseRatio hp0 hp1 hH
    hcharge h nu beta hbeta v z hb hlaw

end Native
end FCAppendix.Bayes.ExclusiveConstruction
