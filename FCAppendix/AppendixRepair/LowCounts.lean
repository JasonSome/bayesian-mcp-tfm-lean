import FCAppendix.AppendixRepair.LowGroup
import FCAppendix.AppendixRepair.TriangularLow
import FCAppendix.PayOnce.BroadcastRescue
import FCAppendix.Finite.MixedBestResponseCounts

set_option maxHeartbeats 2400000
noncomputable section
namespace FCAppendix.Appendix08.LowCounts
open MeasureTheory ProbabilityTheory Set Game Bayes Filter Topology Classical
open Affine Affine.LowBody Affine.Hybrid Affine.Hybrid.NativeContinuation
open Affine.AppendixRepair.TriangularLow
open Existence.Distributional
open scoped BigOperators

abbrev AnyHigherUnderflow {N : ℕ} (c : ℕ) (kind : Fin N → Fin 4) : Prop :=
  HigherUnderflow c kind

def rowHigherUnderflow {N : ℕ} (c : ℕ) : Set (Fin N → RowRival) :=
  {omega | HigherUnderflow c (fun i => (omega i).1)}

lemma measurableSet_rowHigherUnderflow {N : ℕ} (c : ℕ) :
    MeasurableSet (rowHigherUnderflow (N := N) c) := by
  have hm : Measurable (fun omega : Fin N → RowRival => fun i => (omega i).1) :=
    measurable_pi_lambda _ (fun i => (measurable_pi_apply i).fst)
  exact hm (MeasurableSet.of_discrete :
    MeasurableSet {kind : Fin N → Fin 4 | HigherUnderflow c kind})

theorem native_focal_success_implies_higherUnderflow {N : ℕ}
    (xi : ℝ) (hxi : 0 < xi) (hxi1 : xi < 1) (c : ℕ)
    (Gamma : FiniteGame (N+1) 2 c unitInterval) {d U : ℝ}
    (hd : 0 ≤ d) (hdU : d ≤ U)
    (z : UserProfile (N+1) 2) (hz : z ∈ classifiedProfiles (N+1) U) (i : Fin (N+1))
    (hf : (z i).1.2.bid ≤ d)
    (hactive : ∀ k ∈ upperSet d (actualContext U z).1,
      d < (1-xi)*entryBid ((actualContext U z).1 k))
    (seed : Fin 2 → unitInterval)
    (hpositive : 0 < inclusionCount (drawsRealization z)
      ((contextPolicy xi hxi hxi1 c).nativeGame Gamma U).policy seed i) :
    HigherUnderflow c (fun j => (collapsedDeletedRow d U z i j).1) := by
  let e := focalIndex i
  let zn := z ∘ e
  let X := actualContext U z
  let A := upperSet d X.1
  let omega := collapsedDeletedRow d U z i
  have he0 : e 0 = i := focalIndex_zero i
  have hzn : zn ∈ classifiedProfiles (N+1) U := fun k => hz (e k)
  have hfn : (zn 0).1.2.bid ≤ d := by
    simpa only [zn, Function.comp_apply, he0] using hf
  have hctx : actualContext U zn = reindexContext e X := actualContext_reindex e U z
  have hrow : collapsedProfileRow d U zn = omega := collapsedProfileRow_focalIndex d U z i
  have hcard : (upperSet d (actualContext U zn).1).card = A.card := by
    rw [hctx]
    change (upperSet d (X.1 ∘ e)).card = A.card
    rw [upperSet_reindex, Finset.card_map]
  have hr (j : Fin 2) : residual c j (actualContext U zn) = residual c j X := by
    rw [hctx]
    rfl
  have hbid := actualContext_entryBid U z hz i (hf.trans hdU)
  have hi : i ∉ A := by
    intro hk
    have hgt := upperSet_entry_gt X.1 i hk
    rw [hbid] at hgt
    linarith
  have hlow : ∀ k ∉ A, entryBid (X.1 k) ≤ d :=
    fun k hk => nonupper_entry_le hd _ k hk
  rw [ContextPolicy.native_inclusionCount_eq_focalCopy _ Gamma U z hz seed i
    (hf.trans hdU)] at hpositive
  have hsome : i ∈ select xi hxi hxi1 c 0 X (seed 0) ∨
      i ∈ select xi hxi hxi1 c 1 X (seed 1) := by
    by_cases h0 : i ∈ select xi hxi hxi1 c 0 X (seed 0)
    · exact Or.inl h0
    · by_cases h1 : i ∈ select xi hxi hxi1 c 1 X (seed 1)
      · exact Or.inr h1
      · simp [ContextPolicy.selectionPair, contextPolicy, focalCopy, X, h0, h1] at hpositive
  have hu (j : Fin 2) (hs : i ∈ select xi hxi hxi1 c j X (seed j)) :
      classCount 1 omega + classCount (upperTag j) omega < c := by
    have hh := low_included_implies_active_underflow xi hxi hxi1 c X
      (actualContext_nonnegative U z hz) j (seed j) d A hactive hlow i hi hs
    have hn : residual c j (actualContext U zn) -
        (upperSet d (actualContext U zn).1).card =
      c - classCount 1 (collapsedProfileRow d U zn) -
        classCount (upperTag j) (collapsedProfileRow d U zn) :=
      (collapsed_context_data (c := c) hdU zn hzn hfn).2.2 j
    rw [hr j, hcard, hrow] at hn
    omega
  rcases hsome with h0 | h1
  · left
    rw [sum_firstHigher]
    exact hu 0 h0
  · right
    rw [sum_secondHigher]
    exact hu 1 h1

theorem native_higherUnderflow_common_conull {N c : ℕ} {d U eta : ℝ}
    (P : ProbabilityMeasure (ℝ × JointAction 2)) (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (hd : 0 ≤ d) (hdU : d ≤ U)
    (hprofiles : ∀ᵐprofile ∂userProfileLaw (PopulationGame.game (N+1) c P eta heta0 heta1 U),
      ∀ k, lowActionGuard d U ((1+eta)/2) (profile k).1.2) :
    let Gamma := PopulationGame.game (N+1) c P eta heta0 heta1 U
    ∀ᵐomega ∂sampleLaw Gamma, ∀ i : Fin (N+1), ∀ act : JointAction 2,
      act.bid ≤ d → 0 < (focalCount Gamma i act omega).val →
      HigherUnderflow c (fun j => (collapsedDeletedRow d U omega.1.1 i j).1) := by
  dsimp only
  let Gamma := PopulationGame.game (N+1) c P eta heta0 heta1 U
  let xi := (1-eta)/2
  have hxi : 0 < xi := by dsimp only [xi]; linarith
  have hxi1 : xi < 1 := by dsimp only [xi]; linarith
  let C := contextPolicy (m := N+1) xi hxi hxi1 c
  have hgame : C.nativeGame Gamma U = Gamma := rfl
  have hpMP : MeasurePreserving (fun omega : Sample (N+1) 2 unitInterval => omega.1.1)
      (sampleLaw Gamma) (userProfileLaw Gamma) :=
    (measurePreserving_fst (μ := userProfileLaw Gamma)
      (ν := Measure.pi (fun _ : Fin 2 => Gamma.seedLaw))).comp
      (measurePreserving_fst (μ := backgroundLaw Gamma) (ν := permLaw 2))
  filter_upwards [hpMP.quasiMeasurePreserving.ae hprofiles] with omega hp
  intro i act hbd hpositive
  let full := broadcastAction act
  have hfull : 0 < (focalCount Gamma i full omega).val :=
    hpositive.trans_le (focalCount_le_broadcast Gamma i act omega)
  let z := Function.update omega.1.1 i ((0,full),omega.2)
  have hguard := inserted_low_guard hdU omega.1.1 hp i 0 full rfl hbd omega.2
  have hz : z ∈ classifiedProfiles (N+1) U := fun k => (hguard k).1
  have hcpositive : 0 < inclusionCount (drawsRealization z) Gamma.policy omega.1.2 i := by
    rw [← focalCount_eq_inserted_count Gamma i 0 full omega.1.1 omega.1.2 omega.2]
    exact hfull
  rw [← hgame] at hcpositive
  have hactive : ∀ k ∈ upperSet d (actualContext U z).1,
      d < (1-xi)*entryBid ((actualContext U z).1 k) := by
    have hcoeff : 1-xi = (1+eta)/2 := by dsimp only [xi]; ring
    rw [hcoeff]
    exact active_order_of_profile_guard z hguard
  have hu := native_focal_success_implies_higherUnderflow xi hxi hxi1 c Gamma hd hdU z hz i
    (by simpa only [z, Function.update_self, full, broadcastAction] using hbd)
    hactive omega.1.2 hcpositive
  have hr : collapsedDeletedRow d U z i = collapsedDeletedRow d U omega.1.1 i := by
    funext j
    simp only [collapsedDeletedRow, z, Function.update_of_ne (Fin.succAbove_ne i j)]
  simpa only [hr] using hu

theorem native_success_le_underflow_of_guard {N c : ℕ} {d U eta : ℝ}
    (P : ProbabilityMeasure (ℝ × JointAction 2)) (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (hd : 0 ≤ d) (hdU : d ≤ U)
    (hprofiles : ∀ᵐprofile ∂userProfileLaw (PopulationGame.game (N+1) c P eta heta0 heta1 U),
      ∀ k, lowActionGuard d U ((1+eta)/2) (profile k).1.2)
    (i : Fin (N+1)) (row : UserProfile (N+1) 2 → Fin N → RowRival)
    (hrow : Measurable row) (hrowdef : ∀ profile, row profile = collapsedDeletedRow d U profile i)
    (nu : Measure (Fin N → RowRival))
    (hlaw : (userProfileLaw (PopulationGame.game (N+1) c P eta heta0 heta1 U)).map row = nu)
    (act : JointAction 2) (hbd : act.bid ≤ d) :
    let Gamma := PopulationGame.game (N+1) c P eta heta0 heta1 U
    ((problem Gamma i).outcome act).success ≤ nu.real (rowHigherUnderflow c) := by
  dsimp only
  let Gamma := PopulationGame.game (N+1) c P eta heta0 heta1 U
  let E : Set (Sample (N+1) 2 unitInterval) := {omega | row omega.1.1 ∈ rowHigherUnderflow c}
  have hE : MeasurableSet E := (measurableSet_rowHigherUnderflow c).preimage
    (hrow.comp measurable_fst.fst)
  have hpMP : MeasurePreserving (fun omega : Sample (N+1) 2 unitInterval => omega.1.1)
      (sampleLaw Gamma) (userProfileLaw Gamma) :=
    (measurePreserving_fst (μ := userProfileLaw Gamma)
      (ν := Measure.pi (fun _ : Fin 2 => Gamma.seedLaw))).comp
      (measurePreserving_fst (μ := backgroundLaw Gamma) (ν := permLaw 2))
  have hcommon := native_higherUnderflow_common_conull P heta0 heta1 hd hdU hprofiles
  rw [problem_outcome, CountLaw.success, CountLaw.expect_ofMeasure]
  have hi := CountLaw.integrable_comp (sampleLaw Gamma) (focalCount Gamma i act)
    (measurable_focalCount Gamma i act) (fun r : Fin 3 => successIndicator r.val)
  have hbound : (∫ omega, successIndicator (focalCount Gamma i act omega).val ∂sampleLaw Gamma) ≤
      ∫ omega, E.indicator (fun _ => (1 : ℝ)) omega ∂sampleLaw Gamma := by
    apply integral_mono_ae hi ((integrable_const (1 : ℝ)).indicator hE)
    filter_upwards [hcommon] with omega hpoint
    by_cases hzero : (focalCount Gamma i act omega).val = 0
    · rw [successIndicator, if_pos hzero]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) omega
    · have hu := hpoint i act hbd (Nat.pos_of_ne_zero hzero)
      have he : omega ∈ E := by
        change HigherUnderflow c (fun j => (row omega.1.1 j).1)
        rw [hrowdef]
        exact hu
      simp only [successIndicator, if_neg hzero, Set.indicator_of_mem he, le_refl]
  have hind := integral_indicator_one (μ := sampleLaw Gamma) hE
  have hone : (1 : Sample (N+1) 2 unitInterval → ℝ) = (fun _ => 1) := rfl
  rw [hone] at hind
  rw [hind] at hbound
  have hmap : (sampleLaw Gamma).map
      (row ∘ (fun omega : Sample (N+1) 2 unitInterval => omega.1.1)) = nu := by
    rw [← Measure.map_map hrow hpMP.measurable, hpMP.map_eq, hlaw]
  have hm := Measure.map_apply (μ := sampleLaw Gamma) (hrow.comp hpMP.measurable)
    (measurableSet_rowHigherUnderflow c)
  rw [hmap] at hm
  have heq : (sampleLaw Gamma).real E = nu.real (rowHigherUnderflow c) :=
    congrArg ENNReal.toReal hm.symm
  exact hbound.trans_eq heq

theorem rowHigherUnderflow_probability
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (G : Measure ℝ) [IsProbabilityMeasure G] (N c : ℕ) :
    (Measure.pi (fun _ : Fin N => rivalLaw s a h G)).real (rowHigherUnderflow c) =
      (CommonList.iid (categoryLaw s a h hs ha hh hsum G) N).prob (HigherUnderflow c) := by
  letI := rivalLaw_isProbability s a h hs ha hh hsum G
  have hcat := FiniteLaw.ofMeasure_pi_eq_iid (rivalLaw s a h G) N (fun _ => Prod.fst)
    (fun _ => measurable_fst) (categoryLaw s a h hs ha hh hsum G) (fun _ => rfl)
  rw [FiniteLaw.prob_eq_expect, ← hcat, FiniteLaw.expect_ofMeasure]
  simpa only [rowHigherUnderflow, Set.indicator, Set.mem_setOf_eq, Pi.one_apply] using
    (integral_indicator_one (μ := Measure.pi (fun _ : Fin N => rivalLaw s a h G))
      (measurableSet_rowHigherUnderflow (N := N) c)).symm

theorem population_low_success_bound {N c : ℕ} {d U eta : ℝ}
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
    (i : Fin (N+1)) (act : JointAction 2) (hbd : act.bid ≤ d) :
    let P := populationLaw s a h hs ha hh hsum (lowJoint mu pi) PA PH
    let Gamma := PopulationGame.game (N+1) c P eta heta0 heta1 U
    ((problem Gamma i).outcome act).success ≤
      (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob (HigherUnderflow c) := by
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
  have hb := native_success_le_underflow_of_guard P heta0 heta1 hd hdU hprofiles
    i row hrow (fun _ => rfl) _ hlaw act hbd
  rw [rowHigherUnderflow_probability s a h hs ha hh hsum (realLowBidLaw pi.1 : Measure ℝ) N c,
    categoryLaw_eq_low_law s a h hs ha hh hsum (realLowBidLaw pi.1 : Measure ℝ) Gref] at hb
  exact hb

theorem copied_low_success_bound {N c : ℕ} {d U eta : ℝ}
    {Seed : Type*} [MeasurableSpace Seed]
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
    (Gamma : FiniteGame (N+1) 2 c Seed)
    (copy : LowCountReproduction Gamma
      (PopulationGame.game (N+1) c
        (populationLaw s a h hs ha hh hsum (lowJoint mu pi) PA PH) eta heta0 heta1 U) d)
    (i : Fin (N+1)) (act : JointAction 2) (hbd : act.bid ≤ d) :
    ((problem Gamma i).outcome act).success ≤
      (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob (HigherUnderflow c) := by
  rw [copy.outcome_eq i act hbd]
  exact population_low_success_bound hd hdU s a h hs ha hh hsum Gref mu pi PA PH
    heta0 heta1 hactive hupper i act hbd

section FixedValue
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma prob_ne_zero_eq_success (mu : CountLaw n) :
    mu.prob (fun r => r ≠ 0) = mu.success := by
  rw [FiniteLaw.prob_eq_expect]
  apply mu.expect_congr
  intro r
  by_cases hz : r = 0
  · subst r
    simp [successIndicator]
  · have hv : r.val ≠ 0 := fun h => hz (Fin.ext h)
    simp only [hz, ne_eq, not_false_eq_true, if_true, successIndicator, if_neg hv]

theorem mixed_low_success_bound (Gamma : FiniteGame m 2 c Seed) (i : Fin m)
    (nu : Measure (JointAction 2)) [IsProbabilityMeasure nu] (d epsilon : ℝ)
    (hsupport : ∀ᵐact ∂nu, act.bid ≤ d)
    (hbound : ∀ act : JointAction 2, act.bid ≤ d →
      ((problem Gamma i).outcome act).success ≤ epsilon) :
    (mixedCountLaw Gamma i nu).success ≤ epsilon := by
  rw [← prob_ne_zero_eq_success]
  apply mixedCountLaw_prob_le_of_ae Gamma i nu (fun r => r ≠ 0) epsilon
  filter_upwards [hsupport] with act ha
  rw [prob_ne_zero_eq_success]
  exact hbound act ha

theorem conditional_low_success_bound (Gamma : FiniteGame m 2 c Seed) (hm : 0 < m)
    (v d epsilon : ℝ) (hsupport : ∀ᵐact ∂Gamma.σ v, act.bid ≤ d)
    (hbound : ∀ i : Fin m, ∀ act : JointAction 2, act.bid ≤ d →
      ((problem Gamma i).outcome act).success ≤ epsilon) :
    (conditionalTypeCountLaw Gamma hm v).success ≤ epsilon := by
  have hi (i : Fin m) : (typeOutcome Gamma i v).success ≤ epsilon :=
    mixed_low_success_bound Gamma i (Gamma.σ v) d epsilon hsupport (hbound i)
  change (FiniteLaw.uniformAverage hm (fun i => typeOutcome Gamma i v)).expect
    (fun r => successIndicator r.val) ≤ epsilon
  rw [FiniteLaw.expect_uniformAverage]
  apply (div_le_iff₀ (Nat.cast_pos.mpr hm : (0 : ℝ) < m)).mpr
  calc
    (∑ i, (typeOutcome Gamma i v).success) ≤ ∑ _i : Fin m, epsilon :=
      Finset.sum_le_sum (fun i _ => hi i)
    _ = epsilon * m := by simp [mul_comm]

theorem lowBroadcast_map_support {d : ℝ} (nu : Measure (LowValue d)) :
    ∀ᵐact ∂nu.map lowBroadcast, act.bid ≤ d := by
  apply (ae_map_iff (measurable_lowBroadcast d).aemeasurable
    (measurableSet_le (measurable_bid 2) measurable_const)).mpr
  exact ae_of_all _ (fun b => b.property.2)

theorem actual_low_version_support {d : ℝ} (Gamma : FiniteGame m 2 c Seed)
    (v : ℝ) (nu : Measure (LowValue d))
    (hversion : Gamma.σ v = nu.map lowBroadcast) :
    ∀ᵐact ∂Gamma.σ v, act.bid ≤ d := by
  rw [hversion]
  exact lowBroadcast_map_support nu

end FixedValue

structure ReferenceRows (C : CategoryRows) (d eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (c : ℕ → ℕ) (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] where
  U : ℕ → ℝ
  low : ℕ → Law (A := LowValue d) mu
  active : ℕ → ProbabilityMeasure (ℝ × JointAction 2)
  privateLaw : ℕ → ProbabilityMeasure (ℝ × JointAction 2)

namespace ReferenceRows
variable {C : CategoryRows} {d eta : ℝ} {heta0 : 0 ≤ eta} {heta1 : eta < 1}
  {c : ℕ → ℕ} {mu : Measure (LowValue d)} [IsProbabilityMeasure mu]

def game (R : ReferenceRows C d eta heta0 heta1 c mu) (m : ℕ) :
    FiniteGame (m+1) 2 (c (m+1)) unitInterval :=
  PopulationGame.game (m+1) (c (m+1))
    (populationLaw (C.s (m+1)) (C.a (m+1)) (C.h (m+1))
      (C.s_nonneg (m+1)) (C.a_nonneg (m+1)) (C.h_nonneg (m+1)) (C.total (m+1))
      (lowJoint mu (R.low m)) (R.active m) (R.privateLaw m)) eta heta0 heta1 (R.U m)

def Guard (R : ReferenceRows C d eta heta0 heta1 c mu) (m : ℕ) : Prop :=
  d ≤ R.U m ∧
  (∀ᵐx ∂(R.active m : Measure (ℝ × JointAction 2)),
    d < ((1+eta)/2)*x.2.bid ∧ x.2.bid ≤ R.U m ∧ x.2.routeCount=2) ∧
  (∀ᵐx ∂(R.privateLaw m : Measure (ℝ × JointAction 2)),
    R.U m < x.2.bid ∧ x.2.routeCount=1)

theorem success_bound (R : ReferenceRows C d eta heta0 heta1 c mu) (hd : 0 ≤ d)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref] (m : ℕ) (hguard : R.Guard m)
    (i : Fin (m+1)) (act : JointAction 2) (hbd : act.bid ≤ d) :
    ((problem (R.game m) i).outcome act).success ≤
      (CommonList.iid (C.law Gref (m+1)) m).prob (HigherUnderflow (c (m+1))) :=
  population_low_success_bound hd hguard.1
    (C.s (m+1)) (C.a (m+1)) (C.h (m+1))
    (C.s_nonneg (m+1)) (C.a_nonneg (m+1)) (C.h_nonneg (m+1)) (C.total (m+1))
    Gref mu (R.low m) (R.active m) (R.privateLaw m) heta0 heta1 hguard.2.1 hguard.2.2 i act hbd

theorem uniform_success_tendsto (R : ReferenceRows C d eta heta0 heta1 c mu) (hd : 0 ≤ d)
    {a h : ℝ} (ha : Tendsto C.a atTop (𝓝 a)) (hh : Tendsto C.h atTop (𝓝 h))
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref] (rho : ℝ)
    (hc : Tendsto (fun m => (c m : ℝ)/(m : ℝ)) atTop (𝓝 rho)) (hrank : rho < a+h/2)
    (hguards : ∀ᶠm in atTop, R.Guard m) :
    ∀ epsilon > 0, ∀ᶠm in atTop, ∀ i : Fin (m+1), ∀ act : JointAction 2,
      act.bid ≤ d → ((problem (R.game m) i).outcome act).success < epsilon := by
  have ht := (higherUnderflow_tendsto_zero C ha hh Gref c rho hc hrank).comp
    (tendsto_add_atTop_nat 1)
  have ht' : Tendsto (fun m => (CommonList.iid (C.law Gref (m+1)) m).prob
      (HigherUnderflow (c (m+1)))) atTop (𝓝 0) := by
    convert! ht using 1
  intro epsilon hepsilon
  filter_upwards [ht'.eventually_lt_const hepsilon, hguards] with m hm hguard
  intro i act hbd
  exact (R.success_bound hd Gref m hguard i act hbd).trans_lt hm

end ReferenceRows

theorem mixed_low_test_tendsto {Seed : Type*} [MeasurableSpace Seed]
    (M c : ℕ → ℕ) (Gamma : (m : ℕ) → FiniteGame (M m) 2 (c m) Seed)
    (i : (m : ℕ) → Fin (M m)) (nu : ℕ → Measure (JointAction 2))
    [∀ m, IsProbabilityMeasure (nu m)] (d : ℝ)
    (hsupport : ∀ᶠm in atTop, ∀ᵐact ∂nu m, act.bid ≤ d)
    (hlimit : ∀ epsilon > 0, ∀ᶠm in atTop, ∀ i : Fin (M m), ∀ act : JointAction 2,
      act.bid ≤ d → ((problem (Gamma m) i).outcome act).success < epsilon)
    (f : Fin 3 → ℝ) :
    Tendsto (fun m => (mixedCountLaw (Gamma m) (i m) (nu m)).expect f) atTop (𝓝 (f 0)) := by
  apply FiniteLaw.tendsto_expect_of_prob_ne _ 0 _ f
  simp only [prob_ne_zero_eq_success]
  apply tendsto_order.mpr
  constructor
  · intro epsilon hepsilon
    exact Eventually.of_forall fun m => hepsilon.trans_le (mixedCountLaw (Gamma m) (i m) (nu m)).success_nonneg
  · intro epsilon hepsilon
    filter_upwards [hlimit (epsilon/2) (half_pos hepsilon), hsupport] with m hm hs
    exact (mixed_low_success_bound (Gamma m) (i m) (nu m) d (epsilon/2) hs
      (fun act ha => (hm (i m) act ha).le)).trans_lt (half_lt_self hepsilon)

theorem conditional_low_test_tendsto {Seed : Type*} [MeasurableSpace Seed]
    (M c : ℕ → ℕ) (Gamma : (m : ℕ) → FiniteGame (M m) 2 (c m) Seed)
    (hM : ∀ m, 0 < M m) (v d : ℝ)
    (hsupport : ∀ᶠm in atTop, ∀ᵐact ∂(Gamma m).σ v, act.bid ≤ d)
    (hlimit : ∀ epsilon > 0, ∀ᶠm in atTop, ∀ i : Fin (M m), ∀ act : JointAction 2,
      act.bid ≤ d → ((problem (Gamma m) i).outcome act).success < epsilon)
    (f : Fin 3 → ℝ) :
    Tendsto (fun m => (conditionalTypeCountLaw (Gamma m) (hM m) v).expect f)
      atTop (𝓝 (f 0)) := by
  apply FiniteLaw.tendsto_expect_of_prob_ne _ 0 _ f
  simp only [prob_ne_zero_eq_success]
  apply tendsto_order.mpr
  constructor
  · intro epsilon hepsilon
    exact Eventually.of_forall fun m => hepsilon.trans_le
      (conditionalTypeCountLaw (Gamma m) (hM m) v).success_nonneg
  · intro epsilon hepsilon
    filter_upwards [hlimit (epsilon/2) (half_pos hepsilon), hsupport] with m hm hs
    exact (conditional_low_success_bound (Gamma m) (hM m) v d (epsilon/2) hs
      (fun i act ha => (hm i act ha).le)).trans_lt (half_lt_self hepsilon)

theorem all_fixed_low_count_laws {Seed : Type*} [MeasurableSpace Seed]
    (C : CategoryRows) (d eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (c : ℕ → ℕ) (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (R : ReferenceRows C d eta heta0 heta1 c mu) (hd : 0 ≤ d)
    {a h : ℝ} (ha : Tendsto C.a atTop (𝓝 a)) (hh : Tendsto C.h atTop (𝓝 h))
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref] (rho : ℝ)
    (hc : Tendsto (fun m => (c m : ℝ)/(m : ℝ)) atTop (𝓝 rho)) (hrank : rho < a+h/2)
    (hguards : ∀ᶠm in atTop, R.Guard m)
    (Gamma : (m : ℕ) → FiniteGame (m+1) 2 (c (m+1)) Seed)
    (hcopy : ∀ᶠm in atTop, Nonempty (LowCountReproduction (Gamma m) (R.game m) d))
    (sigmaLow : ℕ → Kernel (LowValue d) (LowValue d))
    (hversion : ∀ w : LowValue d, ∀ᶠm in atTop,
      (Gamma m).σ w.1 = (sigmaLow m w).map lowBroadcast) :
    ∀ w : LowValue d, ∀ f : Fin 3 → ℝ,
      Tendsto (fun m => (conditionalTypeCountLaw (Gamma m) (Nat.succ_pos m) w.1).expect f)
        atTop (𝓝 (f 0)) := by
  have href := R.uniform_success_tendsto hd ha hh Gref rho hc hrank hguards
  have hlimit : ∀ epsilon > 0, ∀ᶠm in atTop, ∀ i : Fin (m+1), ∀ act : JointAction 2,
      act.bid ≤ d → ((problem (Gamma m) i).outcome act).success < epsilon := by
    intro epsilon hepsilon
    filter_upwards [href epsilon hepsilon, hcopy] with m hm hcopied
    obtain ⟨copy⟩ := hcopied
    intro i act hbd
    rw [copy.outcome_eq i act hbd]
    exact hm i act hbd
  intro w f
  apply conditional_low_test_tendsto (fun m => m+1) (fun m => c (m+1)) Gamma
    (fun m => Nat.succ_pos m) w.1 d _ hlimit f
  filter_upwards [hversion w] with m hm
  exact actual_low_version_support (Gamma m) w.1 (sigmaLow m w) hm

end FCAppendix.Appendix08.LowCounts
