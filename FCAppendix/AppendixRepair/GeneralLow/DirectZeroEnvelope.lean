import FCAppendix.AppendixRepair.GeneralLow.DirectContextPayoff
import FCAppendix.Affine.Hybrid.NativeLowBounds

set_option maxHeartbeats 1600000
noncomputable section
namespace FCAppendix.Appendix08.GeneralLow.DirectZeroEnvelope
open MeasureTheory ProbabilityTheory Set Game Bayes
open Affine Affine.LowBody Affine.Hybrid Affine.Hybrid.NativeContinuation
open FCAppendix.AppendixRepair.GeneralLow
open DirectContextPayoff
open scoped BigOperators

attribute [local irreducible] Hybrid.NativeEqual.sample

variable {m N c : ℕ}

theorem low_data_same_rivals {d U : ℝ} (hdU : d ≤ U)
    (z z' : UserProfile m 2) (hz : z ∈ classifiedProfiles m U)
    (hz' : z' ∈ classifiedProfiles m U) (i : Fin m)
    (hf : (z i).1.2.bid ≤ d) (hf' : (z' i).1.2.bid ≤ d)
    (hother : ∀ k, k ≠ i → z' k = z k) (c : ℕ) :
    lowList d U z' = Function.update (lowList d U z) i (some (z' i).1.2.bid) ∧
      ∀ j, budget d U c z' j = budget d U c z j := by
  classical
  have hx := actualContext_same_rivals U z z' hz hz' i
    (hf.trans hdU) (hf'.trans hdU) hother
  have hb : (actualContext U z).1 i = some (z i).1.2.bid := by
    change broadcastPart U (observe (drawsRealization z) 0) i = _
    rw [broadcastPart_observe z hz 0]
    simp only [if_pos (hf.trans hdU)]
  have hupper : upperSet d (actualContext U z').1 =
      upperSet d (actualContext U z).1 := by
    rw [hx]
    ext k
    by_cases hk : k = i
    · subst k
      simp [upperSet, contextAtBid, hb, TaggedLocal.tag, hf, hf']
    · simp only [upperSet, Finset.mem_filter, Finset.mem_univ, true_and,
        contextAtBid, Function.update_of_ne hk]
  have hnot : i ∉ upperSet d (actualContext U z).1 := by
    simp [upperSet, hb, TaggedLocal.tag, hf]
  have hl : lowList d U z' =
      Function.update (lowList d U z) i (some (z' i).1.2.bid) := by
    unfold lowList
    rw [hupper, hx]
    funext k
    by_cases hk : k = i
    · subst k
      simp [eraseActiveList, contextAtBid, hnot]
    · simp [eraseActiveList, contextAtBid, Function.update_of_ne hk]
  refine ⟨hl, ?_⟩
  intro j
  have hnon : lowList d U z i ≠ none := by
    rw [lowList_focal hdU z hz i hf]
    simp
  have hvis : ExactLow.visible (lowList d U z') = ExactLow.visible (lowList d U z) := by
    rw [hl]
    exact congrArg PureTemplate.support
      (ExactLow.template_update (lowList d U z) i hnon (z' i).1.2.bid 0 0)
  unfold budget
  rw [hvis, hupper, hx]
  rfl

theorem actual_profile_zero_payoff_le_positive
    (ξ : ℝ) (hξ : 0 < ξ) (hξh : ξ ≤ 1 / 2) (c : ℕ)
    {d U : ℝ} (hdU : d ≤ U) (z z' : UserProfile m 2)
    (hz : z ∈ classifiedProfiles m U) (hz' : z' ∈ classifiedProfiles m U)
    (i : Fin m) (hf : (z i).1.2.bid ≤ d) (hf' : (z' i).1.2.bid ≤ d)
    (hother : ∀ k, k ≠ i → z' k = z k) (hzbid : (z i).1.2.bid = 0)
    (hy : 0 < (z' i).1.2.bid) (w : ℝ) (hw : 0 ≤ w) :
    let hξ1 : ξ < 1 := by linarith
    ExactLow.seedAveragePayoff ξ hξ hξ1 (lowList d U z)
      (budget d U c z 0) (budget d U c z 1) i w ≤
      ExactLow.seedAveragePayoff ξ hξ hξ1 (lowList d U z')
        (budget d U c z' 0) (budget d U c z' 1) i w + 2 * (z' i).1.2.bid := by
  dsimp only
  have h0 : lowList d U z i = some 0 := by
    rw [lowList_focal hdU z hz i hf, hzbid]
  have hd := low_data_same_rivals hdU z z' hz hz' i hf hf' hother c
  rw [hd.1, hd.2 0, hd.2 1]
  exact ExactLow.zero_payoff_le_positive ξ hξ hξh (lowList d U z)
    (budget d U c z 0) (budget d U c z 1) i h0 w hw (z' i).1.2.bid hy

theorem zero_envelope_of_guard (P : ProbabilityMeasure (ℝ × JointAction 2))
    {η d U : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) (hdU : d ≤ U)
    (HC : HigherPolicy.HigherSelector (m := N + 1)
      (ReferenceContext.classifier d U) c unitInterval)
    (hprofiles : ∀ᵐ profile ∂userProfileLaw
      (DirectGame.game (N + 1) c P η hη0 hη1 (ReferenceContext.classifier d U) d HC),
      ∀ k, lowActionGuard d U ((1 + η) / 2) (profile k).1.2)
    (i : Fin (N + 1)) (w : ℝ) (hw : 0 ≤ w) (act : JointAction 2)
    (hk : act.routeCount = 2) (hzero : act.bid = 0)
    (y : ℝ) (hy : 0 < y) (hyd : y ≤ d) :
    let Γ := DirectGame.game (N + 1) c P η hη0 hη1
      (ReferenceContext.classifier d U) d HC
    (problem Γ i).payoff w act ≤
      (problem Γ i).payoff w (NativeLowIncentives.broadcast y hy.le) + 2 * y := by
  dsimp only
  let Γ := DirectGame.game (N + 1) c P η hη0 hη1
    (ReferenceContext.classifier d U) d HC
  let ay := NativeLowIncentives.broadcast y hy.le
  let ξ := (1 - η) / 2
  have hξ : 0 < ξ := by dsimp [ξ]; linarith
  have hξh : ξ ≤ 1 / 2 := by dsimp [ξ]; linarith
  have h0d : act.bid ≤ d := by rw [hzero]; exact hy.le.trans hyd
  rw [broadcast_payoff_eq_profile_seed_integral Γ i w act hk,
    broadcast_payoff_eq_profile_seed_integral Γ i w ay rfl]
  have hi0 := integrable_native_seed_average Γ i w act
  have hiy := integrable_native_seed_average Γ i w ay
  have hadd := integral_add hiy (integrable_const (2 * y))
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hadd
  rw [← hadd]
  apply integral_mono_ae hi0 (hiy.add (integrable_const (2 * y)))
  filter_upwards [hprofiles] with profile hp
  let z0 := Function.update profile i ((w, act), Equiv.refl (Fin 2))
  let zy := Function.update profile i ((w, ay), Equiv.refl (Fin 2))
  have hz0guard := inserted_low_guard hdU profile hp i w act hk h0d (Equiv.refl (Fin 2))
  have hzyguard := inserted_low_guard hdU profile hp i w ay rfl hyd (Equiv.refl (Fin 2))
  have hz0 : z0 ∈ classifiedProfiles (N + 1) U := fun k => (hz0guard k).1
  have hzy : zy ∈ classifiedProfiles (N + 1) U := fun k => (hzyguard k).1
  dsimp only [Pi.add_apply]
  rw [show Γ.seedLaw = (volume : Measure unitInterval) from rfl]
  rw [DirectContextPayoff.seed_average_payoff P η hη0 hη1 hdU HC i w act h0d profile
      (Equiv.refl (Fin 2)) hz0guard,
    DirectContextPayoff.seed_average_payoff P η hη0 hη1 hdU HC i w ay hyd profile
      (Equiv.refl (Fin 2)) hzyguard]
  have hh := actual_profile_zero_payoff_le_positive ξ hξ hξh c hdU z0 zy hz0 hzy i
    (by simpa only [z0, Function.update_self] using h0d)
    (by simpa only [zy, Function.update_self, ay, NativeLowIncentives.broadcast] using hyd)
    (fun k hk' => by simp only [z0, zy, Function.update_of_ne hk'])
    (by simpa only [z0, Function.update_self] using hzero)
    (by simpa only [zy, Function.update_self, ay, NativeLowIncentives.broadcast] using hy) w hw
  dsimp only at hh
  simpa only [zy, Function.update_self, ay, NativeLowIncentives.broadcast] using hh

end FCAppendix.Appendix08.GeneralLow.DirectZeroEnvelope
