import FCAppendix.Affine.UniformFinite.Late.OnPathConditional
import FCAppendix.Affine.UniformFinite.NativeStrategyTraces

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game Bayes
open Uniform05
open scoped BigOperators

namespace Late.StrictOriginal
variable {i : Row} {M : ℕ} [NeZero M] {R : ℝ}

omit [NeZero M] in

theorem presentList_original (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R)
    (d : UserProfile M 2) (hd : d ∈ Strict.strongProfiles M (cap i) R)
    (s : Fin 2 → unitInterval) (a : Fin M) (own : Bid i) (j : Fin 2) :
    Strict.OriginalList (cap i) R (presentList (d,s) a own j) := by
  let ω : Sample M 2 unitInterval := ((d,s), Equiv.refl (Fin 2))
  have hobs : observe (deviated a (Hybrid.lowBroadcast own) ω) j =
      presentList (d,s) a own j :=
    observe_deviated_of_mem a (Hybrid.lowBroadcast own) ω j (by
      change j ∈ firstK ω.2 2
      rw [Hybrid.firstK_full_two]
      simp)
  rw [← hobs]
  exact original_deviation_list E H a (Hybrid.lowBroadcast own) own.property.2 ω hd j

theorem accepts_below_cap_pointwise (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i < R)
    (d : UserProfile M 2) (hd : d ∈ Strict.strongProfiles M (cap i) R)
    (s : Fin 2 → unitInterval) (a : Fin M) (own : Bid i) (j : Fin 2) :
    Accepts (game E H) a own j (d,s) ↔
      Accepts (OriginalPopulation.game E H) a own j (d,s) := by
  change (a ∈ ((game E H).policy j (presentList (d,s) a own j) (s j)).val) ↔ _
  rw [policy_on_original_list E H hR j (presentList (d,s) a own j)
    (presentList_original E H d hd s a own j) (s j)]

theorem background_original_support (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) :
    ∀ᵐω ∂backgroundLaw (game E H), ω.1 ∈ Strict.strongProfiles M (cap i) R :=
  (measurePreserving_fst (μ := userProfileLaw (game E H))
    (ν := Measure.pi (fun _ : Fin 2 => (game E H).seedLaw))).quasiMeasurePreserving.ae
      (game_profile_support E H)

theorem trace_below_cap_common (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i < R) :
    ∀ᵐω ∂backgroundLaw (game E H), ∀a : Fin M, ∀own : Bid i,
      NativeRoutes.namedTrace (game E H) a own ω =
        NativeRoutes.namedTrace (OriginalPopulation.game E H) a own ω := by
  filter_upwards [background_original_support E H] with ω hω
  intro a own
  simp only [NativeRoutes.namedTrace,
    accepts_below_cap_pointwise E H hR ω.1 hω ω.2 a own 0,
    accepts_below_cap_pointwise E H hR ω.1 hω ω.2 a own 1]

theorem traceOutcome_below_cap (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i < R)
    (a : Fin M) (own : Bid i) :
    NativeRoutes.traceOutcome (game E H) a own =
      NativeRoutes.traceOutcome (OriginalPopulation.game E H) a own := by
  apply FiniteLaw.ext_expect
  intro f
  rw [NativeRoutes.traceOutcome, FiniteLaw.expect_ofMeasure,
    NativeRoutes.traceOutcome, FiniteLaw.expect_ofMeasure]
  have hμ : backgroundLaw (OriginalPopulation.game E H) = backgroundLaw (game E H) := rfl
  rw [hμ]
  apply integral_congr_ae
  filter_upwards [trace_below_cap_common E H hR] with ω hω
  rw [hω a own]

theorem game_traceOutcome (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i < R)
    (a : Fin M) (own : Bid i) :
    NativeRoutes.traceOutcome (game E H) a own = NativeProfile.indexedTraceLaw i E.law a own := by
  rw [traceOutcome_below_cap E H hR a own, OriginalPopulation.game_trace_outcome E H hR a own]

theorem game_namedOutcome (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i < R)
    (a : Fin M) (own : Bid i) (j : Fin 2) :
    NativeRoutes.namedOutcome (game E H) a own j =
      NativeProfile.indexedRecipientLaw i E.law a own j := by
  rw [← NativeRoutes.traceOutcome_named, game_traceOutcome E H hR a own]
  rfl

theorem game_typeTraceLaw (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i < R)
    (a : Fin M) (v : Value i) :
    NativeRoutes.typeTraceLaw (game E H) a v = OriginalPopulation.indexedTypeTraceLaw E a v := by
  apply FiniteLaw.ext_expect
  intro f
  rw [NativeRoutes.typeTraceLaw_expect, game_lower_kernel]
  have hf : Measurable (fun act : JointAction 2 =>
      (NativeRoutes.traceOutcome (game E H) a act.bid).expect f) :=
    (FiniteLaw.measurable_expect (NativeRoutes.traceOutcome (game E H) a)
      (NativeRoutes.measurable_traceOutcome_mass (game E H) a) f).comp (measurable_bid 2)
  have hm : Measurable (fun q : unitInterval=>OriginalPopulation.lowerAction i (v,q)) := by
    convert! (OriginalPopulation.measurable_lowerAction i).comp
      (measurable_const.prodMk measurable_id) using 1
  rw [integral_map (μ:=E.sigma v) hm.aemeasurable hf.aestronglyMeasurable,
    OriginalPopulation.indexedTypeTraceLaw, FiniteLaw.expect_average]
  apply integral_congr_ae
  exact ae_of_all _ (fun q => by
    change (NativeRoutes.traceOutcome (game E H) a (baseBid i (v,q))).expect f = _
    rw [game_traceOutcome E H hR a (baseBid i (v,q))])

theorem game_actualTypeTraceLaw (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i < R)
    (a : Fin M) (v : Value i) :
    NativeRoutes.actualTypeTraceLaw (game E H) a v =
      OriginalPopulation.indexedTypeTraceLaw E a v := by
  apply FiniteLaw.ext_expect
  intro f
  rw [NativeRoutes.actualTypeTraceLaw, FiniteLaw.expect_average, game_lower_kernel]
  have hf : Measurable (fun act : JointAction 2 =>
      (NativeRoutes.actionTraceOutcome (game E H) a act).expect f) :=
    FiniteLaw.measurable_expect (NativeRoutes.actionTraceOutcome (game E H) a)
      (NativeRoutes.measurable_actionTraceOutcome_mass (game E H) a) f
  have hm : Measurable (fun q : unitInterval=>OriginalPopulation.lowerAction i (v,q)) := by
    convert! (OriginalPopulation.measurable_lowerAction i).comp
      (measurable_const.prodMk measurable_id) using 1
  rw [integral_map (μ:=E.sigma v) hm.aemeasurable hf.aestronglyMeasurable,
    OriginalPopulation.indexedTypeTraceLaw, FiniteLaw.expect_average]
  apply integral_congr_ae
  apply ae_of_all
  intro q
  change (NativeRoutes.actionTraceOutcome (game E H) a
    (OriginalPopulation.lowerAction i (v,q))).expect f=_
  rw [NativeRoutes.actionTraceOutcome_broadcast (game E H) a
    (OriginalPopulation.lowerAction i (v,q)) rfl]
  change (NativeRoutes.traceOutcome (game E H) a (baseBid i (v,q))).expect f = _
  rw [game_traceOutcome E H hR a (baseBid i (v,q))]

theorem game_actualTypeTraceLaw_eq_broadcast (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i < R)
    (a : Fin M) (v : Value i) :
    NativeRoutes.actualTypeTraceLaw (game E H) a v =
      NativeRoutes.typeTraceLaw (game E H) a v := by
  rw [game_actualTypeTraceLaw E H hR a v, game_typeTraceLaw E H hR a v]

theorem game_actualTypeRecipientLaw (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i < R)
    (a : Fin M) (j : Fin 2) (v : Value i) :
    NativeRoutes.actualTypeRecipientLaw (game E H) a j v =
      (OriginalPopulation.indexedTypeTraceLaw E a v).map (NativeProfile.recipientCount j) := by
  rw [NativeRoutes.actualTypeRecipientLaw, game_actualTypeTraceLaw E H hR a v]

theorem game_typeTraceLaw_count (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i < R)
    (a : Fin M) (v : Value i) :
    (NativeRoutes.typeTraceLaw (game E H) a v).map NativeCounts.traceCount =
      typeOutcome (game E H) a v := by
  rw [game_typeTraceLaw E H hR a v, OriginalPopulation.indexedTypeTraceLaw_count,
    game_typeOutcome E H hR a v]

theorem game_typeRecipientLaw (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i < R)
    (a : Fin M) (j : Fin 2) (v : Value i) :
    NativeRoutes.typeRecipientLaw (game E H) a j v =
      (OriginalPopulation.indexedTypeTraceLaw E a v).map (NativeProfile.recipientCount j) := by
  rw [NativeRoutes.typeRecipientLaw, game_typeTraceLaw E H hR a v]

theorem game_typeTraceLaw_original_integral (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i < R)
    (a : Fin M) (f : Bool × Bool → ℝ) :
    (∫v, (NativeRoutes.typeTraceLaw (game E H) a v).expect f ∂lowerMeasure i) =
      ∫p, (NativeProfile.indexedTraceLaw i E.law a (baseBid i p)).expect f
        ∂(E.pi.1 : Measure (Value i × unitInterval)) := by
  simp_rw [game_typeTraceLaw E H hR]
  exact OriginalPopulation.indexedTypeTraceLaw_original_integral E a f

end Late.StrictOriginal
end FCAppendix.Affine.UniformFinite
