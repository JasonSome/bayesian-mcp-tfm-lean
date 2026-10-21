import FCAppendix.Affine.UniformFinite.NativeNamedCounts

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game Bayes
open Uniform05
open scoped BigOperators

namespace NativeRoutes
variable {M c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem measurable_presentList_bid_joint (a : Fin M) (j : Fin 2) :
    Measurable (fun x : ℝ × Background M 2 Seed => presentList x.2 a x.1 j) := by
  apply measurable_pi_lambda
  intro k
  by_cases hk : k = a
  · subst k
    simp only [presentList_self]
    convert! (measurable_some.comp (measurable_fst : Measurable
        (Prod.fst : ℝ × Background M 2 Seed → ℝ))) using 1
  · have he : (fun x : ℝ × Background M 2 Seed => presentList x.2 a x.1 j k) =
        fun x => presentList x.2 a 0 j k := by
      funext x
      simp only [presentList, if_neg hk]
    rw [he]
    exact ((measurable_pi_apply k).comp (measurable_presentList a 0 j)).comp measurable_snd

theorem measurableSet_accepts_bid_joint (Γ : FiniteGame M 2 c Seed)
    (a : Fin M) (j : Fin 2) :
    MeasurableSet {x : ℝ × Background M 2 Seed | Accepts Γ a x.1 j x.2} := by
  have hseed : Measurable (fun x : ℝ × Background M 2 Seed => x.2.2 j) :=
    (measurable_pi_apply j).comp measurable_snd.snd
  exact ((Γ.policy_measurable j).comp
    ((measurable_presentList_bid_joint a j).prodMk hseed))
      (MeasurableSet.of_discrete : MeasurableSet {S : Finset (Fin M) | a ∈ S})

theorem measurable_namedTrace_bid_joint (Γ : FiniteGame M 2 c Seed) (a : Fin M) :
    Measurable (fun x : ℝ × Background M 2 Seed => namedTrace Γ a x.1 x.2) :=
  (Measurable.ite (measurableSet_accepts_bid_joint Γ a 0)
    measurable_const measurable_const).prodMk
    (Measurable.ite (measurableSet_accepts_bid_joint Γ a 1)
      measurable_const measurable_const)

theorem measurable_traceOutcome_mass (Γ : FiniteGame M 2 c Seed) (a : Fin M)
    (r : Bool × Bool) : Measurable (fun b : ℝ => (traceOutcome Γ a b).mass r) := by
  simp_rw [← FiniteLaw.expect_singleton, traceOutcome, FiniteLaw.expect_ofMeasure]
  convert! ((measurable_of_countable
    (fun x : Bool × Bool => if x = r then (1 : ℝ) else 0)).comp
      (measurable_namedTrace_bid_joint Γ a)).stronglyMeasurable.integral_prod_right'.measurable using 1
  infer_instance

def typeTraceLaw (Γ : FiniteGame M 2 c Seed) (a : Fin M) (v : ℝ) :
    FiniteLaw (Bool × Bool) :=
  FiniteLaw.average (Γ.σ v) (fun act => traceOutcome Γ a act.bid)
    (fun r => (measurable_traceOutcome_mass Γ a r).comp (measurable_bid 2))

theorem typeTraceLaw_expect (Γ : FiniteGame M 2 c Seed) (a : Fin M)
    (v : ℝ) (f : Bool × Bool → ℝ) :
    (typeTraceLaw Γ a v).expect f =
      ∫act, (traceOutcome Γ a act.bid).expect f ∂Γ.σ v :=
  FiniteLaw.expect_average _ _ _ _

def typeRecipientLaw (Γ : FiniteGame M 2 c Seed) (a : Fin M) (j : Fin 2)
    (v : ℝ) : CountLaw 2 := (typeTraceLaw Γ a v).map (NativeProfile.recipientCount j)

theorem traceOutcome_named (Γ : FiniteGame M 2 c Seed) (a : Fin M)
    (b : ℝ) (j : Fin 2) :
    (traceOutcome Γ a b).map (NativeProfile.recipientCount j) = namedOutcome Γ a b j := by
  apply FiniteLaw.ext_expect
  intro f
  rw [FiniteLaw.expect_map, traceOutcome, FiniteLaw.expect_ofMeasure, namedOutcome_expect]
  apply integral_congr_ae
  apply ae_of_all
  intro ω
  fin_cases j
  · by_cases h : Accepts Γ a b 0 ω <;>
      simp [namedTrace, NativeProfile.recipientCount, namedCount, h]
  · by_cases h : Accepts Γ a b 1 ω <;>
      simp [namedTrace, NativeProfile.recipientCount, namedCount, h]

theorem typeRecipientLaw_expect (Γ : FiniteGame M 2 c Seed) (a : Fin M)
    (j : Fin 2) (v : ℝ) (f : Fin 3 → ℝ) :
    (typeRecipientLaw Γ a j v).expect f =
      ∫act, (namedOutcome Γ a act.bid j).expect f ∂Γ.σ v := by
  rw [typeRecipientLaw, FiniteLaw.expect_map, typeTraceLaw_expect]
  apply integral_congr_ae
  exact ae_of_all _ (fun act => by
    change (traceOutcome Γ a act.bid).expect
      (fun r=>f (NativeProfile.recipientCount j r))=_
    rw [← FiniteLaw.expect_map, traceOutcome_named Γ a act.bid j])

def sampleTrace (Γ : FiniteGame M 2 c Seed) (a : Fin M) (act : JointAction 2)
    (ω : Sample M 2 Seed) : Bool × Bool :=
  (if a ∈ allocation (deviated a act ω) Γ.policy ω.1.2 0 then true else false,
    if a ∈ allocation (deviated a act ω) Γ.policy ω.1.2 1 then true else false)

theorem measurable_sampleTrace_joint (Γ : FiniteGame M 2 c Seed) (a : Fin M) :
    Measurable (fun p : JointAction 2 × Sample M 2 Seed => sampleTrace Γ a p.1 p.2) := by
  have hseed (j : Fin 2) : Measurable
      (fun p : JointAction 2 × Sample M 2 Seed => p.2.1.2 j) :=
    (measurable_pi_apply j).comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  have halloc (j : Fin 2) : Measurable
      (fun p : JointAction 2 × Sample M 2 Seed =>
        allocation (deviated a p.1 p.2) Γ.policy p.2.1.2 j) :=
    (Γ.policy_measurable j).comp ((measurable_observe_deviated_joint a j).prodMk (hseed j))
  exact (Measurable.ite
    ((halloc 0) (MeasurableSet.of_discrete : MeasurableSet {S : Finset (Fin M) | a ∈ S}))
    measurable_const measurable_const).prodMk
    (Measurable.ite
      ((halloc 1) (MeasurableSet.of_discrete : MeasurableSet {S : Finset (Fin M) | a ∈ S}))
      measurable_const measurable_const)

theorem measurable_sampleTrace (Γ : FiniteGame M 2 c Seed) (a : Fin M)
    (act : JointAction 2) : Measurable (sampleTrace Γ a act) := by
  convert! (measurable_sampleTrace_joint Γ a).comp
    (measurable_const.prodMk measurable_id) using 1

def actionTraceOutcome (Γ : FiniteGame M 2 c Seed) (a : Fin M)
    (act : JointAction 2) : FiniteLaw (Bool × Bool) :=
  FiniteLaw.ofMeasure (sampleLaw Γ) (sampleTrace Γ a act)
    (measurable_sampleTrace Γ a act)

theorem actionTraceOutcome_expect (Γ : FiniteGame M 2 c Seed) (a : Fin M)
    (act : JointAction 2) (f : Bool × Bool → ℝ) :
    (actionTraceOutcome Γ a act).expect f =
      ∫ω, f (sampleTrace Γ a act ω) ∂sampleLaw Γ :=
  FiniteLaw.expect_ofMeasure _ _ _ _

theorem measurable_actionTraceOutcome_mass (Γ : FiniteGame M 2 c Seed)
    (a : Fin M) (r : Bool × Bool) :
    Measurable (fun act : JointAction 2 => (actionTraceOutcome Γ a act).mass r) := by
  simp_rw [← FiniteLaw.expect_singleton, actionTraceOutcome_expect]
  convert! ((measurable_of_countable
    (fun x : Bool × Bool => if x = r then (1 : ℝ) else 0)).comp
      (measurable_sampleTrace_joint Γ a)).stronglyMeasurable.integral_prod_right'.measurable using 1
  infer_instance

def actualTypeTraceLaw (Γ : FiniteGame M 2 c Seed) (a : Fin M) (v : ℝ) :
    FiniteLaw (Bool × Bool) :=
  FiniteLaw.average (Γ.σ v) (actionTraceOutcome Γ a) (measurable_actionTraceOutcome_mass Γ a)

theorem actualTypeTraceLaw_expect (Γ : FiniteGame M 2 c Seed) (a : Fin M)
    (v : ℝ) (f : Bool × Bool → ℝ) :
    (actualTypeTraceLaw Γ a v).expect f =
      ∫act, ∫ω, f (sampleTrace Γ a act ω) ∂sampleLaw Γ ∂Γ.σ v := by
  rw [actualTypeTraceLaw, FiniteLaw.expect_average]
  simp_rw [actionTraceOutcome_expect]

theorem sampleTrace_count (Γ : FiniteGame M 2 c Seed) (a : Fin M)
    (act : JointAction 2) (ω : Sample M 2 Seed) :
    NativeCounts.traceCount (sampleTrace Γ a act ω) = focalCount Γ a act ω := by
  apply Fin.ext
  change (NativeCounts.traceCount (sampleTrace Γ a act ω)).val =
    inclusionCount (deviated a act ω) Γ.policy ω.1.2 a
  rw [inclusionCount_eq_sum, Fin.sum_univ_two]
  by_cases h0 : a ∈ allocation (deviated a act ω) Γ.policy ω.1.2 0 <;>
    by_cases h1 : a ∈ allocation (deviated a act ω) Γ.policy ω.1.2 1 <;>
      simp [sampleTrace, NativeCounts.traceCount, h0, h1]

theorem actualTypeTraceLaw_count (Γ : FiniteGame M 2 c Seed) (a : Fin M)
    (v : ℝ) :
    (actualTypeTraceLaw Γ a v).map NativeCounts.traceCount = typeOutcome Γ a v := by
  apply FiniteLaw.ext_expect
  intro f
  rw [FiniteLaw.expect_map, actualTypeTraceLaw_expect, typeOutcome_expect]
  apply integral_congr_ae
  apply ae_of_all
  intro act
  change (∫ω, f (NativeCounts.traceCount (sampleTrace Γ a act ω))∂sampleLaw Γ)=
    ((problem Γ a).outcome act).expect f
  rw [problem_outcome, CountLaw.expect_ofMeasure]
  apply integral_congr_ae
  exact ae_of_all _ (fun ω => congrArg f (sampleTrace_count Γ a act ω))

theorem sampleTrace_broadcast (Γ : FiniteGame M 2 c Seed) (a : Fin M)
    (act : JointAction 2) (hr : act.routeCount = 2) (ω : Sample M 2 Seed) :
    sampleTrace Γ a act ω = namedTrace Γ a act.bid ω.1 := by
  simp only [sampleTrace, namedTrace, mem_allocation_deviated_iff, hr,
    Hybrid.firstK_full_two, Finset.mem_univ, true_and]

theorem actionTraceOutcome_broadcast (Γ : FiniteGame M 2 c Seed) (a : Fin M)
    (act : JointAction 2) (hr : act.routeCount = 2) :
    actionTraceOutcome Γ a act = traceOutcome Γ a act.bid := by
  apply FiniteLaw.ext_expect
  intro f
  rw [actionTraceOutcome_expect, traceOutcome, FiniteLaw.expect_ofMeasure]
  simp_rw [sampleTrace_broadcast Γ a act hr]
  have hp := measurePreserving_fst (μ := backgroundLaw Γ) (ν := permLaw 2)
  calc
    _ = ∫ω, f (namedTrace Γ a act.bid ω)
        ∂(sampleLaw Γ).map Prod.fst :=
      (integral_map hp.measurable.aemeasurable
        ((measurable_of_countable f).comp (measurable_namedTrace Γ a act.bid)).aestronglyMeasurable).symm
    _ = _ := by
      change (∫ω, f (namedTrace Γ a act.bid ω)
        ∂((backgroundLaw Γ).prod (permLaw 2)).map Prod.fst)=_
      rw [hp.map_eq]

def actualTypeRecipientLaw (Γ : FiniteGame M 2 c Seed) (a : Fin M) (j : Fin 2)
    (v : ℝ) : CountLaw 2 :=
  (actualTypeTraceLaw Γ a v).map (NativeProfile.recipientCount j)

theorem actualTypeRecipientLaw_expect (Γ : FiniteGame M 2 c Seed) (a : Fin M)
    (j : Fin 2) (v : ℝ) (f : Fin 3 → ℝ) :
    (actualTypeRecipientLaw Γ a j v).expect f =
      ∫act, ∫ω, f (NativeProfile.recipientCount j (sampleTrace Γ a act ω))
        ∂sampleLaw Γ ∂Γ.σ v := by
  rw [actualTypeRecipientLaw, FiniteLaw.expect_map, actualTypeTraceLaw_expect]

end NativeRoutes

namespace OriginalPopulation
variable {i : Row} {M : ℕ} [NeZero M] {R : ℝ}

theorem game_actualTypeTraceLaw (E : ExactRestrictedLaw i M)
    (H : UpperPriorityLaw i R) (hR : cap i < R) (a : Fin M) (v : Value i) :
    NativeRoutes.actualTypeTraceLaw (game E H) a v = indexedTypeTraceLaw E a v := by
  apply FiniteLaw.ext_expect
  intro f
  rw [NativeRoutes.actualTypeTraceLaw, FiniteLaw.expect_average, game_lower_kernel]
  have hf : Measurable (fun act : JointAction 2 =>
      (NativeRoutes.actionTraceOutcome (game E H) a act).expect f) :=
    FiniteLaw.measurable_expect (NativeRoutes.actionTraceOutcome (game E H) a)
      (NativeRoutes.measurable_actionTraceOutcome_mass (game E H) a) f
  have hm : Measurable (fun q : unitInterval=>lowerAction i (v,q)) := by
    convert! (measurable_lowerAction i).comp
      (measurable_const.prodMk measurable_id) using 1
  rw [integral_map (μ:=E.sigma v) hm.aemeasurable hf.aestronglyMeasurable,
    indexedTypeTraceLaw, FiniteLaw.expect_average]
  apply integral_congr_ae
  apply ae_of_all
  intro q
  change (NativeRoutes.actionTraceOutcome (game E H) a (lowerAction i (v,q))).expect f=
    (NativeProfile.indexedTraceLaw i E.law a (baseBid i (v,q))).expect f
  rw [NativeRoutes.actionTraceOutcome_broadcast (game E H) a (lowerAction i (v,q)) rfl]
  change (NativeRoutes.traceOutcome (game E H) a (baseBid i (v,q))).expect f = _
  rw [game_trace_outcome E H hR a (baseBid i (v,q))]

theorem indexedTypeTraceLaw_actual_sample (E : ExactRestrictedLaw i M)
    (H : UpperPriorityLaw i R) (hR : cap i < R) (a : Fin M) (v : Value i)
    (f : Bool × Bool → ℝ) :
    (indexedTypeTraceLaw E a v).expect f =
      ∫act, ∫ω, f (NativeRoutes.sampleTrace (game E H) a act ω)
        ∂sampleLaw (game E H) ∂(game E H).σ v := by
  rw [← game_actualTypeTraceLaw E H hR a v, NativeRoutes.actualTypeTraceLaw_expect]

theorem game_actualTypeRecipientLaw (E : ExactRestrictedLaw i M)
    (H : UpperPriorityLaw i R) (hR : cap i < R)
    (a : Fin M) (j : Fin 2) (v : Value i) :
    NativeRoutes.actualTypeRecipientLaw (game E H) a j v =
      (indexedTypeTraceLaw E a v).map (NativeProfile.recipientCount j) := by
  rw [NativeRoutes.actualTypeRecipientLaw, game_actualTypeTraceLaw E H hR a v]

theorem indexedTypeRecipientLaw_actual_sample (E : ExactRestrictedLaw i M)
    (H : UpperPriorityLaw i R) (hR : cap i < R)
    (a : Fin M) (j : Fin 2) (v : Value i) (f : Fin 3 → ℝ) :
    ((indexedTypeTraceLaw E a v).map (NativeProfile.recipientCount j)).expect f =
      ∫act, ∫ω, f (NativeProfile.recipientCount j (NativeRoutes.sampleTrace (game E H) a act ω))
        ∂sampleLaw (game E H) ∂(game E H).σ v := by
  rw [← game_actualTypeRecipientLaw E H hR a j v, NativeRoutes.actualTypeRecipientLaw_expect]

end OriginalPopulation

end FCAppendix.Affine.UniformFinite
