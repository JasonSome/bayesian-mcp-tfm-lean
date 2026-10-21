import FCAppendix.Affine.Hybrid.Native02.ClosedLowTransport
import FCAppendix.Affine.Hybrid.NativeRealizedContext
import FCAppendix.Affine.Hybrid.PrivateSeedPayoff

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Bayes Game Set Filter Classical LowBody
open scoped BigOperators

section Context
variable {m c : ℕ}

def privateContextCount (C : ContextPolicy m c unitInterval) (X : ClassifiedContext m)
    (i : Fin m) (s : Fin 2 → unitInterval) : Fin 3 := focalCopy (C.selectionPair X s) i

lemma measurable_privateContextCount (C : ContextPolicy m c unitInterval)
    (X : ClassifiedContext m) (i : Fin m) : Measurable (privateContextCount C X i) :=
  (measurable_of_countable (fun P : Finset (Fin m) × Finset (Fin m) => focalCopy P i)).comp
    ((((C.measurable 0).comp (measurable_const.prodMk (measurable_pi_apply 0))).prodMk
      ((C.measurable 1).comp (measurable_const.prodMk (measurable_pi_apply 1)))))

def privateContextLaw (C : ContextPolicy m c unitInterval) (X : ClassifiedContext m)
    (i : Fin m) : CountLaw 2 :=
  CountLaw.ofMeasure (Measure.pi (fun _ : Fin 2 => (volume : Measure unitInterval)))
    (privateContextCount C X i) (measurable_privateContextCount C X i)

def privateAcceptance (C : ContextPolicy m c unitInterval) (j : Fin 2)
    (X : ClassifiedContext m) (i : Fin m) : ℝ :=
  ∫ s : unitInterval, if i ∈ C.select j X s then (1 : ℝ) else 0 ∂volume

lemma measurable_privateAcceptance (C : ContextPolicy m c unitInterval)
    (j : Fin 2) (i : Fin m) : Measurable (fun X => privateAcceptance C j X i) := by
  have hm : Measurable (fun p : ClassifiedContext m × unitInterval =>
      if i ∈ C.select j p.1 p.2 then (1 : ℝ) else 0) :=
    Measurable.ite ((C.measurable j)
      (MeasurableSet.of_discrete : MeasurableSet {S : Finset (Fin m) | i ∈ S}))
      measurable_const measurable_const
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

lemma privateAcceptance_bounds (C : ContextPolicy m c unitInterval) (j : Fin 2)
    (X : ClassifiedContext m) (i : Fin m) :
    0 ≤ privateAcceptance C j X i ∧ privateAcceptance C j X i ≤ 1 := by
  constructor
  · exact integral_nonneg (fun _ => by dsimp only; split <;> norm_num)
  · have hh := integral_mono_of_nonneg
      (μ := (volume : Measure unitInterval))
      (f := fun s => if i ∈ C.select j X s then (1 : ℝ) else 0)
      (g := fun _ => (1 : ℝ)) (ae_of_all _ (fun _ => by dsimp only; split <;> norm_num))
      (integrable_const 1) (ae_of_all _ (fun _ => by dsimp only; split <;> norm_num))
    simpa only [privateAcceptance, integral_const, probReal_univ, smul_eq_mul, mul_one] using hh

lemma privateContextLaw_success (C : ContextPolicy m c unitInterval)
    (X : ClassifiedContext m) (i : Fin m) :
    (privateContextLaw C X i).success =
      privateAcceptance C 0 X i + privateAcceptance C 1 X i -
        privateAcceptance C 0 X i * privateAcceptance C 1 X i := by
  have h0 : Measurable (C.select 0 X) :=
    (C.measurable 0).comp (measurable_const.prodMk measurable_id)
  have h1 : Measurable (C.select 1 X) :=
    (C.measurable 1).comp (measurable_const.prodMk measurable_id)
  have hh := NativeContinuation.private_pair_expected_payoff (m := m) 0 1
    (fun _ => (0 : ℝ)) i (C.select 0 X) (C.select 1 X) h0 h1
  rw [CountLaw.success, privateContextLaw, CountLaw.expect_ofMeasure]
  have he (s : Fin 2 → unitInterval) :
      successIndicator (privateContextCount C X i s).val =
        purePayoff 1 1 (fun _ => (0 : ℝ)) (C.select 0 X (s 0), C.select 1 X (s 1)) i := by
    change successIndicator (focalCopy (C.selectionPair X s) i).val =
      purePayoff 1 1 (fun _ => (0 : ℝ)) (C.selectionPair X s) i
    unfold purePayoff
    generalize focalCopy (C.selectionPair X s) i = k
    have hval : k.val=0 ∨ k.val=1 ∨ k.val=2 := by have h:=k.isLt; omega
    rcases hval with h|h|h
    · rw [show k=0 from Fin.ext h]
      norm_num [successIndicator]
      decide
    · rw [show k=1 from Fin.ext h]
      norm_num [successIndicator]
    · rw [show k=2 from Fin.ext h]
      norm_num [successIndicator]
  simp_rw [he]
  simpa only [sub_zero, zero_mul, one_mul, privateAcceptance] using hh

lemma privateContextLaw_load (C : ContextPolicy m c unitInterval)
    (X : ClassifiedContext m) (i : Fin m) :
    (privateContextLaw C X i).load = privateAcceptance C 0 X i + privateAcceptance C 1 X i := by
  have h0 : Measurable (C.select 0 X) :=
    (C.measurable 0).comp (measurable_const.prodMk measurable_id)
  have h1 : Measurable (C.select 1 X) :=
    (C.measurable 1).comp (measurable_const.prodMk measurable_id)
  have hh := NativeContinuation.private_pair_expected_payoff (m := m) 0 0
    (fun _ => (-1 : ℝ)) i (C.select 0 X) (C.select 1 X) h0 h1
  rw [CountLaw.load, privateContextLaw, CountLaw.expect_ofMeasure]
  have he (s : Fin 2 → unitInterval) :
      ((privateContextCount C X i s).val : ℝ) =
        purePayoff 1 0 (fun _ => (-1 : ℝ)) (C.select 0 X (s 0), C.select 1 X (s 1)) i := by
    change ((focalCopy (C.selectionPair X s) i).val : ℝ) =
      purePayoff 1 0 (fun _ => (-1 : ℝ)) (C.selectionPair X s) i
    unfold purePayoff
    generalize focalCopy (C.selectionPair X s) i = k
    have hval : k.val=0 ∨ k.val=1 ∨ k.val=2 := by have h:=k.isLt; omega
    rcases hval with h|h|h
    · rw [show k=0 from Fin.ext h]
      norm_num
      decide
    · rw [show k=1 from Fin.ext h]
      norm_num
      decide
    · rw [show k=2 from Fin.ext h]
      norm_num
  simp_rw [he]
  simpa only [sub_zero,zero_mul,mul_zero,neg_one_mul,zero_sub,neg_neg,privateAcceptance] using hh

theorem privateContextLaw_masses (C : ContextPolicy m c unitInterval)
    (X : ClassifiedContext m) (i : Fin m) :
    let p := privateAcceptance C 0 X i
    let q := privateAcceptance C 1 X i
    (privateContextLaw C X i).mass 0 = (1-p)*(1-q) ∧
      (privateContextLaw C X i).mass 1 = p*(1-q)+(1-p)*q ∧
      (privateContextLaw C X i).mass 2 = p*q := by
  dsimp only
  have hs := privateContextLaw_success C X i
  have hl := privateContextLaw_load C X i
  have ht := (privateContextLaw C X i).total
  simp only [CountLaw.success, CountLaw.load, FiniteLaw.expect] at hs hl
  norm_num [Fin.sum_univ_succ, successIndicator] at hs hl ht
  constructor
  · nlinarith
  · constructor <;> nlinarith

end Context

section Realized
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma closed_native_allocation_mem_iff (C : ContextPolicy m c Seed)
    (Γ : FiniteGame m 2 c Seed) (R : ℝ) (z : UserProfile m 2)
    (hz : z ∈ closedProfiles m R) (s : Fin 2 → Seed) (j : Fin 2) (i : Fin m)
    (hi : (z i).1.2.bid < R) :
    i ∈ allocation (drawsRealization z) (ClosedPolicy.nativeGame C Γ R).policy s j ↔
      i ∈ C.select j (actualClosedContext R z) (s j) := by
  have hlow : lowerPart R (observe (drawsRealization z) j) i ≠ none := by
    rw [lowerPart_observe z hz j]
    simp only [if_pos hi, ne_eq, Option.some_ne_none, not_false_eq_true]
  have hf := ClosedPolicy.factors C R j (observe (drawsRealization z) j) (s j) i hlow
  rw [observedClosedContext_eq_actual z hz j] at hf
  exact hf

lemma closed_native_inclusionCount_eq_focalCopy (C : ContextPolicy m c Seed)
    (Γ : FiniteGame m 2 c Seed) (R : ℝ) (z : UserProfile m 2)
    (hz : z ∈ closedProfiles m R) (s : Fin 2 → Seed) (i : Fin m)
    (hi : (z i).1.2.bid < R) :
    inclusionCount (drawsRealization z) (ClosedPolicy.nativeGame C Γ R).policy s i =
      (focalCopy (C.selectionPair (actualClosedContext R z) s) i).val := by
  rw [inclusionCount_eq_sum, Fin.sum_univ_two]
  simp only [closed_native_allocation_mem_iff C Γ R z hz s 0 i hi,
    closed_native_allocation_mem_iff C Γ R z hz s 1 i hi]
  by_cases h0 : i ∈ C.select 0 (actualClosedContext R z) (s 0) <;>
    by_cases h1 : i ∈ C.select 1 (actualClosedContext R z) (s 1) <;>
    simp [ContextPolicy.selectionPair, focalCopy, h0, h1]

lemma actualClosedContext_entryBid (R : ℝ) (z : UserProfile m 2)
    (hz : z ∈ closedProfiles m R) (i : Fin m) (hi : (z i).1.2.bid < R) :
    entryBid ((actualClosedContext R z).1 i) = (z i).1.2.bid := by
  change entryBid (lowerPart R (observe (drawsRealization z) 0) i) = _
  rw [lowerPart_observe z hz 0]
  simp only [if_pos hi, entryBid]

def insertedLowerProfile (i : Fin m) (a : JointAction 2) (z : UserProfile m 2) :
    UserProfile m 2 := Function.update z i ((0, a), Equiv.refl (Fin 2))

def insertedLowerContext (R : ℝ) (i : Fin m) (a : JointAction 2)
    (z : UserProfile m 2) : ClassifiedContext m :=
  observedClosedContext R 0 (observe (drawsRealization (insertedLowerProfile i a z)) 0)

lemma measurable_insertedLowerContext (R : ℝ) (i : Fin m) (a : JointAction 2) :
    Measurable (insertedLowerContext R i a) := by
  have hupdate : Measurable (insertedLowerProfile i a) := by
    apply measurable_pi_lambda
    intro k
    by_cases hk : k = i
    · subst k
      simp only [insertedLowerProfile, Function.update_self]
      exact measurable_const
    · simp only [insertedLowerProfile, Function.update_of_ne hk]
      exact measurable_pi_apply k
  exact (measurable_observedClosedContext R 0).comp ((measurable_observe_draws 0).comp hupdate)

lemma insertedLowerProfile_mem {R : ℝ} (i : Fin m) (a : JointAction 2)
    (hb : a.bid < R) (hk : a.routeCount = 2) (z : UserProfile m 2)
    (hz : z ∈ closedProfiles m R) : insertedLowerProfile i a z ∈ closedProfiles m R := by
  intro k
  by_cases hi : k = i
  · subst k
    exact Or.inl ⟨by simpa [insertedLowerProfile] using hb, by simp [insertedLowerProfile, hk]⟩
  · simpa only [insertedLowerProfile, Function.update_of_ne hi] using hz k

lemma insertedLowerContext_eq_actual {R : ℝ} (i : Fin m) (a : JointAction 2)
    (hb : a.bid < R) (hk : a.routeCount = 2) (z : UserProfile m 2)
    (hz : z ∈ closedProfiles m R) :
    insertedLowerContext R i a z = actualClosedContext R (insertedLowerProfile i a z) :=
  observedClosedContext_eq_actual _ (insertedLowerProfile_mem i a hb hk z hz) 0

lemma insertedLowerContext_entryBid {R : ℝ} (i : Fin m) (a : JointAction 2)
    (hb : a.bid < R) (hk : a.routeCount = 2) (z : UserProfile m 2)
    (hz : z ∈ closedProfiles m R) : entryBid ((insertedLowerContext R i a z).1 i) = a.bid := by
  rw [insertedLowerContext_eq_actual i a hb hk z hz]
  simpa only [insertedLowerProfile, Function.update_self] using
    actualClosedContext_entryBid R (insertedLowerProfile i a z)
      (insertedLowerProfile_mem i a hb hk z hz) i (by simpa [insertedLowerProfile] using hb)

lemma focalCount_broadcast_route_independent (Γ : FiniteGame m 2 c Seed)
    (i : Fin m) (a : JointAction 2) (hk : a.routeCount = 2)
    (z : UserProfile m 2) (s : Fin 2 → Seed) (τ σ : Equiv.Perm (Fin 2)) :
    focalCount Γ i a ((z, s), τ) = focalCount Γ i a ((z, s), σ) := by
  have hx : deviated i a ((z, s), τ) = deviated i a ((z, s), σ) := by
    unfold deviated
    rw [hk, firstK_full_two, firstK_full_two]
  change boundedCount (deviated i a ((z, s), τ)) Γ.policy s i =
    boundedCount (deviated i a ((z, s), σ)) Γ.policy s i
  rw [hx]

theorem closed_focalCount_eq_context (C : ContextPolicy m c unitInterval)
    (Γ : FiniteGame m 2 c unitInterval) {R : ℝ} (i : Fin m) (a : JointAction 2)
    (hb : a.bid < R) (hk : a.routeCount = 2) (z : UserProfile m 2)
    (hz : z ∈ closedProfiles m R) (s : Fin 2 → unitInterval) (τ : Equiv.Perm (Fin 2)) :
    focalCount (ClosedPolicy.nativeGame C Γ R) i a ((z, s), τ) =
      privateContextCount C (insertedLowerContext R i a z) i s := by
  rw [focalCount_broadcast_route_independent _ i a hk z s τ (Equiv.refl (Fin 2))]
  apply Fin.ext
  rw [focalCount_eq_inserted_count _ i 0 a z s (Equiv.refl (Fin 2))]
  have hz' := insertedLowerProfile_mem i a hb hk z hz
  have hh := closed_native_inclusionCount_eq_focalCopy C Γ R (insertedLowerProfile i a z) hz' s i
    (by simpa only [insertedLowerProfile, Function.update_self] using hb)
  simpa only [privateContextCount,insertedLowerProfile,
    insertedLowerContext_eq_actual i a hb hk z hz] using hh

end Realized

section Integrals
variable {m c : ℕ}

lemma outcome_expect_profile_seed_route (Γ : FiniteGame m 2 c unitInterval)
    (i : Fin m) (a : JointAction 2) (f : Fin 3 → ℝ) :
    ((problem Γ i).outcome a).expect f =
      ∫ z, ∫ s, ∫ τ, f (focalCount Γ i a ((z, s), τ))
        ∂permLaw 2 ∂Measure.pi (fun _ : Fin 2 => Γ.seedLaw) ∂userProfileLaw Γ := by
  rw [problem_outcome, CountLaw.expect_ofMeasure]
  have hi := CountLaw.integrable_comp (sampleLaw Γ) (focalCount Γ i a)
    (measurable_focalCount Γ i a) f
  change (∫ ω, f (focalCount Γ i a ω)
    ∂((userProfileLaw Γ).prod (Measure.pi (fun _ : Fin 2 => Γ.seedLaw))).prod (permLaw 2)) = _
  change Integrable (fun ω => f (focalCount Γ i a ω))
    (((userProfileLaw Γ).prod (Measure.pi (fun _ : Fin 2 => Γ.seedLaw))).prod (permLaw 2)) at hi
  rw [integral_prod _ hi, integral_prod _ hi.integral_prod_left]

theorem closed_broadcast_count_expectation (C : ContextPolicy m c unitInterval)
    (Γ : FiniteGame m 2 c unitInterval) {R : ℝ} (hseed : Γ.seedLaw = volume)
    (hfull : ∀ᵐ z ∂userProfileLaw Γ, z ∈ closedProfiles m R)
    (i : Fin m) (a : JointAction 2) (hb : a.bid < R) (hk : a.routeCount = 2)
    (f : Fin 3 → ℝ) :
    ((problem (ClosedPolicy.nativeGame C Γ R) i).outcome a).expect f =
      ∫ z, (privateContextLaw C (insertedLowerContext R i a z) i).expect f ∂userProfileLaw Γ := by
  rw [outcome_expect_profile_seed_route]
  change (∫ z, ∫ s, ∫ τ, f (focalCount (ClosedPolicy.nativeGame C Γ R) i a ((z, s), τ))
    ∂permLaw 2 ∂Measure.pi (fun _ : Fin 2 => Γ.seedLaw) ∂userProfileLaw Γ) = _
  apply integral_congr_ae
  filter_upwards [hfull] with z hz
  rw [privateContextLaw, CountLaw.expect_ofMeasure, hseed]
  apply integral_congr_ae
  apply ae_of_all
  intro s
  simp_rw [closed_focalCount_eq_context C Γ i a hb hk z hz s]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]

theorem closed_broadcast_count_masses (C : ContextPolicy m c unitInterval)
    (Γ : FiniteGame m 2 c unitInterval) {R : ℝ} (hseed : Γ.seedLaw = volume)
    (hfull : ∀ᵐ z ∂userProfileLaw Γ, z ∈ closedProfiles m R)
    (i : Fin m) (a : JointAction 2) (hb : a.bid < R) (hk : a.routeCount = 2) :
    let p := fun z => privateAcceptance C 0 (insertedLowerContext R i a z) i
    let q := fun z => privateAcceptance C 1 (insertedLowerContext R i a z) i
    ((problem (ClosedPolicy.nativeGame C Γ R) i).outcome a).mass 0 =
      ∫ z, (1-p z)*(1-q z) ∂userProfileLaw Γ ∧
    ((problem (ClosedPolicy.nativeGame C Γ R) i).outcome a).mass 1 =
      ∫ z, p z*(1-q z)+(1-p z)*q z ∂userProfileLaw Γ ∧
    ((problem (ClosedPolicy.nativeGame C Γ R) i).outcome a).mass 2 =
      ∫ z, p z*q z ∂userProfileLaw Γ := by
  dsimp only
  have hm (r : Fin 3) : ((problem (ClosedPolicy.nativeGame C Γ R) i).outcome a).mass r =
      ∫ z, (privateContextLaw C (insertedLowerContext R i a z) i).mass r ∂userProfileLaw Γ := by
    have he := closed_broadcast_count_expectation C Γ hseed hfull i a hb hk
      (fun k => if k = r then (1 : ℝ) else 0)
    simpa [FiniteLaw.expect, eq_comm] using he
  constructor
  · rw [hm 0]
    apply integral_congr_ae
    exact ae_of_all _ (fun z => (privateContextLaw_masses C (insertedLowerContext R i a z) i).1)
  · constructor
    · rw [hm 1]
      apply integral_congr_ae
      exact ae_of_all _ (fun z => (privateContextLaw_masses C (insertedLowerContext R i a z) i).2.1)
    · rw [hm 2]
      apply integral_congr_ae
      exact ae_of_all _ (fun z => (privateContextLaw_masses C (insertedLowerContext R i a z) i).2.2)

theorem closed_broadcast_payoff_integral (C : ContextPolicy m c unitInterval)
    (Γ : FiniteGame m 2 c unitInterval) {R η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hA : Γ.A = Schedule.affine 2 η hη0 hη1) (hg : Γ.g = 0)
    (hseed : Γ.seedLaw = volume)
    (hfull : ∀ᵐ z ∂userProfileLaw Γ, z ∈ closedProfiles m R)
    (i : Fin m) (v : ℝ) (a : JointAction 2) (hb : a.bid < R) (hk : a.routeCount = 2) :
    let p := fun z => privateAcceptance C 0 (insertedLowerContext R i a z) i
    let q := fun z => privateAcceptance C 1 (insertedLowerContext R i a z) i
    (problem (ClosedPolicy.nativeGame C Γ R) i).payoff v a =
      ∫ z, v*(p z+q z-p z*q z)-a.bid*(p z+q z-(1-η)*p z*q z) ∂userProfileLaw Γ := by
  dsimp only
  change ((problem (ClosedPolicy.nativeGame C Γ R) i).outcome a).expect
    (fun r => userPayoff v a.bid Γ.g Γ.A.charge Γ.G.charge r.val) = _
  rw [closed_broadcast_count_expectation C Γ hseed hfull i a hb hk]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  change (privateContextLaw C (insertedLowerContext R i a z) i).utility v a.bid Γ.g Γ.A Γ.G = _
  rw [hg, hA, CountLaw.utility_eq, CountLaw.charge_affine, CountLaw.duplicates,
    privateContextLaw_success, privateContextLaw_load]
  ring

theorem closed_singleton_payoff_integral (C : ContextPolicy m c unitInterval)
    (Γ : FiniteGame m 2 c unitInterval) {R : ℝ} (hg : Γ.g = 0)
    (hseed : Γ.seedLaw = volume)
    (hfull : ∀ᵐ z ∂userProfileLaw Γ, z ∈ closedProfiles m R)
    (i : Fin m) (v : ℝ) (a : JointAction 2) (hb : a.bid < R) (hk : a.routeCount = 1) :
    let broad := NativeLowIncentives.broadcast a.bid a.bid_nonneg
    let p := fun z => privateAcceptance C 0 (insertedLowerContext R i broad z) i
    let q := fun z => privateAcceptance C 1 (insertedLowerContext R i broad z) i
    (problem (ClosedPolicy.nativeGame C Γ R) i).payoff v a =
      (v-a.bid)/2 * ∫ z, p z+q z ∂userProfileLaw Γ := by
  dsimp only
  let broad := NativeLowIncentives.broadcast a.bid a.bid_nonneg
  have hbroad : broad.bid = a.bid := rfl
  have hl := closed_broadcast_count_expectation C Γ hseed hfull i broad hb rfl
    (fun r => (r.val : ℝ))
  change ((problem (ClosedPolicy.nativeGame C Γ R) i).outcome broad).load =
    ∫ z, (privateContextLaw C (insertedLowerContext R i broad z) i).load ∂userProfileLaw Γ at hl
  simp_rw [privateContextLaw_load] at hl
  rw [load_eq_mean _ (by norm_num : 0 < 2), show broad.routeCount = 2 from rfl,
    Nat.cast_ofNat, hbroad] at hl
  rw [singleton_payoff _ (by norm_num : 0 < 2) i a hk v]
  change (v-Γ.g-a.bid)*meanAcceptProb (ClosedPolicy.nativeGame C Γ R) i a.bid = _
  rw [hg]
  rw [← hl]
  ring

end Integrals
end FCAppendix.Affine.Hybrid.Native02
