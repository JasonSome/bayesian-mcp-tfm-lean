import FCAppendix.Ample.FreeBaseIncentives
import FCAppendix.Ample.DeficitTransport
import FCAppendix.Ample.DownstreamFixedValueLaw

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology Real
open scoped ENNReal BigOperators
open Ample Ample.DownstreamNormalizationCore

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def activeDrawLaw (Γ : FiniteGame m n c Seed) : Measure (ℝ × JointAction n) :=
  (Γ.F (Ioi Γ.g))⁻¹ • (Γ.F ⊗ₘ Γ.σ).restrict {x | Γ.g < x.1}

def activeSurplusLaw (F : Measure ℝ) (g : ℝ) : Measure ℝ :=
  ((F (Ioi g))⁻¹ • F.restrict (Ioi g)).map (fun v => v - g)

def actualDeficit (Γ : FiniteGame m n c Seed) (w : ℝ) : ℝ :=
  if hm : 0 < m then deficit (problem Γ ⟨0, hm⟩) w else w

def actualFailure (Γ : FiniteGame m n c Seed) (a : JointAction n) : ℝ :=
  if hm : 0 < m then 1 - ((problem Γ ⟨0, hm⟩).outcome a).success else 1

def actualMeanLoad (Γ : FiniteGame m n c Seed) (a : JointAction n) : ℝ :=
  if hm : 0 < m then ((problem Γ ⟨0, hm⟩).outcome a).load else 0

def actualAllFailure (Γ : FiniteGame m n c Seed) : ℝ :=
  if hm : 0 < m then allPositiveCongestion Γ ⟨0, hm⟩ else 1

def actualBestReply (Γ : FiniteGame m n c Seed) (w : ℝ) (a : JointAction n) : Prop :=
  ∀ hm : 0 < m, (problem Γ ⟨0, hm⟩).BestResponse (w+Γ.g) a

def actualRouteMass (Γ : FiniteGame m n c Seed) (j : ℕ) : ℝ :=
  (Γ.F ⊗ₘ Γ.σ).real {x | x.2.routeCount = j}

def actualInclusionMass (Γ : FiniteGame m n c Seed) (j : ℕ) : ℝ :=
  if hm : 0 < m then
    ∫ x, ((problem Γ ⟨0, hm⟩).outcome x.2).prob (fun r => r.val = j)
      ∂(Γ.F ⊗ₘ Γ.σ)
  else if j = 0 then 1 else 0

def actualMenu (Γ : FiniteGame m n c Seed) : AffineMenu (JointAction n) where
  failure := actualFailure Γ
  payment := fun a => a.bid * actualMeanLoad Γ a
  failure_nonneg := by
    intro a
    unfold actualFailure
    split_ifs with hm
    · exact sub_nonneg.mpr ((problem Γ ⟨0, hm⟩).outcome a).success_le_one
    · norm_num
  payment_nonneg := by
    intro a
    unfold actualMeanLoad
    split_ifs with hm
    · exact mul_nonneg a.bid_nonneg ((problem Γ ⟨0, hm⟩).outcome a).load_nonneg
    · simp

theorem actualMenu_isEnvelope (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (hA : Γ.A = Schedule.ppi n) (hfree : FreeDuplicateBase Γ) :
    IsEnvelope (actualMenu Γ) (actualDeficit Γ) := by
  intro w _hw
  let i : Fin m := ⟨0, hm⟩
  have hpay := ppi_free_payoff Γ hA hfree i w
  simp only [actualMenu, actualFailure, actualMeanLoad, actualDeficit, dif_pos hm]
  constructor
  · intro a
    have h := (problem Γ i).action_le_envelope (w + Γ.g) a
    rw [hpay a] at h
    change w - (problem Γ i).envelope (w + Γ.g) ≤ _
    linarith
  · intro t ht
    have h := (problem Γ i).envelope_le (w + Γ.g) (w - t) (by
      intro a
      rw [hpay a]
      linarith [ht a])
    change t ≤ w - (problem Γ i).envelope (w + Γ.g)
    linarith

theorem actualMenu_bestReply (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (hA : Γ.A = Schedule.ppi n) (hfree : FreeDuplicateBase Γ)
    {w : ℝ} {a : JointAction n}
    (ha : (problem Γ ⟨0, hm⟩).BestResponse (w + Γ.g) a) :
    IsBestReply (actualMenu Γ) w a := by
  intro b
  have h := ha b
  rw [ppi_free_payoff Γ hA hfree, ppi_free_payoff Γ hA hfree] at h
  simp only [actualMenu, actualFailure, actualMeanLoad, dif_pos hm]
  linarith

theorem actualFailure_eq_congestProb (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hA : Γ.A = Schedule.ppi n)
    (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (a : JointAction n) (hb : 0 < a.bid) :
    actualFailure Γ a = congestProb n (m - 1) c a.routeCount
      (visibleClassMass Γ a.bid) := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  simp only [actualFailure, dif_pos (Nat.succ_pos N), Nat.succ_sub_one]
  exact ppi_failure_eq_congestProb Γ hA hatom hj _ a hb

theorem actual_AM1 (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (hA : Γ.A = Schedule.ppi n) (hf : FreeDuplicateBase Γ)
    (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j) (hn : 0 < n)
    {w : ℝ} (hw : 0 < w) (a : JointAction n)
    (ha : (problem Γ ⟨0, hm⟩).BestResponse (w+Γ.g) a) :
    actualDeficit Γ w ≤ w*actualAllFailure Γ ∧
      actualFailure Γ a ≤ actualAllFailure Γ ∧
      a.bid*(a.routeCount : ℝ)*meanAcceptProb Γ ⟨0, hm⟩ a.bid ≤
        w*actualAllFailure Γ := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  simpa only [actualDeficit, actualFailure, actualAllFailure,
    dif_pos (Nat.succ_pos N)] using
    ppi_free_AM1 Γ hA hf hatom hj hn ⟨0, Nat.succ_pos N⟩ hw a ha

theorem actualDeficit_le_allFailure (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (hA : Γ.A = Schedule.ppi n) (hf : FreeDuplicateBase Γ)
    (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    {w : ℝ} (hw : 0 ≤ w) : actualDeficit Γ w ≤ w*actualAllFailure Γ := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have hb := envelope_ge_allPositive_outside Γ hA hf hatom hj
    ⟨0, Nat.succ_pos N⟩ hw
  simp only [actualDeficit, actualAllFailure, dif_pos (Nat.succ_pos N)]
  change w - (problem Γ ⟨0, Nat.succ_pos N⟩).envelope (w + Γ.g) ≤ _
  linarith

theorem activeDrawLaw_surplus_map (Γ : FiniteGame m n c Seed) :
    (activeDrawLaw Γ).map (fun x => x.1 - Γ.g) = activeSurplusLaw Γ.F Γ.g := by
  have hfst : ((Γ.F ⊗ₘ Γ.σ).restrict {x | Γ.g < x.1}).map Prod.fst =
      Γ.F.restrict (Ioi Γ.g) := by
    change ((Γ.F ⊗ₘ Γ.σ).restrict (Prod.fst ⁻¹' Ioi Γ.g)).map Prod.fst = _
    rw [← Measure.restrict_map measurable_fst measurableSet_Ioi,
      ← Measure.fst, Measure.fst_compProd]
  unfold activeDrawLaw activeSurplusLaw
  change ((Γ.F (Ioi Γ.g))⁻¹ •
    (Γ.F ⊗ₘ Γ.σ).restrict {x | Γ.g < x.1}).map
      ((fun v : ℝ => v - Γ.g) ∘ Prod.fst) = _
  have hsub : Measurable (fun v : ℝ => v - Γ.g) := measurable_id.sub_const Γ.g
  rw [← Measure.map_map hsub measurable_fst,
    Measure.map_smul, hfst]

theorem activeSurplusLaw_nonpositive_null (F : Measure ℝ) (g : ℝ) :
    activeSurplusLaw F g (Iic 0) = 0 := by
  unfold activeSurplusLaw
  have hsub : Measurable (fun v : ℝ => v - g) := measurable_id.sub_const g
  rw [Measure.map_apply hsub measurableSet_Iic,
    Measure.smul_apply,
    Measure.restrict_apply (hsub measurableSet_Iic)]
  have he : (fun v : ℝ => v - g) ⁻¹' Iic 0 ∩ Ioi g = ∅ := by
    ext v
    simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioi,
      mem_empty_iff_false, iff_false, not_and]
    intro hv
    linarith
  rw [he, measure_empty, smul_zero]

def IsActiveEndpoint (F : Measure ℝ) (g ell : ℝ) : Prop :=
  0 ≤ ell ∧ activeSurplusLaw F g (Iio ell) = 0 ∧
    ∀ a, ell < a → 0 < activeSurplusLaw F g (Iic a)

theorem activeEndpointLaw_actual {M C : ℕ → ℕ}
    (Γ : ∀ t, FiniteGame (M t) n (C t) Seed) {F : Measure ℝ} {g ell : ℝ}
    (hF : ∀ t, (Γ t).F = F) (hg : ∀ t, (Γ t).g = g)
    (he : IsActiveEndpoint F g ell) :
    ActiveEndpointLaw (fun t => activeDrawLaw (Γ t))
      (fun _ x => x.1 - g) (activeSurplusLaw F g) ell := by
  refine ⟨fun _ => measurable_fst.sub_const g, ?_, ?_, he.2.1, he.2.2⟩
  · intro t
    simpa only [← hg t, ← hF t] using activeDrawLaw_surplus_map (Γ t)
  · exact activeSurplusLaw_nonpositive_null F g

def HasPopulationRate (M : ℕ → ℕ) (p : ℕ → ℝ) (J : ℝ) : Prop :=
  (∀ᶠ t in atTop, 0 < p t) ∧
  Tendsto (fun t => populationLogRate (M t) (p t)) atTop (𝓝 J)

def RouteLimit {M C : ℕ → ℕ}
    (Γ : ∀ t, FiniteGame (M t) n (C t) Seed) (pi : ℕ → ℝ) : Prop :=
  ∀ j ∈ Finset.Icc 0 n,
    Tendsto (fun t => actualRouteMass (Γ t) j) atTop (𝓝 (pi j))

theorem actualAllFailure_eq_congestProb (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) :
    actualAllFailure Γ = congestProb n (m - 1) c n (visibleClassMass Γ 0) := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  simp only [actualAllFailure, dif_pos (Nat.succ_pos N), Nat.succ_sub_one]
  have he := joint_rank_congestion_eq Γ (⟨0, Nat.succ_pos N⟩ : Fin (N+1))
    0 (Finset.univ : Finset (Fin n))
  simpa only [allPositiveCongestion, congestProb, selected_self,
    Finset.mem_univ, forall_true_left] using he

theorem actualFailure_nonneg (Γ : FiniteGame m n c Seed) (a : JointAction n) :
    0 ≤ actualFailure Γ a := (actualMenu Γ).failure_nonneg a

theorem actualAllFailure_nonneg (Γ : FiniteGame m n c Seed) :
    0 ≤ actualAllFailure Γ := by
  unfold actualAllFailure
  split_ifs
  · exact measureReal_nonneg
  · norm_num

theorem actualDeficit_ratio_bounds (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (w z : ℝ) (hw : 0 < w) (hz : 0 < z) :
    min 1 (w / z) * actualDeficit Γ z ≤ actualDeficit Γ w ∧
      actualDeficit Γ w ≤ max 1 (w / z) * actualDeficit Γ z := by
  simpa only [actualDeficit, dif_pos hm] using
    deficit_ratio_bounds (problem Γ ⟨0, hm⟩) w z hw hz

theorem actualDeficit_eq_loss (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (hA : Γ.A = Schedule.ppi n) (hf : FreeDuplicateBase Γ)
    (w : ℝ) (a : JointAction n)
    (ha : (problem Γ ⟨0, hm⟩).BestResponse (w + Γ.g) a) :
    actualDeficit Γ w = w * actualFailure Γ a + a.bid * actualMeanLoad Γ a := by
  have he := ((problem Γ ⟨0, hm⟩).bestResponse_iff_attains (w + Γ.g) a).mp ha
  rw [ppi_free_payoff Γ hA hf] at he
  simp only [actualDeficit, actualFailure, actualMeanLoad, dif_pos hm]
  change w - (problem Γ ⟨0, hm⟩).envelope (w + Γ.g) = _
  rw [← he]
  ring

end FCAppendix.Bayes
