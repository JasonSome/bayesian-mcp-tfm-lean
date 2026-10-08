import FCAppendix.Ample.SlackAccounting
import FCAppendix.Finite.PPIRankBands

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma ppi_positive_success_of_positive_mass_lt_one
    (Γ : FiniteGame m n c Seed) (hm : 0 < m) (hn : 0 < n) (hc : 0 < c)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hP : positiveRouteMass Γ (fun _ => True) < 1)
    (i : Fin m) {w : ℝ} (hw : 0 < w) (a : JointAction n)
    (ha : (problem Γ i).BestResponse (w + Γ.g) a) :
    0 < ((problem Γ i).outcome a).success := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  let j : Fin n := ⟨0, hn⟩
  have hp : alphaGt Γ j 0 < 1 := by
    rw [← visibleClassMass_marginal Γ 0 j]
    exact (arrivalMean_le_tail Γ hn 0 le_rfl).trans_lt
      (by simpa only [positiveRouteTail_zero] using hP)
  have hq := binomBelow_pos_of_lt_one N c hc (alphaGt Γ j 0)
    (show 0 ≤ alphaGt Γ j 0 from measureReal_nonneg) hp
  exact hq.trans_le (ppi_success_ge_zero_rank Γ hA hj hatom i j w hw a
    (by simpa only [add_comm] using ha))

theorem ppi_ae_positive_draw_iff
    (Γ : FiniteGame m n c Seed) (hm : 0 < m) (hn : 0 < n) (hc : 0 < c)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hu : UsersOptimal Γ) (hact : NonpositiveAbstention Γ) (hz : RejectsZeroBids Γ) :
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ),
      (0 < x.2.bid ∧ 0 < x.2.routeCount) ↔ Γ.g < x.1 := by
  let i : Fin m := ⟨0, hm⟩
  let E : Set (ℝ × JointAction n) := {x | 0 < x.2.bid ∧ 0 < x.2.routeCount}
  have hE : MeasurableSet E :=
    (measurableSet_lt measurable_const ((measurable_bid n).comp measurable_snd)).inter
      (measurableSet_lt measurable_const ((measurable_routeCount n).comp measurable_snd))
  by_cases hP : positiveRouteMass Γ (fun _ => True) < 1
  · filter_upwards [ae_bestResponse_compProd Γ hu i, hact] with x hbr hactive
    constructor
    · intro hx
      by_contra hv
      have he := hactive (le_of_not_gt hv)
      omega
    · intro hv
      have hs := ppi_positive_success_of_positive_mass_lt_one Γ hm hn hc hA hatom hj
        hP i (by linarith : 0 < x.1 - Γ.g) x.2
        (by simpa only [sub_add_cancel] using hbr)
      have hk := route_pos_of_success_pos Γ i x.2 hs
      have hb : 0 < x.2.bid := by
        by_contra hnot
        have hb0 := le_antisymm (le_of_not_gt hnot) x.2.bid_nonneg
        rw [success_zero_of_bid_zero Γ hn hz i x.2 hb0] at hs
        exact lt_irrefl 0 hs
      exact ⟨hb, hk⟩
  · have hPE : (Γ.F ⊗ₘ Γ.σ).real E = 1 := by
      have he : positiveRouteMass Γ (fun _ => True) = (Γ.F ⊗ₘ Γ.σ).real E := by
        simp only [positiveRouteMass, E, and_true]
      rw [← he]
      exact le_antisymm (positiveRouteMass_le_one Γ _) (le_of_not_gt hP)
    have hPE' : (Γ.F ⊗ₘ Γ.σ) E = 1 := by
      apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.one_ne_top).mp
      simpa only [Measure.real, ENNReal.toReal_one] using hPE
    have hae : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x ∈ E := by
      rw [ae_iff]
      change (Γ.F ⊗ₘ Γ.σ) Eᶜ = 0
      rw [measure_compl hE (measure_ne_top _ _), measure_univ, hPE', tsub_self]
    filter_upwards [hae, hact] with x hx hxact
    constructor
    · intro _
      by_contra hv
      have he := hxact (le_of_not_gt hv)
      have hk : 0 < x.2.routeCount := hx.2
      omega
    · intro _
      exact hx

theorem ppi_positiveParticipation_eq
    (Γ : FiniteGame m n c Seed) (hm : 0 < m) (hn : 0 < n) (hc : 0 < c)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hu : UsersOptimal Γ) (hact : NonpositiveAbstention Γ) (hz : RejectsZeroBids Γ) :
    positiveRouteMass Γ (fun _ => True) = Γ.F.real (Ioi Γ.g) := by
  rw [← joint_value_probability Γ (Ioi Γ.g) measurableSet_Ioi]
  apply measureReal_congr
  filter_upwards [ppi_ae_positive_draw_iff Γ hm hn hc hA hatom hj hu hact hz] with x hx
  change (0 < x.2.bid ∧ 0 < x.2.routeCount ∧ True) = (Γ.g < x.1)
  simpa only [and_true] using propext hx

theorem ppi_ae_routed_bid_pos
    (Γ : FiniteGame m n c Seed) (hm : 0 < m) (hn : 0 < n) (hc : 0 < c)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hu : UsersOptimal Γ) (hact : NonpositiveAbstention Γ) (hz : RejectsZeroBids Γ) :
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.routeCount → 0 < x.2.bid := by
  filter_upwards [ppi_ae_positive_draw_iff Γ hm hn hc hA hatom hj hu hact hz, hact]
    with x hx hxa hk
  have hv : Γ.g < x.1 := by
    by_contra hnot
    have hh := hxa (le_of_not_gt hnot)
    omega
  exact (hx.mpr hv).1

theorem ppi_submitted_eq_positive
    (Γ : FiniteGame m n c Seed) (hm : 0 < m) (hn : 0 < n) (hc : 0 < c)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hu : UsersOptimal Γ) (hact : NonpositiveAbstention Γ) (hz : RejectsZeroBids Γ) :
    submittedMarginal Γ = Ample.contactMarginal n (visibleClassMass Γ 0) := by
  rw [submittedMarginal, arrivalMean_eq_integral]
  congr 1
  apply integral_congr_ae
  filter_upwards [ppi_ae_routed_bid_pos Γ hm hn hc hA hatom hj hu hact hz] with x hx
  by_cases hk : 0 < x.2.routeCount
  · simp [cutRouteCount, hx hk]
  · have hk0 : x.2.routeCount = 0 := by omega
    simp [cutRouteCount, hk0]

theorem ppi_positiveRouteMass_eq_raw
    (Γ : FiniteGame m n c Seed) (hm : 0 < m) (hn : 0 < n) (hc : 0 < c)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hu : UsersOptimal Γ) (hact : NonpositiveAbstention Γ) (hz : RejectsZeroBids Γ)
    (P : ℕ → Prop) (hP : ∀ k, P k → 0 < k) :
    positiveRouteMass Γ P = (Γ.F ⊗ₘ Γ.σ).real {x | P x.2.routeCount} := by
  apply measureReal_congr
  filter_upwards [ppi_ae_routed_bid_pos Γ hm hn hc hA hatom hj hu hact hz] with x hx
  apply propext
  change (0 < x.2.bid ∧ 0 < x.2.routeCount ∧ P x.2.routeCount) ↔ P x.2.routeCount
  exact ⟨fun h => h.2.2, fun h => ⟨hx (hP _ h), hP _ h, h⟩⟩

end FCAppendix.Bayes
