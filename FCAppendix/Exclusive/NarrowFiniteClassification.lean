import FCAppendix.Exclusive.NarrowOrderedGraph
import FCAppendix.Exclusive.TariffInterim
import FCAppendix.Game.JointMeasurability
import FCAppendix.PayOnce.Participation

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Filter Topology Set Game Exclusive
open scoped ProbabilityTheory BigOperators

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

structure FiniteBroadcastDifferential (Γ : FiniteGame m n c Seed)
    (tariff : UserTariff) (i : Fin m) (E : Set ℝ) (lo hi : ℝ)
    (A C A' C' : ℝ → ℝ) : Prop where
  success_hasDeriv : ∀ b ∈ Ioo lo hi, HasDerivAt A (A' b) b
  cost_hasDeriv : ∀ b ∈ Ioo lo hi, HasDerivAt C (C' b) b
  success_derivative_pos : ∀ b ∈ Ioo lo hi, 0 < A' b
  supported : ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v,
    v ∈ E → a.routeCount = n → a.bid ∈ Ioo lo hi →
      ((problem Γ i).outcome a).success = A a.bid ∧
      a.bid * tariff.expected ((problem Γ i).outcome a) +
        Γ.g * ((problem Γ i).outcome a).charge Γ.G = C a.bid ∧
      v * A' a.bid = C' a.bid

noncomputable def exclusiveTariffEnvelope (Γ : FiniteGame m n c Seed)
    (tariff : UserTariff) (i : Fin m) (v : ℝ) : ℝ :=
  sSup (Set.range (exclusiveTariffPayoff Γ tariff i v))

private theorem exclusiveTariffPayoff_upper (Γ : FiniteGame m n c Seed)
    (tariff : UserTariff) (ht : tariff.Allowed) (i : Fin m)
    (v : ℝ) (a : JointAction n) :
    exclusiveTariffPayoff Γ tariff i v a ≤ max v 0 := by
  let μ := (problem Γ i).outcome a
  have hc : 0 ≤ tariff.expected μ :=
    μ.expect_nonneg (fun r => tariff.charge_nonneg ht r.val)
  have hG : 0 ≤ μ.charge Γ.G := μ.charge_nonneg Γ.G
  have hs : v * μ.success ≤ max v 0 := by
    by_cases hv : 0 ≤ v
    · rw [max_eq_left hv]
      nlinarith [μ.success_le_one]
    · rw [max_eq_right (le_of_not_ge hv)]
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hv) μ.success_nonneg
  have h1 := mul_nonneg a.bid_nonneg hc
  have h2 := mul_nonneg Γ.g_nonneg hG
  dsimp only [exclusiveTariffPayoff]
  change v * μ.success - a.bid * tariff.expected μ - Γ.g * μ.charge Γ.G ≤ max v 0
  linarith

private theorem exclusiveTariff_range_bounded (Γ : FiniteGame m n c Seed)
    (tariff : UserTariff) (ht : tariff.Allowed) (i : Fin m) (v : ℝ) :
    BddAbove (Set.range (exclusiveTariffPayoff Γ tariff i v)) := by
  refine ⟨max v 0, ?_⟩
  rintro _ ⟨a, rfl⟩
  exact exclusiveTariffPayoff_upper Γ tariff ht i v a

private theorem exclusiveTariff_range_nonempty (Γ : FiniteGame m n c Seed)
    (tariff : UserTariff) (i : Fin m) (v : ℝ) :
    (Set.range (exclusiveTariffPayoff Γ tariff i v)).Nonempty :=
  ⟨_, ⟨Interim.abstain n, rfl⟩⟩

theorem exclusiveTariff_action_le_envelope (Γ : FiniteGame m n c Seed)
    (tariff : UserTariff) (ht : tariff.Allowed) (i : Fin m) (v : ℝ) (a : JointAction n) :
    exclusiveTariffPayoff Γ tariff i v a ≤ exclusiveTariffEnvelope Γ tariff i v :=
  le_csSup (exclusiveTariff_range_bounded Γ tariff ht i v) ⟨a, rfl⟩

theorem exclusiveTariff_bestResponse_attains (Γ : FiniteGame m n c Seed)
    (tariff : UserTariff) (ht : tariff.Allowed) (i : Fin m) {v : ℝ} {a : JointAction n}
    (ha : ExclusiveTariffBestResponse Γ tariff i v a) :
    exclusiveTariffPayoff Γ tariff i v a = exclusiveTariffEnvelope Γ tariff i v := by
  apply le_antisymm (exclusiveTariff_action_le_envelope Γ tariff ht i v a)
  apply csSup_le (exclusiveTariff_range_nonempty Γ tariff i v)
  rintro _ ⟨b, rfl⟩
  exact ha b

theorem exclusiveTariffEnvelope_convex (Γ : FiniteGame m n c Seed)
    (tariff : UserTariff) (ht : tariff.Allowed) (i : Fin m) :
    ConvexOn ℝ Set.univ (exclusiveTariffEnvelope Γ tariff i) := by
  refine ⟨convex_univ, ?_⟩
  intro v _ w _ s t hs ht0 hst
  change exclusiveTariffEnvelope Γ tariff i (s * v + t * w) ≤
    s * exclusiveTariffEnvelope Γ tariff i v + t * exclusiveTariffEnvelope Γ tariff i w
  apply csSup_le (exclusiveTariff_range_nonempty Γ tariff i (s * v + t * w))
  rintro _ ⟨a, rfl⟩
  have he : exclusiveTariffPayoff Γ tariff i (s * v + t * w) a =
      s * exclusiveTariffPayoff Γ tariff i v a + t * exclusiveTariffPayoff Γ tariff i w a := by
    have he' : t = 1 - s := by linarith
    rw [he']
    unfold exclusiveTariffPayoff
    ring
  rw [he]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (exclusiveTariff_action_le_envelope Γ tariff ht i v a) hs)
    (mul_le_mul_of_nonneg_left (exclusiveTariff_action_le_envelope Γ tariff ht i w a) ht0)

theorem exclusiveTariff_supporting_line (Γ : FiniteGame m n c Seed)
    (tariff : UserTariff) (ht : tariff.Allowed) (i : Fin m) {v : ℝ} {a : JointAction n}
    (ha : ExclusiveTariffBestResponse Γ tariff i v a) (w : ℝ) :
    exclusiveTariffEnvelope Γ tariff i v +
      (w - v) * ((problem Γ i).outcome a).success ≤ exclusiveTariffEnvelope Γ tariff i w := by
  have h := exclusiveTariff_action_le_envelope Γ tariff ht i w a
  have he : exclusiveTariffPayoff Γ tariff i w a =
      exclusiveTariffPayoff Γ tariff i v a +
        (w - v) * ((problem Γ i).outcome a).success := by
    unfold exclusiveTariffPayoff
    ring
  rw [he, exclusiveTariff_bestResponse_attains Γ tariff ht i ha] at h
  exact h

def narrowBestReplyGraph (Γ : FiniteGame m n c Seed) (tariff : UserTariff)
    (i : Fin m) (E : Set ℝ) (lo hi : ℝ) (A A' C' : ℝ → ℝ) (v b : ℝ) : Prop :=
  v ∈ E ∧ ∃ a : JointAction n, a.bid = b ∧ a.routeCount = n ∧ b ∈ Ioo lo hi ∧
    ExclusiveTariffBestResponse Γ tariff i v a ∧
    ((problem Γ i).outcome a).success = A b ∧ v * A' b = C' b

private theorem narrowBestReplyGraph_mem (Γ : FiniteGame m n c Seed)
    (tariff : UserTariff) (i : Fin m) (E : Set ℝ) (lo hi : ℝ) (A A' C' : ℝ → ℝ)
    {v b : ℝ} (h : narrowBestReplyGraph Γ tariff i E lo hi A A' C' v b) :
    b ∈ Ioo lo hi := by
  rcases h with ⟨_, a, _, _, hb, _⟩
  exact hb

theorem narrowBestReplyGraph_ordered (Γ : FiniteGame m n c Seed)
    (tariff : UserTariff) (ht : tariff.Allowed) (i : Fin m)
    (E : Set ℝ) (lo hi : ℝ) (A C A' C' : ℝ → ℝ)
    (hd : FiniteBroadcastDifferential Γ tariff i E lo hi A C A' C') :
    Exclusive.Narrow.OrderedGraph.Ordered
      (narrowBestReplyGraph Γ tariff i E lo hi A A' C') := by
  have hstrict := Exclusive.Narrow.OrderedGraph.strictMonoOn_of_positive_derivative
    hd.success_hasDeriv hd.success_derivative_pos
  intro v w b d hv hw hvw
  rcases hv with ⟨_, x, hxb, _, hb, hx, hxA, _⟩
  rcases hw with ⟨_, y, hyd, _, hdm, hy, hyA, _⟩
  have hsubv := exclusiveTariff_supporting_line Γ tariff ht i hx w
  have hsubw := exclusiveTariff_supporting_line Γ tariff ht i hy v
  have hs := FCAppendix.Subgradient.ordered hvw hsubv hsubw
  rw [hxA, hyA] at hs
  by_contra hnot
  exact (not_lt_of_ge hs) (hstrict hdm hb (lt_of_not_ge hnot))

theorem narrowBestReplyGraph_same_bid (Γ : FiniteGame m n c Seed)
    (tariff : UserTariff) (i : Fin m) (E : Set ℝ) (lo hi : ℝ) (A C A' C' : ℝ → ℝ)
    (hd : FiniteBroadcastDifferential Γ tariff i E lo hi A C A' C')
    {v w b : ℝ}
    (hv : narrowBestReplyGraph Γ tariff i E lo hi A A' C' v b)
    (hw : narrowBestReplyGraph Γ tariff i E lo hi A A' C' w b) : v = w := by
  rcases hv with ⟨_, x, _, _, hb, _, _, hvf⟩
  rcases hw with ⟨_, y, _, _, _, _, _, hwf⟩
  apply sub_eq_zero.mp
  exact (mul_eq_zero.mp (show (v - w) * A' b = 0 by nlinarith [hvf, hwf])).resolve_right
    (hd.success_derivative_pos b hb).ne'

theorem ae_narrowBestReplyGraph (Γ : FiniteGame m n c Seed)
    (tariff : UserTariff) (hu : ExclusiveTariffUsersOptimal Γ tariff) (i : Fin m)
    (E : Set ℝ) (hE : MeasurableSet E) (lo hi : ℝ) (A C A' C' : ℝ → ℝ)
    (hd : FiniteBroadcastDifferential Γ tariff i E lo hi A C A' C')
    (hband : ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v,
      v ∈ E → a.routeCount = n ∧ a.bid ∈ Ioo lo hi) :
    ∀ᵐ v ∂Γ.F.restrict E, ∀ᵐ a ∂Γ.σ v,
      narrowBestReplyGraph Γ tariff i E lo hi A A' C' v a.bid := by
  filter_upwards [ae_restrict_of_ae (hu i), ae_restrict_of_ae hd.supported,
    ae_restrict_of_ae hband, ae_restrict_mem hE] with v hv hdv hbv hvE
  filter_upwards [hv, hdv, hbv] with a ha hda hba
  obtain ⟨har, hab⟩ := hba hvE
  obtain ⟨hA, _, hFOC⟩ := hda hvE har hab
  exact ⟨hvE, a, rfl, har, hab, ha, hA, hFOC⟩

theorem finite_narrow_purity_and_order (Γ : FiniteGame m n c Seed)
    (tariff : UserTariff) (ht : tariff.Allowed)
    (hu : ExclusiveTariffUsersOptimal Γ tariff) (i : Fin m)
    (E : Set ℝ) (hE : MeasurableSet E) [NullSingletonClass (Γ.F.restrict E)]
    (lo hi : ℝ) (hlohi : lo < hi) (A C A' C' : ℝ → ℝ)
    (hd : FiniteBroadcastDifferential Γ tariff i E lo hi A C A' C')
    (hband : ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v,
      v ∈ E → a.routeCount = n ∧ a.bid ∈ Ioo lo hi) :
    ∃ β : ℝ → ℝ, Monotone β ∧ Measurable β ∧
      (∀ v, β v ∈ Icc lo hi) ∧
      (∀ᵐ v ∂Γ.F.restrict E, ∀ᵐ a ∂Γ.σ v, a.bid = β v) ∧
      (∀ᵐ v ∂Γ.F.restrict E,
        narrowBestReplyGraph Γ tariff i E lo hi A A' C' v (β v)) ∧
      (∀ v w, narrowBestReplyGraph Γ tariff i E lo hi A A' C' v (β v) →
        narrowBestReplyGraph Γ tariff i E lo hi A A' C' w (β w) →
        v < w → β v < β w) := by
  classical
  let R := narrowBestReplyGraph Γ tariff i E lo hi A A' C'
  have hR := narrowBestReplyGraph_ordered Γ tariff ht i E lo hi A C A' C' hd
  have hl : ∀ ⦃v b⦄, R v b → lo ≤ b := fun {_} {_} h =>
    (narrowBestReplyGraph_mem Γ tariff i E lo hi A A' C' h).1.le
  have hh : ∀ ⦃v b⦄, R v b → b ≤ hi := fun {_} {_} h =>
    (narrowBestReplyGraph_mem Γ tariff i E lo hi A A' C' h).2.le
  let β := Exclusive.Narrow.OrderedGraph.representative R lo
  have hmono : Monotone β :=
    Exclusive.Narrow.OrderedGraph.representative_monotone hlohi.le hh
  have hgraph := ae_narrowBestReplyGraph Γ tariff hu i E hE lo hi A C A' C' hd hband
  have hpure : ∀ᵐ v ∂Γ.F.restrict E, ∀ᵐ a ∂Γ.σ v, a.bid = β v := by
    filter_upwards [hgraph,
      (Exclusive.Narrow.OrderedGraph.branching_countable hR).ae_notMem (Γ.F.restrict E)]
      with v hv hnot
    filter_upwards [hv] with a ha
    exact (Exclusive.Narrow.OrderedGraph.representative_eq hlohi.le hl hh hR hnot ha).symm
  have hβgraph : ∀ᵐ v ∂Γ.F.restrict E, R v (β v) := by
    filter_upwards [hgraph, hpure] with v hv hp
    letI : IsMarkovKernel Γ.σ := Γ.hσ
    obtain ⟨a, ha, he⟩ := (hv.and hp).exists
    simpa only [he] using ha
  refine ⟨β, hmono, hmono.measurable,
    Exclusive.Narrow.OrderedGraph.representative_mem hlohi.le hh, hpure, hβgraph, ?_⟩
  intro v w hv hw hvw
  have hle := hR hv hw hvw
  apply lt_of_le_of_ne hle
  intro he
  have hvw' : v = w := narrowBestReplyGraph_same_bid Γ tariff i E lo hi A C A' C' hd
    hv (by simpa only [he] using hw)
  exact hvw.ne hvw'

theorem conditional_bidLaw_dirac (Γ : FiniteGame m n c Seed)
    (E : Set ℝ) (β : ℝ → ℝ)
    (hpure : ∀ᵐ v ∂Γ.F.restrict E, ∀ᵐ a ∂Γ.σ v, a.bid = β v) :
    ∀ᵐ v ∂Γ.F.restrict E,
      Measure.map (fun a : JointAction n => a.bid) (Γ.σ v) = Measure.dirac (β v) := by
  letI : IsMarkovKernel Γ.σ := Γ.hσ
  filter_upwards [hpure] with v hv
  calc
    _ = Measure.map (fun _ : JointAction n => β v) (Γ.σ v) := Measure.map_congr hv
    _ = Measure.dirac (β v) := by simp

theorem conditional_actionLaw_dirac (Γ : FiniteGame m n c Seed)
    (E : Set ℝ) (β : ℝ → ℝ) (hβ : ∀ v, 0 ≤ β v)
    (hpure : ∀ᵐ v ∂Γ.F.restrict E, ∀ᵐ a ∂Γ.σ v, a.bid = β v)
    (hfull : ∀ᵐ v ∂Γ.F.restrict E, ∀ᵐ a ∂Γ.σ v, a.routeCount = n) :
    ∀ᵐ v ∂Γ.F.restrict E, Γ.σ v = Measure.dirac (fullBid n (β v) (hβ v)) := by
  letI : IsMarkovKernel Γ.σ := Γ.hσ
  filter_upwards [hpure, hfull] with v hv hr
  have he : ∀ᵐ a ∂Γ.σ v, a = fullBid n (β v) (hβ v) := by
    filter_upwards [hv, hr] with a hba hra
    rcases a with ⟨b, hb, k, hk⟩
    change b = β v at hba
    change k = n at hra
    subst b
    subst k
    rfl
  calc
    Γ.σ v = Measure.map id (Γ.σ v) := Measure.map_id.symm
    _ = Measure.map (fun _ : JointAction n => fullBid n (β v) (hβ v)) (Γ.σ v) :=
      Measure.map_congr he
    _ = Measure.dirac (fullBid n (β v) (hβ v)) := by simp

theorem finite_narrow_bidLaw_no_atoms (Γ : FiniteGame m n c Seed)
    (tariff : UserTariff) (i : Fin m) (E : Set ℝ) (hE : MeasurableSet E)
    [NullSingletonClass (Γ.F.restrict E)]
    (lo hi : ℝ) (A C A' C' : ℝ → ℝ)
    (hd : FiniteBroadcastDifferential Γ tariff i E lo hi A C A' C')
    (hband : ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v,
      v ∈ E → a.routeCount = n ∧ a.bid ∈ Ioo lo hi) :
    ∀ b : ℝ, (Measure.map (fun x : ℝ × JointAction n => x.2.bid)
      ((Γ.F.restrict E) ⊗ₘ Γ.σ)) {b} = 0 := by
  letI : IsProbabilityMeasure Γ.F := Γ.hF
  letI : IsMarkovKernel Γ.σ := Γ.hσ
  intro b
  have hnone : ∀ᵐ v ∂Γ.F.restrict E, ∀ᵐ a ∂Γ.σ v, a.bid ≠ b := by
    filter_upwards [ae_restrict_of_ae hd.supported, ae_restrict_of_ae hband,
      ae_restrict_mem hE,
      (Set.countable_singleton (C' b / A' b)).ae_notMem (Γ.F.restrict E)]
      with v hv hb hvE hvne
    filter_upwards [hv, hb] with a ha hab
    intro he
    obtain ⟨har, hai⟩ := hab hvE
    obtain ⟨_, _, hFOC⟩ := ha hvE har hai
    rw [he] at hFOC hai
    have hvpin : v = C' b / A' b :=
      (eq_div_iff (hd.success_derivative_pos b hai).ne').mpr hFOC
    exact hvne (by simpa using hvpin)
  have hmeas : Measurable (fun x : ℝ × JointAction n => x.2.bid) :=
    (measurable_bid n).comp measurable_snd
  have hjoint : ∀ᵐ x ∂((Γ.F.restrict E) ⊗ₘ Γ.σ), x.2.bid ≠ b :=
    Measure.ae_compProd_of_ae_ae
      ((measurableSet_singleton b).preimage hmeas).compl hnone
  have hz : ((Γ.F.restrict E) ⊗ₘ Γ.σ) {x : ℝ × JointAction n | x.2.bid = b} = 0 := by
    simpa only [ae_iff, not_not] using hjoint
  rw [Measure.map_apply hmeas (measurableSet_singleton b)]
  exact hz

theorem ae_common_tail_changing_identities {μ : Measure ℝ} (M : ℕ → ℕ) (t₀ : ℕ)
    (P : (t : ℕ) → Fin (M t) → ℝ → Prop)
    (hP : ∀ t, t₀ ≤ t → ∀ i, ∀ᵐ v ∂μ, P t i v) :
    ∀ᵐ v ∂μ, ∀ t, t₀ ≤ t → ∀ i, P t i v := by
  apply ae_all_iff.mpr
  intro t
  by_cases ht : t₀ ≤ t
  · filter_upwards [ae_all_iff.mpr (hP t ht)] with v hv _ using hv
  · exact Eventually.of_forall (fun _ hv => False.elim (ht hv))

end FCAppendix.Bayes
