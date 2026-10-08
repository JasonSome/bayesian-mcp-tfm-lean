import FCAppendix.PayOnce.GeneralParticipation
import FCAppendix.Finite.GameEnvelope

namespace FCAppendix.Interim.Problem

open MeasureTheory Set Filter Topology

variable {n : ℕ}

noncomputable def rightSuccess (P : Problem n) (v : ℝ) : ℝ :=
  derivWithin P.envelope (Ioi v) v

theorem rightSuccess_subgradient (P : Problem n) (v w : ℝ) :
    P.envelope v + (w - v) * P.rightSuccess v ≤ P.envelope w :=
  Subgradient.rightDeriv_subgradient P.envelope_convex (by simp) (by simp)

theorem rightSuccess_monotone (P : Problem n) : Monotone P.rightSuccess := by
  intro v w hvw
  rcases hvw.eq_or_lt with h | h
  · rw [h]
  · exact Subgradient.ordered h (P.rightSuccess_subgradient v w)
      (P.rightSuccess_subgradient w v)

theorem bestResponse_success_eq_rightSuccess (P : Problem n) {v : ℝ}
    (hv : ContinuousAt P.rightSuccess v) {a : Game.JointAction n}
    (ha : P.BestResponse v a) : (P.outcome a).success = P.rightSuccess v := by
  exact Subgradient.eq_of_continuousAt
    (x := v - 1) (y := v + 1)
    (fun u _ w _ => P.rightSuccess_subgradient u w) (by constructor <;> linarith)
    (fun w _ => P.supporting_line v a ha w) hv

theorem countable_exceptional_success (P : Problem n) :
    {v | ¬ ContinuousAt P.rightSuccess v}.Countable :=
  P.rightSuccess_monotone.countable_not_continuousAt

end FCAppendix.Interim.Problem

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Set Filter Topology

variable {m n c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem ae_positive_avoids_countable (Γ : FiniteGame m n c Seed)
    (hatom : PositiveValueAtomless Γ) {N : Set ℝ} (hN : N.Countable) :
    ∀ᵐ v ∂Γ.F, Γ.g < v → v ∉ N := by
  have he : N ∩ Ioi Γ.g = ⋃ v ∈ N ∩ Ioi Γ.g, ({v} : Set ℝ) := by
    ext v
    simp
  have hn : Γ.F (N ∩ Ioi Γ.g) = 0 := by
    rw [he]
    exact (measure_biUnion_null_iff (hN.mono inter_subset_left)).mpr
      fun v hv => hatom v hv.2
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hn] with v hv hpos hn
  exact hv ⟨hn, hpos⟩

noncomputable def pureBid (Γ : FiniteGame m n c Seed) (i : Fin m) (v : ℝ) : ℝ :=
  max (v - Γ.g - (problem Γ i).envelope v / (problem Γ i).rightSuccess v) 0

theorem measurable_pureBid (Γ : FiniteGame m n c Seed) (i : Fin m) :
    Measurable (pureBid Γ i) :=
  ((measurable_id.sub_const Γ.g).sub
    ((problem Γ i).envelope_lipschitzWith.continuous.measurable.div
      (problem Γ i).rightSuccess_monotone.measurable)).max measurable_const

theorem bestResponse_bid_eq_pureBid (Γ : FiniteGame m n c Seed)
    (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (i : Fin m) {v : ℝ} (hv : ContinuousAt (problem Γ i).rightSuccess v)
    {a : JointAction n} (ha : (problem Γ i).BestResponse v a)
    (hpos : 0 < ((problem Γ i).outcome a).success) : a.bid = pureBid Γ i v := by
  have hs := (problem Γ i).bestResponse_success_eq_rightSuccess hv ha
  have hp := ((problem Γ i).bestResponse_iff_attains v a).mp ha
  rw [payoff_once Γ hA hG, hs] at hp
  have hspos : 0 < (problem Γ i).rightSuccess v := by rwa [← hs]
  have he : (problem Γ i).envelope v / (problem Γ i).rightSuccess v = v - a.bid - Γ.g :=
    (div_eq_iff hspos.ne').mpr hp.symm
  unfold pureBid
  rw [he]
  have hb : v - Γ.g - (v - a.bid - Γ.g) = a.bid := by ring
  rw [hb, max_eq_left a.bid_nonneg]

theorem bestResponse_bid_le_of_positive (Γ : FiniteGame m n c Seed)
    (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (i : Fin m) {v w : ℝ} (hvw : v < w) {a b : JointAction n}
    (ha : (problem Γ i).BestResponse v a) (hb : (problem Γ i).BestResponse w b)
    (hs : 0 < ((problem Γ i).outcome a).success) (haV : a.bid < v - Γ.g) :
    a.bid ≤ b.bid := by
  have hsuccess := (problem Γ i).success_order v w hvw a b ha hb
  have hcomp := ha b
  rw [payoff_once Γ hA hG, payoff_once Γ hA hG] at hcomp
  by_contra hnot
  have hlt : b.bid < a.bid := lt_of_not_ge hnot
  have hsur : 0 < v - a.bid - Γ.g := by linarith
  have hmul := mul_le_mul_of_nonneg_left hsuccess hsur.le
  have hstrict := mul_pos (sub_pos.mpr hlt) hs
  nlinarith

theorem ae_positive_pure_bid (Γ : FiniteGame m (k + 1) c Seed)
    (hk : 1 ≤ k) (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k + 1)) (hG : Γ.G = Schedule.once (k + 1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hatom : PositiveValueAtomless Γ) (i : Fin m) :
    ∀ᵐ v ∂Γ.F, Γ.g < v → ∀ᵐ a ∂Γ.σ v,
      a.bid = pureBid Γ i v ∧ a.routeCount = k + 1 := by
  have hp := (po_broadcast Γ hk hc hcm hA hG hu B hB hsym hatom).1 i
  have hcont := ae_positive_avoids_countable Γ hatom
    (problem Γ i).countable_exceptional_success
  filter_upwards [hu i, hp, hcont] with v hv hp hvcont hpos
  have hv' : ContinuousAt (problem Γ i).rightSuccess v := by
    simpa only [mem_setOf_eq, not_not] using hvcont hpos
  filter_upwards [hv, hp] with a ha hpa
  obtain ⟨hb0, hbv, hpay, hr⟩ := hpa hpos
  have hs : 0 < ((problem Γ i).outcome a).success := by
    rw [payoff_once Γ hA hG] at hpay
    exact (mul_pos_iff.mp hpay).resolve_right (fun h => (CountLaw.success_nonneg _).not_gt h.2) |>.2
  exact ⟨bestResponse_bid_eq_pureBid Γ hA hG i hv' ha hs, hr⟩

theorem exists_positive_sorting_set (Γ : FiniteGame m (k + 1) c Seed)
    (hk : 1 ≤ k) (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k + 1)) (hG : Γ.G = Schedule.once (k + 1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hatom : PositiveValueAtomless Γ) (i : Fin m) :
    ∃ T : Set ℝ, (∀ᵐ v ∂Γ.F, Γ.g < v → v ∈ T) ∧ T ⊆ Ioi Γ.g ∧
      MonotoneOn (pureBid Γ i) T ∧
      ∀ v ∈ T, 0 < pureBid Γ i v ∧ pureBid Γ i v < v - Γ.g ∧
        ∀ᵐ a ∂Γ.σ v, a.bid = pureBid Γ i v ∧ a.routeCount = k + 1 := by
  let T : Set ℝ := {v | Γ.g < v ∧
    (∀ᵐ a ∂Γ.σ v, a.bid = pureBid Γ i v ∧ a.routeCount = k + 1) ∧
    ∃ a : JointAction (k + 1), (problem Γ i).BestResponse v a ∧
      0 < a.bid ∧ a.bid < v - Γ.g ∧
      0 < ((problem Γ i).outcome a).success ∧ a.bid = pureBid Γ i v}
  have hp := (po_broadcast Γ hk hc hcm hA hG hu B hB hsym hatom).1 i
  have hpure := ae_positive_pure_bid Γ hk hc hcm hA hG hu B hB hsym hatom i
  refine ⟨T, ?_, fun _ h => h.1, ?_, ?_⟩
  · filter_upwards [hu i, hp, hpure] with v hv hp hq hpos
    refine ⟨hpos, hq hpos, ?_⟩
    obtain ⟨a, ha, hpa, hqa⟩ := (hv.and (hp.and (hq hpos))).exists
    have hpay := (hpa hpos).2.2.1
    rw [payoff_once Γ hA hG] at hpay
    have hs : 0 < ((problem Γ i).outcome a).success :=
      (mul_pos_iff.mp hpay).resolve_right (fun h => (CountLaw.success_nonneg _).not_gt h.2) |>.2
    exact ⟨a, ha, (hpa hpos).1, (hpa hpos).2.1, hs, hqa.1⟩
  · intro v hv w hw hvw
    rcases hvw.eq_or_lt with he | hlt
    · rw [he]
    · obtain ⟨a, ha, _, hba, hsa, hea⟩ := hv.2.2
      obtain ⟨b, hb, _, _, _, heb⟩ := hw.2.2
      rw [← hea, ← heb]
      exact bestResponse_bid_le_of_positive Γ hA hG i hlt ha hb hsa hba
  · intro v hv
    obtain ⟨a, _, hba, hva, _, he⟩ := hv.2.2
    exact ⟨he ▸ hba, he ▸ hva, hv.2.1⟩

theorem exists_nonnegative_monotone_extension {f : ℝ → ℝ} {T : Set ℝ} {g : ℝ}
    (hmono : MonotoneOn f T) (hpos : ∀ v ∈ T, 0 ≤ f v)
    (hbound : ∀ v ∈ T, f v ≤ v - g) :
    ∃ F : ℝ → ℝ, Monotone F ∧ (∀ v, 0 ≤ F v) ∧
      (∀ v, F v ≤ max (v - g) 0) ∧ EqOn F f T := by
  let S : ℝ → Set ℝ := fun v => insert 0 (f '' (T ∩ Iic v))
  have hne (v : ℝ) : (S v).Nonempty := ⟨0, Or.inl rfl⟩
  have hbd (v : ℝ) : BddAbove (S v) := by
    refine ⟨max (v - g) 0, ?_⟩
    rintro z (hz | ⟨w, hw, rfl⟩)
    · simpa only [hz] using le_max_right (v - g) 0
    · exact (hbound w hw.1).trans ((sub_le_sub_right hw.2 g).trans (le_max_left _ _))
  refine ⟨fun v => sSup (S v), ?_, ?_, ?_, ?_⟩
  · intro v w hvw
    apply csSup_le (hne v)
    intro z hz
    apply le_csSup (hbd w)
    rcases hz with hz | ⟨u, hu, rfl⟩
    · exact Or.inl hz
    · exact Or.inr ⟨u, ⟨hu.1, hu.2.trans hvw⟩, rfl⟩
  · intro v
    exact le_csSup (hbd v) (Or.inl rfl)
  · intro v
    apply csSup_le (hne v)
    rintro z (hz | ⟨w, hw, rfl⟩)
    · simpa only [hz] using le_max_right (v - g) 0
    · exact (hbound w hw.1).trans ((sub_le_sub_right hw.2 g).trans (le_max_left _ _))
  · intro v hv
    apply le_antisymm
    · apply csSup_le (hne v)
      rintro z (hz | ⟨w, hw, rfl⟩)
      · simpa only [hz] using hpos v hv
      · exact hmono hw.1 hv hw.2
    · exact le_csSup (hbd v) (Or.inr ⟨v, ⟨hv, show v ≤ v from le_rfl⟩, rfl⟩)

theorem exists_monotone_pure_bid (Γ : FiniteGame m (k + 1) c Seed)
    (hk : 1 ≤ k) (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k + 1)) (hG : Γ.G = Schedule.once (k + 1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hatom : PositiveValueAtomless Γ) (i : Fin m) :
    ∃ bid : ℝ → ℝ, Monotone bid ∧ Measurable bid ∧
      (∀ v, 0 ≤ bid v ∧ bid v ≤ max (v - Γ.g) 0) ∧
      ∀ᵐ v ∂Γ.F, Γ.g < v → 0 < bid v ∧ bid v < v - Γ.g ∧
        ∀ᵐ a ∂Γ.σ v, a.bid = bid v ∧ a.routeCount = k + 1 := by
  obtain ⟨T, hT, _, hm, hs⟩ := exists_positive_sorting_set Γ hk hc hcm hA hG hu B hB hsym hatom i
  obtain ⟨bid, hb, hb0, hbnd, he⟩ := exists_nonnegative_monotone_extension hm
    (fun v hv => (hs v hv).1.le) (fun v hv => (hs v hv).2.1.le)
  refine ⟨bid, hb, hb.measurable, fun v => ⟨hb0 v, hbnd v⟩, ?_⟩
  filter_upwards [hT] with v hv hpos
  have hgood := hs v (hv hpos)
  rw [he (hv hpos)]
  exact hgood

end FCAppendix.Bayes
