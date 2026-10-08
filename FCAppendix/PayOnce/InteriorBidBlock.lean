import FCAppendix.PayOnce.ClosedSaturatedTail
import FCAppendix.PayOnce.ActualVanishingWindow

namespace FCAppendix.PayOnce.KernelDemand
open MeasureTheory ProbabilityTheory Filter Topology Set

theorem interior_bid_mass_pos {n : ℕ} (hn : 2 ≤ n) (G : ProbabilityMeasure ENNReal)
    {L ρ : ℝ} (hL : 0 < L) (hρ : 0 < ρ) (hD : demand n (G : Measure ENNReal) L = ρ)
    (hsat : (G : Measure ENNReal) (Ici (ENNReal.ofReal ((n:ℝ)*L))) = 0) :
    0 < (G : Measure ENNReal) (Ioo (ENNReal.ofReal L) (ENNReal.ofReal ((n:ℝ)*L))) := by
  have htail : 0 < (G : Measure ENNReal) (Ioi (ENNReal.ofReal L)) := by
    have hh := demand_le_tail_mass hn G hL
    rw [hD] at hh
    exact (ENNReal.toReal_pos_iff.mp (hρ.trans_le hh)).1
  have hsub : Ioi (ENNReal.ofReal L) ⊆
      Ioo (ENNReal.ofReal L) (ENNReal.ofReal ((n:ℝ)*L)) ∪ Ici (ENNReal.ofReal ((n:ℝ)*L)) := by
    intro b hb
    rcases lt_or_ge b (ENNReal.ofReal ((n:ℝ)*L)) with h | h
    · exact Or.inl ⟨hb,h⟩
    · exact Or.inr h
  have hh := (measure_mono (μ := (G : Measure ENNReal)) hsub).trans (measure_union_le _ _)
  rw [hsat, add_zero] at hh
  exact htail.trans_le hh

theorem exists_interior_bid_window {n : ℕ} (hn : 2 ≤ n) (G : ProbabilityMeasure ENNReal)
    {L ρ : ℝ} (hL : 0 < L) (hρ : 0 < ρ) (hD : demand n (G : Measure ENNReal) L = ρ)
    (hsat : (G : Measure ENNReal) (Ici (ENNReal.ofReal ((n:ℝ)*L))) = 0) :
    ∃ a b : ℝ, L < a ∧ a < b ∧ b < (n:ℝ)*L ∧
      0 < (G : Measure ENNReal) (Ioo (ENNReal.ofReal a) (ENNReal.ofReal b)) := by
  have hpos := interior_bid_mass_pos hn G hL hρ hD hsat
  obtain ⟨x,hx,hxs⟩ := Measure.nonempty_inter_support_of_pos hpos
  have hxtop : x ≠ ⊤ := ne_top_of_lt hx.2
  have hnL : 0 < (n:ℝ)*L := mul_pos (Nat.cast_pos.mpr (by omega)) hL
  have hLx : L < x.toReal := by
    have hh := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hxtop).mpr hx.1
    simpa only [ENNReal.toReal_ofReal hL.le] using hh
  have hxn : x.toReal < (n:ℝ)*L := by
    have hh := (ENNReal.toReal_lt_toReal hxtop ENNReal.ofReal_ne_top).mpr hx.2
    simpa only [ENNReal.toReal_ofReal hnL.le] using hh
  obtain ⟨a,hLa,hax⟩ := exists_between hLx
  obtain ⟨b,hxb,hbn⟩ := exists_between hxn
  refine ⟨a,b,hLa,hax.trans hxb,hbn,?_⟩
  apply (Measure.mem_support_iff_forall (μ := (G : Measure ENNReal)) x).mp hxs
  have ha : ENNReal.ofReal a < x := by
    rw [← ENNReal.ofReal_toReal hxtop]
    exact (ENNReal.ofReal_lt_ofReal_iff (hL.trans hLx)).mpr hax
  have hb : x < ENNReal.ofReal b := by
    rw [← ENNReal.ofReal_toReal hxtop]
    exact (ENNReal.ofReal_lt_ofReal_iff ((hL.trans hLx).trans hxb)).mpr hxb
  exact Ioo_mem_nhds ha hb

end FCAppendix.PayOnce.KernelDemand

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Filter Topology Set Game
open PayOnce

theorem payOnce_interior_bid_window
    {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (hk : 1 ≤ k) (hc : ∀ t, 0 < C t) (hcm : ∀ t, C t < M t)
    (hM : Tendsto M atTop atTop)
    (hA : ∀ t, (Γ t).A = Schedule.once (k+1)) (hG : ∀ t, (Γ t).G = Schedule.once (k+1))
    (hu : ∀ t, UsersOptimal (Γ t)) (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, PosteriorProposerOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t)) (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    (F : Measure ℝ) [IsProbabilityMeasure F] [NullSingletonClass F]
    (hF : ∀ t, (Γ t).F = F) {g : ℝ} (hg : ∀ t, (Γ t).g = g)
    (hactive : ∀ᵐ v ∂F, g < v)
    {ρ : ℝ} (hρ : Tendsto (fun t => (C t : ℝ)/(M t)) atTop (𝓝 ρ))
    (hρb : ρ ∈ Ioo (0:ℝ) 1) {G : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => CompactifiedBidLaws.bidLaw (Γ t)) atTop (𝓝 G)) :
    ∃! L, 0 < L ∧ KernelDemand.demand (k+1) (G : Measure ENNReal) L = ρ ∧
      (G : Measure ENNReal) (Ici (ENNReal.ofReal (((k+1:ℕ):ℝ)*L))) = 0 ∧
      ∃ a b : ℝ, L < a ∧ a < b ∧ b < ((k+1:ℕ):ℝ)*L ∧
        0 < (G : Measure ENNReal) (Ioo (ENNReal.ofReal a) (ENNReal.ofReal b)) := by
  obtain ⟨_,L,hL,huniq⟩ := payOnce_positive_capacity_root Γ hk hc hcm hM hA hG hu B hB hsym hatom
    F hF hg hactive hρ hρb hweak
  have hvalue t : PositiveValueAtomless (Γ t) := by
    intro v _
    rw [hF t]
    exact measure_singleton v
  have hfull t := ae_full_routes_positive_bids_of_active (Γ t) (hc t) (hcm t) (hA t) (hG t)
    (hu t) (B t) (hB t) (hsym t) (hvalue t) (by simpa only [hF t, hg t] using hactive)
  have hsat := actual_limit_closed_saturated_tail_zero Γ hk (fun t => (hc t).trans (hcm t))
    (fun t => (hcm t).le) hM hA hG hu B hB hsym hatom
    (fun t => (hfull t).mono fun _ hx => hx.2) (fun t => (hfull t).mono fun _ hx => hx.1)
    F hF hweak hρ hL.1 hL.2
  refine ⟨L,⟨hL.1,hL.2,hsat,?_⟩,fun T hT => huniq T ⟨hT.1,hT.2.1⟩⟩
  exact KernelDemand.exists_interior_bid_window (by omega) G hL.1 hρb.1 hL.2 hsat

end FCAppendix.Bayes
