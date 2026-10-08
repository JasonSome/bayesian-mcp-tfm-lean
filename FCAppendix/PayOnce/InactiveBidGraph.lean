import FCAppendix.PayOnce.DummyCompactIdentification
import FCAppendix.PayOnce.FixedAtomIdentificationTruncation
import FCAppendix.PayOnce.InactiveZeroAtomExclusion
import FCAppendix.PayOnce.InactiveInteriorBidWindow
import FCAppendix.PayOnce.InactiveScaledComparisons

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.DummyKernel PayOnce.DummyRareSuccess PayOnce.CompactifiedBidLaws
open PayOnce.AnalyticalKernel (rescaledRealLaw_one)
variable {N C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_bid_graph_limit
    (Γ : ∀ t, FiniteGame (N t+1) (k+1) (C t) Seed)
    (hk : 1 ≤ k) (hc : ∀ t, 0 < C t) (hcm : ∀ t, C t < N t+1)
    (hN : Tendsto N atTop atTop)
    (hA : ∀ t, (Γ t).A = Schedule.once (k+1)) (hG : ∀ t, (Γ t).G = Schedule.once (k+1))
    (hu : ∀ t, UsersOptimal (Γ t)) (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, PosteriorProposerOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t))
    (hvalue : ∀ t, PositiveValueAtomless (Γ t)) (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    (hinactive : ∀ t, InactiveAbstain (Γ t))
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : ∀ t, (Γ t).F = F) {g : ℝ} (hg : ∀ t, (Γ t).g = g)
    {ρ : ℝ} (hρ : Tendsto (fun t => (C t : ℝ)/(N t+1)) atTop (𝓝 ρ))
    (hρb : ρ ∈ Ioo (0:ℝ) (F.real (Ioi g))) {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => bidLaw (Γ t)) atTop (𝓝 G₀)) :
    ∃! L, 0 < L ∧ KernelDemand.demand (k+1) (G₀ : Measure ENNReal) L = ρ ∧
      ∀ f : ℝ × ℝ → ℝ, Continuous f →
        (∀ w : ℝ, 0 ≤ w → f (w,Limit.bidStar (k+1) L w) = 0) →
        ∀ δ : ℝ, 0 < δ →
          Tendsto (fun t => ((Γ t).F ⊗ₘ (Γ t).σ)
            {x | δ ≤ f (max (x.1-g) 0,effectiveBid x.2)}) atTop (𝓝 0) := by
  have hNpos t : 0 < N t := by have := hc t; have := hcm t; omega
  have hM : Tendsto (fun t => N t+1) atTop atTop := (tendsto_add_atTop_nat 1).comp hN
  have hρM : Tendsto (fun t => (C t:ℝ)/((N t+1:ℕ):ℝ)) atTop (𝓝 ρ) := by
    simpa only [Nat.cast_add,Nat.cast_one] using hρ
  obtain ⟨_,L,hroot,hunique⟩ := payOnce_inactive_positive_capacity_root Γ hk hc hcm hM hA hG hu B hB hsym hvalue hatom hinactive
    F hF hg hρM hρb hweak
  obtain ⟨L',hblock,_⟩ := payOnce_inactive_interior_bid_window Γ hk hc hcm hM hA hG hu B hB hsym hvalue hatom hinactive
    F hF hg hρM hρb hweak
  have heL : L' = L := hunique L' ⟨hblock.1,hblock.2.1⟩
  subst L'
  obtain ⟨a,z,ha,haz,hz,hwin⟩ := hblock.2.2.2
  let G : ℕ → ProbabilityMeasure ℝ := fun t => PayOnce.BidScaling.realBidLaw (Γ t)
  have hraw t : scaledLaw (G t) 1 = bidLaw (Γ t) := by
    apply Subtype.ext
    change (PayOnce.BidScaling.realBidLaw (Γ t) : Measure ℝ).map (fun b : ℝ => ENNReal.ofReal (b/1)) = _
    simp only [div_one]
    exact (compactifiedBidLaw_eq_map_effectiveBidLaw (Γ t)).symm
  have hweakRaw : Tendsto (fun t => scaledLaw (G t) 1) atTop (𝓝 G₀) := by
    simpa only [hraw] using hweak
  have hratio : Tendsto (fun t => ((N t:ℝ)+1)/N t) atTop (𝓝 1) := by
    have hh := (tendsto_const_nhds (x := (1:ℝ))).add
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hN))
    simp only [add_zero] at hh
    apply hh.congr
    intro t
    have hne : (N t:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hNpos t).ne'
    dsimp only [Function.comp_def]
    field_simp
  have hcap : Tendsto (fun t => (C t:ℝ)/N t) atTop (𝓝 ρ) := by
    have hh := hρ.mul hratio
    simp only [mul_one] at hh
    apply hh.congr
    intro t
    have hn : (0:ℝ) < N t := Nat.cast_pos.mpr (hNpos t)
    field_simp
  choose T hTm hTp hTae hcompare using fun t =>
    exists_ae_inactive_scaled_comparisons (Γ t) hk (hc t) (hcm t) (hA t) (hG t)
      (hu t) (B t) (hB t) (hsym t) (hvalue t) (hatom t) (hinactive t) ⟨0,by omega⟩ 1 zero_lt_one
  let P := fun t => (Γ t).F ⊗ₘ (Γ t).σ
  have hpart t := ae_effectiveBid_participation (Γ t) (hc t) (hcm t) (hA t) (hG t)
    (hu t) (B t) (hB t) (hsym t) (hvalue t)
  have hbound t : ∀ᵐ x ∂P t, 0 ≤ max (x.1-g) 0 ∧ effectiveBid x.2 ≤ max (x.1-g) 0 := by
    filter_upwards [hpart t] with x hx
    exact ⟨le_max_right _ _,by simpa only [hg t] using hx.2.1⟩
  have htail : ∀ q : ENNReal, 0 < q → ∃ R : ℝ, ∀ t, P t {x | R < max (x.1-g) 0} ≤ q := by
    intro q hq
    by_cases hqtop : q = ⊤
    · exact ⟨0,fun _ => hqtop ▸ le_top⟩
    have hqR : 0 < q.toReal := ENNReal.toReal_pos hq.ne' hqtop
    obtain ⟨R,hR⟩ := ((TailQuantile.tail_tendsto_zero F).eventually_lt_const hqR).exists
    refine ⟨max (R-g) 0,fun t => ?_⟩
    have hsub : {x : ℝ × JointAction (k+1) | max (R-g) 0 < max (x.1-g) 0} ⊆ Prod.fst ⁻¹' Ioi R := by
      intro x hx
      change max (R-g) 0 < max (x.1-g) 0 at hx
      rw [lt_max_iff] at hx
      rcases hx with hx | hx
      · have hh := (le_max_left (R-g) 0).trans_lt hx
        change R < x.1
        linarith
      · exact (not_lt_of_ge (le_max_right _ _) hx).elim
    have he : P t (Prod.fst ⁻¹' Ioi R) = F (Ioi R) := by
      rw [← Measure.fst_apply measurableSet_Ioi,Measure.fst_compProd,hF t]
    apply (measure_mono hsub).trans
    rw [he]
    exact (ENNReal.toReal_le_toReal (measure_ne_top F _) hqtop).mp hR.le
  have hzeroLimit := payOnce_inactive_limit_zero_atom Γ hk hc hcm hN hA hG hu B hB hsym hvalue hatom hinactive
    F hF hg hρ hρb hweak
  have hzero t : (bidLaw (Γ t) : Measure ENNReal) {0} = (G₀ : Measure ENNReal) {0} := by
    rw [hzeroLimit,compactifiedBidLaw_zero_mass (Γ t) (hc t) (hcm t) (hA t) (hG t)
      (hu t) (B t) (hB t) (hsym t) (hvalue t),hF t,hg t]
  have hmap t : (bidLaw (Γ t) : Measure ENNReal) =
      (P t).map (fun x => ENNReal.ofReal (effectiveBid x.2)) := by
    rw [compactifiedBidLaw_eq_map_effectiveBidLaw (Γ t),realEffectiveBidLaw_eq_action_map,
      Measure.map_map ENNReal.measurable_ofReal
        (show Measurable (fun x : ℝ × JointAction (k+1) => effectiveBid x.2) from
          (measurable_effectiveBid (k+1)).comp measurable_snd)]
    rfl
  have hgood t : ∀ᵐ x ∂P t, 0 < effectiveBid x.2 →
      effectiveBid x.2 ∈ regularSupportedSet (ι := Fin (N t)) (k+1) (C t) (G t : Measure ℝ) (T t) ∧
      ∀ y ∈ T t, (max (x.1-g) 0-y)*coverage (k+1) (C t) (by omega)
          (Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))) y ≤
        (max (x.1-g) 0-effectiveBid x.2)*coverage (k+1) (C t) (by omega)
          (Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))) (effectiveBid x.2) := by
    filter_upwards [hcompare t,hpart t] with x hx hp hpos
    have hv := hp.1.mp hpos
    have hfull := hp.2.2 hv
    have heff : effectiveBid x.2 = x.2.bid := by
      simp only [effectiveBid,hfull,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false]
    have hw : max (x.1-g) 0 = x.1-g := max_eq_left (sub_pos.mpr (by simpa only [hg t] using hv)).le
    constructor
    · simpa only [div_one,rescaledRealLaw_one,Set.image_id',G,heff] using (hx hv).2.1
    · simpa only [heff,hg t,hw] using (hx hv).2.2
  refine ⟨L,⟨hroot.1,hroot.2,?_⟩,fun U hU => hunique U ⟨hU.1,hU.2.1⟩⟩
  intro f hf hgraph δ hδ
  refine tendsto_defect_mass_zero_of_compact_blocks_fixed_atom P
    (fun _ x => effectiveBid x.2) (fun _ x => max (x.1-g) 0)
    (fun _ => (measurable_effectiveBid (k+1)).comp measurable_snd) hbound htail
    (fun t => bidLaw (Γ t)) G₀ hmap hweak hzero
    (fun t => {x | δ ≤ f (max (x.1-g) 0,effectiveBid x.2)}) ?_ ?_
  · intro t
    filter_upwards [hpart t] with x hp hE
    by_contra hnot
    have hb0 : effectiveBid x.2 = 0 := le_antisymm (le_of_not_gt hnot) (effectiveBid_nonneg _)
    have hw0 : max (x.1-g) 0 = 0 := by
      apply max_eq_right
      have hv : ¬ (Γ t).g < x.1 := fun hv => hnot (hp.1.mpr hv)
      rw [hg t] at hv
      exact sub_nonpos.mpr (le_of_not_gt hv)
    have hf0 := hgraph 0 le_rfl
    rw [Limit.bidStar_of_le hroot.1.le,max_self] at hf0
    change δ ≤ f (max (x.1-g) 0,effectiveBid x.2) at hE
    rw [hw0,hb0,hf0] at hE
    exact hδ.not_ge hE
  · intro ε hε R
    exact tendsto_compact_identification_defect_zero N hNpos hN (by omega) P
      (fun _ x => effectiveBid x.2) (fun _ x => max (x.1-g) 0)
      (fun _ => (measurable_effectiveBid (k+1)).comp measurable_snd)
      G (fun t => realEffectiveBidLaw_eq_action_map (Γ t))
      (fun t => ae_realEffectiveBidLaw_nonneg (Γ t)) hweakRaw hρb.1 hroot.1 hroot.2
      (fun U hU he => hunique U ⟨hU,he⟩) hcap ha haz hz hwin T hgood f hf hgraph hε hδ

end FCAppendix.Bayes
