import FCAppendix.PayOnce.CompactIdentification
import FCAppendix.PayOnce.IdentificationTruncation
import FCAppendix.PayOnce.InteriorBidBlock
import FCAppendix.PayOnce.ZeroAtomExclusion

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.AnalyticalKernel PayOnce.AnalyticalRareSuccess PayOnce.CompactifiedBidLaws
variable {N C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_bid_graph_limit
    (Γ : ∀ t, FiniteGame (N t+1) (k+1) (C t) Seed)
    (hk : 1 ≤ k) (hc : ∀ t, 0 < C t) (hcm : ∀ t, C t < N t+1)
    (hN : Tendsto N atTop atTop)
    (hA : ∀ t, (Γ t).A = Schedule.once (k+1)) (hG : ∀ t, (Γ t).G = Schedule.once (k+1))
    (hu : ∀ t, UsersOptimal (Γ t)) (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, PosteriorProposerOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t)) (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    (F : Measure ℝ) [IsProbabilityMeasure F] [NullSingletonClass F]
    (hF : ∀ t, (Γ t).F = F) {g : ℝ} (hg : ∀ t, (Γ t).g = g)
    (hactive : ∀ᵐ v ∂F, g < v)
    {ρ : ℝ} (hρ : Tendsto (fun t => (C t : ℝ)/(N t+1)) atTop (𝓝 ρ))
    (hρb : ρ ∈ Ioo (0:ℝ) 1) {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => bidLaw (Γ t)) atTop (𝓝 G₀)) :
    ∃! L, 0 < L ∧ KernelDemand.demand (k+1) (G₀ : Measure ENNReal) L = ρ ∧
      ∀ f : ℝ × ℝ → ℝ, Continuous f →
        (∀ w : ℝ, 0 ≤ w → f (w,Limit.bidStar (k+1) L w) = 0) →
        ∀ δ : ℝ, 0 < δ →
          Tendsto (fun t => ((Γ t).F ⊗ₘ (Γ t).σ)
            {x | δ ≤ f (x.1-g,x.2.bid)}) atTop (𝓝 0) := by
  have hNpos t : 0 < N t := by have := hc t; have := hcm t; omega
  have hM : Tendsto (fun t => N t+1) atTop atTop := (tendsto_add_atTop_nat 1).comp hN
  have hρM : Tendsto (fun t => (C t:ℝ)/((N t+1:ℕ):ℝ)) atTop (𝓝 ρ) := by
    simpa only [Nat.cast_add,Nat.cast_one] using hρ
  obtain ⟨_,L,hroot,hunique⟩ := payOnce_positive_capacity_root Γ hk hc hcm hM hA hG hu B hB hsym hatom
    F hF hg hactive hρM hρb hweak
  obtain ⟨L',hblock,_⟩ := payOnce_interior_bid_window Γ hk hc hcm hM hA hG hu B hB hsym hatom
    F hF hg hactive hρM hρb hweak
  have heL : L' = L := hunique L' ⟨hblock.1,hblock.2.1⟩
  subst L'
  obtain ⟨a,z,ha,haz,hz,hwin⟩ := hblock.2.2.2
  have hvalue t : PositiveValueAtomless (Γ t) := by
    intro v _
    rw [hF t]
    exact measure_singleton v
  have hfull t := ae_full_routes_positive_bids_of_active (Γ t) (hc t) (hcm t) (hA t) (hG t)
    (hu t) (B t) (hB t) (hsym t) (hvalue t) (by simpa only [hF t,hg t] using hactive)
  have hroute t := (hfull t).mono fun _ hz => hz.2
  have hbid t := (hfull t).mono fun _ hz => hz.1
  let G : ℕ → ProbabilityMeasure ℝ := fun t => ⟨realBidLaw (Γ t),inferInstance⟩
  have hraw t : scaledLaw (G t) 1 = bidLaw (Γ t) := by
    apply Subtype.ext
    change (realBidLaw (Γ t)).map (fun b : ℝ => ENNReal.ofReal (b/1)) = _
    simp only [div_one]
    exact (compactifiedBidLaw_eq_map_realBidLaw (Γ t) (by omega) (hroute t)).symm
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
    exists_ae_scaled_analytical_comparisons (Γ t) hk (hcm t).le (hA t) (hG t)
      (hu t) (B t) (hB t) (hsym t) (hatom t) (hroute t) (hbid t) ⟨0,by omega⟩ 1 zero_lt_one
  have hzero := payOnce_limit_no_zero_atom Γ hk hc hcm hN hA hG hu B hB hsym hatom
    F hF hg hactive hρ hρb hweak
  let P := fun t => (Γ t).F ⊗ₘ (Γ t).σ
  have hpositive t : ∀ᵐ x ∂P t, g < x.1 := by
    have hv : ∀ᵐ v ∂(Γ t).F, g < v := by rw [hF t]; exact hactive
    exact Measure.ae_compProd_of_ae_fst (Γ t).σ (measurableSet_lt measurable_const measurable_id) hv
  have hbound t : ∀ᵐ x ∂P t, 0 ≤ x.1-g ∧ x.2.bid ≤ x.1-g := by
    have hno := ae_no_overbid_compProd_onPath (Γ t) (by omega) (hc t)
      (posterior_isAEEquilibrium (Γ t) (hu t) (B t) (hB t))
    filter_upwards [hno,hroute t,hpositive t] with x hx hr hv
    have hh := hx (by rw [hr]; omega)
    rw [hg t,max_eq_left (sub_pos.mpr hv).le] at hh
    exact ⟨(sub_pos.mpr hv).le,hh⟩
  have htail : ∀ q : ENNReal, 0 < q → ∃ R : ℝ, ∀ t, P t {x | R < x.1-g} ≤ q := by
    intro q hq
    by_cases hqtop : q = ⊤
    · exact ⟨0,fun _ => hqtop ▸ le_top⟩
    have hqR : 0 < q.toReal := ENNReal.toReal_pos hq.ne' hqtop
    obtain ⟨R,hR⟩ := ((TailQuantile.tail_tendsto_zero F).eventually_lt_const hqR).exists
    refine ⟨R-g,fun t => ?_⟩
    have he : P t {x | R-g < x.1-g} = F (Ioi R) := by
      have hset : {x : ℝ × JointAction (k+1) | R-g < x.1-g} = Prod.fst ⁻¹' Ioi R := by
        ext x
        simp only [mem_setOf_eq,mem_preimage,mem_Ioi,sub_lt_sub_iff_right]
      rw [hset,← Measure.fst_apply measurableSet_Ioi,Measure.fst_compProd,hF t]
    rw [he]
    exact (ENNReal.toReal_le_toReal (measure_ne_top F _) hqtop).mp hR.le
  have hmap t : (bidLaw (Γ t) : Measure ENNReal) =
      (P t).map (fun x => ENNReal.ofReal x.2.bid) := by
    rw [compactifiedBidLaw_eq_map_realBidLaw (Γ t) (by omega) (hroute t),realBidLaw_eq_action_map]
    have hm : Measurable (fun x : ℝ × JointAction (k+1) => x.2.bid) :=
      (measurable_bid (k+1)).comp measurable_snd
    rw [Measure.map_map ENNReal.measurable_ofReal hm]
    rfl
  have hgood t : ∀ᵐ x ∂P t,
      x.2.bid ∈ regularSupportedSet (ι := Fin (N t)) (k+1) (C t) (G t : Measure ℝ) (T t) ∧
      ∀ y ∈ T t, (x.1-g-y)*coverage (k+1) (C t) (by omega) (by simpa using (hcm t).le)
          (Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))) y ≤
        (x.1-g-x.2.bid)*coverage (k+1) (C t) (by omega) (by simpa using (hcm t).le)
          (Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))) x.2.bid := by
    filter_upwards [hcompare t] with x hx
    refine ⟨?_,?_⟩
    · simpa only [div_one,rescaledRealLaw_one,Set.image_id',G] using hx.2.1
    · dsimp only [G,ProbabilityMeasure.coe_mk]
      rw [← hg t]
      exact hx.2.2
  refine ⟨L,⟨hroot.1,hroot.2,?_⟩,fun U hU => hunique U ⟨hU.1,hU.2.1⟩⟩
  intro f hf hgraph δ hδ
  apply tendsto_defect_mass_zero_of_compact_blocks P (fun _ x => x.2.bid) (fun _ x => x.1-g)
    (fun _ => (measurable_bid (k+1)).comp measurable_snd) hbound htail
    (fun t => bidLaw (Γ t)) G₀ hmap hweak hzero (fun t => {x | δ ≤ f (x.1-g,x.2.bid)})
  intro ε hε R
  exact tendsto_compact_identification_defect_zero N hNpos hN (by omega) P
    (fun _ x => x.2.bid) (fun _ x => x.1-g) (fun _ => (measurable_bid (k+1)).comp measurable_snd)
    G (fun t => realBidLaw_eq_action_map (Γ t)) (fun t => ae_realBidLaw_pos (Γ t) (hbid t))
    hweakRaw hρb.1 hroot.1 hroot.2 (fun U hU he => hunique U ⟨hU,he⟩)
    (fun t => by simpa using (hcm t).le) hcap ha haz hz hwin T hgood f hf hgraph hε hδ

end FCAppendix.Bayes
