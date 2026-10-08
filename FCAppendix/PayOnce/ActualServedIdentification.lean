import FCAppendix.PayOnce.ServedIdentification
import FCAppendix.PayOnce.InteriorBidBlock
import FCAppendix.PayOnce.ActualFocalAllocation

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.AnalyticalKernel PayOnce.AnalyticalRareSuccess PayOnce.CompactifiedBidLaws
variable {N C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_served_cluster_formulas
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
      ∃ A : ℕ → Set (ℝ × JointAction (k+1)),
        (∀ t, ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ), x ∈ A t) ∧
        ∀ φ : ℕ → ℕ, StrictMono φ → ∀ x : ℕ → ℝ × JointAction (k+1),
          (∀ t, x t ∈ A (φ t)) → ∀ b v : ℝ, L < b →
            Tendsto (fun t => (x t).2.bid) atTop (𝓝 b) →
            Tendsto (fun t => (x t).1) atTop (𝓝 v) →
            L < v-g ∧ kernel (k+1) b L = Limit.pStar (k+1) L (v-g) ∧
              b = L/H (k+1) (Limit.pStar (k+1) L (v-g)) ∧ b < ((k+1:ℕ):ℝ)*L := by
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
  let A := fun t => {x : ℝ × JointAction (k+1) |
    x.2.bid ∈ regularSupportedSet (ι := Fin (N t)) (k+1) (C t) (G t : Measure ℝ) (T t) ∧
    ∀ y ∈ T t, (x.1-g-y)*coverage (k+1) (C t) (by omega) (by simpa using (hcm t).le)
      (Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))) y ≤
      (x.1-g-x.2.bid)*coverage (k+1) (C t) (by omega) (by simpa using (hcm t).le)
        (Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))) x.2.bid}
  have hAa t : ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ), x ∈ A t := by
    filter_upwards [hcompare t] with x hx
    refine ⟨?_,?_⟩
    · simpa only [div_one,rescaledRealLaw_one,Set.image_id',G] using hx.2.1
    · dsimp only [G, ProbabilityMeasure.coe_mk]
      rw [← hg t]
      exact hx.2.2
  refine ⟨L,⟨hroot.1,hroot.2,A,hAa,?_⟩,fun U hU => hunique U ⟨hU.1,hU.2.1⟩⟩
  intro φ hφ x hx b v hb hxb hxv
  have hcSub : ∀ t, C (φ t) ≤ Fintype.card (Fin ((N ∘ φ) t))+1 := by
    intro t
    rw [Fintype.card_fin]
    exact (hcm (φ t)).le
  exact served_formulas_of_supported_IC_limit (N ∘ φ) (fun t => hNpos (φ t))
    (hN.comp hφ.tendsto_atTop) (by omega) (G ∘ φ)
    (fun t => ae_realBidLaw_pos (Γ (φ t)) (hbid (φ t))) (hweakRaw.comp hφ.tendsto_atTop)
    hcSub hroot.1 hroot.2
    (fun U hU he => hunique U ⟨hU,he⟩) (hcap.comp hφ.tendsto_atTop) ha haz hz hwin
    (fun t => (hx t).1) hb hxb (hxv.sub_const g) (fun t => (hx t).2)

end FCAppendix.Bayes
