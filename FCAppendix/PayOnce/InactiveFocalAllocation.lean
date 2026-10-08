import FCAppendix.PayOnce.DummyFocalLimit
import FCAppendix.PayOnce.InactivePositiveRoot

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.DummyKernel PayOnce.CompactifiedBidLaws
variable {N C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_focal_allocation_limit
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
      ∀ x : ℕ → ℝ, (∀ t, 0 < x t) →
        Tendsto (fun t => ∫ r : Fin (N t) → ℝ,
          |allocation (k+1) (C t) (by omega) r (x t)-kernel (k+1) (x t) L|
            ∂Measure.pi (fun _ : Fin (N t) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))) atTop (𝓝 0) := by
  have hNpos t : 0 < N t := by have := hc t; have := hcm t; omega
  have hM : Tendsto (fun t => N t+1) atTop atTop := (tendsto_add_atTop_nat 1).comp hN
  have hρM : Tendsto (fun t => (C t:ℝ)/((N t+1:ℕ):ℝ)) atTop (𝓝 ρ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hρ
  obtain ⟨_,L,hL,huniq⟩ := payOnce_inactive_positive_capacity_root Γ hk hc hcm hM hA hG hu B hB hsym hvalue hatom hinactive
    F hF hg hρM hρb hweak
  refine ⟨L,⟨hL.1,hL.2,?_⟩,fun T hT => huniq T ⟨hT.1,hT.2.1⟩⟩
  intro x hx
  let G : ℕ → ProbabilityMeasure ℝ := fun t => BidScaling.realBidLaw (Γ t)
  have hraw t : scaledLaw (G t) 1 = bidLaw (Γ t) := by
    apply Subtype.ext
    change (G t : Measure ℝ).map (fun b : ℝ => ENNReal.ofReal (b/1)) = _
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
  exact tendsto_focal_allocation_kernel_error N hNpos hN (by omega) G
    (fun t => ae_realEffectiveBidLaw_nonneg (Γ t)) hweakRaw hL.1 hL.2 (fun T hT he => huniq T ⟨hT,he⟩) hcap x hx

end FCAppendix.Bayes
