import FCAppendix.PayOnce.InactiveEntryTailRatio
import FCAppendix.PayOnce.EntryHazard

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel PayOnce.EntryDerivativeLower
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

private theorem exponential_absorption {A x : ℝ} (hAx : 2*A ≤ x) :
    A*exp (-x) ≤ 1/2 := by
  have hx : x ≤ exp x := by linarith [add_one_le_exp x]
  have he : exp x*exp (-x) = 1 := by rw [← exp_add]; simp
  have h₁ := mul_le_mul_of_nonneg_right hAx (exp_nonneg (-x))
  have h₂ := mul_le_mul_of_nonneg_right hx (exp_nonneg (-x))
  nlinarith

theorem payOnce_inactive_rare_entry_hazard_of_regular
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) :
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    ∃ η H D : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < H ∧ 0 < D ∧
      ∀ᶠ t in atTop, 2 ≤ M t ∧ ∀ b : ℝ,
        bar t-η ≤ b → b ≤ bar t → H/((M t-1:ℕ):ℝ) ≤ bar t-b →
        let P := Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
        (∀ᵐ r ∂P, RegularClearing (k+1) (C t) r b) →
          HasDerivAt (coverage (k+1) (C t) hn P)
            (deriv (coverage (k+1) (C t) hn P) b) b ∧
          0 < deriv (coverage (k+1) (C t) hn P) b ∧
          coverage (k+1) (C t) hn P b/deriv (coverage (k+1) (C t) hn P) b ≤
            D/(((M t-1:ℕ):ℝ)*(bar t-b)) := by
  dsimp only
  have hk := h.proposers_two
  have hn : 2 ≤ k+1 := by omega
  let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
  let bar := fun t => KernelDemand.populationPrice (k+1)
    (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  have hL : 0 < L := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  obtain ⟨η₁,K,A,κ,hη₁,hη₁1,hK,hA,hκ,htail⟩ :=
    payOnce_inactive_entry_tail_ratio Γ B F g ρ h hlocal
  obtain ⟨η₀,hη₀,_,hhazard⟩ := exists_entry_hazard_cutoff.{0} hn
  let η := min η₁ (min η₀ (L/4))
  have hη : 0 < η := lt_min hη₁ (lt_min hη₀ (by positivity))
  have hη₁' : η ≤ η₁ := min_le_left _ _
  have hη₀' : η ≤ η₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hηL : η ≤ L/4 := (min_le_right _ _).trans (min_le_right _ _)
  let H := max K (2*A/(κ*η))
  have hH : 0 < H := hK.trans_le (le_max_left _ _)
  let bhi := L+1
  have hbhi : 0 < bhi := by dsimp [bhi]; positivity
  let α := entrySlopeConstant (k+1)/(2*bhi)
  have hα : 0 < α := div_pos (entrySlopeConstant_pos hn) (by positivity)
  let D := ((k+1:ℕ):ℝ)*A*(1+1/η)/(α*κ)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨η,H,D,hη,hη₁'.trans hη₁1,hH,hD,?_⟩
  have hbar := (payOnce_inactive_population_price Γ B F g ρ h).2
  have hlo : ∀ᶠ t in atTop, L/2 < bar t := hbar.eventually (eventually_gt_nhds (by linarith : L/2 < L))
  have hhi : ∀ᶠ t in atTop, bar t < bhi := hbar.eventually (eventually_lt_nhds (by dsimp [bhi]; linarith : L < bhi))
  filter_upwards [htail,hlo,hhi] with t ht htlo hthi
  refine ⟨ht.1,?_⟩
  intro b hb hbbar hd hreg
  let N := M t-1
  let P := Measure.pi (fun _ : Fin N => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
  have hN : (0:ℝ) < N := Nat.cast_pos.mpr (by dsimp [N]; omega)
  have hbp : 0 < b := by linarith
  have hbb : b ≤ bhi := hbbar.trans hthi.le
  have hdp : 0 < bar t-b := (div_pos hH hN).trans_le hd
  have hKgap : K/(N:ℝ) ≤ bar t-b :=
    (div_le_div_of_nonneg_right (le_max_left _ _) hN.le).trans hd
  have htails := ht.2 b (by linarith) hbbar hKgap
  dsimp only at htails
  have hNd : H ≤ (N:ℝ)*(bar t-b) := by
    have hh := (div_le_iff₀ hN).mp hd
    nlinarith
  have hrate : 0 < κ*(N:ℝ)*(bar t-b) := by positivity
  have hlarge : 2*A ≤ κ*(N:ℝ)*(bar t-b)*η := by
    have hKH := (le_max_right K (2*A/(κ*η))).trans hNd
    have hh := (div_le_iff₀ (mul_pos hκ hη)).mp hKH
    nlinarith
  have habs : A*exp (-(κ*(N:ℝ)*(bar t-b))*η) ≤ 1/2 := by
    simpa only [neg_mul] using exponential_absorption hlarge
  have hh := hhazard P (C t) b bhi hbp hbb hreg η ⟨hη,hη₀'⟩
    (κ*(N:ℝ)*(bar t-b)) A hrate hA.le htails.1 (by
      intro s hs
      simpa only [neg_mul] using htails.2 s hs.1 (hs.2.trans hη₁')) habs
  refine ⟨hh.1,hh.2.1,hh.2.2.trans_eq ?_⟩
  change ((k+1:ℕ):ℝ)*A*(1+1/η)/(α*(κ*(N:ℝ)*(bar t-b))) = D/((N:ℝ)*(bar t-b))
  dsimp only [D]
  rw [div_div]
  congr 1
  ring

end FCAppendix.Bayes
