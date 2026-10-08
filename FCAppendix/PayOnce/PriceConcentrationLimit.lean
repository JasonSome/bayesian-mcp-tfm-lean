import FCAppendix.PayOnce.PriceConcentration
import FCAppendix.PayOnce.InteriorRivalCounts

namespace FCAppendix.PayOnce.PriceConcentration
open MeasureTheory ProbabilityTheory Set Filter Topology CommonList KernelTailEvent
open Probability PriceInteriorBounds AnalyticalKernel CompactifiedBidLaws
open scoped BigOperators

theorem exists_eventually_price_margins
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    {n : ℕ} (hn : 2 ≤ n) (G : ℕ → ProbabilityMeasure ℝ)
    (hpos : ∀ t, ∀ᵐ b ∂(G t : Measure ℝ), 0 ≤ b)
    {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => scaledLaw (G t) 1) atTop (𝓝 G₀))
    {c : ℕ → ℕ} {ρ L : ℝ} (hL : 0 < L)
    (hroot : KernelDemand.demand n (G₀ : Measure ENNReal) L = ρ)
    (hunique : ∀ T, 0 < T → KernelDemand.demand n (G₀ : Measure ENNReal) T = ρ → T = L)
    (hcapacity : Tendsto (fun t => (c t:ℝ)/(N t:ℝ)) atTop (𝓝 ρ))
    {a z : ℝ} (ha : L < a) (haz : a < z) (hz : z < (n:ℝ)*L)
    (hwin : 0 < (G₀ : Measure ENNReal) (Ioo (ENNReal.ofReal a) (ENNReal.ofReal z))) :
    ∃ ℓ u q δlo δhi : ℝ,
      0 < ℓ ∧ ℓ < L ∧ L < u ∧ u < a ∧ z < (n:ℝ)*ℓ ∧
      0 < q ∧ 0 < δlo ∧ 0 < δhi ∧
      ∀ᶠ t in atTop, 0 < N t ∧
        (c t:ℝ)/(N t:ℝ) ≤ (∫ b, kernel n b ℓ ∂(G t : Measure ℝ))-δlo ∧
        (∫ b, kernel n b u ∂(G t : Measure ℝ))+δhi ≤ ((c t:ℝ)-1)/(N t:ℝ) ∧
        2*q ≤ (G t : Measure ℝ).real (Ioo a z) := by
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  let η := min (L/4) (min ((a-L)/2) (((n:ℝ)*L-z)/(2*n)))
  have hη : 0 < η := lt_min (by positivity) (lt_min (by linarith) (by positivity))
  have hηL : η ≤ L/4 := min_le_left _ _
  have hηa : η ≤ (a-L)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηz : η ≤ ((n:ℝ)*L-z)/(2*n) := (min_le_right _ _).trans (min_le_right _ _)
  have hlo : 0 < L-η := by linarith
  have hhi : 0 < L+η := by linarith
  have ha' : L+η < a := by linarith
  have hz' : z < (n:ℝ)*(L-η) := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*(n:ℝ))).mp hηz
    nlinarith
  let Dlo := KernelDemand.demand n (G₀ : Measure ENNReal) (L-η)
  let Dhi := KernelDemand.demand n (G₀ : Measure ENNReal) (L+η)
  have hdlo : ρ < Dlo := by
    have hle := KernelDemand.demand_antitone hn (G₀ : Measure ENNReal) hlo hL (by linarith : L-η ≤ L)
    rw [hroot] at hle
    apply lt_of_le_of_ne hle
    intro he
    have hh := hunique (L-η) hlo he.symm
    linarith
  have hdhi : Dhi < ρ := by
    have hle := KernelDemand.demand_antitone hn (G₀ : Measure ENNReal) hL hhi (by linarith : L ≤ L+η)
    rw [hroot] at hle
    apply lt_of_le_of_ne hle
    intro he
    have hh := hunique (L+η) hhi he
    linarith
  let δlo := (Dlo-ρ)/2
  let δhi := (ρ-Dhi)/2
  have hδlo : 0 < δlo := by dsimp only [δlo]; linarith
  have hδhi : 0 < δhi := by dsimp only [δhi]; linarith
  have hinv : Tendsto (fun t => ((N t:ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hN)
  have hcm1 : Tendsto (fun t => ((c t:ℝ)-1)/(N t:ℝ)) atTop (𝓝 ρ) := by
    simpa only [sub_zero,Function.comp_def,sub_div,one_div] using hcapacity.sub hinv
  have htlo := (tendsto_rival_kernel_mean_nonneg hn G hpos hweak hlo).sub hcapacity
  have hthi := hcm1.sub (tendsto_rival_kernel_mean_nonneg hn G hpos hweak hhi)
  have helo := htlo.eventually_const_lt
    (show δlo < KernelDemand.demand n (G₀ : Measure ENNReal) (L-η)-ρ by dsimp only [δlo,Dlo]; linarith)
  have hehi := hthi.eventually_const_lt
    (show δhi < ρ-KernelDemand.demand n (G₀ : Measure ENNReal) (L+η) by dsimp only [δhi,Dhi]; linarith)
  obtain ⟨q,hq,hqmass⟩ := eventually_window_mass_pos G hweak (hL.trans ha) haz hwin
  refine ⟨L-η,L+η,q/2,δlo,δhi,hlo,by linarith,by linarith,ha',hz',
    by positivity,hδlo,hδhi,?_⟩
  filter_upwards [helo,hehi,hqmass,hN.eventually_ge_atTop 1] with t htlo hthi hqt htN
  refine ⟨by omega,by linarith,by linarith,?_⟩
  linarith

theorem exists_eventually_price_concentration
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    {n : ℕ} (hn : 2 ≤ n) (G : ℕ → ProbabilityMeasure ℝ)
    (hpos : ∀ t, ∀ᵐ b ∂(G t : Measure ℝ), 0 ≤ b)
    {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => scaledLaw (G t) 1) atTop (𝓝 G₀))
    {c : ℕ → ℕ} {ρ L : ℝ} (hL : 0 < L)
    (hroot : KernelDemand.demand n (G₀ : Measure ENNReal) L = ρ)
    (hunique : ∀ T, 0 < T → KernelDemand.demand n (G₀ : Measure ENNReal) T = ρ → T = L)
    (hcapacity : Tendsto (fun t => (c t:ℝ)/(N t:ℝ)) atTop (𝓝 ρ))
    {a z : ℝ} (ha : L < a) (haz : a < z) (hz : z < (n:ℝ)*L)
    (hwin : 0 < (G₀ : Measure ENNReal) (Ioo (ENNReal.ofReal a) (ENNReal.ofReal z))) :
    ∃ ℓ u q d : ℝ,
      0 < ℓ ∧ ℓ < L ∧ L < u ∧ u < a ∧ z < (n:ℝ)*ℓ ∧ 0 < q ∧ 0 < d ∧
      ∀ᶠ t in atTop,
        (Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))).real
          (goodEvent n (N t) (c t) ℓ u a z q)ᶜ ≤ 3*Real.exp (-d*(N t:ℝ)) ∧
        ∀ T ε : ℝ, T ∈ Icc ℓ u →
          |(∫ b, kernel n b T ∂(G t : Measure ℝ))-(c t:ℝ)/(N t:ℝ)| ≤ 1/(N t:ℝ) →
          0 ≤ ε →
          ∀ b R : (Fin (N t) → ℝ) → ℝ, (∀ r, 0 < R r) →
          (∀ r, kernel n (b r) (R r)+∑ j, kernel n (r j) (R r) =
            (min (c t) (Fintype.card (DummyKernel.Active r)+1):ℕ)) →
          (Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))).real {r | ε ≤ |R r-T|} ≤
            3*Real.exp (-d*(N t:ℝ))+(2*Real.exp 8)*Real.exp (-(N t:ℝ)*ε^2/(2*((n:ℝ)*z/q)^2)) := by
  obtain ⟨ℓ,u,q,δlo,δhi,hℓ,hℓL,hLu,hua,hzℓ,hq,hδlo,hδhi,he⟩ :=
    exists_eventually_price_margins N hN hn G hpos hweak hL hroot hunique hcapacity ha haz hz hwin
  let d := min (2*δlo^2) (min (2*δhi^2) (2*q^2))
  have hd : 0 < d := by dsimp only [d]; positivity
  have hdlo : d ≤ 2*δlo^2 := min_le_left _ _
  have hdhi : d ≤ 2*δhi^2 := (min_le_right _ _).trans (min_le_left _ _)
  have hdq : d ≤ 2*q^2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ℓ,u,q,d,hℓ,hℓL,hLu,hua,hzℓ,hq,hd,?_⟩
  filter_upwards [he] with t ht
  obtain ⟨htN,htlo,hthi,htmass⟩ := ht
  constructor
  · exact goodEvent_compl_le_exponential hn htN (G t : Measure ℝ) hℓ (hL.trans hLu)
      hq.le hδlo.le hδhi.le htlo hthi htmass hdlo hdhi hdq
  · intro T ε hT hbias hε b R hR hcap
    exact price_tail_le_gaussian hn htN (G t : Measure ℝ) hℓ hT hua haz hzℓ
      hq hδlo.le hδhi.le htlo hthi htmass hdlo hdhi hdq b R hR hcap hbias hε

end FCAppendix.PayOnce.PriceConcentration
