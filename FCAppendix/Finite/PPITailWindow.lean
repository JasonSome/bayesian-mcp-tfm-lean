import FCAppendix.Finite.PPITailAnchor

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Filter Set Topology

theorem left_linear_bound_of_deriv {q : ℝ → ℝ} {t f : ℝ}
    (hq : HasDerivAt q (-f) t) (hf : 0 < f) :
    ∃ d > 0, ∀ v ∈ Ioo (t - d) t, q t + (f / 2) * (t - v) ≤ q v := by
  obtain ⟨d, hd, hb⟩ := Metric.eventually_nhds_iff.mp (hq.isLittleO.bound (half_pos hf))
  refine ⟨d, hd, ?_⟩
  intro v hv
  have hdist : dist v t < d := by
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hv.2)]
    linarith [hv.1]
  have hh := hb hdist
  simp only [Real.norm_eq_abs, smul_eq_mul] at hh
  rw [abs_of_neg (sub_neg.mpr hv.2)] at hh
  have hlo := (abs_le.mp hh).1
  nlinarith

theorem ppi_success_le_inverse_square
    {N n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame (N + 1) n c Seed) (hc : c ≤ N + 1)
    (hA : Γ.A = Schedule.ppi n) (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hatom : PositiveVisibleAtomless Γ) (hu : UsersOptimal Γ)
    (hzero : ∀ j, visibleBidMeasure Γ j {0} = 0)
    (i : Fin (N + 1)) (j : Fin n) (hN : 0 < N)
    (v t f ρ h : ℝ) (hf : 0 < f) (hh : 0 < h) (hvt : v < t - h)
    (hρ : 0 < ρ)
    (hvalue : (n : ℝ) * ρ + f / 2 * (t - v) ≤ Γ.F.real (Ioi v))
    (hcenter : (c : ℝ) - N * ρ ≤ N * f / (4 * n) * h)
    (act : JointAction n) (ha : (problem Γ i).BestResponse v act) :
    ((problem Γ i).outcome act).success ≤
      (4 * (n : ℝ) ^ 3 / ((N : ℝ) * f ^ 2)) / (t - v) ^ 2 := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt j.isLt)
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hgap : 0 < t - v := by linarith
  let δ := (N : ℝ) * f / (4 * n) * (t - v)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have htail : 0 < Γ.F.real (Ioi v) := by
    have hh := mul_pos hn hρ
    have hh' := mul_pos (half_pos hf) hgap
    linarith
  have hlin : (N : ℝ) * f / (4 * n) * h ≤ (N : ℝ) * f / (4 * n) * (t - v) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hq : (n : ℝ) * ρ / n + (f / 2 * (t - v)) / n ≤ Γ.F.real (Ioi v) / n := by
    simpa only [add_div] using div_le_div_of_nonneg_right hvalue hn.le
  have hnq := mul_le_mul_of_nonneg_left hq hNR.le
  have heq : (N : ℝ) * ((n : ℝ) * ρ / n + (f / 2 * (t - v)) / n) =
      N * ρ + 2 * δ := by dsimp [δ]; field_simp; ring
  rw [heq] at hnq
  have hbound : δ ≤ (N : ℝ) * (Γ.F.real (Ioi v) / n) - c := by
    change (N : ℝ) * f / (4 * n) * h ≤ δ at hlin
    linarith
  have hb := ppi_success_le_value_tail_gap Γ (by simpa only [Nat.add_sub_cancel] using hc)
    hA hj hatom hu hzero i j v htail act ha δ hδ
    (by simpa only [Nat.add_sub_cancel] using hbound)
  simp only [Nat.add_sub_cancel] at hb
  convert hb using 1
  dsimp [δ]
  field_simp

namespace NearPPIAssumptions

theorem ppi_tail_anchor
    {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {N C : ℕ → ℕ} {Γ : ∀ k, FiniteGame (N k + 1) n (C k) Seed}
    {F : Measure ℝ} [IsProbabilityMeasure F] [NullSingletonClass F]
    {g ρ vstar : ℝ} {a : ℕ → ℝ}
    (h : NearPPIAssumptions (fun k => N k + 1) C Γ F g a ρ vstar)
    (i : ∀ k, Fin (N k + 1)) (hA : ∀ k, (Γ k).A = Schedule.ppi n)
    (hzero : ∀ k j, visibleBidMeasure (Γ k) j {0} = 0)
    (f : ℝ → ℝ) (hf : Measurable f) (U : Set ℝ) (hUn : U ∈ 𝓝 vstar)
    (hF : F.restrict U = (volume.withDensity (fun x => ENNReal.ofReal (f x))).restrict U)
    (hc : ContinuousAt f vstar) (hpos : 0 < f vstar)
    (hC : Tendsto (fun k => ((C k : ℝ) - (N k + 1 : ℕ) * ρ) /
      Real.sqrt (N k + 1 : ℕ)) atTop (𝓝 0)) :
    let scale := fun k => (n : ℝ) * Real.sqrt (ρ * (1 - ρ)) /
      (f vstar * Real.sqrt (N k + 1 : ℕ))
    ∀ ε > 0, ∃ R₀ ≥ 0, ∀ R ≥ R₀, ∀ᶠ k in atTop,
      (problem (Γ k) (i k)).envelope (vstar - scale k * R) / scale k < ε := by
  dsimp only
  let j : Fin n := ⟨0, by have hh := h.proposers_two; omega⟩
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt j.isLt)
  let A := (n : ℝ) * Real.sqrt (ρ * (1 - ρ)) / f vstar
  have hApos : 0 < A := by
    dsimp [A]
    exact div_pos (mul_pos hn (Real.sqrt_pos.mpr
      (mul_pos h.ratio_pos (sub_pos.mpr h.ratio_lt_one)))) hpos
  let scale := fun k => (n : ℝ) * Real.sqrt (ρ * (1 - ρ)) /
    (f vstar * Real.sqrt (N k + 1 : ℕ))
  have hscale_def (k : ℕ) : scale k = A / Real.sqrt (N k + 1 : ℕ) := by
    dsimp [scale, A]
    ring
  have hscale_pos (k : ℕ) : 0 < scale k := by
    rw [hscale_def]
    exact div_pos hApos (Real.sqrt_pos.mpr (by positivity))
  have hscale : Tendsto scale atTop (𝓝 0) := by
    change Tendsto (fun k => scale k) atTop (𝓝 0)
    simp_rw [hscale_def]
    exact tendsto_const_nhds.div_atTop
      (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp h.population_grows))
  have hN : Tendsto N atTop atTop := by
    apply tendsto_atTop.mpr
    intro B
    filter_upwards [h.population_grows.eventually_ge_atTop (B + 1)] with k hk
    omega
  have hNs : Tendsto (fun k => Real.sqrt (N k) * scale k) atTop (𝓝 A) := by
    have hh := (sqrt_opponent_population_ratio N hN).mul_const A
    simp only [one_mul] at hh
    apply hh.congr
    intro k
    rw [hscale_def]
    ring
  have hcenter : Tendsto (fun k => ((C k : ℝ) - N k * ρ) / ((N k : ℝ) * scale k))
      atTop (𝓝 0) := by
    have hh := (opponent_capacity_centering N C ρ hN hC).div hNs hApos.ne'
    simp only [zero_div] at hh
    apply hh.congr'
    filter_upwards [hN.eventually_gt_atTop 0] with k hk
    dsimp only [Pi.div_apply]
    rw [div_div, ← mul_assoc, ← sq, Real.sq_sqrt (Nat.cast_nonneg _)]
  let D := 4 * (n : ℝ) ^ 3 / f vstar ^ 2
  let Q := fun k => D / (N k : ℝ)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hQ : ∀ k, 0 ≤ Q k := by intro k; dsimp [Q]; positivity
  have hQscale : Tendsto (fun k => Q k / scale k ^ 2) atTop (𝓝 (D / A ^ 2)) := by
    have hh := (tendsto_const_nhds (x := D)).div (hNs.pow 2) (pow_ne_zero 2 hApos.ne')
    apply hh.congr
    intro k
    change D / (Real.sqrt (N k) * scale k) ^ 2 = D / (N k : ℝ) / scale k ^ 2
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    exact (div_div D (N k : ℝ) (scale k ^ 2)).symm
  have hQone : Tendsto (fun k => Q k / scale k) atTop (𝓝 0) := by
    have hh := hQscale.mul hscale
    simp only [mul_zero] at hh
    apply hh.congr
    intro k
    have hs := (hscale_pos k).ne'
    field_simp
  obtain ⟨d₁, hd₁, hlinear⟩ := left_linear_bound_of_deriv
    (value_tail_hasDerivAt_of_local_density F f hf vstar U hUn hF hc hpos) hpos
  obtain ⟨d₂, hd₂, sel, hsel⟩ := exists_local_ae_bestResponse_selections
    (fun k => N k + 1) C Γ i F h.common_values (fun k => (h.equilibria k).users)
    f hf vstar U hUn hF hc hpos
  let d := min d₁ d₂
  have hd : 0 < d := lt_min hd₁ hd₂
  have hsel' (k : ℕ) : ∀ᵐ v, v ∈ Ioo (vstar - d) vstar →
      (problem (Γ k) (i k)).BestResponse v (sel k v) := by
    filter_upwards [hsel k] with v hv hvI
    apply hv
    constructor <;> linarith [min_le_right d₁ d₂, hvI.1, hvI.2]
  have hupper : ∀ᶠ k in atTop, ∀ v ∈ Ioo (vstar - d) (vstar - scale k), ∀ act,
      (problem (Γ k) (i k)).BestResponse v act →
      ((problem (Γ k) (i k)).outcome act).success ≤ Q k / (vstar - v) ^ 2 := by
    have htol : 0 < f vstar / (4 * n) := by positivity
    filter_upwards [hN.eventually_gt_atTop 0,
      hcenter.eventually (eventually_lt_nhds htol)] with k hk hck
    intro v hv act ha
    have hNR : (0 : ℝ) < N k := Nat.cast_pos.mpr hk
    have hcv : (C k : ℝ) - N k * ρ ≤ N k * f vstar / (4 * n) * scale k := by
      have hb := (div_lt_iff₀ (mul_pos hNR (hscale_pos k))).mp hck
      calc
        _ ≤ (f vstar / (4 * n)) * ((N k : ℝ) * scale k) := hb.le
        _ = _ := by ring
    have hval := hlinear v (show v ∈ Ioo (vstar - d₁) vstar from
      ⟨by linarith [min_le_left d₁ d₂, hv.1], by linarith [hscale_pos k, hv.2]⟩)
    rw [h.efficient_cutoff, ← h.common_values k] at hval
    have hb := ppi_success_le_inverse_square (Γ k) (h.capacity_lt_population k).le
      (hA k) (h.feasible_continuations k) (h.visible_atomless k)
      (h.equilibria k).users (hzero k) (i k) j hk
      v vstar (f vstar) ρ (scale k) hpos (hscale_pos k) hv.2 h.ratio_pos hval hcv act ha
    convert hb using 1
    dsimp [Q, D]
    ring
  apply Interim.Problem.envelope_tail_anchor_of_square_bound
    (fun k => problem (Γ k) (i k)) vstar g d hd h.common_fee scale Q hscale
    (Eventually.of_forall hscale_pos) hQ hQone (D / A ^ 2 + 1) (by positivity)
    ((hQscale.eventually (eventually_lt_nhds (by linarith : D / A ^ 2 < D / A ^ 2 + 1))).mono
      (fun _ hk => hk.le)) sel hsel' hupper

end NearPPIAssumptions
end FCAppendix.Bayes
