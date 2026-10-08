import FCAppendix.Ample.PositiveBaseRoutes

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Filter Set Topology

theorem eventually_all_identities_of_selections
    (M : ℕ → ℕ) (hm : ∀ t, 0 < M t) (R : ∀ t, Fin (M t) → Prop)
    (h : ∀ i : (∀ t, Fin (M t)), ∀ᶠ t in atTop, R t (i t)) :
    ∀ᶠ t in atTop, ∀ i : Fin (M t), R t i := by
  classical
  let bad (t : ℕ) : Prop := ∃ i : Fin (M t), ¬ R t i
  let i : ∀ t, Fin (M t) := fun t =>
    if ht : bad t then Classical.choose ht else ⟨0, hm t⟩
  filter_upwards [h i] with t ht
  intro j
  by_contra hj
  have hb : bad t := ⟨j, hj⟩
  have hn := Classical.choose_spec hb
  have he : i t = Classical.choose hb := by simp only [i, dif_pos hb]
  rw [he] at ht
  exact hn ht

namespace ReceiptSequenceAssumptions
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
  {M C : ℕ → ℕ} {Γ : ∀ t, FiniteGame (M t) n (C t) Seed}
  {B : ∀ t, PosteriorSystem (Γ t)} {F : Measure ℝ} [IsProbabilityMeasure F]
  {g a ρ : ℝ}

omit [IsProbabilityMeasure F] in

theorem with_ppi_factor_one
    (h : ReceiptSequenceAssumptions M C Γ B F g a ρ)
    (hA : ∀ t, (Γ t).A = Schedule.ppi n) :
    ReceiptSequenceAssumptions M C Γ B F g 1 ρ :=
  { h with
    factor_pos := by norm_num
    receipt_lower := by intro t r _ _; simp [hA t, Schedule.ppi] }

theorem ample_positive_base_one_route_uniform
    (h : ReceiptSequenceAssumptions M C Γ B F g a ρ)
    (hn : 2 ≤ n) (hg : F {g} = 0) (hample : F.real (Ioi g) < (n : ℝ) * ρ)
    (hA : ∀ t, (Γ t).A = Schedule.ppi n)
    (hzero : ∀ t, RejectsZeroBids (Γ t))
    (d : ℝ) (hd : 0 < d)
    (hG : ∀ t r, 2 ≤ r → r ≤ n → d ≤ g * ((Γ t).G.charge r - 1))
    (v : ℝ) (hv : g < v) :
    ∀ᶠ t in atTop, ∀ (i : Fin (M t)) (act : JointAction n),
      (problem (Γ t) i).BestResponse v act → act.routeCount = 1 := by
  obtain ⟨L, hL⟩ := eventually_atTop.mp (h.population_grows.eventually_gt_atTop 0)
  have hs := h.along (fun t => t + L) (tendsto_add_atTop_nat L)
  have hh : ∀ᶠ t in atTop, ∀ (i : Fin (M (t + L))) (act : JointAction n),
      (problem (Γ (t + L)) i).BestResponse v act → act.routeCount = 1 := by
    apply eventually_all_identities_of_selections (fun t => M (t + L))
      (fun t => hL (t + L) (by omega))
    intro i
    exact hs.ample_positive_base_one_route hn hg hample
      (fun t => hA (t + L)) (fun t => hzero (t + L)) d hd
      (fun t => hG (t + L)) i v hv
  obtain ⟨T, hT⟩ := eventually_atTop.mp hh
  refine eventually_atTop.mpr ⟨T + L, ?_⟩
  intro t ht
  have hLt : L ≤ t := by omega
  have hr := hT (t - L) (by omega)
  rw [Nat.sub_add_cancel hLt] at hr
  exact hr

theorem ample_positive_base_ae_actual_chosen_singleton
    (h : ReceiptSequenceAssumptions M C Γ B F g a ρ)
    (hn : 2 ≤ n) (hg : F {g} = 0) (hample : F.real (Ioi g) < (n : ℝ) * ρ)
    (hA : ∀ t, (Γ t).A = Schedule.ppi n)
    (hzero : ∀ t, RejectsZeroBids (Γ t))
    (d : ℝ) (hd : 0 < d)
    (hG : ∀ t r, 2 ≤ r → r ≤ n → d ≤ g * ((Γ t).G.charge r - 1)) :
    ∀ᵐ v ∂F, g < v → ∀ᶠ t in atTop,
      ∀ᵐ act ∂(Γ t).σ v, act.routeCount = 1 := by
  filter_upwards [ae_all_rows_bestResponse M C Γ F h.common_values h.users] with v hv
  intro hvg
  filter_upwards [h.ample_positive_base_one_route_uniform hn hg hample hA hzero
    d hd hG v hvg, h.population_grows.eventually_gt_atTop 0] with t ht hmt
  filter_upwards [hv t ⟨0, hmt⟩] with act hact
  exact ht ⟨0, hmt⟩ act hact

theorem ample_positive_base_main
    (h : ReceiptSequenceAssumptions M C Γ B F g a ρ)
    (hn : 2 ≤ n) (hg : F {g} = 0) (hample : F.real (Ioi g) < (n : ℝ) * ρ)
    (hactive : 0 < F.real (Ioi g))
    (hA : ∀ t, (Γ t).A = Schedule.ppi n)
    (hzero : ∀ t, RejectsZeroBids (Γ t))
    (d : ℝ) (hd : 0 < d)
    (hG : ∀ t r, 2 ≤ r → r ≤ n → d ≤ g * ((Γ t).G.charge r - 1)) :
    (∀ v, g < v → ∀ᶠ t in atTop, ∀ (i : Fin (M t)) (act : JointAction n),
      (problem (Γ t) i).BestResponse v act → act.routeCount = 1) ∧
    (∀ᵐ v ∂F, g < v → ∀ᶠ t in atTop,
      ∀ᵐ act ∂(Γ t).σ v, act.routeCount = 1) ∧
    (∀ᵐ v ∂F, g < v → ∀ (i : ∀ t, Fin (M t)) (f : ℕ → ℝ),
      Tendsto (fun t => (typeOutcome (Γ t) (i t) v).expect (fun r => f r.val))
        atTop (𝓝 (f 1))) ∧
    Tendsto (fun t => finiteCoverage (Γ t)) atTop (𝓝 (F.real (Ioi g))) ∧
    Tendsto (fun t => finiteLoad (Γ t)) atTop (𝓝 (F.real (Ioi g))) ∧
    Tendsto (fun t => finiteLoad (Γ t) - finiteCoverage (Γ t)) atTop (𝓝 0) ∧
    Tendsto (fun t => finiteMultiplicity (Γ t)) atTop (𝓝 1) := by
  let h1 := h.with_ppi_factor_one hA
  have ha : F.real (Ioi g) < (n : ℝ) * ρ * (1 : ℝ) ^ 2 := by
    simpa only [one_pow, mul_one] using hample
  exact ⟨fun v hv => h.ample_positive_base_one_route_uniform hn hg hample hA hzero d hd hG v hv,
    h.ample_positive_base_ae_actual_chosen_singleton hn hg hample hA hzero d hd hG,
    h1.ample_positive_base_ae_actual_count hg ha d hd hG,
    h1.ample_positive_base_aggregates hg ha d hd hG hactive⟩

theorem ample_ppi_all_supported_limits
    (h : ReceiptSequenceAssumptions M C Γ B F g a ρ)
    (hg : F {g} = 0) (hample : F.real (Ioi g) < (n : ℝ) * ρ)
    (hA : ∀ t, (Γ t).A = Schedule.ppi n)
    (i : ∀ t, Fin (M t)) (v : ℝ) (hv : g < v) :
    ∀ ε > 0, ∀ᶠ t in atTop, ∀ act : JointAction n,
      (problem (Γ t) (i t)).BestResponse v act →
      1 - ((problem (Γ t) (i t)).outcome act).success < ε ∧ act.bid < ε ∧
      g * (((problem (Γ t) (i t)).outcome act).charge (Γ t).G -
        ((problem (Γ t) (i t)).outcome act).success) < ε := by
  exact (h.with_ppi_factor_one hA).ample_bestResponses hg
    (by simpa only [one_pow, mul_one] using hample) i v hv

end ReceiptSequenceAssumptions
end FCAppendix.Bayes
