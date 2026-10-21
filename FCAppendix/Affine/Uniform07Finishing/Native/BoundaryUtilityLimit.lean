import FCAppendix.Affine.Uniform07Finishing.Native.NativeConditional
import FCAppendix.Affine.Uniform07Finishing.Native.BoundaryVersion
import FCAppendix.Affine.Uniform07Finishing.Native.UniformUpperLimits

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical

variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem source_boundary_product_value (row : Uniform07.Row) :
    lowerProductQuadratic (Uniform07.entry row) (Uniform07.cutoff row)
      (lowerTargetProbability (Uniform07.entry row) (Uniform07.cutoff row)) =
        (Uniform07.cutoff row-Uniform07.entry row)^2/Uniform07.cutoff row := by
  have ht := Uniform07.cutoff_pos row
  have hlamt := source_entry_lt_cutoff row
  have hstar : 0≤ 1-Uniform07.entry row/Uniform07.cutoff row := by
    have hdiv := (div_le_one ht).mpr hlamt.le
    linarith
  simp only [lowerProductQuadratic,lowerTargetProbability,max_eq_left hstar]
  field_simp [ht.ne']
  ring

theorem source_boundary_product_le (row : Uniform07.Row) {p : ℝ} (hp : 0≤ p) :
    lowerProductQuadratic (Uniform07.entry row) (Uniform07.cutoff row) p ≤
      (Uniform07.cutoff row-Uniform07.entry row)^2/Uniform07.cutoff row := by
  have hgap := lower_product_quadratic_gap
    (lam:=Uniform07.entry row) (Uniform07.cutoff_pos row) hp
  rw [source_boundary_product_value row] at hgap
  have hs := mul_nonneg (Uniform07.cutoff_pos row).le
    (sq_nonneg (p-lowerTargetProbability (Uniform07.entry row) (Uniform07.cutoff row)))
  linarith

theorem actual_boundary_utility_error (row : Uniform07.Row)
    (Γ : FiniteGame m 2 c Seed)
    (hA : Γ.A=Schedule.affine 2 (Uniform07.eta row)
      (Uniform07.eta_pos row).le (sourceProduct_eta_le_one row))
    (hg : Γ.g=0) (u : Fin m) (ε : ℝ) (hε : 0≤ε)
    (bT : Icc (0:ℝ) (Early.bidCap row))
    (hIC : ∀ b : Icc (0:ℝ) (Early.bidCap row),
      (problem Γ u).payoff (Uniform07.cutoff row)
        (sourceLowerBroadcastAction (Early.bidCap row) b) ≤
      (problem Γ u).payoff (Uniform07.cutoff row)
        (sourceLowerBroadcastAction (Early.bidCap row) bT))
    (hmom : ∀ b : Icc (0:ℝ) (Early.bidCap row),
      |((problem Γ u).outcome (sourceLowerBroadcastAction (Early.bidCap row) b)).load-
        2*sourceProductProbability row b|≤ε ∧
      |((problem Γ u).outcome (sourceLowerBroadcastAction (Early.bidCap row) b)).duplicates-
        (sourceProductProbability row b)^2|≤ε) :
    |(problem Γ u).payoff (Uniform07.cutoff row)
      (sourceLowerBroadcastAction (Early.bidCap row) bT)-
        (Uniform07.cutoff row-Uniform07.entry row)^2/Uniform07.cutoff row| ≤
      2*(Uniform07.cutoff row+Early.bidCap row)*ε := by
  let b₀ : Icc (0:ℝ) (Early.bidCap row) :=
    ⟨sourceLowerBenchmarkBid row (Uniform07.cutoff row),
      sourceLowerBenchmarkBid_mem row (Uniform07.cutoff_pos row) le_rfl⟩
  have hT := actual_product_payoff_error_of_moments row Γ hA hg u
    (Uniform07.cutoff row) ε (Uniform07.cutoff_pos row).le hε bT
    (hmom bT).1 (hmom bT).2
  have h₀ := actual_product_payoff_error_of_moments row Γ hA hg u
    (Uniform07.cutoff row) ε (Uniform07.cutoff_pos row).le hε b₀
    (hmom b₀).1 (hmom b₀).2
  have hb₀ : sourceProductProbability row b₀ =
      lowerTargetProbability (Uniform07.entry row) (Uniform07.cutoff row) :=
    sourceLowerBenchmarkBid_probability row (Uniform07.cutoff_pos row)
  rw [hb₀,source_boundary_product_value row] at h₀
  have hbest := hIC b₀
  have hmax := source_boundary_product_le row (sourceProductProbability_mem row bT.2).1
  have hlow := (abs_le.mp h₀).1
  have hhigh := (abs_le.mp hT).2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem sourceLowerBroadcastAction_eq_of_bid_route
    (U : ℝ) (a : JointAction 2) (hU : a.bid≤ U) (hk : a.routeCount=2) :
    sourceLowerBroadcastAction U ⟨a.bid,⟨a.bid_nonneg,hU⟩⟩=a := by
  cases a
  simp_all [sourceLowerBroadcastAction]

theorem actual_boundary_utility_error_of_broadcast_best
    (row : Uniform07.Row) (Γ : FiniteGame m 2 c Seed)
    (hA : Γ.A=Schedule.affine 2 (Uniform07.eta row)
      (Uniform07.eta_pos row).le (sourceProduct_eta_le_one row))
    (hg : Γ.g=0) (R : ℝ) (hUR : Early.bidCap row< R)
    (u : Fin m) (ε : ℝ) (hε : 0≤ε) (aT : JointAction 2)
    (hTU : aT.bid≤ Early.bidCap row) (hTk : aT.routeCount=2)
    (hIC : ∀ a : JointAction 2, a.routeCount=2 → a.bid< R →
      (problem Γ u).payoff (Uniform07.cutoff row) a ≤
        (problem Γ u).payoff (Uniform07.cutoff row) aT)
    (hmom : ∀ b : Icc (0:ℝ) (Early.bidCap row),
      |((problem Γ u).outcome (sourceLowerBroadcastAction (Early.bidCap row) b)).load-
        2*sourceProductProbability row b|≤ε ∧
      |((problem Γ u).outcome (sourceLowerBroadcastAction (Early.bidCap row) b)).duplicates-
        (sourceProductProbability row b)^2|≤ε) :
    |(problem Γ u).payoff (Uniform07.cutoff row) aT-
        (Uniform07.cutoff row-Uniform07.entry row)^2/Uniform07.cutoff row| ≤
      2*(Uniform07.cutoff row+Early.bidCap row)*ε := by
  let bT : Icc (0:ℝ) (Early.bidCap row) := ⟨aT.bid,⟨aT.bid_nonneg,hTU⟩⟩
  have hT : sourceLowerBroadcastAction (Early.bidCap row) bT=aT :=
    sourceLowerBroadcastAction_eq_of_bid_route _ aT hTU hTk
  have hB (b : Icc (0:ℝ) (Early.bidCap row)) :=
    hIC (sourceLowerBroadcastAction (Early.bidCap row) b) rfl (b.2.2.trans_lt hUR)
  simpa only [hT] using actual_boundary_utility_error row Γ hA hg u ε hε bT
    (fun b=>by simpa only [hT] using hB b) hmom

theorem actual_boundary_utility_tendsto_of_moments
    (row : Uniform07.Row) (M C : ℕ→ℕ)
    (Γ : (k : ℕ)→ FiniteGame (M k) 2 (C k) Seed)
    (hA : ∀ k, (Γ k).A=Schedule.affine 2 (Uniform07.eta row)
      (Uniform07.eta_pos row).le (sourceProduct_eta_le_one row))
    (hg : ∀ k, (Γ k).g=0) (u : (k : ℕ)→ Fin (M k))
    (bT : ℕ→ Icc (0:ℝ) (Early.bidCap row))
    (ε : ℕ→ℝ) (hε : ∀ᶠ k in atTop, 0≤ε k)
    (hε0 : Tendsto ε atTop (𝓝 0))
    (hIC : ∀ᶠ k in atTop, ∀ b : Icc (0:ℝ) (Early.bidCap row),
      (problem (Γ k) (u k)).payoff (Uniform07.cutoff row)
        (sourceLowerBroadcastAction (Early.bidCap row) b) ≤
      (problem (Γ k) (u k)).payoff (Uniform07.cutoff row)
        (sourceLowerBroadcastAction (Early.bidCap row) (bT k)))
    (hmom : ∀ᶠ k in atTop, ∀ i : Fin (M k),
      ∀ b : Icc (0:ℝ) (Early.bidCap row),
      |((problem (Γ k) i).outcome (sourceLowerBroadcastAction (Early.bidCap row) b)).load-
        2*sourceProductProbability row b|≤ε k ∧
      |((problem (Γ k) i).outcome (sourceLowerBroadcastAction (Early.bidCap row) b)).duplicates-
        (sourceProductProbability row b)^2|≤ε k) :
    Tendsto (fun k=>(problem (Γ k) (u k)).payoff (Uniform07.cutoff row)
      (sourceLowerBroadcastAction (Early.bidCap row) (bT k))) atTop
        (𝓝 ((Uniform07.cutoff row-Uniform07.entry row)^2/Uniform07.cutoff row)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  have hE : Tendsto (fun k=>2*(Uniform07.cutoff row+Early.bidCap row)*ε k)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hε0.const_mul
      (2*(Uniform07.cutoff row+Early.bidCap row))
  apply squeeze_zero' (.of_forall fun _=>abs_nonneg _) _ hE
  filter_upwards [hε,hIC,hmom] with k hεk hICk hmomk
  exact actual_boundary_utility_error row (Γ k) (hA k) (hg k)
    (u k) (ε k) hεk (bT k) hICk (hmomk (u k))

end FCAppendix.Affine.Uniform07Finishing
