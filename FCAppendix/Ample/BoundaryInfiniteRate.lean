import FCAppendix.Ample.BoundaryRates

noncomputable section
namespace FCAppendix.Ample.CompletionDraft
open Filter Set Topology Real

def Superexponential (M : ℕ → ℕ) (p : ℕ → ℝ) : Prop :=
  ∀ R : ℝ, ∀ᶠ t in atTop, p t ≤ exp (-R * (M t : ℝ))

theorem zero_mass_superexponential
    (M N d : ℕ → ℕ) (k : ℕ) (a p : ℕ → ℝ)
    (hM : Tendsto M atTop atTop)
    (hN : Tendsto (fun t => (N t : ℝ) / M t) atTop (𝓝 1))
    (hd : Tendsto (fun t => (d t : ℝ) / M t) atTop (𝓝 0))
    (ha : Tendsto a atTop (𝓝 0))
    (hupper : ∀ θ : ℝ, 0 ≤ θ → ∀ᶠ t in atTop,
      p t ≤ exp (θ * (k : ℝ) * d t) *
        (a t + (1 - a t) * exp (-θ)) ^ N t) :
    Superexponential M p := by
  intro R
  let θ : ℝ := |R| + 1
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hRθ : R < θ := by dsimp [θ]; linarith [le_abs_self R]
  let q : ℕ → ℝ := fun t => a t + (1 - a t) * exp (-θ)
  have hq : Tendsto q atTop (𝓝 (exp (-θ))) := by
    simpa [q] using ha.add ((ha.const_sub 1).mul_const (exp (-θ)))
  have hqpos : ∀ᶠ t in atTop, 0 < q t :=
    hq.eventually (eventually_gt_nhds (exp_pos (-θ)))
  have hlog : Tendsto (fun t => log (q t)) atTop (𝓝 (-θ)) := by
    simpa only [Function.comp_def, log_exp] using
      (continuousAt_log (exp_ne_zero (-θ))).tendsto.comp hq
  let E : ℕ → ℝ := fun t => θ * (k : ℝ) * ((d t : ℝ) / M t) +
      ((N t : ℝ) / M t) * log (q t)
  have hE : Tendsto E atTop (𝓝 (-θ)) := by
    simpa [E] using (hd.const_mul (θ * (k : ℝ))).add (hN.mul hlog)
  have hsmall : ∀ᶠ t in atTop, E t < -R :=
    (tendsto_order.mp hE).2 (-R) (by linarith)
  filter_upwards [hupper θ hθ.le, hqpos, hsmall,
    hM.eventually_gt_atTop 0] with t hup hqt het hMt
  have hMtR : (0 : ℝ) < M t := by exact_mod_cast hMt
  have he : exp (θ * (k : ℝ) * d t) * q t ^ N t =
      exp ((M t : ℝ) * E t) := by
    rw [show q t ^ N t = exp ((N t : ℝ) * log (q t)) by
      rw [exp_nat_mul, exp_log hqt], ← exp_add]
    congr 1
    dsimp [E]
    field_simp [ne_of_gt hMtR]
  change p t ≤ exp (θ * (k : ℝ) * d t) * q t ^ N t at hup
  rw [he] at hup
  exact hup.trans (exp_le_exp.mpr (by nlinarith))

theorem boundary_contact_zero_mass
    {n : ℕ} (μ : ℕ → FiniteLaw (Finset (Fin n)))
    (M C : ℕ → ℕ) (S : Finset (Fin n))
    (hM : Tendsto M atTop atTop)
    (hC : Tendsto (fun t => (C t : ℝ) / M t) atTop (𝓝 1))
    (hscarce : ∀ᶠ t in atTop, C t < M t)
    (ha : Tendsto (fun t => Shortage.allMass (μ t) S) atTop (𝓝 0)) :
    Superexponential M
      (fun t => Shortage.congestionProb (μ t) (M t - 1) (C t) S) := by
  apply zero_mass_superexponential M (fun t => M t - 1)
    (fun t => M t - 1 - C t) S.card
    (fun t => Shortage.allMass (μ t) S) _ hM
    (rival_fraction_tendsto_one M hM)
    (boundary_shortage_fraction_tendsto_zero M C hM hC hscarce) ha
  intro θ hθ
  exact Eventually.of_forall fun t =>
    Shortage.chernoff_shortage (μ t) (M t - 1) (C t) S hθ

theorem superexponential_div_deficit_tendsto_zero
    (M : ℕ → ℕ) (p C : ℕ → ℝ) (hM : Tendsto M atTop atTop)
    (hp : ∀ᶠ t in atTop, 0 ≤ p t)
    (hC : ∀ᶠ t in atTop, 0 < C t)
    (hsuper : Superexponential M p) {J : ℝ}
    (hJ : Tendsto (fun t => populationLogRate (M t) (C t)) atTop (𝓝 J)) :
    Tendsto (fun t => p t / C t) atTop (𝓝 0) := by
  have hcsmall : ∀ᶠ t in atTop,
      populationLogRate (M t) (C t) < J + 1 :=
    (tendsto_order.mp hJ).2 _ (by linarith)
  have hbound : ∀ᶠ t in atTop, p t / C t ≤ exp (-(M t : ℝ)) := by
    filter_upwards [hsuper (J + 2), hp, hC, hcsmall,
      hM.eventually_gt_atTop 0] with t hpt _hp0 hc hcj hm
    have hmR : (0 : ℝ) < M t := by exact_mod_cast hm
    have hlog : -(J + 1) * (M t : ℝ) < log (C t) := by
      dsimp [populationLogRate] at hcj
      have hh := (div_lt_iff₀ hmR).mp hcj
      linarith
    have hclower : exp (-(J + 1) * (M t : ℝ)) ≤ C t := by
      rw [← exp_log hc]
      exact exp_le_exp.mpr hlog.le
    have hdiv : p t / C t ≤ exp (-(J+2)*(M t:ℝ)) /
        exp (-(J+1)*(M t:ℝ)) := by
      calc
        _ ≤ exp (-(J+2)*(M t:ℝ)) / C t :=
          div_le_div_of_nonneg_right hpt hc.le
        _ ≤ _ := div_le_div_of_nonneg_left (exp_pos _).le (exp_pos _) hclower
    refine hdiv.trans_eq ?_
    rw [← exp_sub]
    congr 1
    ring
  have he : Tendsto (fun t => exp (-(M t : ℝ))) atTop (𝓝 0) :=
    tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_natCast_atTop_atTop.comp hM)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds he
    (by filter_upwards [hp, hC] with t hpt hct; exact div_nonneg hpt hct.le) hbound

end FCAppendix.Ample.CompletionDraft
