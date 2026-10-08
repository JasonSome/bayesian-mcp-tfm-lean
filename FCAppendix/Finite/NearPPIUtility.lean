import FCAppendix.Finite.CutoffIdentification

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter Set Topology
open scoped BigOperators ProbabilityTheory

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem typeUtility_monotone (Γ : FiniteGame m n c Seed) : Monotone (typeUtility Γ) := by
  intro v w hvw
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ =>
    (problem Γ i).envelope_monotone hvw) (Nat.cast_nonneg _)

theorem typeUtility_lipschitz_inequality (Γ : FiniteGame m n c Seed) (hm : 0 < m) (v w : ℝ) :
    |typeUtility Γ v - typeUtility Γ w| ≤ |v - w| := by
  rw [typeUtility, typeUtility, ← sub_div, ← Finset.sum_sub_distrib, abs_div,
    abs_of_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  apply (div_le_iff₀ (Nat.cast_pos.mpr hm : (0 : ℝ) < m)).mpr
  calc
    _ ≤ ∑ i, |(problem Γ i).envelope v - (problem Γ i).envelope w| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, |v - w| := Finset.sum_le_sum fun i _ =>
      (problem Γ i).envelope_lipschitz_inequality v w
    _ = _ := by simp [mul_comm]

theorem monotone_utility_le_mean_error (F : Measure ℝ) [IsProbabilityMeasure F]
    (U e : ℝ → ℝ) (c w : ℝ) (hmono : Monotone U)
    (hI : Integrable e F) (he : 0 ≤ᵐ[F] e)
    (hupper : ∀ᵐ v ∂F, v < c → U v ≤ e v) :
    F.real (Ioo w c) * U w ≤ ∫ v, e v ∂F := by
  classical
  have hh := integral_mono_ae ((integrable_const (U w)).indicator measurableSet_Ioo) hI
    (show (Ioo w c).indicator (fun _ => U w) ≤ᵐ[F] e from by
      filter_upwards [he, hupper] with v he hu
      by_cases hv : v ∈ Ioo w c
      · rw [indicator_of_mem hv]
        exact (hmono hv.1.le).trans (hu hv.2)
      · rw [indicator_of_notMem hv]
        exact he)
  simpa only [integral_indicator_const _ measurableSet_Ioo, smul_eq_mul] using hh

theorem typeUtility_limit_of_errors
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed)
    (hm : ∀ k, 0 < M k)
    (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ∀ k, (Γ k).F = F)
    (g p : ℝ) (hg : ∀ k, (Γ k).g = g) (hp : 0 ≤ p)
    (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k) (hΓ : ∀ k, UsersOptimal (Γ k))
    (hA : ∀ k r, 0 < r → r ≤ n → a k * (r : ℝ) ≤ (Γ k).A.charge r)
    (δ : ℕ → ℝ → ℝ)
    (hlower : ∀ k (i : Fin (M k)) v,
      max (v - g - p) 0 - δ k v ≤ (problem (Γ k) i).envelope v)
    (hδ : ∀ v, Tendsto (fun k => δ k v) atTop (𝓝 0))
    (he0 : Tendsto (fun k => ∫ v, typePaymentError (Γ k) (a k) p v ∂F) atTop (𝓝 0))
    (hleft : ∀ v < g + p, 0 < F.real (Ioo v (g + p))) :
    ∀ v, Tendsto (fun k => typeUtility (Γ k) v) atTop (𝓝 (max (v - (g + p)) 0)) := by
  have hIe (k : ℕ) : Integrable (typePaymentError (Γ k) (a k) p) F := by
    rw [← hF k]
    exact integrable_typePaymentError (Γ k) (a k) p (ha k) hp
  have hbelow (w : ℝ) (hw : w < g + p) :
      Tendsto (fun k => typeUtility (Γ k) w) atTop (𝓝 0) := by
    have hmass := hleft w hw
    apply squeeze_zero (fun k => typeUtility_nonneg (Γ k) w)
      (g := fun k => (∫ v, typePaymentError (Γ k) (a k) p v ∂F) / F.real (Ioo w (g + p)))
    · intro k
      apply (le_div_iff₀ hmass).mpr
      have hup := ae_typeUtility_le_price_error (Γ k) (hm k) (hΓ k) (a k) p (ha k) hp (hA k)
      rw [hF k] at hup
      have hh := monotone_utility_le_mean_error F (typeUtility (Γ k))
        (typePaymentError (Γ k) (a k) p) (g + p) w (typeUtility_monotone (Γ k)) (hIe k)
        (Eventually.of_forall (typePaymentError_nonneg (Γ k) (a k) p)) (by
          filter_upwards [hup] with v hv hvc
          rw [hg k] at hv
          have hS := (conditionalTypeCountLaw (Γ k) (hm k) v).success_nonneg
          have hD := (conditionalTypeCountLaw (Γ k) (hm k) v).duplicates_nonneg
          have hPD := mul_nonneg hp hD
          have hnet : v - g - p ≤ 0 := by linarith
          have hmult := mul_nonpos_of_nonpos_of_nonneg hnet hS
          linarith)
      simpa only [mul_comm] using hh
    · simpa only [zero_div] using he0.div_const (F.real (Ioo w (g + p)))
  apply NearPPI.utility_limit_across_support_gaps
    (fun k => typeUtility_monotone (Γ k))
    (fun k => typeUtility_lipschitz_inequality (Γ k) (hm k))
    (fun k v => by simpa only [sub_add_eq_sub_sub] using
      typeUtility_lower (Γ k) (hm k) v _ (fun i => hlower k i v)) hδ
  intro ε hε
  refine ⟨g + p - ε / 2, by linarith, by linarith, ?_⟩
  exact hbelow _ (by linarith)

theorem cutoff_gt_fee_of_scarcity (F : Measure ℝ) [IsFiniteMeasure F]
    (g vstar β : ℝ) (hcut : F.real (Ioi vstar) = β) (hscarce : β < F.real (Ioi g)) :
    g < vstar := by
  by_contra h
  have hvg : vstar ≤ g := le_of_not_gt h
  have hh : F.real (Ioi g) ≤ F.real (Ioi vstar) :=
    measureReal_mono (fun _ hx => lt_of_le_of_lt hvg hx)
  rw [hcut] at hh
  exact (not_le_of_gt hscarce) hh

theorem nearPPI_typeUtility_limit
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed) (j : Fin n)
    (F : Measure ℝ) [IsProbabilityMeasure F] [NullSingletonClass F]
    (hF : ∀ k, (Γ k).F = F) (g : ℝ) (hg : ∀ k, (Γ k).g = g)
    (a : ℕ → ℝ) (ρ vstar : ℝ) (hρ0 : 0 < ρ) (hρ : ρ < 1)
    (hM : Tendsto M atTop atTop)
    (hcap : Tendsto (fun k => (C k : ℝ) / M k) atTop (𝓝 ρ))
    (ha : Tendsto a atTop (𝓝 1))
    (hΓ : ∀ k, IsAEEquilibrium (Γ k))
    (hp : ∀ k j, ProposerRationalAtFeasibleLists (Γ k) j)
    (hatom : ∀ k, PositiveVisibleAtomless (Γ k))
    (hA : ∀ k r, 0 < r → r ≤ n → a k * (r : ℝ) ≤ (Γ k).A.charge r)
    (hscarce : (n : ℝ) * ρ < F.real (Ioi g))
    (hcutoff : F.real (Ioi vstar) = (n : ℝ) * ρ)
    (hleft : ∀ v < vstar, 0 < F.real (Ioo v vstar))
    (hright : ∀ v > vstar, 0 < F.real (Ioo vstar v)) :
    ∀ v, Tendsto (fun k => typeUtility (Γ k) v) atTop (𝓝 (max (v - vstar) 0)) := by
  have hpos : 0 < vstar - g := sub_pos.mpr (cutoff_gt_fee_of_scarcity F g vstar _ hcutoff hscarce)
  have hquant := nearPPI_visible_quantile_limit M C Γ j F hF g hg a ρ vstar hρ0 hρ hM hcap ha
    hΓ hp hatom hA hscarce hcutoff hleft hright
  obtain ⟨δ, _, _, hδ0, hlower⟩ := exists_vanishing_singleton_error M C Γ j g hg
    a ρ (ρ / 2) (vstar - g) hρ (by positivity) (by linarith) hM hcap ha hΓ hp hatom hA
    (hquant (ρ / 2) (by positivity) (by linarith))
  have he0 := tendsto_mean_typePaymentError_of_visible_tail M C Γ j a (vstar - g) ρ hpos.le hρ0.le
    hM ha hcap (fun k => (hΓ k).proposers) hA
    (visible_tail_below_common_quantile_limit M C Γ j ρ (vstar - g) hpos hquant)
  simp_rw [hF] at he0
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((hM.eventually_gt_atTop 0).and
    ((tendsto_order.mp ha).1 0 zero_lt_one))
  have hs : Tendsto (fun k : ℕ => k + N) atTop atTop := tendsto_add_atTop_nat N
  have hcut : g + (vstar - g) = vstar := by ring
  have hleft' : ∀ v < g + (vstar - g), 0 < F.real (Ioo v (g + (vstar - g))) := by
    simpa only [hcut] using hleft
  have hU := typeUtility_limit_of_errors (fun k => M (k + N)) (fun k => C (k + N))
    (fun k => Γ (k + N)) (fun k => (hN (k + N) (by omega)).1)
    F (fun k => hF (k + N)) g (vstar - g) (fun k => hg (k + N)) hpos.le
    (fun k => a (k + N)) (fun k => (hN (k + N) (by omega)).2.le) (fun k => (hΓ (k + N)).users)
    (fun k => hA (k + N)) (fun k => δ (k + N)) (fun k => hlower (k + N))
    (fun v => (hδ0 v).comp hs) (he0.comp hs) hleft'
  intro v
  apply (tendsto_add_atTop_iff_nat N).mp
  simpa only [hcut] using hU v

end FCAppendix.Bayes
