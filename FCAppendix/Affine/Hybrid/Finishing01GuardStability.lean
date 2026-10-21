import FCAppendix.Affine.Hybrid.Finishing01Definitions

noncomputable section
namespace FCAppendix.Affine.Hybrid.Finish01
open Set Filter Topology MeasureTheory ProbabilityTheory

lemma normalizedGuard_mono_upper {xi L U W : ℝ} {p : Fin 4 → ℝ}
    (hxi : xi < 1) (hUW : U ≤ W)
    (h : NormalizedGuardRegion xi L W p) :
    NormalizedGuardRegion xi L U p := by
  rcases h with ⟨hD,hR,hRD,hF,hlo,hhi⟩
  refine ⟨hD,hR,hRD,hF,?_,?_⟩
  · exact (mul_le_mul_of_nonneg_left hUW (sub_pos.mpr hxi).le).trans_lt hlo
  · exact (mul_le_mul_of_nonneg_left hUW hF.le).trans_lt hhi

lemma activeGuard_mono_upper {N : ℕ} {xi L U W z : ℝ}
    (hxi : xi < 1) (hUW : U ≤ W) (c : ℕ) (kind : Fin N → Fin 4)
    (h : activePatternGuarded xi L W c z kind) :
    activePatternGuarded xi L U c z kind := by
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,
    normalizedGuard_mono_upper hxi hUW h.2.2.2.2.1,h.2.2.2.2.2⟩

lemma eventually_normalizedGuard_noisy_upper {xi L U : ℝ} {p : Fin 4 → ℝ}
    (h : NormalizedGuardRegion xi L U p) :
    ∀ᶠ e : ℝ in 𝓝 0, NormalizedGuardRegion xi L (U*(1+e)) p := by
  have hlo : (1-xi)*(U*(1+(0:ℝ))) < normalizedFactor xi p*L := by
    simpa only [add_zero,mul_one] using h.2.2.2.2.1
  have hhi : normalizedFactor xi p*(U*(1+(0:ℝ))) < L := by
    simpa only [add_zero,mul_one] using h.2.2.2.2.2
  have clo : Continuous (fun e : ℝ => (1-xi)*(U*(1+e))) := by fun_prop
  have chi : Continuous (fun e : ℝ => normalizedFactor xi p*(U*(1+e))) := by fun_prop
  filter_upwards [clo.continuousAt.eventually (Iio_mem_nhds hlo),
    chi.continuousAt.eventually (Iio_mem_nhds hhi)] with e helo hehi
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,helo,hehi⟩

namespace Primitives
variable (P : Primitives)

theorem active_guard_stability {N : ℕ} (c : ℕ) (kind : Fin N → Fin 4)
    (eps : ℕ → unitInterval) (heps : Tendsto eps atTop (𝓝 0)) :
    ∀ᶠ j in atTop,
      (activePatternGuarded P.xi P.L (P.U*(1+(eps j:ℝ))) c P.z kind ↔
        activePatternGuarded P.xi P.L P.U c P.z kind) := by
  have hepsR : Tendsto (fun j => (eps j:ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Set.Icc.coe_zero] using
      (continuous_subtype_val.tendsto (0:unitInterval)).comp heps
  by_cases hg : activePatternGuarded P.xi P.L P.U c P.z kind
  · have ht := hepsR.eventually (eventually_normalizedGuard_noisy_upper hg.2.2.2.2.1)
    filter_upwards [ht] with j hj
    exact ⟨fun _ => hg,fun _ => ⟨hg.1,hg.2.1,hg.2.2.1,hg.2.2.2.1,hj,hg.2.2.2.2.2⟩⟩
  · apply Eventually.of_forall
    intro j
    have hUW : P.U ≤ P.U*(1+(eps j:ℝ)) := by
      nlinarith [P.U_pos,(eps j).property.1]
    exact ⟨fun hj => False.elim (hg (activeGuard_mono_upper P.xi_lt_one hUW c kind hj)),
      fun h => False.elim (hg h)⟩

theorem all_pattern_guard_stability {N : ℕ} (c : ℕ)
    (eps : ℕ → unitInterval) (heps : Tendsto eps atTop (𝓝 0)) :
    ∀ᶠ j in atTop, ∀ kind : Fin N → Fin 4,
      (activePatternGuarded P.xi P.L (P.U*(1+(eps j:ℝ))) c P.z kind ↔
        activePatternGuarded P.xi P.L P.U c P.z kind) := by
  exact eventually_all.mpr (fun kind => P.active_guard_stability c kind eps heps)

theorem all_pattern_physical_guard_identity {N : ℕ} (c : ℕ)
    (eps : ℕ → unitInterval) (heps : Tendsto eps atTop (𝓝 0)) :
    ∀ᶠ j in atTop, ∀ kind : Fin N → Fin 4, ∀ t : ActivePhysicalData N,
      activePhysicalPatternPayoff P.xi P.z P.L (P.U*(1+(eps j:ℝ))) c kind t =
        activePhysicalPatternPayoff P.xi P.z P.L P.U c kind t := by
  filter_upwards [P.all_pattern_guard_stability (N:=N) c eps heps] with j hj kind t
  unfold activePhysicalPatternPayoff
  dsimp only
  rw [propext (hj kind)]

theorem eventually_noise_below (eps : ℕ → unitInterval)
    (heps : Tendsto eps atTop (𝓝 0)) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ j in atTop, (eps j:ℝ)*P.U < r := by
  have hepsR : Tendsto (fun j => (eps j:ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Set.Icc.coe_zero] using
      (continuous_subtype_val.tendsto (0:unitInterval)).comp heps
  have ht : Tendsto (fun j => (eps j:ℝ)*P.U) atTop (𝓝 0) := by
    simpa using hepsR.mul_const P.U
  exact ht.eventually (Iio_mem_nhds hr)

end Primitives
end FCAppendix.Affine.Hybrid.Finish01
