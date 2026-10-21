import FCAppendix.Affine.UniformFinite.NoisyFixedPoint

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open MeasureTheory ProbabilityTheory Set Filter Topology
open Existence.Distributional

def noiseSchedule (a : unitInterval) (n : ℕ) : unitInterval :=
  ⟨(a:ℝ)/(n+1),div_nonneg a.property.1 (by positivity),by
    apply (div_le_iff₀ (by positivity : (0:ℝ)< n+1)).mpr
    nlinarith [a.property.2,(Nat.cast_nonneg n : (0:ℝ)≤n)]⟩

lemma noiseSchedule_pos (a : unitInterval) (ha : 0<(a:ℝ)) (n : ℕ) :
    0<(noiseSchedule a n:ℝ) := div_pos ha (by positivity)

lemma noiseSchedule_le (a : unitInterval) (n : ℕ) : (noiseSchedule a n:ℝ)≤ a := by
  apply (div_le_iff₀ (by positivity : (0:ℝ)< n+1)).mpr
  nlinarith [a.property.1,(Nat.cast_nonneg n : (0:ℝ)≤n)]

lemma noiseSchedule_tendsto_zero (a : unitInterval) :
    Tendsto (noiseSchedule a) atTop (𝓝 0) := by
  apply tendsto_subtype_rng.mpr
  convert! ((tendsto_const_nhds (x := (a:ℝ))).mul
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))) using 1
  · funext n
    change (a:ℝ)/(n+1)=(a:ℝ)*(1/(n+1))
    ring
  · simp

theorem exists_actual_noisy_compact_limit (i : Row) (N : ℕ)
    (a : unitInterval) (ha : 0<(a:ℝ)) :
    ∃(eps : ℕ→ unitInterval)(pi : ℕ→ Joint i)(pi0 : Joint i)
      (sigma : ℕ→ Kernel (Value i) unitInterval),
      (∀n,0<(eps n:ℝ) ∧ (eps n:ℝ)≤ a) ∧
      Tendsto eps atTop (𝓝 0) ∧
      (∀n,NoisyIC i N (eps n) (pi n)) ∧
      (∀n,DisintegratedNoisyIC i N (eps n) (pi n) (sigma n)) ∧
      Tendsto pi atTop (𝓝 pi0) ∧
      Tendsto (fun n=> physicalLaw i (eps n,pi n)) atTop (𝓝 (physicalLaw i (0,pi0))) ∧
      Tendsto (fun n=> restrictedLaw i (eps n,pi n)) atTop (𝓝 (restrictedLaw i (0,pi0))) := by
  choose pi sigma hmark hdis hIC hconditional using
    (fun n=> exists_noisy_restricted_law i N (noiseSchedule a n) (noiseSchedule_pos a ha n))
  obtain ⟨pi0,phi,hphi,hlim⟩ := CompactSpace.tendsto_subseq pi
  have heps := (noiseSchedule_tendsto_zero a).comp hphi.tendsto_atTop
  refine ⟨noiseSchedule a∘phi,pi∘phi,pi0,sigma∘phi,?_,heps,?_,?_,hlim,?_,?_⟩
  · intro n
    exact ⟨noiseSchedule_pos a ha (phi n),noiseSchedule_le a (phi n)⟩
  · exact fun n=> hIC (phi n)
  · exact fun n=>⟨hmark (phi n),hdis (phi n),hconditional (phi n)⟩
  · exact (continuous_physicalLaw i).continuousAt.tendsto.comp (heps.prodMk_nhds hlim)
  · exact (continuous_restrictedLaw i).continuousAt.tendsto.comp (heps.prodMk_nhds hlim)

end FCAppendix.Affine.UniformFinite
