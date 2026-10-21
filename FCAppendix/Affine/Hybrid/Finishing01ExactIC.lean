import FCAppendix.Affine.Hybrid.Finishing01AugmentedIdentities
import FCAppendix.Affine.Hybrid.Finishing01ExactContinuity

noncomputable section
namespace FCAppendix.Affine.Hybrid.Finish01
open Set Filter Topology MeasureTheory ProbabilityTheory Classical
open Existence.Distributional
open scoped BigOperators
namespace Primitives
variable (P : Primitives)

theorem noisy_weighted_comparison {N : ℕ} (c : ℕ)
    (low : ProbabilityMeasure P.Low) (mu : Measure P.Value)
    [IsProbabilityMeasure mu] (pi : Law (A:=P.Bid) mu)
    (eps : unitInterval) (heps : 0 < (eps:ℝ))
    (sigma : Kernel P.Value P.Bid) [IsMarkovKernel sigma]
    (hdis : mu⊗ₘsigma=(pi.1 : Measure P.Latent))
    (hopt : ∀ᵐ v ∂mu, ∀ᵐ b ∂sigma v, ∀ b' : P.Bid,
      activeNoisyExpectedUtility (N:=N) P.L_pos eps.property.1 P.xi P.z c P.categories low mu
          (pi,(v,b')) ≤
        activeNoisyExpectedUtility (N:=N) P.L_pos eps.property.1 P.xi P.z c P.categories low mu
          (pi,(v,b)))
    (a : C(P.Latent,ℝ)) (ha : ∀ x, 0 ≤ a x) (b' : P.Bid) :
    (∫ x, a x * activeNoisyExpectedUtility (N:=N) P.L_pos eps.property.1
      P.xi P.z c P.categories low mu (pi,(x.1,b')) ∂(pi.1 : Measure P.Latent)) -
    (∫ x, a x * activeNoisyExpectedUtility (N:=N) P.L_pos eps.property.1
      P.xi P.z c P.categories low mu (pi,x) ∂(pi.1 : Measure P.Latent)) ≤ 0 := by
  let u : C(P.Latent,ℝ) := ⟨fun x => activeNoisyExpectedUtility (N:=N)
    P.L_pos eps.property.1 P.xi P.z c P.categories low mu (pi,x),
    (continuous_activeNoisyExpectedUtility P.L_pos heps P.xi_pos P.xi_lt_one
      P.z c P.categories low mu).comp (continuous_const.prodMk continuous_id)⟩
  let d : C(P.Latent,ℝ) := ⟨fun x => u (x.1,b'),
    u.continuous.comp (continuous_fst.prodMk continuous_const)⟩
  have hbest : ∀ᵐ x ∂(pi.1 : Measure P.Latent), d x ≤ u x := by
    rw [←hdis]
    apply Measure.ae_compProd_of_ae_ae (measurableSet_le d.continuous.measurable u.continuous.measurable)
    filter_upwards [hopt] with v hv
    filter_upwards [hv] with b hb
    exact hb b'
  have hd : Integrable (fun x => a x*d x) (pi.1 : Measure P.Latent) :=
    (ContinuousMap.equivBoundedOfCompact _ _ (a*d)).integrable _
  have hi : Integrable (fun x => a x*u x) (pi.1 : Measure P.Latent) :=
    (ContinuousMap.equivBoundedOfCompact _ _ (a*u)).integrable _
  exact sub_nonpos.mpr (integral_mono_ae hd hi
    (hbest.mono (fun x hx => mul_le_mul_of_nonneg_left hx (ha x))))

theorem augmented_test_sum_tendsto {N : ℕ} (c : ℕ)
    (low : ProbabilityMeasure P.Low) [NullSingletonClass (low : Measure P.Low)]
    (eps : ℕ → unitInterval) (heps : Tendsto eps atTop (𝓝 0))
    (pi : ℕ → ProbabilityMeasure P.Latent) (pi0 : ProbabilityMeasure P.Latent)
    (hpi : Tendsto pi atTop (𝓝 pi0))
    [NullSingletonClass (pi0.map measurable_snd.aemeasurable : Measure P.Bid)]
    (a : C(P.Latent,ℝ)) (action : C(P.Latent,P.Bid)) :
    Tendsto (fun j => ∑ kind : Fin N → Fin 4, (CommonList.iid P.categories N).mass kind *
      ∫ t : P.AugmentedRow N, a t.2.1.1 * P.augmentedPatternPayoff c kind action t
        ∂(P.augmentedLaw N low (eps j) (pi j) : Measure _)) atTop
      (𝓝 (∑ kind : Fin N → Fin 4, (CommonList.iid P.categories N).mass kind *
        ∫ t : P.AugmentedRow N, a t.2.1.1 * P.augmentedPatternPayoff c kind action t
          ∂(P.augmentedLaw N low 0 pi0 : Measure _))) := by
  exact tendsto_finsetSum Finset.univ (fun kind _ =>
    tendsto_const_nhds.mul
      (P.augmented_test_tendsto c kind low eps heps pi pi0 hpi a action))

theorem pass_actual_active_noisy_IC_tests {M c : ℕ}
    (low : ProbabilityMeasure P.Low) [NullSingletonClass (low : Measure P.Low)]
    (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (W : P.NoisyWitness M c low mu)
    [NullSingletonClass (W.joint.1.map measurable_snd.aemeasurable : Measure P.Bid)]
    (b' : P.Bid) (a : C(P.Latent,ℝ)) (ha : ∀ x, 0 ≤ a x) :
    ∫ x, a x * (P.exactUtility (M-1) c low mu W.joint (x.1,b') -
      P.exactUtility (M-1) c low mu W.joint x) ∂(W.joint.1 : Measure P.Latent) ≤ 0 := by
  let incumbent : C(P.Latent,P.Bid) := ⟨Prod.snd,continuous_snd⟩
  let deviation : C(P.Latent,P.Bid) := ContinuousMap.const _ b'
  have hpi : Tendsto (fun j => (W.noisy j).1) atTop (𝓝 W.joint.1) :=
    continuous_subtype_val.continuousAt.tendsto.comp W.joint_tendsto
  have hi := P.augmented_test_sum_tendsto (N:=M-1) c low W.eps W.eps_zero
    (fun j => (W.noisy j).1) W.joint.1 hpi a incumbent
  have hd := P.augmented_test_sum_tendsto (N:=M-1) c low W.eps W.eps_zero
    (fun j => (W.noisy j).1) W.joint.1 hpi a deviation
  have hnonpos : ∀ᶠ j in atTop,
      (∑ kind : Fin (M-1) → Fin 4, (CommonList.iid P.categories (M-1)).mass kind *
        ∫ t : P.AugmentedRow (M-1), a t.2.1.1 * P.augmentedPatternPayoff c kind deviation t
          ∂(P.augmentedLaw (M-1) low (W.eps j) (W.noisy j).1 : Measure _)) -
      (∑ kind : Fin (M-1) → Fin 4, (CommonList.iid P.categories (M-1)).mass kind *
        ∫ t : P.AugmentedRow (M-1), a t.2.1.1 * P.augmentedPatternPayoff c kind incumbent t
          ∂(P.augmentedLaw (M-1) low (W.eps j) (W.noisy j).1 : Measure _)) ≤ 0 := by
    filter_upwards [P.all_pattern_guard_stability (N:=M-1) c W.eps W.eps_zero] with j hj
    rw [P.augmented_test_sum_noisy (M-1) c low mu (W.noisy j) (W.eps j)
      (W.eps_pos j) hj a deviation,
      P.augmented_test_sum_noisy (M-1) c low mu (W.noisy j) (W.eps j)
      (W.eps_pos j) hj a incumbent]
    obtain ⟨sigma,hm,hdis,ho⟩ := W.noisy_IC j
    letI : IsMarkovKernel sigma := hm
    exact P.noisy_weighted_comparison c low mu (W.noisy j) (W.eps j)
      (W.eps_pos j) sigma hdis ho a ha b'
  have hlim := le_of_tendsto (hd.sub hi) hnonpos
  rw [P.augmented_test_sum_zero (M-1) c low mu W.joint a deviation,
    P.augmented_test_sum_zero (M-1) c low mu W.joint a incumbent] at hlim
  have hu := P.continuous_exactUtility (M-1) c low mu W.joint
  have hdI : Integrable (fun x : P.Latent =>
      a x * P.exactUtility (M-1) c low mu W.joint (x.1,b')) (W.joint.1 : Measure P.Latent) :=
    (ContinuousMap.equivBoundedOfCompact _ _ ⟨_,a.continuous.mul
      (hu.comp (continuous_fst.prodMk continuous_const))⟩).integrable _
  have hiI : Integrable (fun x : P.Latent =>
      a x * P.exactUtility (M-1) c low mu W.joint x) (W.joint.1 : Measure P.Latent) :=
    (ContinuousMap.equivBoundedOfCompact _ _ ⟨_,a.continuous.mul hu⟩).integrable _
  change (∫ x, a x * P.exactUtility (M-1) c low mu W.joint (x.1,b') ∂(W.joint.1 : Measure P.Latent)) -
    (∫ x, a x * P.exactUtility (M-1) c low mu W.joint x ∂(W.joint.1 : Measure P.Latent)) ≤ 0 at hlim
  rw [←integral_sub hdI hiI] at hlim
  simpa only [mul_sub] using hlim

theorem exact_IC_of_actual_noisyWitness {M c : ℕ}
    (low : ProbabilityMeasure P.Low) (hlow : NullSingletonClass (low : Measure P.Low))
    (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (W : P.NoisyWitness M c low mu)
    (hG : NullSingletonClass (W.joint.1.map measurable_snd.aemeasurable : Measure P.Bid)) :
    ∀ᵐ x ∂(W.joint.1 : Measure P.Latent), ∀ b' : P.Bid,
      P.exactUtility (M-1) c low mu W.joint (x.1,b') ≤
        P.exactUtility (M-1) c low mu W.joint x := by
  letI := hlow
  letI := hG
  apply P.common_conull_all_bids (M-1) c low mu W.joint
  intro b'
  apply P.continuous_tests_imply_ae_deviation_order (M-1) c low mu W.joint b'
  exact fun a ha => P.pass_actual_active_noisy_IC_tests low mu W b' a ha

end Primitives
end FCAppendix.Affine.Hybrid.Finish01
