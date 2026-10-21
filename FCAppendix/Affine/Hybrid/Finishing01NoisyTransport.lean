import FCAppendix.Affine.Hybrid.Finishing01GuardStability
import FCAppendix.Affine.LowBody.PhysicalWeakPayoff

noncomputable section
namespace FCAppendix.Affine.Hybrid.Finish01
open Set Filter Topology MeasureTheory ProbabilityTheory Classical
open Existence.Distributional
open scoped BigOperators

theorem integral_reassociate_noise_rows
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (mu : Measure A) [IsFiniteMeasure mu]
    (nu : Measure B) [IsProbabilityMeasure nu]
    (rho : Measure C) [IsProbabilityMeasure rho]
    (f : (A×B)×C → ℝ) (hf : Measurable f)
    (K : ℝ) (hK : ∀ p, |f p| ≤ K) :
    (∫ p, f p ∂(mu.prod nu).prod rho) =
      ∫ x, ∫ r, ∫ z, f ((x,z),r) ∂nu ∂rho ∂mu := by
  have hfull : Integrable f ((mu.prod nu).prod rho) :=
    Integrable.of_bound hf.aestronglyMeasurable K
      (ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using hK p))
  have hm : Measurable (fun p : A×B => ∫ r, f (p,r) ∂rho) :=
    hf.stronglyMeasurable.integral_prod_right'.measurable
  have hb (p : A×B) : ‖∫ r, f (p,r) ∂rho‖ ≤ K := by
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (ae_of_all rho (fun r => by simpa only [Real.norm_eq_abs] using hK (p,r)))
  have hi : Integrable (fun p : A×B => ∫ r, f (p,r) ∂rho) (mu.prod nu) :=
    Integrable.of_bound hm.aestronglyMeasurable K (ae_of_all _ hb)
  rw [integral_prod _ hfull,integral_prod _ hi]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  have hxr : Integrable (fun p : B×C => f ((x,p.1),p.2)) (nu.prod rho) :=
    Integrable.of_bound (hf.comp (by fun_prop)).aestronglyMeasurable K
      (ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using hK ((x,p.1),p.2)))
  exact integral_integral_swap hxr

theorem rowLaw_map {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [TopologicalSpace.MetrizableSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [CompactSpace Y] [TopologicalSpace.MetrizableSpace Y]
    (N : ℕ) (nu : ProbabilityMeasure X) (f : X → Y) (hf : Measurable f) :
    (rowLaw N (nu.map hf.aemeasurable) : Measure (Fin N → Y)) =
      Measure.map (fun r i => f (r i)) (rowLaw N nu : Measure (Fin N → X)) := by
  rw [LowBody.rowLaw_eq_measure_pi,LowBody.rowLaw_eq_measure_pi]
  exact (Measure.pi_map_pi (fun _ : Fin N => hf.aemeasurable)).symm

namespace Primitives
variable (P : Primitives)

abbrev Latent := P.Value × P.Bid
abbrev AgentNoise := P.Latent × unitInterval
abbrev NumericRows (N : ℕ) (eps : ℝ) :=
  (Fin N → P.Low) × (Fin N → ActivePhysicalBid P.L P.U eps)

def noisyNumericRows (N : ℕ) (eps : unitInterval)
    (low : ProbabilityMeasure P.Low) (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (pi : Law (A:=P.Bid) mu) : ProbabilityMeasure (P.NumericRows N eps) :=
  productLaw (rowLaw N low)
    (rowLaw N (activeImplementedBidLaw P.L_pos eps.property.1 mu pi))

def clusterPhysicalData {N : ℕ} (eps : ℝ)
    (action : P.Latent → P.Bid) (p : P.AgentNoise × P.NumericRows N eps) :
    ActivePhysicalData N :=
  (p.1.1.1,activeNoisyRealBid eps (action p.1.1) p.1.2,
    (fun j => (p.2.1 j : ℝ)),fun j => (p.2.2 j : ℝ))

lemma measurable_clusterPhysicalData {N : ℕ} (eps : ℝ)
    (action : P.Latent → P.Bid) (ha : Measurable action) :
    Measurable (P.clusterPhysicalData (N:=N) eps action) := by
  unfold clusterPhysicalData activeNoisyRealBid
  fun_prop

def clusterGain {N : ℕ} (eps : ℝ) (c : ℕ) (kind : Fin N → Fin 4)
    (target : P.Bid) (p : P.AgentNoise × P.NumericRows N eps) : ℝ :=
  activePhysicalPatternPayoff P.xi P.z P.L (P.U*(1+eps)) c kind
      (P.clusterPhysicalData eps (fun _ => target) p) -
    activePhysicalPatternPayoff P.xi P.z P.L (P.U*(1+eps)) c kind
      (P.clusterPhysicalData eps Prod.snd p)

lemma measurable_clusterGain {N : ℕ} (eps : ℝ) (c : ℕ)
    (kind : Fin N → Fin 4) (target : P.Bid) :
    Measurable (P.clusterGain eps c kind target) := by
  exact ((measurable_activePhysicalPatternPayoff P.xi_pos P.xi_lt_one P.z P.L
      (P.U*(1+eps)) c kind).comp
      (P.measurable_clusterPhysicalData eps _ measurable_const)).sub
    ((measurable_activePhysicalPatternPayoff P.xi_pos P.xi_lt_one P.z P.L
      (P.U*(1+eps)) c kind).comp
      (P.measurable_clusterPhysicalData eps _ measurable_snd))

def payoffBound : ℝ := |P.vlo|+|P.vhi|+6*P.U

lemma payoffBound_nonneg : 0 ≤ P.payoffBound := by
  unfold payoffBound
  have hU := P.U_pos
  positivity

lemma abs_clusterPhysicalPayoff {N : ℕ} (eps : unitInterval) (c : ℕ)
    (kind : Fin N → Fin 4) (action : P.Latent → P.Bid)
    (p : P.AgentNoise × P.NumericRows N eps) :
    |activePhysicalPatternPayoff P.xi P.z P.L (P.U*(1+(eps:ℝ))) c kind
      (P.clusterPhysicalData eps action p)| ≤ P.payoffBound := by
  let t : ActivePatternInput N P.d P.vlo P.vhi P.L P.U eps :=
    ((p.1.1.1,action p.1.1),p.2)
  have h := abs_activePatternNoisyPayoff_le P.L_pos eps.property.1 P.xi_pos
    P.xi_lt_one P.z c kind t p.1.2
  rw [activePatternNoisyPayoff_eq_physical] at h
  have hv : |(p.1.1.1:ℝ)| ≤ |P.vlo|+|P.vhi| :=
    abs_le.mpr ⟨by linarith [p.1.1.1.property.1,neg_abs_le P.vlo,abs_nonneg P.vhi],
      by linarith [p.1.1.1.property.2,le_abs_self P.vhi,abs_nonneg P.vlo]⟩
  change |activePhysicalPatternPayoff P.xi P.z P.L (P.U*(1+(eps:ℝ))) c kind
    (P.clusterPhysicalData eps action p)| ≤ _ at h
  exact h.trans (by dsimp [payoffBound]; nlinarith [P.U_pos,eps.property.2])

lemma abs_clusterGain {N : ℕ} (eps : unitInterval) (c : ℕ)
    (kind : Fin N → Fin 4) (target : P.Bid) (p : P.AgentNoise × P.NumericRows N eps) :
    |P.clusterGain eps c kind target p| ≤ 2*P.payoffBound := by
  exact (abs_sub _ _).trans (by
    linarith [P.abs_clusterPhysicalPayoff eps c kind (fun _ => target) p,
      P.abs_clusterPhysicalPayoff eps c kind Prod.snd p])

lemma noisy_utility_difference_eq_cluster {N : ℕ} (eps : unitInterval)
    (heps : 0 < (eps:ℝ)) (c : ℕ) (low : ProbabilityMeasure P.Low)
    (mu : Measure P.Value) [IsProbabilityMeasure mu] (pi : Law (A:=P.Bid) mu)
    (target : P.Bid) (x : P.Latent) :
    activeNoisyExpectedUtility (N:=N) P.L_pos eps.property.1 P.xi P.z c P.categories low mu
        (pi,(x.1,target)) -
      activeNoisyExpectedUtility (N:=N) P.L_pos eps.property.1 P.xi P.z c P.categories low mu
        (pi,x) =
      ∑ kind : Fin N → Fin 4, (CommonList.iid P.categories N).mass kind *
        ∫ r, ∫ z : unitInterval, P.clusterGain eps c kind target ((x,z),r)
          ∂volume ∂(P.noisyNumericRows N eps low mu pi : Measure _) := by
  let R := P.noisyNumericRows N eps low mu pi
  have hsm (kind : Fin N → Fin 4) (a : P.Bid) :
      Integrable (fun r : P.NumericRows N eps =>
        activePatternSmoothedPayoff P.L_pos eps.property.1 P.xi P.z c kind ((x.1,a),r))
          (R : Measure _) := by
    have hc := (continuous_activePatternSmoothedPayoff P.L_pos heps P.xi_pos
      P.xi_lt_one P.z c kind).comp
        (show Continuous (fun r : P.NumericRows N eps => ((x.1,a),r)) by fun_prop)
    exact (ContinuousMap.equivBoundedOfCompact _ _ ⟨_,hc⟩).integrable _
  unfold activeNoisyExpectedUtility
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro kind _
  rw [←mul_sub]
  change (CommonList.iid P.categories N).mass kind *
    ((∫ r : P.NumericRows N eps,
      activePatternSmoothedPayoff P.L_pos eps.property.1 P.xi P.z c kind ((x.1,target),r)
        ∂(R : Measure _)) -
    (∫ r : P.NumericRows N eps,
      activePatternSmoothedPayoff P.L_pos eps.property.1 P.xi P.z c kind ((x.1,x.2),r)
        ∂(R : Measure _))) = _
  rw [←integral_sub (hsm kind target) (hsm kind x.2)]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro r
  dsimp only
  rw [activePatternSmoothedPayoff_eq_integral,activePatternSmoothedPayoff_eq_integral]
  have hnoise (a : P.Bid) : Integrable (fun z : unitInterval =>
      activePatternNoisyPayoff P.L_pos eps.property.1 P.xi P.z c kind ((x.1,a),r) z) volume := by
    have he (z : unitInterval) := activePatternNoisyPayoff_eq_physical
      P.L_pos eps.property.1 P.xi P.z c kind ((x.1,a),r) z
    have hm : Measurable (fun z : unitInterval =>
        activePatternNoisyPayoff P.L_pos eps.property.1 P.xi P.z c kind ((x.1,a),r) z) := by
      simp_rw [he]
      exact (measurable_activePhysicalPatternPayoff P.xi_pos P.xi_lt_one P.z P.L
        (P.U*(1+(eps:ℝ))) c kind).comp (by
          unfold activeNoisyPhysicalData activeNoisyRealBid
          fun_prop)
    apply Integrable.of_bound hm.aestronglyMeasurable P.payoffBound
    apply ae_of_all
    intro z
    rw [he]
    rw [Real.norm_eq_abs]
    convert! P.abs_clusterPhysicalPayoff eps c kind (fun _ => a) ((x,z),r) using 1
  rw [←integral_sub (hnoise target) (hnoise x.2)]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by
    dsimp only
    rw [activePatternNoisyPayoff_eq_physical,activePatternNoisyPayoff_eq_physical]
    rfl)

theorem actual_cluster_integral_nonpos {N : ℕ} (eps : unitInterval)
    (heps : 0 < (eps:ℝ)) (c : ℕ) (low : ProbabilityMeasure P.Low)
    (mu : Measure P.Value) [IsProbabilityMeasure mu] (pi : Law (A:=P.Bid) mu)
    (sigma : Kernel P.Value P.Bid) [IsMarkovKernel sigma]
    (hdis : mu⊗ₘsigma=(pi.1 : Measure P.Latent))
    (hopt : ∀ᵐ v ∂mu, ∀ᵐ b ∂sigma v, ∀ b' : P.Bid,
      activeNoisyExpectedUtility (N:=N) P.L_pos eps.property.1 P.xi P.z c P.categories low mu
          (pi,(v,b')) ≤
        activeNoisyExpectedUtility (N:=N) P.L_pos eps.property.1 P.xi P.z c P.categories low mu
          (pi,(v,b)))
    (E : Set P.Latent) (target : P.Bid) :
    let Gamma := ((pi.1 : Measure P.Latent).restrict E).prod (volume : Measure unitInterval)
    ∑ kind : Fin N → Fin 4, (CommonList.iid P.categories N).mass kind *
      ∫ p, P.clusterGain eps c kind target p
        ∂Gamma.prod (P.noisyNumericRows N eps low mu pi : Measure _) ≤ 0 := by
  let R := P.noisyNumericRows N eps low mu pi
  let nu := (pi.1 : Measure P.Latent).restrict E
  have hnonpos := active_noisy_integrated_deviation_nonpos (N:=N) P.L_pos heps
    P.xi_pos P.xi_lt_one P.z c P.categories low mu pi sigma hdis hopt
      (fun _ => target) measurable_const E
  have hm (kind : Fin N → Fin 4) : Measurable (fun x : P.Latent =>
      ∫ r, ∫ z : unitInterval, P.clusterGain eps c kind target ((x,z),r) ∂volume ∂(R : Measure _)) := by
    have h0 : Measurable (fun p : (P.Latent×P.NumericRows N eps)×unitInterval =>
        P.clusterGain eps c kind target ((p.1.1,p.2),p.1.2)) :=
      (P.measurable_clusterGain eps c kind target).comp (by fun_prop)
    exact h0.stronglyMeasurable.integral_prod_right'.measurable.stronglyMeasurable.integral_prod_right'.measurable
  have hb (kind : Fin N → Fin 4) (x : P.Latent) :
      ‖∫ r, ∫ z : unitInterval, P.clusterGain eps c kind target ((x,z),r)
        ∂volume ∂(R : Measure _)‖ ≤ 2*P.payoffBound := by
    apply (show (∀ᵐ r ∂(R : Measure _),
      ‖∫ z : unitInterval, P.clusterGain eps c kind target ((x,z),r) ∂volume‖ ≤ 2*P.payoffBound) → _ from
        fun h => by simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const h)
    apply ae_of_all
    intro r
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (ae_of_all (volume : Measure unitInterval) (fun z => by
        simpa only [Real.norm_eq_abs] using P.abs_clusterGain eps c kind target ((x,z),r)))
  have hi (kind : Fin N → Fin 4) : Integrable (fun x : P.Latent =>
      (CommonList.iid P.categories N).mass kind *
        ∫ r, ∫ z : unitInterval, P.clusterGain eps c kind target ((x,z),r)
          ∂volume ∂(R : Measure _)) nu :=
    (Integrable.of_bound (hm kind).aestronglyMeasurable (2*P.payoffBound)
      (ae_of_all _ (hb kind))).const_mul _
  simp_rw [P.noisy_utility_difference_eq_cluster eps heps c low mu pi target] at hnonpos
  rw [integral_finsetSum _ (fun kind _ => hi kind)] at hnonpos
  simp_rw [integral_const_mul] at hnonpos
  change (∑ kind : Fin N → Fin 4, (CommonList.iid P.categories N).mass kind *
    ∫ p, P.clusterGain eps c kind target p
      ∂(nu.prod (volume : Measure unitInterval)).prod (R : Measure _)) ≤ 0
  convert! hnonpos using 1
  apply Finset.sum_congr rfl
  intro kind _
  congr 1
  exact integral_reassociate_noise_rows nu (volume : Measure unitInterval) (R : Measure _)
    (P.clusterGain eps c kind target) (P.measurable_clusterGain eps c kind target)
    (2*P.payoffBound) (P.abs_clusterGain eps c kind target)

end Primitives
end FCAppendix.Affine.Hybrid.Finish01
