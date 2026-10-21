import FCAppendix.Affine.Hybrid.Finishing01PhysicalContinuity

set_option synthInstance.maxSize 1000
set_option maxHeartbeats 1500000
noncomputable section
namespace FCAppendix.Affine.Hybrid.Finish01
open Set Filter Topology MeasureTheory ProbabilityTheory Classical
open Existence.Distributional
open scoped BigOperators
namespace Primitives
variable (P : Primitives)

abbrev AugmentedRow (N : ℕ) :=
  unitInterval × (P.AgentNoise × ((Fin N → P.Low) × (Fin N → P.AgentNoise)))

def agentNoiseLaw (pi : ProbabilityMeasure P.Latent) : ProbabilityMeasure P.AgentNoise :=
  productLaw pi (⟨volume,inferInstance⟩ : ProbabilityMeasure unitInterval)

def augmentedLaw (N : ℕ) (low : ProbabilityMeasure P.Low)
    (eps : unitInterval) (pi : ProbabilityMeasure P.Latent) :
    ProbabilityMeasure (P.AugmentedRow N) :=
  productLaw (diracProba eps) (productLaw (P.agentNoiseLaw pi)
    (productLaw (rowLaw N low) (rowLaw N (P.agentNoiseLaw pi))))

lemma continuous_agentNoiseLaw : Continuous P.agentNoiseLaw :=
  continuous_productLaw.comp (continuous_id.prodMk continuous_const)

lemma continuous_augmentedLaw (N : ℕ) (low : ProbabilityMeasure P.Low) :
    Continuous (fun t : unitInterval × ProbabilityMeasure P.Latent => P.augmentedLaw N low t.1 t.2) := by
  exact continuous_productLaw.comp ((continuous_diracProba.comp continuous_fst).prodMk
    (continuous_productLaw.comp ((P.continuous_agentNoiseLaw.comp continuous_snd).prodMk
      (continuous_productLaw.comp (continuous_const.prodMk
        ((continuous_rowLaw N).comp (P.continuous_agentNoiseLaw.comp continuous_snd)))))))

def augmentedPhysicalData {N : ℕ} (action : C(P.Latent,P.Bid))
    (t : P.AugmentedRow N) : ActivePhysicalData N :=
  (t.2.1.1.1,activeNoisyRealBid t.1 (action t.2.1.1) t.2.1.2,
    (fun j => (t.2.2.1 j:ℝ)),
    fun j => activeNoisyRealBid t.1 (t.2.2.2 j).1.2 (t.2.2.2 j).2)

lemma continuous_augmentedPhysicalData {N : ℕ} (action : C(P.Latent,P.Bid)) :
    Continuous (P.augmentedPhysicalData (N:=N) action) := by
  unfold augmentedPhysicalData activeNoisyRealBid
  fun_prop

lemma noisy_bid_universal_mem (eps : unitInterval) (b : P.Bid) (z : unitInterval) :
    activeNoisyRealBid eps b z ∈ Icc P.L (2*P.U) := by
  have h := activeNoisyRealBid_mem P.L_pos eps.property.1 b z
  refine ⟨h.1,h.2.trans ?_⟩
  nlinarith [P.U_pos,eps.property.2]

lemma augmented_active_bid_mem {N : ℕ} (action : C(P.Latent,P.Bid))
    (kind : Fin N → Fin 4) (t : P.AugmentedRow N) :
    ∀ i, activePhysicalActiveBids kind (P.augmentedPhysicalData action t) i ∈ Icc P.L (2*P.U) := by
  intro i
  rcases Fin.eq_zero_or_eq_succ i.val with hi | ⟨j,hj⟩
  · simpa only [activePhysicalActiveBids,augmentedPhysicalData,hi,Fin.cases_zero] using
      P.noisy_bid_universal_mem t.1 (action t.2.1.1) t.2.1.2
  · simpa only [activePhysicalActiveBids,augmentedPhysicalData,hj,Fin.cases_succ] using
      P.noisy_bid_universal_mem t.1 (t.2.2.2 j).1.2 (t.2.2.2 j).2

lemma augmented_lower_bid_nonneg {N : ℕ} (action : C(P.Latent,P.Bid))
    (kind : Fin N → Fin 4) (t : P.AugmentedRow N) :
    ∀ i, 0 ≤ activePhysicalBids kind (P.augmentedPhysicalData action t) i := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact P.L_pos.le.trans (P.noisy_bid_universal_mem t.1 (action t.2.1.1) t.2.1.2).1
  · simp only [activePhysicalBids,augmentedPhysicalData,Fin.cons_succ]
    split_ifs
    · exact (t.2.2.1 j).property.1
    · exact P.L_pos.le.trans
        (P.noisy_bid_universal_mem t.1 (t.2.2.2 j).1.2 (t.2.2.2 j).2).1
    · exact le_rfl

def augmentedPatternPayoff {N : ℕ} (c : ℕ) (kind : Fin N → Fin 4)
    (action : C(P.Latent,P.Bid)) (t : P.AugmentedRow N) : ℝ :=
  activePhysicalPatternPayoff P.xi P.z P.L P.U c kind (P.augmentedPhysicalData action t)

lemma measurable_augmentedPatternPayoff {N : ℕ} (c : ℕ) (kind : Fin N → Fin 4)
    (action : C(P.Latent,P.Bid)) : Measurable (P.augmentedPatternPayoff c kind action) :=
  (measurable_activePhysicalPatternPayoff P.xi_pos P.xi_lt_one P.z P.L P.U c kind).comp
    (P.continuous_augmentedPhysicalData action).measurable

def augmentedBadSet {N : ℕ} (kind : Fin N → Fin 4) (action : C(P.Latent,P.Bid)) :
    Set (P.AugmentedRow N) := P.augmentedPhysicalData action ⁻¹' physicalBadSet P.kappa kind

lemma isClosed_augmentedBadSet {N : ℕ} (kind : Fin N → Fin 4)
    (action : C(P.Latent,P.Bid)) : IsClosed (P.augmentedBadSet kind action) :=
  (isClosed_physicalBadSet P.kappa kind).preimage (P.continuous_augmentedPhysicalData action)

lemma continuousAt_augmentedPatternPayoff {N : ℕ} (c : ℕ) (kind : Fin N → Fin 4)
    (action : C(P.Latent,P.Bid)) (t : P.AugmentedRow N)
    (ht : t ∉ P.augmentedBadSet kind action) :
    ContinuousAt (P.augmentedPatternPayoff c kind action) t := by
  exact (continuousAt_physical_of_not_bad P.xi_pos P.xi_lt_one P.z P.L P.U c kind
    (P.augmentedPhysicalData action t) (P.augmented_lower_bid_nonneg action kind t)
      (fun i => P.L_pos.trans_le (P.augmented_active_bid_mem action kind t i).1) ht).comp
        (P.continuous_augmentedPhysicalData action).continuousAt

lemma exists_augmented_payoff_bound {N : ℕ} (c : ℕ) (kind : Fin N → Fin 4)
    (action : C(P.Latent,P.Bid)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : P.AugmentedRow N, |P.augmentedPatternPayoff c kind action t| ≤ K := by
  by_cases hguard : activePatternGuarded P.xi P.L P.U c P.z kind
  · obtain ⟨K,hK⟩ := exists_joint_sourceOwnerPayoff_box_bound
      (L:=P.L) (U:=2*P.U) (vlo:=P.vlo) (vhi:=P.vhi) P.L_pos P.xi P.eta
        (activePatternResidual c P.z kind) (activePatternOwner c P.z kind 0)
        (activePatternOwner c P.z kind 1) (activePatternFocal kind)
        hguard.1 hguard.2.2.1 hguard.2.2.2.1
    refine ⟨|K|,abs_nonneg K,?_⟩
    intro t
    have h := hK t.2.1.1.1 t.2.1.1.1.property
      (activePhysicalActiveBids kind (P.augmentedPhysicalData action t))
      (P.augmented_active_bid_mem action kind t)
    simpa only [augmentedPatternPayoff,activePhysicalPatternPayoff,if_pos hguard,
      augmentedPhysicalData,eta,Real.norm_eq_abs] using h.trans (le_abs_self K)
  · refine ⟨P.payoffBound,P.payoffBound_nonneg,?_⟩
    intro t
    have hv : |(t.2.1.1.1:ℝ)| ≤ |P.vlo|+|P.vhi| := abs_le.mpr
      ⟨by linarith [t.2.1.1.1.property.1,neg_abs_le P.vlo,abs_nonneg P.vhi],
        by linarith [t.2.1.1.1.property.2,le_abs_self P.vhi,abs_nonneg P.vlo]⟩
    have hb := P.noisy_bid_universal_mem t.1 (action t.2.1.1) t.2.1.2
    have hba : |activeNoisyRealBid t.1 (action t.2.1.1) t.2.1.2| ≤ 2*P.U := by
      rw [abs_of_pos (P.L_pos.trans_le hb.1)]
      exact hb.2
    unfold augmentedPatternPayoff activePhysicalPatternPayoff
    dsimp only
    rw [if_neg hguard]
    split_ifs
    · have h := LowBody.abs_equalPayoff_le P.xi_pos P.xi_lt_one
        (activePatternTemplate c kind).residual₀ 0 (t.2.1.1.1:ℝ)
          (activePhysicalBids kind (P.augmentedPhysicalData action t))
      simp only [augmentedPhysicalData,activePhysicalBids,Fin.cons_zero] at h
      exact h.trans (by change _ ≤ |P.vlo|+|P.vhi|+6*P.U; nlinarith [P.U_pos])
    · have h := LowBody.abs_purePayoff_le (1-P.xi) (t.2.1.1.1:ℝ)
        (activePhysicalBids kind (P.augmentedPhysicalData action t))
        ((activePatternTemplate c kind).selection (1-P.xi)
          (activePhysicalBids kind (P.augmentedPhysicalData action t))) 0
      have hk : |1-P.xi| ≤ 1 := by rw [abs_of_pos (show 0 < 1 - P.xi from P.kappa_pos)]; linarith [P.xi_pos]
      simp only [augmentedPhysicalData,activePhysicalBids,Fin.cons_zero] at h
      apply h.trans
      have hh := mul_le_mul_of_nonneg_right hk (abs_nonneg (activeNoisyRealBid t.1 (action t.2.1.1) t.2.1.2))
      dsimp only [payoffBound]
      nlinarith

lemma agent_base_bid_ae_ne (pi : ProbabilityMeasure P.Latent)
    [NullSingletonClass (pi.map measurable_snd.aemeasurable : Measure P.Bid)]
    (b : ℝ) : ∀ᵐ x ∂(P.agentNoiseLaw pi : Measure P.AgentNoise), (x.1.2:ℝ) ≠ b := by
  have h := ae_subtype_val_ne (pi.map measurable_snd.aemeasurable : Measure P.Bid) b
  have hx : ∀ᵐ x ∂(pi : Measure P.Latent), (x.2:ℝ) ≠ b :=
    ae_of_ae_map measurable_snd.aemeasurable h
  exact (measurePreserving_fst (μ:=(pi : Measure P.Latent))
    (ν:=(volume : Measure unitInterval))).quasiMeasurePreserving.ae hx

lemma augmentedBadSet_null {N : ℕ} (low : ProbabilityMeasure P.Low)
    [NullSingletonClass (low : Measure P.Low)] (pi : ProbabilityMeasure P.Latent)
    [NullSingletonClass (pi.map measurable_snd.aemeasurable : Measure P.Bid)]
    (kind : Fin N → Fin 4) (action : C(P.Latent,P.Bid)) :
    (P.augmentedLaw N low 0 pi : Measure _) (P.augmentedBadSet kind action)=0 := by
  have hm : MeasurableSet {t : P.AugmentedRow N | t ∉ P.augmentedBadSet kind action} :=
    (P.isClosed_augmentedBadSet kind action).measurableSet.compl
  apply measure_eq_zero_iff_ae_notMem.mpr
  change ∀ᵐ t ∂(Measure.dirac (0:unitInterval)).prod
    ((P.agentNoiseLaw pi : Measure P.AgentNoise).prod
      ((rowLaw N low : Measure (Fin N → P.Low)).prod
        (rowLaw N (P.agentNoiseLaw pi) : Measure (Fin N → P.AgentNoise)))), _
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  simp only [ae_dirac_eq,Filter.eventually_pure]
  have hm0 := hm.preimage ((measurable_const (a := (0 : unitInterval))).prodMk measurable_id)
  apply (Measure.ae_prod_iff_ae_ae hm0).mpr
  apply ae_of_all
  intro x
  rw [LowBody.rowLaw_eq_measure_pi,LowBody.rowLaw_eq_measure_pi]
  have h := ae_two_rows_not_bad (low : Measure P.Low) (P.agentNoiseLaw pi : Measure P.AgentNoise)
    (fun b : P.Low => (b:ℝ)) (fun y : P.AgentNoise => (y.1.2:ℝ))
    measurable_subtype_coe (by fun_prop)
    (ae_subtype_val_ne (low : Measure P.Low)) (P.agent_base_bid_ae_ne pi)
    P.kappa_pos (P.bid_pos (action x.1)) (x.1.1:ℝ) kind
  simpa only [augmentedBadSet,mem_preimage,augmentedPhysicalData,activeNoisyRealBid,
    mul_zero,zero_mul,one_mul,mul_one,add_zero,Set.Icc.coe_zero,id_eq,mem_setOf_eq] using h

theorem augmented_test_tendsto {N : ℕ} (c : ℕ) (kind : Fin N → Fin 4)
    (low : ProbabilityMeasure P.Low) [NullSingletonClass (low : Measure P.Low)]
    (eps : ℕ → unitInterval) (heps : Tendsto eps atTop (𝓝 0))
    (pi : ℕ → ProbabilityMeasure P.Latent) (pi0 : ProbabilityMeasure P.Latent)
    (hpi : Tendsto pi atTop (𝓝 pi0))
    [NullSingletonClass (pi0.map measurable_snd.aemeasurable : Measure P.Bid)]
    (a : C(P.Latent,ℝ)) (action : C(P.Latent,P.Bid)) :
    Tendsto (fun j => ∫ t : P.AugmentedRow N,
      a t.2.1.1 * P.augmentedPatternPayoff c kind action t
        ∂(P.augmentedLaw N low (eps j) (pi j) : Measure _)) atTop
      (𝓝 (∫ t : P.AugmentedRow N,
        a t.2.1.1 * P.augmentedPatternPayoff c kind action t
          ∂(P.augmentedLaw N low 0 pi0 : Measure _))) := by
  obtain ⟨K,hK,hbound⟩ := P.exists_augmented_payoff_bound c kind action
  have ht : Tendsto (fun j => P.augmentedLaw N low (eps j) (pi j)) atTop
      (𝓝 (P.augmentedLaw N low 0 pi0)) := by
    have hp : Tendsto (fun j => (eps j, pi j)) atTop (𝓝 ((0 : unitInterval), pi0)) := heps.prodMk_nhds hpi
    convert! ((P.continuous_augmentedLaw N low).tendsto ((0 : unitInterval), pi0)).comp hp using 1
  let f : P.AugmentedRow N → ℝ := fun t =>
    a t.2.1.1 * P.augmentedPatternPayoff c kind action t
  have hm : Measurable f := by
    exact (a.continuous.measurable.comp (show Measurable (fun t : P.AugmentedRow N => t.2.1.1) by fun_prop)).mul
      (P.measurable_augmentedPatternPayoff c kind action)
  have hc : ∀ t ∉ P.augmentedBadSet kind action, ContinuousAt f t := by
    intro t ht
    exact (a.continuous.comp (show Continuous (fun t : P.AugmentedRow N => t.2.1.1) by fun_prop)).continuousAt.mul
      (P.continuousAt_augmentedPatternPayoff c kind action t ht)
  have hb : ∀ t : P.AugmentedRow N, |f t| ≤ ‖a‖ * K := by
    intro t
    rw [show f t = a t.2.1.1 * P.augmentedPatternPayoff c kind action t from rfl, abs_mul]
    exact mul_le_mul (by simpa only [Real.norm_eq_abs] using a.norm_coe_le_norm t.2.1.1)
      (hbound t) (abs_nonneg _) (norm_nonneg _)
  exact LowBody.tendsto_integral_of_closed_null_discontinuities f hm
    (P.augmentedBadSet kind action) (P.isClosed_augmentedBadSet kind action) hc
    (mul_nonneg (norm_nonneg a) hK) hb
    (fun j => P.augmentedLaw N low (eps j) (pi j)) (P.augmentedLaw N low 0 pi0)
    ht (P.augmentedBadSet_null low pi0 kind action)

end Primitives
end FCAppendix.Affine.Hybrid.Finish01
