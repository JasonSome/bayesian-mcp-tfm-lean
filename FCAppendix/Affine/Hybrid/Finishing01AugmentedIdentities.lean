import FCAppendix.Affine.Hybrid.Finishing01AugmentedLimit
import FCAppendix.Affine.Hybrid.Finishing01MenusNoisyTransport

noncomputable section
namespace FCAppendix.Affine.Hybrid.Finish01
open Set Filter Topology MeasureTheory ProbabilityTheory Classical
open Existence.Distributional
open scoped BigOperators
namespace Primitives
variable (P : Primitives)

abbrev AugmentedRivals (N : ℕ) := (Fin N → P.Low) × (Fin N → P.AgentNoise)

def augmentedRivalLaw (N : ℕ) (low : ProbabilityMeasure P.Low)
    (pi : ProbabilityMeasure P.Latent) : ProbabilityMeasure (P.AugmentedRivals N) :=
  productLaw (rowLaw N low) (rowLaw N (P.agentNoiseLaw pi))

def augmentedRealBidLaw (eps : unitInterval) (pi : ProbabilityMeasure P.Latent) : Measure ℝ :=
  (P.agentNoiseLaw pi : Measure P.AgentNoise).map
    (fun x => activeNoisyRealBid eps x.1.2 x.2)

lemma measurable_agentRealBid (eps : unitInterval) :
    Measurable (fun x : P.AgentNoise => activeNoisyRealBid eps x.1.2 x.2) := by
  unfold activeNoisyRealBid
  fun_prop

instance augmentedRealBidLaw_isProbability (eps : unitInterval)
    (pi : ProbabilityMeasure P.Latent) : IsProbabilityMeasure (P.augmentedRealBidLaw eps pi) :=
  Measure.isProbabilityMeasure_map (P.measurable_agentRealBid eps).aemeasurable

theorem augmentedRealBidLaw_eq_implemented (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (pi : Law (A:=P.Bid) mu) (eps : unitInterval) :
    P.augmentedRealBidLaw eps pi.1 =
      Finishing01Menus.implementedReal P eps.property.1 mu pi := by
  let psi : P.AgentNoise → P.Value × ActivePhysicalBid P.L P.U eps :=
    fun x => (x.1.1,activeNoisyBid P.L_pos eps.property.1 x)
  have hpsi : Measurable psi :=
    (measurable_fst.comp measurable_fst).prodMk
      (continuous_activeNoisyBid P.L_pos eps.property.1).measurable
  change ((pi.1 : Measure P.Latent).prod (volume : Measure unitInterval)).map
      (fun x : P.AgentNoise => activeNoisyRealBid eps x.1.2 x.2) =
    ((((pi.1 : Measure P.Latent).prod (volume : Measure unitInterval)).map psi).map
      Prod.snd).map Subtype.val
  rw [Measure.map_map measurable_subtype_coe measurable_snd,
    Measure.map_map (measurable_subtype_coe.comp measurable_snd) hpsi]
  rfl

theorem augmentedRealBidLaw_zero (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (pi : Law (A:=P.Bid) mu) :
    P.augmentedRealBidLaw 0 pi.1 = Finishing01Menus.baseReal P mu pi := by
  let f : P.Latent → ℝ := fun x => (x.2:ℝ)
  have hf : Measurable f := measurable_subtype_coe.comp measurable_snd
  have hp := (measurePreserving_fst (μ:=(pi.1 : Measure P.Latent))
    (ν:=(volume : Measure unitInterval))).map_eq
  have hm := congrArg (fun nu : Measure P.Latent => nu.map f) hp
  rw [Measure.map_map hf measurable_fst] at hm
  change ((pi.1 : Measure P.Latent).prod (volume : Measure unitInterval)).map
      (fun x : P.AgentNoise => activeNoisyRealBid 0 x.1.2 x.2) =
    ((pi.1 : Measure P.Latent).map Prod.snd).map Subtype.val
  rw [Measure.map_map measurable_subtype_coe measurable_snd]
  simpa only [f,Function.comp_def,activeNoisyRealBid,zero_mul,add_zero,mul_one] using hm

def augmentedRowIntegral (N c : ℕ) (low : ProbabilityMeasure P.Low)
    (eps : unitInterval) (pi : ProbabilityMeasure P.Latent) (kind : Fin N → Fin 4)
    (action : C(P.Latent,P.Bid)) (p : P.AgentNoise) : ℝ :=
  ∫ r : P.AugmentedRivals N, P.augmentedPatternPayoff c kind action (eps,(p,r))
    ∂(P.augmentedRivalLaw N low pi : Measure _)

def augmentedConditionalPattern (N c : ℕ) (low : ProbabilityMeasure P.Low)
    (eps : unitInterval) (pi : ProbabilityMeasure P.Latent) (kind : Fin N → Fin 4)
    (action : C(P.Latent,P.Bid)) (x : P.Latent) : ℝ :=
  ∫ z : unitInterval, P.augmentedRowIntegral N c low eps pi kind action (x,z)

def augmentedConditionalUtility (N c : ℕ) (low : ProbabilityMeasure P.Low)
    (eps : unitInterval) (pi : ProbabilityMeasure P.Latent)
    (action : C(P.Latent,P.Bid)) (x : P.Latent) : ℝ :=
  ∑ kind : Fin N → Fin 4, (CommonList.iid P.categories N).mass kind *
    P.augmentedConditionalPattern N c low eps pi kind action x

lemma measurable_augmentedRowIntegral (N c : ℕ) (low : ProbabilityMeasure P.Low)
    (eps : unitInterval) (pi : ProbabilityMeasure P.Latent) (kind : Fin N → Fin 4)
    (action : C(P.Latent,P.Bid)) :
    Measurable (P.augmentedRowIntegral N c low eps pi kind action) := by
  have hm : Measurable (fun p : P.AgentNoise × P.AugmentedRivals N =>
      P.augmentedPatternPayoff c kind action (eps,p)) :=
    (P.measurable_augmentedPatternPayoff c kind action).comp
      (measurable_const.prodMk measurable_id)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

lemma measurable_augmentedConditionalPattern (N c : ℕ) (low : ProbabilityMeasure P.Low)
    (eps : unitInterval) (pi : ProbabilityMeasure P.Latent) (kind : Fin N → Fin 4)
    (action : C(P.Latent,P.Bid)) :
    Measurable (P.augmentedConditionalPattern N c low eps pi kind action) :=
  (P.measurable_augmentedRowIntegral N c low eps pi kind action).stronglyMeasurable.integral_prod_right'.measurable

lemma norm_augmentedRowIntegral_le {N c : ℕ} (low : ProbabilityMeasure P.Low)
    (eps : unitInterval) (pi : ProbabilityMeasure P.Latent) (kind : Fin N → Fin 4)
    (action : C(P.Latent,P.Bid)) (K : ℝ)
    (hK : ∀ t : P.AugmentedRow N, |P.augmentedPatternPayoff c kind action t| ≤ K)
    (p : P.AgentNoise) :
    ‖P.augmentedRowIntegral N c low eps pi kind action p‖ ≤ K := by
  simpa only [augmentedRowIntegral,probReal_univ,mul_one,one_mul] using
    norm_integral_le_of_norm_le_const (C := K) (f := fun r : P.AugmentedRivals N => P.augmentedPatternPayoff c kind action (eps,(p,r))) (ae_of_all
      (P.augmentedRivalLaw N low pi : Measure _) (fun r => by
        simpa only [Real.norm_eq_abs] using hK (eps,(p,r))))

lemma norm_augmentedConditionalPattern_le {N c : ℕ} (low : ProbabilityMeasure P.Low)
    (eps : unitInterval) (pi : ProbabilityMeasure P.Latent) (kind : Fin N → Fin 4)
    (action : C(P.Latent,P.Bid)) (K : ℝ)
    (hK : ∀ t : P.AugmentedRow N, |P.augmentedPatternPayoff c kind action t| ≤ K)
    (x : P.Latent) :
    ‖P.augmentedConditionalPattern N c low eps pi kind action x‖ ≤ K := by
  simpa only [augmentedConditionalPattern,probReal_univ,mul_one,one_mul] using
    norm_integral_le_of_norm_le_const (ae_of_all (volume : Measure unitInterval)
      (fun z => P.norm_augmentedRowIntegral_le low eps pi kind action K hK (x,z)))

theorem augmented_test_pattern (N c : ℕ) (low : ProbabilityMeasure P.Low)
    (eps : unitInterval) (pi : ProbabilityMeasure P.Latent) (kind : Fin N → Fin 4)
    (a : C(P.Latent,ℝ)) (action : C(P.Latent,P.Bid)) :
    (∫ t : P.AugmentedRow N, a t.2.1.1 * P.augmentedPatternPayoff c kind action t
      ∂(P.augmentedLaw N low eps pi : Measure _)) =
    ∫ x : P.Latent, a x * P.augmentedConditionalPattern N c low eps pi kind action x
      ∂(pi : Measure P.Latent) := by
  obtain ⟨K,hK,hbound⟩ := P.exists_augmented_payoff_bound c kind action
  let f : P.AugmentedRow N → ℝ :=
    fun t => a t.2.1.1 * P.augmentedPatternPayoff c kind action t
  have hf : Measurable f :=
    (a.continuous.measurable.comp (by fun_prop)).mul
      (P.measurable_augmentedPatternPayoff c kind action)
  have hb (t : P.AugmentedRow N) : ‖f t‖ ≤ ‖a‖*K := by
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul (by simpa only [Real.norm_eq_abs] using a.norm_coe_le_norm t.2.1.1)
      (hbound t) (abs_nonneg _) (norm_nonneg a)
  have hi : Integrable f (P.augmentedLaw N low eps pi : Measure _) :=
    Integrable.of_bound hf.aestronglyMeasurable (‖a‖*K) (ae_of_all _ hb)
  have hi0 : Integrable (fun p : P.AgentNoise × P.AugmentedRivals N => f (eps,p))
      ((P.agentNoiseLaw pi : Measure P.AgentNoise).prod
        (P.augmentedRivalLaw N low pi : Measure _)) :=
    Integrable.of_bound (hf.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (‖a‖*K) (ae_of_all _ (fun p => hb (eps,p)))
  have him : Integrable (fun p : P.AgentNoise =>
      a p.1 * P.augmentedRowIntegral N c low eps pi kind action p)
      ((pi : Measure P.Latent).prod (volume : Measure unitInterval)) := by
    apply Integrable.of_bound
      ((a.continuous.measurable.comp measurable_fst).mul
        (P.measurable_augmentedRowIntegral N c low eps pi kind action)).aestronglyMeasurable
      (‖a‖*K)
    apply ae_of_all
    intro p
    dsimp only [Pi.mul_apply, Function.comp_def]
    rw [norm_mul]
    exact mul_le_mul (a.norm_coe_le_norm p.1)
      (P.norm_augmentedRowIntegral_le low eps pi kind action K hbound p)
      (norm_nonneg _) (norm_nonneg a)
  change (∫ t, f t ∂(Measure.dirac eps).prod
    ((P.agentNoiseLaw pi : Measure P.AgentNoise).prod
      (P.augmentedRivalLaw N low pi : Measure _))) = _
  have hi' : Integrable f ((Measure.dirac eps).prod ((P.agentNoiseLaw pi : Measure P.AgentNoise).prod (P.augmentedRivalLaw N low pi : Measure _))) := hi
  rw [integral_prod _ hi',integral_dirac,integral_prod _ hi0]
  simp_rw [f,integral_const_mul]
  change (∫ p : P.AgentNoise, a p.1 * P.augmentedRowIntegral N c low eps pi kind action p
    ∂(pi : Measure P.Latent).prod (volume : Measure unitInterval)) = _
  rw [integral_prod _ him]
  simp_rw [integral_const_mul]
  rfl

theorem augmented_test_sum_eq_conditional (N c : ℕ) (low : ProbabilityMeasure P.Low)
    (eps : unitInterval) (pi : ProbabilityMeasure P.Latent)
    (a : C(P.Latent,ℝ)) (action : C(P.Latent,P.Bid)) :
    (∑ kind : Fin N → Fin 4, (CommonList.iid P.categories N).mass kind *
      ∫ t : P.AugmentedRow N, a t.2.1.1 * P.augmentedPatternPayoff c kind action t
        ∂(P.augmentedLaw N low eps pi : Measure _)) =
    ∫ x : P.Latent, a x * P.augmentedConditionalUtility N c low eps pi action x
      ∂(pi : Measure P.Latent) := by
  have hi (kind : Fin N → Fin 4) : Integrable (fun x : P.Latent =>
      a x * P.augmentedConditionalPattern N c low eps pi kind action x)
      (pi : Measure P.Latent) := by
    obtain ⟨K,hK,hbound⟩ := P.exists_augmented_payoff_bound c kind action
    apply Integrable.of_bound
      (a.continuous.measurable.mul
        (P.measurable_augmentedConditionalPattern N c low eps pi kind action)).aestronglyMeasurable
      (‖a‖*K)
    apply ae_of_all
    intro x
    dsimp only [Pi.mul_apply, Function.comp_def]
    rw [norm_mul]
    exact mul_le_mul (a.norm_coe_le_norm x)
      (P.norm_augmentedConditionalPattern_le low eps pi kind action K hbound x)
      (norm_nonneg _) (norm_nonneg a)
  have he (x : P.Latent) :
      a x * P.augmentedConditionalUtility N c low eps pi action x =
      ∑ kind : Fin N → Fin 4, (CommonList.iid P.categories N).mass kind *
        (a x * P.augmentedConditionalPattern N c low eps pi kind action x) := by
    unfold augmentedConditionalUtility
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro kind _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun kind _ => (hi kind).const_mul _)]
  apply Finset.sum_congr rfl
  intro kind _
  rw [integral_const_mul,P.augmented_test_pattern N c low eps pi kind a action]

theorem augmentedRowIntegral_eq_patternInterim (N c : ℕ) (low : ProbabilityMeasure P.Low)
    (eps : unitInterval) (pi : ProbabilityMeasure P.Latent) (kind : Fin N → Fin 4)
    (action : C(P.Latent,P.Bid)) (p : P.AgentNoise) :
    P.augmentedRowIntegral N c low eps pi kind action p =
      Finishing01Menus.patternInterim P.xi P.z P.L P.U c kind
        (Finishing01Menus.lowReal P low) (P.augmentedRealBidLaw eps pi)
        p.1.1 (activeNoisyRealBid eps (action p.1) p.2) := by
  exact (Finishing01Menus.patternInterim_map P.xi_pos P.xi_lt_one P.z P.L P.U c kind
    low (P.agentNoiseLaw pi) Subtype.val
    (fun x : P.AgentNoise => activeNoisyRealBid eps x.1.2 x.2)
    measurable_subtype_coe (P.measurable_agentRealBid eps)
    p.1.1 (activeNoisyRealBid eps (action p.1) p.2)).symm

theorem augmentedConditionalUtility_eq_raw (N c : ℕ) (low : ProbabilityMeasure P.Low)
    (eps : unitInterval) (pi : ProbabilityMeasure P.Latent)
    (action : C(P.Latent,P.Bid)) (x : P.Latent) :
    P.augmentedConditionalUtility N c low eps pi action x =
      ∫ z : unitInterval, Finishing01Menus.actualRowInterim (N:=N)
        P.xi P.z P.L P.U c P.categories (Finishing01Menus.lowReal P low)
          (P.augmentedRealBidLaw eps pi) x.1 (activeNoisyRealBid eps (action x) z) := by
  have hi (kind : Fin N → Fin 4) : Integrable (fun z : unitInterval =>
      P.augmentedRowIntegral N c low eps pi kind action (x,z)) volume := by
    obtain ⟨K,hK,hbound⟩ := P.exists_augmented_payoff_bound c kind action
    exact Integrable.of_bound
      ((P.measurable_augmentedRowIntegral N c low eps pi kind action).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable K
      (ae_of_all _ (fun z => P.norm_augmentedRowIntegral_le low eps pi kind action K hbound (x,z)))
  have he (z : unitInterval) :
      Finishing01Menus.actualRowInterim (N:=N) P.xi P.z P.L P.U c P.categories
        (Finishing01Menus.lowReal P low) (P.augmentedRealBidLaw eps pi)
          x.1 (activeNoisyRealBid eps (action x) z) =
      ∑ kind : Fin N → Fin 4, (CommonList.iid P.categories N).mass kind *
        P.augmentedRowIntegral N c low eps pi kind action (x,z) := by
    unfold Finishing01Menus.actualRowInterim FiniteLaw.expect
    apply Finset.sum_congr rfl
    intro kind _
    rw [P.augmentedRowIntegral_eq_patternInterim]
  simp_rw [he]
  rw [integral_finsetSum _ (fun kind _ => (hi kind).const_mul _)]
  simp only [augmentedConditionalUtility,augmentedConditionalPattern,integral_const_mul]

theorem augmentedConditionalUtility_zero (N c : ℕ) (low : ProbabilityMeasure P.Low)
    (mu : Measure P.Value) [IsProbabilityMeasure mu] (pi : Law (A:=P.Bid) mu)
    (action : C(P.Latent,P.Bid)) (x : P.Latent) :
    P.augmentedConditionalUtility N c low 0 pi.1 action x =
      P.exactUtility N c low mu pi (x.1,action x) := by
  rw [P.augmentedConditionalUtility_eq_raw,P.augmentedRealBidLaw_zero mu pi,
    Finishing01Menus.exactUtility_eq_actualRowInterim]
  have hz (z : unitInterval) : activeNoisyRealBid (0:unitInterval) (action x) z =
      (action x:ℝ) := by
    change (action x:ℝ)*(1+(0:ℝ)*(z:ℝ))=(action x:ℝ)
    ring
  simp_rw [hz]
  simp only [integral_const,probReal_univ,one_smul]

theorem augmentedConditionalUtility_noisy (N c : ℕ) (low : ProbabilityMeasure P.Low)
    (mu : Measure P.Value) [IsProbabilityMeasure mu] (pi : Law (A:=P.Bid) mu)
    (eps : unitInterval)
    (hguard : ∀ kind : Fin N → Fin 4,
      activePatternGuarded P.xi P.L (P.U*(1+(eps:ℝ))) c P.z kind ↔
        activePatternGuarded P.xi P.L P.U c P.z kind)
    (action : C(P.Latent,P.Bid)) (x : P.Latent) :
    P.augmentedConditionalUtility N c low eps pi.1 action x =
      activeNoisyExpectedUtility (N:=N) P.L_pos eps.property.1 P.xi P.z c P.categories
        low mu (pi,(x.1,action x)) := by
  rw [P.augmentedConditionalUtility_eq_raw,
    Finishing01Menus.noisyExpectedUtility_eq_actualRow_noise,
    P.augmentedRealBidLaw_eq_implemented mu pi eps]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  unfold Finishing01Menus.actualRowInterim FiniteLaw.expect
  apply Finset.sum_congr rfl
  intro kind _
  congr 1
  unfold Finishing01Menus.patternInterim
  apply integral_congr_ae
  apply ae_of_all
  intro r
  unfold activePhysicalPatternPayoff
  rw [propext (hguard kind)]

theorem augmented_test_sum_zero (N c : ℕ) (low : ProbabilityMeasure P.Low)
    (mu : Measure P.Value) [IsProbabilityMeasure mu] (pi : Law (A:=P.Bid) mu)
    (a : C(P.Latent,ℝ)) (action : C(P.Latent,P.Bid)) :
    (∑ kind : Fin N → Fin 4, (CommonList.iid P.categories N).mass kind *
      ∫ t : P.AugmentedRow N, a t.2.1.1 * P.augmentedPatternPayoff c kind action t
        ∂(P.augmentedLaw N low 0 pi.1 : Measure _)) =
    ∫ x : P.Latent, a x * P.exactUtility N c low mu pi (x.1,action x)
      ∂(pi.1 : Measure P.Latent) := by
  rw [P.augmented_test_sum_eq_conditional]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => congrArg (fun y : ℝ => a x*y)
    (P.augmentedConditionalUtility_zero N c low mu pi action x))

theorem augmented_test_sum_noisy (N c : ℕ) (low : ProbabilityMeasure P.Low)
    (mu : Measure P.Value) [IsProbabilityMeasure mu] (pi : Law (A:=P.Bid) mu)
    (eps : unitInterval) (_heps : 0 < (eps:ℝ))
    (hguard : ∀ kind : Fin N → Fin 4,
      activePatternGuarded P.xi P.L (P.U*(1+(eps:ℝ))) c P.z kind ↔
        activePatternGuarded P.xi P.L P.U c P.z kind)
    (a : C(P.Latent,ℝ)) (action : C(P.Latent,P.Bid)) :
    (∑ kind : Fin N → Fin 4, (CommonList.iid P.categories N).mass kind *
      ∫ t : P.AugmentedRow N, a t.2.1.1 * P.augmentedPatternPayoff c kind action t
        ∂(P.augmentedLaw N low eps pi.1 : Measure _)) =
    ∫ x : P.Latent, a x * activeNoisyExpectedUtility (N:=N) P.L_pos eps.property.1
      P.xi P.z c P.categories low mu (pi,(x.1,action x))
      ∂(pi.1 : Measure P.Latent) := by
  rw [P.augmented_test_sum_eq_conditional]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => congrArg (fun y : ℝ => a x*y)
    (P.augmentedConditionalUtility_noisy N c low mu pi eps hguard action x))

end Primitives
end FCAppendix.Affine.Hybrid.Finish01
