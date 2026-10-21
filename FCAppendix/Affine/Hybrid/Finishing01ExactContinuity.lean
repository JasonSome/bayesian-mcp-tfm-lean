import FCAppendix.Affine.Hybrid.Finishing01PhysicalContinuity
import FCAppendix.Affine.Hybrid.Finishing01MenusNoisyTransport
import FCAppendix.Affine.LowBody.ICFromContinuousTests

noncomputable section
namespace FCAppendix.Affine.Hybrid.Finish01
open Set Filter Topology MeasureTheory ProbabilityTheory Classical
open Existence.Distributional
open scoped BigOperators
namespace Primitives
variable (P : Primitives)

abbrev BaseRows (N : ℕ) := (Fin N → P.Low) × (Fin N → P.Bid)

def baseData {N : ℕ} (x : P.Latent) (r : P.BaseRows N) : ActivePhysicalData N :=
  (x.1,x.2,(fun j => (r.1 j:ℝ)),fun j => (r.2 j:ℝ))

lemma base_active_positive {N : ℕ} (kind : Fin N → Fin 4)
    (x : P.Latent) (r : P.BaseRows N) :
    ∀ i, 0 < activePhysicalActiveBids kind (P.baseData x r) i := by
  intro i
  rcases Fin.eq_zero_or_eq_succ i.val with hi | ⟨j,hj⟩
  · simpa only [activePhysicalActiveBids,baseData,hi,Fin.cases_zero] using P.bid_pos x.2
  · simpa only [activePhysicalActiveBids,baseData,hj,Fin.cases_succ] using P.bid_pos (r.2 j)

lemma base_lower_nonneg {N : ℕ} (kind : Fin N → Fin 4)
    (x : P.Latent) (r : P.BaseRows N) :
    ∀ i, 0 ≤ activePhysicalBids kind (P.baseData x r) i := by
  intro i
  refine Fin.cases (P.bid_pos x.2).le (fun j => ?_) i
  simp only [activePhysicalBids,baseData,Fin.cons_succ]
  split_ifs
  · exact (r.1 j).property.1
  · exact (P.bid_pos (r.2 j)).le
  · exact le_rfl

lemma continuous_patternExpected {N : ℕ} (c : ℕ) (kind : Fin N → Fin 4)
    (low : ProbabilityMeasure P.Low) [NullSingletonClass (low : Measure P.Low)]
    (G : ProbabilityMeasure P.Bid) [NullSingletonClass (G : Measure P.Bid)] :
    Continuous (fun x : P.Latent => ∫ r : P.BaseRows N,
      activePhysicalPatternPayoff P.xi P.z P.L P.U c kind (P.baseData x r)
        ∂(productLaw (rowLaw N low) (rowLaw N G) : Measure _)) := by
  let R := productLaw (rowLaw N low) (rowLaw N G)
  let F : P.Latent → P.BaseRows N → ℝ := fun x r =>
    activePhysicalPatternPayoff P.xi P.z P.L P.U c kind (P.baseData x r)
  have hm (x : P.Latent) : Measurable (F x) :=
    (measurable_activePhysicalPatternPayoff P.xi_pos P.xi_lt_one P.z P.L P.U c kind).comp
      (show Measurable (fun r : P.BaseRows N => P.baseData x r) by unfold baseData; fun_prop)
  have hbound (x : P.Latent) (r : P.BaseRows N) : |F x r| ≤ P.payoffBound := by
    have h := Finishing01Menus.abs_physicalPatternPayoff_le P.xi_pos P.xi_lt_one P.L_pos
      P.z c kind x.1 x.2 (fun j => (r.1 j:ℝ)) (fun j => (r.2 j:ℝ))
      x.2.property (fun j => (r.2 j).property)
    have hv : |(x.1:ℝ)| ≤ |P.vlo|+|P.vhi| := abs_le.mpr
      ⟨by linarith [x.1.property.1,neg_abs_le P.vlo,abs_nonneg P.vhi],
        by linarith [x.1.property.2,le_abs_self P.vhi,abs_nonneg P.vlo]⟩
    exact h.trans (by dsimp [payoffBound]; nlinarith [P.U_pos])
  apply continuous_iff_continuousAt.mpr
  intro x
  have hnotbad : ∀ᵐ r ∂(R : Measure _), P.baseData x r ∉ physicalBadSet P.kappa kind := by
    change ∀ᵐ r ∂((rowLaw N low : Measure (Fin N → P.Low)).prod (rowLaw N G : Measure (Fin N → P.Bid))), _
    rw [LowBody.rowLaw_eq_measure_pi,LowBody.rowLaw_eq_measure_pi]
    exact ae_two_rows_not_bad (low : Measure P.Low) (G : Measure P.Bid)
      Subtype.val Subtype.val measurable_subtype_coe measurable_subtype_coe
      (ae_subtype_val_ne (low : Measure P.Low)) (ae_subtype_val_ne (G : Measure P.Bid))
      P.kappa_pos (P.bid_pos x.2) x.1 kind
  have hcont : ∀ᵐ r ∂(R : Measure _), ContinuousAt (fun y : P.Latent => F y r) x := by
    filter_upwards [hnotbad] with r hr
    exact (continuousAt_physical_of_not_bad P.xi_pos P.xi_lt_one P.z P.L P.U c kind
      (P.baseData x r) (P.base_lower_nonneg kind x r) (P.base_active_positive kind x r) hr).comp
      (f := fun y : P.Latent => P.baseData y r)
      (show ContinuousAt (fun y : P.Latent => P.baseData y r) x by unfold baseData; fun_prop)
  exact MeasureTheory.continuousAt_of_dominated (μ:=(R : Measure _)) (F:=F)
    (bound:=fun _ => P.payoffBound)
    (Eventually.of_forall (fun x => (hm x).aestronglyMeasurable))
    (Eventually.of_forall (fun x => ae_of_all _ (fun r => by
      simpa only [Real.norm_eq_abs] using hbound x r)))
    (integrable_const P.payoffBound) hcont

theorem continuous_exactUtility (N c : ℕ)
    (low : ProbabilityMeasure P.Low) [NullSingletonClass (low : Measure P.Low)]
    (mu : Measure P.Value) [IsProbabilityMeasure mu] (pi : Law (A:=P.Bid) mu)
    [NullSingletonClass (pi.1.map measurable_snd.aemeasurable : Measure P.Bid)] :
    Continuous (P.exactUtility N c low mu pi) := by
  unfold exactUtility
  apply continuous_finsetSum
  intro kind _
  exact continuous_const.mul (P.continuous_patternExpected c kind low
    (pi.1.map measurable_snd.aemeasurable))

theorem continuous_tests_imply_ae_deviation_order (N c : ℕ)
    (low : ProbabilityMeasure P.Low) [NullSingletonClass (low : Measure P.Low)]
    (mu : Measure P.Value) [IsProbabilityMeasure mu] (pi : Law (A:=P.Bid) mu)
    [NullSingletonClass (pi.1.map measurable_snd.aemeasurable : Measure P.Bid)]
    (b' : P.Bid)
    (htests : ∀ a : C(P.Latent,ℝ), (∀ x, 0 ≤ a x) →
      ∫ x, a x*(P.exactUtility N c low mu pi (x.1,b')-P.exactUtility N c low mu pi x)
        ∂(pi.1 : Measure P.Latent) ≤ 0) :
    ∀ᵐ x ∂(pi.1 : Measure P.Latent),
      P.exactUtility N c low mu pi (x.1,b') ≤ P.exactUtility N c low mu pi x := by
  have hu := P.continuous_exactUtility N c low mu pi
  let f : C(P.Latent,ℝ) := ⟨fun x => P.exactUtility N c low mu pi (x.1,b')-
    P.exactUtility N c low mu pi x,(hu.comp (continuous_fst.prodMk continuous_const)).sub hu⟩
  have h := LowBody.ae_nonpos_outside_closed_of_tests
    (pi.1 : Measure P.Latent) f f.continuous.measurable ∅ isClosed_empty
    (fun x _ => f.continuous.continuousAt) (norm_nonneg f)
    (fun x => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x)
    (fun a ha _ => htests a ha)
  filter_upwards [h] with x hx
  exact sub_nonpos.mp (hx (by simp))

theorem common_conull_all_bids (N c : ℕ)
    (low : ProbabilityMeasure P.Low) [NullSingletonClass (low : Measure P.Low)]
    (mu : Measure P.Value) [IsProbabilityMeasure mu] (pi : Law (A:=P.Bid) mu)
    [NullSingletonClass (pi.1.map measurable_snd.aemeasurable : Measure P.Bid)]
    (hfixed : ∀ b' : P.Bid, ∀ᵐ x ∂(pi.1 : Measure P.Latent),
      P.exactUtility N c low mu pi (x.1,b') ≤ P.exactUtility N c low mu pi x) :
    ∀ᵐ x ∂(pi.1 : Measure P.Latent), ∀ b' : P.Bid,
      P.exactUtility N c low mu pi (x.1,b') ≤ P.exactUtility N c low mu pi x := by
  obtain ⟨D,hDc,hDd⟩ := TopologicalSpace.exists_countable_dense P.Bid
  have hall : ∀ᵐ x ∂(pi.1 : Measure P.Latent), ∀ b' ∈ D,
      P.exactUtility N c low mu pi (x.1,b') ≤ P.exactUtility N c low mu pi x :=
    (ae_ball_iff hDc).mpr (fun b' _ => hfixed b')
  have hu := P.continuous_exactUtility N c low mu pi
  filter_upwards [hall] with x hx
  have hc : IsClosed {b' : P.Bid |
      P.exactUtility N c low mu pi (x.1,b') ≤ P.exactUtility N c low mu pi x} :=
    isClosed_le (hu.comp (continuous_const.prodMk continuous_id)) continuous_const
  have hsub := closure_minimal (fun b hb => hx b hb) hc
  intro b'
  exact hsub (hDd.closure_eq ▸ mem_univ b')

theorem exact_IC_any_disintegration (N c : ℕ)
    (low : ProbabilityMeasure P.Low) [NullSingletonClass (low : Measure P.Low)]
    (mu : Measure P.Value) [IsProbabilityMeasure mu] (pi : Law (A:=P.Bid) mu)
    [NullSingletonClass (pi.1.map measurable_snd.aemeasurable : Measure P.Bid)]
    (hIC : ∀ᵐ x ∂(pi.1 : Measure P.Latent), ∀ b' : P.Bid,
      P.exactUtility N c low mu pi (x.1,b') ≤ P.exactUtility N c low mu pi x)
    (sigma : Kernel P.Value P.Bid) [IsMarkovKernel sigma]
    (hdis : mu⊗ₘsigma=(pi.1 : Measure P.Latent)) :
    ∀ᵐ v ∂mu, ∀ᵐ b ∂sigma v, ∀ b' : P.Bid,
      P.exactUtility N c low mu pi (v,b') ≤ P.exactUtility N c low mu pi (v,b) := by
  rw [←hdis] at hIC
  exact Measure.ae_ae_of_ae_compProd hIC

end Primitives
end FCAppendix.Affine.Hybrid.Finish01
