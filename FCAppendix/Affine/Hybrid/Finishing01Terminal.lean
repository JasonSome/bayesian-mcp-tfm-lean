import FCAppendix.Affine.Hybrid.Finishing01Finite
import FCAppendix.Affine.Hybrid.Finishing01FamilyPrefix
import FCAppendix.Affine.Hybrid.Finishing01ClearingCountLimits
import FCAppendix.Affine.Hybrid.Finishing01ClearingUniqueness

noncomputable section
namespace FCAppendix.Affine.Hybrid.Finish01
open Set Filter Topology MeasureTheory ProbabilityTheory Classical
open Existence.Distributional
namespace Primitives
variable (P : Primitives)

structure ActiveNumericFamily (c : ℕ → ℕ)
    (muLow : Measure P.Low) [IsProbabilityMeasure muLow]
    (mu : Measure P.Value) [IsProbabilityMeasure mu] where
  threshold : ℕ
  low : ℕ → ProbabilityMeasure P.Low
  joint : ℕ → Law (A:=P.Bid) mu
  multiplier : P.Price
  source_interval : (multiplier:ℝ) ∈
    Icc (P.vlo*phi P.xi P.z P.qbar) (P.vhi*phi P.xi P.z P.qbar)
  clearing : (∫ v : P.Value, P.qResponse v multiplier ∂mu)=P.qbar
  unique : ∀ nu : P.Price, (∫ v : P.Value, P.qResponse v nu ∂mu)=P.qbar → nu=multiplier
  lowWitness : ∀ M : ℕ, threshold ≤ M → P.LowSourceState M (c M) muLow
  low_eq : ∀ (M : ℕ) (h : threshold ≤ M), low M=(lowWitness M h).bidLaw
  activeWitness : ∀ M : ℕ, threshold ≤ M → P.FiniteLawSolution M (c M) (low M) mu
  joint_eq : ∀ (M : ℕ) (h : threshold ≤ M), joint M=(activeWitness M h).joint
  price_tendsto : Tendsto (fun M => P.price mu (joint M)) atTop (𝓝 (multiplier:ℝ))
  supported_graph : ∀ eps > 0, ∀ᶠ M in atTop,
    ∀ᵐ t ∂((joint M).1 : Measure P.Latent), |(t.2:ℝ)-P.beta t.1 multiplier| < eps
  conditional_counts : P.OriginalConditionalCountLimit c low mu joint multiplier

theorem construct_active_numeric_family (c : ℕ → ℕ)
    (hc : Tendsto (fun M => (c M:ℝ)/(M:ℝ)) atTop (𝓝 P.rho))
    (muLow : Measure P.Low) [IsProbabilityMeasure muLow]
    (hpositive : ∀ᵐ v : P.Low ∂muLow, 0 < (v:ℝ))
    (mu : Measure P.Value) [IsProbabilityMeasure mu] :
    Nonempty (P.ActiveNumericFamily c muLow mu) := by
  obtain ⟨M0,hfinite⟩ := Filter.eventually_atTop.mp
    (P.exists_eventual_active_numeric_solution c hc muLow hpositive mu)
  choose lowTail ETail _htrue using hfinite
  let low := P.extend_low_prefix M0 (fun M h => (lowTail M h).bidLaw)
  let pi := P.extend_joint_prefix mu M0 (fun M h => (ETail M h).joint)
  have hicTail : ∀ M ≥ M0, ∀ᵐ t ∂((pi M).1 : Measure P.Latent), ∀ b' : P.Bid,
      P.exactUtility (M-1) (c M) (low M) mu (pi M) (t.1,b') ≤
        P.exactUtility (M-1) (c M) (low M) mu (pi M) t :=
    P.extended_family_exact_IC c muLow mu M0 lowTail ETail
  have hIC : P.EventualActualIC c low mu pi :=
    Filter.eventually_atTop.mpr ⟨M0,hicTail⟩
  obtain ⟨lam,hsource,hclear,hunique,hprice,hgraph⟩ :=
    P.unique_clearing_and_full_sequence c hc low mu pi hIC
  have hcounts := P.original_conditional_counts c hc low mu pi hIC lam hprice
  let activeTail : ∀ M : ℕ, M0 ≤ M → P.FiniteLawSolution M (c M) (low M) mu :=
    fun M h =>
      { joint := (ETail M h).joint
        atomless := (ETail M h).atomless
        interior := (ETail M h).interior
        all_bid_IC := by
          simpa only [low,P.extend_low_prefix_tail M0 _ M h] using (ETail M h).all_bid_IC }
  refine ⟨{
    threshold := M0
    low := low
    joint := pi
    multiplier := lam
    source_interval := hsource
    clearing := hclear
    unique := hunique
    lowWitness := lowTail
    low_eq := ?_
    activeWitness := activeTail
    joint_eq := ?_
    price_tendsto := hprice
    supported_graph := hgraph
    conditional_counts := hcounts }⟩
  · intro M h
    exact P.extend_low_prefix_tail M0 _ M h
  · intro M h
    simp only [pi,activeTail,P.extend_joint_prefix_tail mu M0 _ M h]

namespace ActiveNumericFamily
variable {P} {c : ℕ → ℕ} {muLow : Measure P.Low} [IsProbabilityMeasure muLow]
  {mu : Measure P.Value} [IsProbabilityMeasure mu]

theorem global_unique_clearing (F : P.ActiveNumericFamily c muLow mu)
    (nu : ℝ) (q : P.Value → ℝ) (hq : ∀ v, q v ∈ Ioo (0:ℝ) 1)
    (hphi : ∀ v, phi P.xi P.z (q v)=nu/(v:ℝ))
    (hqclear : (∫ v : P.Value, q v ∂mu)=P.qbar) : nu=(F.multiplier:ℝ) :=
  P.global_unique_interior_clearing mu F.multiplier F.clearing nu q hq hphi hqclear

theorem atomless (F : P.ActiveNumericFamily c muLow mu) (M : ℕ) (h : F.threshold ≤ M) :
    NullSingletonClass ((F.joint M).1.map measurable_snd.aemeasurable : Measure P.Bid) := by
  rw [F.joint_eq M h]
  exact (F.activeWitness M h).atomless

theorem all_bid_IC (F : P.ActiveNumericFamily c muLow mu) (M : ℕ) (h : F.threshold ≤ M) :
    ∀ᵐ t ∂((F.joint M).1 : Measure P.Latent), ∀ b' : P.Bid,
      P.exactUtility (M-1) (c M) (F.low M) mu (F.joint M) (t.1,b') ≤
        P.exactUtility (M-1) (c M) (F.low M) mu (F.joint M) t := by
  rw [F.joint_eq M h]
  exact (F.activeWitness M h).all_bid_IC

theorem eventual_IC (F : P.ActiveNumericFamily c muLow mu) :
    P.EventualActualIC c F.low mu F.joint :=
  Filter.eventually_atTop.mpr ⟨F.threshold,F.all_bid_IC⟩

theorem low_atomless (F : P.ActiveNumericFamily c muLow mu) (M : ℕ) (h : F.threshold ≤ M) :
    NullSingletonClass (F.low M : Measure P.Low) := by
  rw [F.low_eq M h]
  exact (F.lowWitness M h).witness.compact_atomless

theorem common_conull_original_IC (F : P.ActiveNumericFamily c muLow mu)
    (sigma : ℕ → Kernel P.Value P.Bid)
    (hmark : ∀ M, IsMarkovKernel (sigma M))
    (hdis : ∀ M, mu⊗ₘsigma M=((F.joint M).1 : Measure P.Latent)) :
    ∀ᵐ v ∂mu, ∀ M ≥ F.threshold, ∀ᵐ b ∂sigma M v, ∀ b' : P.Bid,
      P.exactUtility (M-1) (c M) (F.low M) mu (F.joint M) (v,b') ≤
        P.exactUtility (M-1) (c M) (F.low M) mu (F.joint M) (v,b) := by
  have each (M : ℕ) : ∀ᵐ v ∂mu, F.threshold ≤ M →
      ∀ᵐ b ∂sigma M v, ∀ b' : P.Bid,
        P.exactUtility (M-1) (c M) (F.low M) mu (F.joint M) (v,b') ≤
          P.exactUtility (M-1) (c M) (F.low M) mu (F.joint M) (v,b) := by
    by_cases h : F.threshold ≤ M
    · letI := hmark M
      letI := F.low_atomless M h
      letI := F.atomless M h
      have hx := P.exact_IC_any_disintegration (M-1) (c M) (F.low M) mu
        (F.joint M) (F.all_bid_IC M h) (sigma M) (hdis M)
      exact hx.mono (fun v hv _ => hv)
    · exact ae_of_all _ (fun _ h' => (h h').elim)
  exact ae_all_iff.mpr each

theorem all_original_conditional_count_laws (F : P.ActiveNumericFamily c muLow mu)
    (sigma : ℕ → Kernel P.Value P.Bid)
    (hmark : ∀ M, IsMarkovKernel (sigma M))
    (hdis : ∀ M, mu⊗ₘsigma M=((F.joint M).1 : Measure P.Latent)) :
    ∀ᵐ v ∂mu, ∀ j : Fin 3,
      Tendsto (fun M => P.conditionalCountMass M (c M) (F.low M) mu
        (F.joint M) (sigma M) v j) atTop
        (𝓝 (limitingCountMass P.z (P.qResponse v F.multiplier) j)) :=
  F.conditional_counts sigma hmark hdis

end ActiveNumericFamily

theorem exists_eventual_active_numeric_family (c : ℕ → ℕ)
    (hc : Tendsto (fun M => (c M:ℝ)/(M:ℝ)) atTop (𝓝 P.rho))
    (muLow : Measure P.Low) [IsProbabilityMeasure muLow]
    (hpositive : ∀ᵐ v : P.Low ∂muLow, 0 < (v:ℝ))
    (mu : Measure P.Value) [IsProbabilityMeasure mu] :
    ∃ M0 : ℕ, ∃ low : ℕ → ProbabilityMeasure P.Low, ∃ pi : ℕ → Law (A:=P.Bid) mu,
      ∃ lam : ℝ,
      lam ∈ Icc (P.vlo*phi P.xi P.z P.qbar) (P.vhi*phi P.xi P.z P.qbar) ∧
      (∫ v : P.Value, P.qResponse v lam ∂mu)=P.qbar ∧
      (∀ lam', lam' ∈ Icc (P.h0*P.L) (P.h0*P.U) →
        (∫ v : P.Value, P.qResponse v lam' ∂mu)=P.qbar → lam'=lam) ∧
      (∀ M ≥ M0, ∃ A : P.LowSourceState M (c M) muLow, low M=A.bidLaw) ∧
      (∀ M ≥ M0, NullSingletonClass ((pi M).1.map measurable_snd.aemeasurable : Measure P.Bid)) ∧
      (∀ M ≥ M0, ∀ᵐ t ∂((pi M).1 : Measure P.Latent), ∀ b' : P.Bid,
        P.exactUtility (M-1) (c M) (low M) mu (pi M) (t.1,b') ≤
          P.exactUtility (M-1) (c M) (low M) mu (pi M) t) ∧
      Tendsto (fun M => P.price mu (pi M)) atTop (𝓝 lam) ∧
      (∀ eps > 0, ∀ᶠ M in atTop, ∀ᵐ t ∂((pi M).1 : Measure P.Latent),
        |(t.2:ℝ)-P.beta t.1 lam| < eps) ∧
      (∀ sigma : ℕ → Kernel P.Value P.Bid,
        (∀ M, IsMarkovKernel (sigma M)) →
        (∀ M, mu⊗ₘsigma M=((pi M).1 : Measure P.Latent)) →
        ∀ᵐ v ∂mu, ∀ j : Fin 3,
          Tendsto (fun M => P.conditionalCountMass M (c M) (low M) mu
            (pi M) (sigma M) v j) atTop
            (𝓝 (limitingCountMass P.z (P.qResponse v lam) j))) := by
  let F := Classical.choice (P.construct_active_numeric_family c hc muLow hpositive mu)
  refine ⟨F.threshold,F.low,F.joint,F.multiplier,F.source_interval,F.clearing,?_,
    ?_,F.atomless,F.all_bid_IC,F.price_tendsto,F.supported_graph,F.conditional_counts⟩
  · intro nu hnu hclear
    exact congrArg Subtype.val (F.unique ⟨nu,hnu⟩ hclear)
  · intro M h
    exact ⟨F.lowWitness M h,F.low_eq M h⟩

end Primitives
end FCAppendix.Affine.Hybrid.Finish01
