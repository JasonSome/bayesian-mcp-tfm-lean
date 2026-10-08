import FCAppendix.PayOnce.InactiveCentralBidCopies
import FCAppendix.PayOnce.DummyConditionalMarginal
import FCAppendix.PayOnce.InactiveCentralActualProfiles
import FCAppendix.PayOnce.GaussianCopiesCoefficient
import FCAppendix.Probability.CountMomentAsymptotics

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel Probability
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_central_copies
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
    let α := 2/((((k+1:ℕ):ℝ)-1)*L)
    let s := inactiveGaussianScale M F (k+1) g ρ
    let μ := fun t => Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
    ∃ b : ℕ → ℝ → ℝ, (∀ t, Monotone (b t)) ∧ (∀ t, Measurable (b t)) ∧
      (∀ t v, 0 ≤ b t v ∧ b t v ≤ max (v-g) 0) ∧
      (∀ᶠ t in atTop, ∀ᵐ z ∂((Γ t).F ⊗ₘ (Γ t).σ), effectiveBid z.2=b t z.1) ∧
      ∃ A : Set ℝ, (∀ᵐ v ∂F, v ∈ A) ∧
        (∀ᶠ t in atTop, ∀ v ∈ A, g<v → InactiveCentralRegular Γ hn g b t v) ∧
        (∀ᶠ t in atTop, ∀ v ∈ A, TypeProfileMarginalAgreement (Γ t) hn (b t v) v) ∧
        ∀ (x : ℕ → ℝ) (x₀ : ℝ), Tendsto x atTop (𝓝 x₀) →
          (∀ᶠ t in atTop, inactiveCentralValue M C F (k+1) g ρ (x t) t ∈ A) →
          let v := fun t => inactiveCentralValue M C F (k+1) g ρ (x t) t
          let y := GaussianResponse.response x₀
          let p := fun (t : ℕ) (r : Fin (M t-1) → ℝ) => allocation (k+1) (C t) hn r (b t (v t))
          TendstoInDistribution (fun t r => p t r/s t) atTop (fun Z => α*max (y-Z) 0) μ (gaussianReal 0 1) ∧
          (∀ j : ℕ, Tendsto (fun t => (∫ r, (p t r)^j ∂μ t)/(s t)^j) atTop
            (𝓝 (α^j*(∫ Z : ℝ, (max (y-Z) 0)^j ∂gaussianReal 0 1)))) ∧
          ∀ D : ℕ → CountLaw (k+1), (∀ᶠ t in atTop, ∃ i : Fin (M t), D t=typeOutcome (Γ t) i (v t)) →
            (∀ j : ℕ, Tendsto (fun t => (D t).prob (fun r => r.val=j)/(s t)^j) atTop
              (𝓝 ((Nat.choose (k+1) j:ℝ)*α^j*(∫ Z : ℝ, (max (y-Z) 0)^j ∂gaussianReal 0 1)))) ∧
            Tendsto (fun t => ((D t).load/(D t).success-1)/s t) atTop
              (𝓝 ((1/L)*GaussianResponse.secondPositivePart y/gaussianSuccessPrimitive y)) ∧
            Tendsto (fun t => ((D t).prob (fun r => 2 ≤ r.val)/(D t).success)/s t) atTop
              (𝓝 ((1/L)*GaussianResponse.secondPositivePart y/gaussianSuccessPrimitive y)) := by
  dsimp only
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
  let α := 2/((((k+1:ℕ):ℝ)-1)*L)
  let s := inactiveGaussianScale M F (k+1) g ρ
  let μ := fun t => Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
  obtain ⟨hL,_hD,b,hmono,hmeas,hbound,heq,hlim⟩ := payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h
  obtain ⟨A,hA,hreg⟩ := payOnce_inactive_central_regular_set Γ B F g ρ h b heq
  let Q := fun t v => ∀ i : Fin (M t), ∀ j : ℕ,
    (typeOutcome (Γ t) i v).prob (fun r => r.val=j) =
      ∫ r, ManyProposers.binomialMass (k+1) (allocation (k+1) (C t) hn r (b t v)) j ∂μ t
  have ht : ∀ᶠ t in atTop, ∀ᵐ v ∂F, Q t v ∧ TypeProfileMarginalAgreement (Γ t) hn (b t v) v := by
    filter_upwards [payOnce_inactive_eventual_type_countMass Γ B F g ρ h b heq,
      payOnce_inactive_eventual_type_profileMarginal Γ B F g ρ h b heq] with t hc hp
    exact hc.and hp
  obtain ⟨T,hT⟩ := eventually_atTop.mp ht
  let A' := A ∩ {v | ∀ t, T ≤ t → Q t v ∧ TypeProfileMarginalAgreement (Γ t) hn (b t v) v}
  have hA' : ∀ᵐ v ∂F, v ∈ A' := by
    exact hA.and (ae_all_iff.mpr fun t => ae_all_iff.mpr fun ht => hT t ht)
  refine ⟨b,hmono,hmeas,hbound,heq,A',hA',hreg.mono (fun t ht v hv => ht v hv.1),?_,?_⟩
  · filter_upwards [eventually_ge_atTop T] with t ht v hv
    exact (hv.2 t ht).2
  · intro x x₀ hx hxA
    let v := fun t => inactiveCentralValue M C F (k+1) g ρ (x t) t
    let y := GaussianResponse.response x₀
    have hv : ∀ᶠ t in atTop, g < v t := by
      have hh := (payOnce_inactive_central_value_tendsto Γ B F g ρ h x hx).eventually_const_lt hL
      filter_upwards [hh] with t ht
      change 0<v t-g at ht
      linarith
    have hregular : ∀ᶠ t in atTop, InactiveCentralRegular Γ hn g b t (v t) := by
      filter_upwards [hreg,hxA,hv] with t ht hxt hvt
      exact ht _ hxt.1 hvt
    have hy : Tendsto (fun t => (b t (v t)-KernelDemand.populationPrice (k+1)
        (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))/s t) atTop (𝓝 y) :=
      payOnce_inactive_pure_bid_of_central_values Γ B F g ρ h hlocal b hmono
        (fun t w => (hbound t w).2) hlim v
        (payOnce_inactive_central_value_coordinate Γ B F g ρ h hlocal x hx)
        (hregular.mono fun _ ht => ht.1)
    have hall := payOnce_inactive_central_bid_copies Γ B F g ρ h hlocal (fun t => b t (v t)) hy
    refine ⟨hall.1,hall.2.1,?_⟩
    intro D hD
    have hcounts : ∀ j : ℕ, Tendsto (fun t => (D t).prob (fun r => r.val=j)/(s t)^j) atTop
        (𝓝 ((Nat.choose (k+1) j:ℝ)*α^j*(∫ Z : ℝ, (max (y-Z) 0)^j ∂gaussianReal 0 1))) := by
      intro j
      apply (hall.2.2 j).congr'
      filter_upwards [hxA,hD,eventually_ge_atTop T] with t hxt hDt ht
      obtain ⟨i,hi⟩ := hDt
      rw [hi,(hxt.2 t ht).1 i j]
    have hS : Tendsto (fun t => (D t).success/s t) atTop
        (𝓝 (((k+1:ℕ):ℝ)*α*gaussianSuccessPrimitive y)) := by
      apply (payOnce_inactive_central_coverage_of_normalized_bid Γ B F g ρ h hlocal (fun t => b t (v t)) hy).congr'
      filter_upwards [hregular,hD] with t ht hDt
      obtain ⟨i,hi⟩ := hDt
      rw [hi,(ht.2 i).1]
    have hsp : ∀ᶠ t in atTop, 0 < s t := by
      filter_upwards [h.population_grows.eventually_gt_atTop 0] with t ht
      exact payOnce_inactive_gaussian_scale_pos Γ B F g ρ h hlocal ht
    have hTpos : 0 < gaussianSuccessPrimitive y := GaussianResponse.successPrimitive_pos y
    have hα : 0 < α := by
      have hnR : (2:ℝ) ≤ (k+1:ℕ) := by exact_mod_cast hn
      dsimp only [α]
      apply div_pos (by norm_num)
      exact mul_pos (by linarith) hL
    have hc : 0 < ((k+1:ℕ):ℝ)*α*gaussianSuccessPrimitive y := by positivity
    have hh := CountLaw.conditional_copies_limit_of_mass_limits hn D s hsp
      (inactiveGaussianScale_tendsto_zero M F (k+1) g ρ h.population_grows)
      (fun j => (Nat.choose (k+1) j.val:ℝ)*α^j.val*(∫ Z : ℝ, (max (y-Z) 0)^j.val ∂gaussianReal 0 1))
      (fun j _ => hcounts j.val) hc hS
    have hcoef : ((Nat.choose (k+1) 2:ℝ)*α^2*(∫ Z : ℝ, (max (y-Z) 0)^2 ∂gaussianReal 0 1))/
        (((k+1:ℕ):ℝ)*α*gaussianSuccessPrimitive y) =
          (1/L)*GaussianResponse.secondPositivePart y/gaussianSuccessPrimitive y := by
      rw [GaussianResponse.integral_normal_positivePart_sq]
      exact GaussianResponse.copies_coefficient hn hL hTpos
    refine ⟨hcounts,?_,?_⟩
    · simpa only [hcoef] using hh.2.2.1
    · simpa only [hcoef] using hh.2.2.2

end FCAppendix.Bayes
