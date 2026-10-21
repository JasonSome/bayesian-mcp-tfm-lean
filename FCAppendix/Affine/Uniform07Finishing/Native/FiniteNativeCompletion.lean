import FCAppendix.Affine.Uniform07Finishing.Native.FixedValueCompletion
import FCAppendix.Affine.Uniform07Finishing.Native.SourceSuccessCap
import FCAppendix.Affine.Uniform07Finishing.Native.BoundaryUtilityLimit

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open Existence.RankEnvelope StrictNative

variable {m : ℕ} [Nonempty (Fin m)]
variable (row : Uniform07.Row) (hm : 2≤ m) (hc : 1≤ Uniform07.capacity m)
    {R Λ z width ε : ℝ} (hR : 0< R) (hUR : Early.bidCap row< R)
    (hRt : R< Uniform07.cutoff row)
    (hΛ : (54/100:ℝ)*Uniform07.cutoff row<Λ) (hε : 0<ε)
    (PL : ProbabilityMeasure (ℝ×JointAction 2))
    (hLvalue : (PL : Measure (ℝ×JointAction 2)).map Prod.fst=
      (sourceLowerValueLaw row : Measure ℝ))
    (hLroute : ∀ᵐ x ∂(PL : Measure (ℝ×JointAction 2)),
      x.2.bid≤ Early.bidCap row ∧ x.2.routeCount=2)
    (hLatom : ∀ y : ℝ, (PL : Measure (ℝ×JointAction 2)) {x|x.2.bid=y}=0)

local notation "Γ₀" => sourceNativeGame row hc R Λ
  (source_guard_multiplier_positive row hΛ) PL
  (literalSourceAlpha row Λ z width ε)
  (measurable_literalSourceAlpha row hΛ z width ε)
local notation "Γ" => literalSourceNativeGame row hc R Λ z width ε hΛ PL
local notation "t" => Uniform07.cutoff row
local notation "q" => source_upper_rank row m

include hm hR hUR hRt hε hLvalue hLroute hLatom in

theorem literal_source_fixed_value_completion
    (hRhi : R≤ sourceLowerPriceCeiling row)
    (hs : sourceLowerSuccessCap row< q t)
    (hguard : error q t R< Uniform07.eta row*R*(1-2*sourceUpperFailure row m))
    (aT : JointAction 2) (hTU : aT.bid≤ Early.bidCap row) (hTk : aT.routeCount=2)
    (hT : ∀ u : Fin m, ∀ b : JointAction 2, b.routeCount=2 → b.bid< R →
      (problem Γ₀ u).payoff t b≤(problem Γ₀ u).payoff t aT)
    (hmatch : ∀ u : Fin m, (problem Γ₀ u).payoff t aT=utility q t R t)
    (hcross : ∀ v : ℝ, 0< v → v≤ t → ∀ u : Fin m,
      ∀ a : JointAction 2, a.routeCount=1 → a.bid< R →
        ∃ b : JointAction 2, b.routeCount=2 ∧ b.bid< R ∧
          (problem Γ₀ u).payoff v a<(problem Γ₀ u).payoff v b)
    (hbad : ∀ u (a : JointAction 2), a.bid< R →
      (userProfileLaw Γ).real (sourceSuccessGood row hc R Λ z width ε PL u a)ᶜ≤
        (1-sourceLowerMarginalCap row)^2/2)
    (hpay : ∀ u : Fin m, ∀ w : ℝ×Icc (0:ℝ) (Early.bidCap row), 0<(w.2:ℝ) →
      ContinuousAt (fun y : ℝ×Icc (0:ℝ) (Early.bidCap row)=>
        (problem Γ₀ u).payoff y.1 (sourceLowerBroadcastAction (Early.bidCap row) y.2)) w)
    (hLowerIC : ∀ᵐ x ∂(PL : Measure (ℝ×JointAction 2)),
      ∀ u : Fin m, ∀ b : JointAction 2, b.routeCount=2 → b.bid< R →
        (problem Γ₀ u).payoff x.1 b≤(problem Γ₀ u).payoff x.1 x.2) :
    ∃ κ : Kernel ℝ (JointAction 2), ∃ hκM : IsMarkovKernel κ,
      κ=ᵐ[Uniform07.uniformLaw](Γ).σ ∧
      (∀ v, v∉Ioo 0 t → κ v=(Γ).σ v) ∧
      let G := @withStrategy m 2 (Uniform07.capacity m) unitInterval _ Γ κ hκM
      G.F=Uniform07.uniformLaw ∧
      G.A=Schedule.affine 2 (Uniform07.eta row)
        (Uniform07.eta_pos row).le (sourceProduct_eta_le_one row) ∧
      G.G=Schedule.once 2 ∧ G.g=0 ∧ G.seedLaw=volume ∧
      G.F⊗ₘG.σ=(sourcePopulation row m hc R PL : Measure (ℝ×JointAction 2)) ∧
      IsBayesianEquilibrium G ∧ VisibleAtomless G ∧
      (∀ u : Fin m, ∀ a : JointAction 2, (problem G u).outcome a=(problem Γ₀ u).outcome a) ∧
      (∀ v, 0< v → v≤ 1 → ∀ᵐ a ∂G.σ v, ∀ u : Fin m, ∀ d : JointAction 2,
        (problem G u).payoff v d≤(problem G u).payoff v a) ∧
      (∀ v, 0< v → v< t → ∀ᵐ a ∂G.σ v, a.bid≤ Early.bidCap row ∧ a.routeCount=2) ∧
      (∀ v, t≤ v → G.σ v=Measure.dirac (Hybrid.upperAction (sourceUpperBid row m R) v)) ∧
      (∀ v, 0< v → v≤ 1 → v≠t → ∀ᵐ a ∂G.σ v,
        a.routeCount=if v< t then 2 else 1) := by
  have hcap := sourceNative_lower_success_cap_of_plan_bad_mass row (by omega)
    hc hR hRhi hΛ hε PL hbad
  have hbT : aT.bid< R := hTU.trans_lt hUR
  have hEQ : IsBayesianEquilibrium Γ :=
    completeSourceNativeGame_equilibrium_of_lower_chain row hm hc hR hUR hRt
      (source_guard_multiplier_positive row hΛ) PL hLvalue hLroute
      (literalSourceAlpha row Λ z width ε)
      (measurable_literalSourceAlpha row hΛ z width ε)
      hguard aT hTk hbT hT hmatch hcross (sourceLowerSuccessCap row) hs hcap hLowerIC
  have hVis : VisibleAtomless Γ := by
    have hV := sourceNativeGame_visible_atomless row hm hc hR hRt
      (source_guard_multiplier_positive row hΛ) PL hLvalue hLroute
      (literalSourceAlpha row Λ z width ε)
      (measurable_literalSourceAlpha row hΛ z width ε) hLatom
    exact hV
  have hShape : ∀ᵐ x ∂(Γ).F⊗ₘ(Γ).σ,
      x.1∈Ioo 0 t → x.2.bid≤ Early.bidCap row ∧ x.2.routeCount=2 := by
    rw [literalSourceNativeGame_joint_law row hm hc hR hRt hΛ PL hLvalue hLroute]
    filter_upwards [source_population_support row m hm hc hR hRt PL hLvalue hLroute]
      with x hx hxlow
    rcases hx with hl | hh
    · exact ⟨hl.2.2.1,hl.2.2.2⟩
    · exact (not_lt_of_ge hh.1.le hxlow.2).elim
  have hPay : ∀ u : Fin m, ∀ w : ℝ×Icc (0:ℝ) (Early.bidCap row), 0<(w.2:ℝ) →
      ContinuousAt (fun y : ℝ×Icc (0:ℝ) (Early.bidCap row)=>
        (problem Γ u).payoff y.1 (sourceLowerBroadcastAction (Early.bidCap row) y.2)) w := by
    intro u w hw
    simpa only [literalSourceNativeGame,completeSourceNativeGame_payoff] using hpay u w hw
  have hUpper (v : ℝ) (hv:t≤ v) (u : Fin m) (a : JointAction 2) :
      (problem Γ u).payoff v a≤
        (problem Γ u).payoff v (Hybrid.upperAction (sourceUpperBid row m R) v) := by
    simpa only [literalSourceNativeGame,completeSourceNativeGame_payoff] using
      sourceNativeGame_upper_best_all_routes row hm hc hR hUR hRt
        (source_guard_multiplier_positive row hΛ) PL hLvalue hLroute
        (literalSourceAlpha row Λ z width ε)
        (measurable_literalSourceAlpha row hΛ z width ε)
        hguard aT hT hmatch hcross (sourceLowerSuccessCap row) hs hcap v hv u a
  have hUpperKernel (v : ℝ) (hv:t≤ v) :
      (Γ).σ v=Measure.dirac (Hybrid.upperAction (sourceUpperBid row m R) v) :=
    sourceNativeGame_fixed_upper row hc (source_guard_multiplier_positive row hΛ) PL
      (literalSourceAlpha row Λ z width ε)
      (measurable_literalSourceAlpha row hΛ z width ε) v hv
  obtain ⟨κ,hκM,hκ,hoff,hκEQ,hκVis,hκIC,hκshape,hκUpper,hκroute⟩ :=
    exists_full_positive_uniform_version Γ (Early.bidCap row) t
      (Uniform07.cutoff_pos row) (Uniform07.cutoff_lt_one row).le rfl rfl
      hEQ hVis hShape hPay (Hybrid.upperAction (sourceUpperBid row m R))
      (fun _=>rfl) hUpperKernel hUpper
  letI : IsMarkovKernel κ:=hκM
  refine ⟨κ,hκM,hκ,hoff,rfl,rfl,rfl,rfl,rfl,?_,hκEQ,hκVis,?_,
    hκIC,hκshape,hκUpper,hκroute⟩
  · rw [withStrategy_joint_law Γ κ hκ,
      literalSourceNativeGame_joint_law row hm hc hR hRt hΛ PL hLvalue hLroute]
  · intro u a
    rw [withStrategy_outcome Γ κ hκ]
    exact completeSourceNativeGame_outcome row hc R Λ
      (source_guard_multiplier_positive row hΛ) PL
      (literalSourceAlpha row Λ z width ε)
      (measurable_literalSourceAlpha row hΛ z width ε) u a

end FCAppendix.Affine.Uniform07Finishing
