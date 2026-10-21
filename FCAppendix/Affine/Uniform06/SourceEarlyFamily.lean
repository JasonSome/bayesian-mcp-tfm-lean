import FCAppendix.Affine.Uniform06.ActiveLocalization
import FCAppendix.Affine.Uniform06.SourceRankFamily

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.SourceEarlyFamily

open MeasureTheory Set Filter Topology
open Uniform07 LowBody Rank LiteralExperiment LiteralPrefixStieltjes
open LowRankMeasures CrossoverRankDensity SourcePrefixConstructor
open SharpPureDerivative SharpPureMeasure PureRankCounts PurePivotalSource

section Family
variable {C : ℕ → Type*}
    (G : ∀ m,C m → ProbabilityMeasure (ℝ × ℝ))
    (g : ∀ m,C m → GuardData)
    (cm : ∀ m,C m → (Fin (m-1) → Fin 4) → ℝ)

structure EarlyMenuFields (i : Row) : Prop where
  value_marginal : ∀ m (E : C m),(G m E:Measure (ℝ × ℝ)).map Prod.fst=
    LowChernoff.conditionalValueLaw i
  permitted : ∀ m (E : C m),∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),
    p.2 ∈ Icc (LowChernoff.physicalFloor i p.1) (min p.1 (ReceiptGap.cap i))
  all_action_IC : ∀ m (E : C m),∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),
    ∀ b ∈ Icc (LowChernoff.physicalFloor i p.1) (min p.1 (ReceiptGap.cap i)),
      payoff (eta i) p.1 b (sourceSuccess i m (G m E) (g m E) (cm m E) b)
        (sourceDuplicate i m (G m E) (g m E) (cm m E) b) ≤
      payoff (eta i) p.1 p.2 (sourceSuccess i m (G m E) (g m E) (cm m E) p.2)
        (sourceDuplicate i m (G m E) (g m E) (cm m E) p.2)
  product_menu : ∀ e > (0:ℝ),∀ᶠ m in atTop,∀ E : C m,
    ∀ v ∈ Icc (0:ℝ) (cutoff i),
      ∀ b ∈ Icc (LowChernoff.physicalFloor i v) (min v (ReceiptGap.cap i)),
        |payoff (eta i) v b (sourceSuccess i m (G m E) (g m E) (cm m E) b)
          (sourceDuplicate i m (G m E) (g m E) (cm m E) b)-
            ActiveLocalization.product (xi i) v (g m E).multiplier b| ≤ e
  comparison : ∀ m (E : C m) v,entry i < v → v ≤ cutoff i →
    0 < (g m E).multiplier → (g m E).multiplier < v →
      ActiveLocalization.bestBid (xi i) v (g m E).multiplier ∈
        Icc (LowChernoff.physicalFloor i v) (min v (ReceiptGap.cap i))
  root_limit : ∀ e > (0:ℝ),∀ᶠ m in atTop,∀ E : C m,
    |(g m E).multiplier-entry i| < e

theorem bestBid_eq_activeBid (i : Row) (v : ℝ) :
    ActiveLocalization.bestBid (xi i) v (entry i)=ActiveGraphComponent.activeBid i v := by
  unfold ActiveLocalization.bestBid ActiveGraphComponent.activeBid
  rw [LiteralRankIC.source_kappa]

theorem source_early_active_closed (i : Row) (h05 : EarlyMenuFields G g cm i) :
    ∀ a > (0:ℝ),∀ ε > (0:ℝ),∀ᶠ m in atTop,∀ E : C m,
      ∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),p.1 ∈ Icc (entry i+a) (cutoff i) →
        |p.2-ActiveGraphComponent.activeBid i p.1| < ε := by
  have hcommon : ∀ m (E : C m),∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),
      p.1 ∈ Icc (0:ℝ) (cutoff i) ∧
      p.2 ∈ Icc (LowChernoff.physicalFloor i p.1) (min p.1 (ReceiptGap.cap i)) ∧
      ∀ b ∈ Icc (LowChernoff.physicalFloor i p.1) (min p.1 (ReceiptGap.cap i)),
        payoff (eta i) p.1 b (sourceSuccess i m (G m E) (g m E) (cm m E) b)
          (sourceDuplicate i m (G m E) (g m E) (cm m E) b) ≤
        payoff (eta i) p.1 p.2 (sourceSuccess i m (G m E) (g m E) (cm m E) p.2)
          (sourceDuplicate i m (G m E) (g m E) (cm m E) p.2) := by
    intro m E
    filter_upwards [EarlyRankCeiling.same_joint_value_support i
      (G m E:Measure (ℝ × ℝ)) (h05.value_marginal m E),
      h05.permitted m E,h05.all_action_IC m E] with p hv hp hi
    exact ⟨hv,hp,hi⟩
  have hξ1 : xi i < 1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  have hLam : 0 < entry i :=
    mul_pos (by cases i <;> norm_num [x,xQ]) (cutoff_pos i)
  have hLamT : entry i < cutoff i := by
    have hx : x i < 1 := by cases i <;> norm_num [x,xQ]
    unfold entry
    nlinarith [cutoff_pos i]
  have hactive := ActiveLocalization.uniform_active_graph_from_early_menu C
    (fun m E => (G m E:Measure (ℝ × ℝ))) (fun m E => (g m E).multiplier)
    (fun m E v b => payoff (eta i) v b
      (sourceSuccess i m (G m E) (g m E) (cm m E) b)
      (sourceDuplicate i m (G m E) (g m E) (cm m E) b))
    (fun _ _ v => Icc (LowChernoff.physicalFloor i v) (min v (ReceiptGap.cap i)))
    (xi_pos i) hξ1 hLam hLamT hcommon h05.comparison h05.product_menu h05.root_limit
  simpa only [bestBid_eq_activeBid] using hactive

theorem source_early_active (i : Row) (h05 : EarlyMenuFields G g cm i) :
    ∀ a > (0:ℝ),∀ ε > (0:ℝ),∀ᶠ m in atTop,∀ E : C m,
      ∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),p.1 ∈ Ioc (entry i+a) (cutoff i) →
        |p.2-ActiveGraphComponent.activeBid i p.1| ≤ ε := by
  intro a ha ε hε
  filter_upwards [source_early_active_closed G g cm i h05 a ha ε hε] with m hm
  intro E
  filter_upwards [hm E] with p hp hv
  exact (hp ⟨hv.1.le,hv.2⟩).le

theorem source_common_used (i : Row) (h05 : EarlyMenuFields G g cm i)
    (hatom : ∀ m (E : C m) b,((G m E:Measure (ℝ × ℝ)).map Prod.snd) {b}=0) :
    ∀ m (E : C m),∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),p ∈
      LiteralRankIC.usedSet i m (G m E:Measure (ℝ × ℝ)) (g m E) (cm m E) (ReceiptGap.cap i) := by
  intro m E
  exact LiteralRankIC.usedSet_full i m (G m E:Measure (ℝ × ℝ))
    (h05.value_marginal m E) (hatom m E) (g m E) (cm m E) (ReceiptGap.cap i)
    (h05.permitted m E) (h05.all_action_IC m E)

theorem eventually_source_prefix (i : Row) (h05 : EarlyMenuFields G g cm i)
    (hfields : ∀ m (E : C m),LiteralFields i (g m E))
    (hpsi : ∀ m (E : C m),
      (∫ p,PrefixRoot.sourcePsi i (g m E).rejectionRoot p.2 ∂(G m E:Measure (ℝ × ℝ)))=
        3*PrefixRoot.requiredDemand i) :
    ∀ᶠ m in atTop,∀ E : C m,
      (g m E).radius ≤ cutoff i/100 ∧
      PrefixConditions (xi i) (g m E) (sortEnd i) ∧
      LowRankMeasures.extensionEnd i ≤ (g m E).multiplier-(g m E).radius := by
  have ha : 0 < cutoff i/40000 := by have ht := cutoff_pos i; positivity
  have he : 0 < activeError i := by have ht := cutoff_pos i; unfold activeError; positivity
  filter_upwards [h05.root_limit (cutoff i/40000) ha,
    source_early_active_closed G g cm i h05 (cutoff i/40000) ha (activeError i) he]
      with m hr hac
  intro E
  have hA : ∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),p.1 ∈ Icc (sortEnd i) (cutoff i) →
      |p.2-ActiveGraphComponent.activeBid i p.1| ≤ activeError i := by
    filter_upwards [hac E] with p hp hv
    apply (hp ⟨?_,hv.2⟩).le
    unfold sortEnd at hv
    have ht := cutoff_pos i
    linarith only [hv.1,ht]
  have hp := original_prefix_constructor i (G m E:Measure (ℝ × ℝ))
    (h05.value_marginal m E) (g m E) (hfields m E) (hr E) (hpsi m E) hA
  refine ⟨?_,hp.1,hp.2⟩
  rw [(hfields m E).radius_eq]
  unfold radius
  have ht := cutoff_pos i
  linarith

theorem early_source_constructor (i : Row) (h05 : EarlyMenuFields G g cm i)
    (hatom : ∀ m (E : C m) b,((G m E:Measure (ℝ × ℝ)).map Prod.snd) {b}=0)
    (hfields : ∀ m (E : C m),LiteralFields i (g m E))
    (hpsi : ∀ m (E : C m),
      (∫ p,PrefixRoot.sourcePsi i (g m E).rejectionRoot p.2 ∂(G m E:Measure (ℝ × ℝ)))=
        3*PrefixRoot.requiredDemand i) :
    (∀ a > (0:ℝ),∀ ε > (0:ℝ),∀ᶠ m in atTop,∀ E : C m,
      ∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),p.1 ∈ Ioc (entry i+a) (cutoff i) →
        |p.2-ActiveGraphComponent.activeBid i p.1| ≤ ε) ∧
    (∀ m (E : C m),∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),p ∈
      LiteralRankIC.usedSet i m (G m E:Measure (ℝ × ℝ)) (g m E) (cm m E) (ReceiptGap.cap i)) ∧
    (∀ᶠ m in atTop,∀ E : C m,(g m E).radius ≤ cutoff i/100 ∧
      PrefixConditions (xi i) (g m E) (sortEnd i) ∧
      LowRankMeasures.extensionEnd i ≤ (g m E).multiplier-(g m E).radius) :=
  ⟨source_early_active G g cm i h05,source_common_used G g cm i h05 hatom,
    eventually_source_prefix G g cm i h05 hfields hpsi⟩

theorem eventually_source_rank_chain (i : Row) (h05 : EarlyMenuFields G g cm i)
    (hatom : ∀ m (E : C m) b,((G m E:Measure (ℝ × ℝ)).map Prod.snd) {b}=0)
    (hfields : ∀ m (E : C m),LiteralFields i (g m E))
    (hpsi : ∀ m (E : C m),
      (∫ p,PrefixRoot.sourcePsi i (g m E).rejectionRoot p.2 ∂(G m E:Measure (ℝ × ℝ)))=
        3*PrefixRoot.requiredDemand i) :
    ∃ γ : ℝ,0 < γ ∧ ∀ᶠ m in atTop,∀ E : C m,
      lowBidMeasure i (G m E) (crossoverEnd i) ≪ volume ∧
      (∀ lo : ℝ,0 < lo → ∀ A : Set ℝ,MeasurableSet A → A ⊆ Icc lo (crossoverEnd i) →
        (lowBidMeasure i (G m E) (crossoverEnd i)).real A ≤
          densityCoefficient i m (g m E) (crossoverEnd i)*
            (volume.real A/(1-contraction i m*kappa i)+
              (∫ b in A,1/b)/(1-contraction i m))) ∧
      ∀ lo : ℝ,0 < lo → kappa i*ReceiptGap.cap i < lo → lo < crossoverEnd i →
        (∃ F : StieltjesFunction ℝ,Continuous F ∧ (∀ b,F b ∈ Icc (0:ℝ) 1) ∧
          (∀ b ∈ Icc lo (crossoverEnd i),F b=
            expectedUnequalPureFirst (m-1) (capacity m) (kappa i) (cutoff i)
              ((G m E:Measure (ℝ × ℝ)).map Prod.snd) b) ∧
          F.measure.restrict (Ioc lo (crossoverEnd i)) ≪ volume) ∧
        (∀ᵐ b ∂(bidMeasure i (G m E)).restrict (Ioo lo (crossoverEnd i)),
          DifferentiableAt ℝ (sourceRank (cutoff i) ((G m E:Measure (ℝ × ℝ)).map Prod.snd)) b ∧
          DifferentiableAt ℝ (expectedUnequalPureFirst (m-1) (capacity m) (kappa i) (cutoff i)
            ((G m E:Measure (ℝ × ℝ)).map Prod.snd)) b ∧
          |deriv (expectedUnequalPureFirst (m-1) (capacity m) (kappa i) (cutoff i)
              ((G m E:Measure (ℝ × ℝ)).map Prod.snd)) b-
            2*rankSlope i m (sourceRank (cutoff i) ((G m E:Measure (ℝ × ℝ)).map Prod.snd) b)*
              deriv (sourceRank (cutoff i) ((G m E:Measure (ℝ × ℝ)).map Prod.snd)) b| ≤
            2*rankSlope i m (sourceRank (cutoff i) ((G m E:Measure (ℝ × ℝ)).map Prod.snd) b)*
              deriv (sourceRank (cutoff i) ((G m E:Measure (ℝ × ℝ)).map Prod.snd)) b*
                relativeError γ m) := by
  exact SourceRankFamily.eventually_source_rank_chain G g cm i
    h05.value_marginal h05.permitted hatom hfields hpsi h05.root_limit
    (source_early_active G g cm i h05) h05.all_action_IC

theorem eventually_source_stieltjes_IC (i : Row) (h05 : EarlyMenuFields G g cm i)
    (hatom : ∀ m (E : C m) b,((G m E:Measure (ℝ × ℝ)).map Prod.snd) {b}=0)
    (hfields : ∀ m (E : C m),LiteralFields i (g m E))
    (hpsi : ∀ m (E : C m),
      (∫ p,PrefixRoot.sourcePsi i (g m E).rejectionRoot p.2 ∂(G m E:Measure (ℝ × ℝ)))=
        3*PrefixRoot.requiredDemand i) :
    ∀ᶠ m in atTop, ∀ E : C m, ∀ lo : ℝ, 0 < lo → lo ≤ crossoverEnd i →
      ∃ (F D : StieltjesFunction ℝ),
        Continuous F ∧ Continuous D ∧ IsFiniteMeasure F.measure ∧ IsFiniteMeasure D.measure ∧
        (∀ b ∈ Icc (lo/2) (crossoverEnd i),
          F b=sourceSuccess i m (G m E) (g m E) (cm m E) b ∧
          D b=sourceDuplicate i m (G m E) (g m E) (cm m E) b) ∧
        (let U := (lowBidMeasure i (G m E) (crossoverEnd i)).support ∩ Icc lo (crossoverEnd i)
         F.measure.restrict U ≪ volume ∧ D.measure.restrict U ≪ volume ∧
           (F.measure.restrict U).withDensityᵥ
             (fun b => PureRankCounts.sourceRank (cutoff i) ((G m E:Measure (ℝ × ℝ)).map Prod.snd) b-b)=
             (volume.restrict U).withDensityᵥ (fun b =>
               sourceSuccess i m (G m E) (g m E) (cm m E) b+
                 eta i*sourceDuplicate i m (G m E) (g m E) (cm m E) b)+
             (D.measure.restrict U).withDensityᵥ (fun b => eta i*b)) := by
  exact SourcePrefixConstructor.eventually_family_crossover_stieltjes_IC C G g cm i
    h05.value_marginal h05.permitted hatom hfields hpsi h05.root_limit
    (source_early_active G g cm i h05) h05.all_action_IC

end Family
end FCAppendix.Affine.Uniform06.SourceEarlyFamily
