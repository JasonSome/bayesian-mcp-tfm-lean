import FCAppendix.Affine.Uniform06.SourcePrimitiveStieltjes
import FCAppendix.Affine.Uniform06.LiteralPureBid

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.SourceRankOutput

open MeasureTheory Set Filter Topology LowBody
open Uniform07 LiteralExperiment LiteralPrefixStieltjes LowRankMeasures
open SourcePrefixConstructor SourceEarlyFamily PrimitiveStieltjesMeasures
open CrossoverRankDensity SharpPureDerivative SharpPureMeasure
open PureRankCounts PurePivotalSource

section Family
variable {C : ℕ → Type*}
    (G : ∀ m,C m → ProbabilityMeasure (ℝ × ℝ))
    (g : ∀ m,C m → GuardData)
    (cm : ∀ m,C m → (Fin (m-1) → Fin 4) → ℝ)

def RankRegularity (i : Row) : Prop :=
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
                relativeError γ m)

def ClosedSupportIC (i : Row) : Prop :=
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
             (D.measure.restrict U).withDensityᵥ (fun b => eta i*b))

def PrimitiveMeasures (i : Row) : Prop :=
  ∀ᶠ m in atTop,∀ E : C m,∀ lo : ℝ,0 < lo → lo ≤ crossoverEnd i →
      Nonempty (PrimitiveStieltjesBounds i m (G m E:Measure (ℝ × ℝ))
        (g m E) (cm m E) lo (crossoverEnd i))

structure Output (i : Row) : Prop where
  common_used : ∀ m (E : C m),∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),p ∈
    LiteralRankIC.usedSet i m (G m E:Measure (ℝ × ℝ)) (g m E) (cm m E) (ReceiptGap.cap i)
  sorting : ∀ᶠ m in atTop,∀ E : C m,
    ∀ p ∈ LiteralRankIC.usedSet i m (G m E:Measure (ℝ × ℝ)) (g m E) (cm m E) (ReceiptGap.cap i),
      p.1< sortEnd i →
      ∀ q ∈ LiteralRankIC.usedSet i m (G m E:Measure (ℝ × ℝ)) (g m E) (cm m E) (ReceiptGap.cap i),
        p.1< q.1 → p.2≤ q.2
  used_rank : ∀ᶠ m in atTop,∀ E : C m,∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),
    p.1< sortEnd i → sourceRank (cutoff i) ((G m E:Measure (ℝ × ℝ)).map Prod.snd) p.2=p.1
  pure_bid : ∀ᶠ m in atTop,∀ E : C m,∃ B : ℝ→ℝ,
    Monotone B ∧ Measurable B ∧ (∀ v,B v∈Icc (0:ℝ) (ReceiptGap.cap i)) ∧
      ∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),p.1< sortEnd i →
        p.2=B p.1 ∧ sourceRank (cutoff i)
          ((G m E:Measure (ℝ × ℝ)).map Prod.snd) (B p.1)=p.1
  regularity : RankRegularity G g i
  primitive_measures : PrimitiveMeasures G g cm i
  closed_support_IC : ClosedSupportIC G g cm i

theorem from_early_source (i : Row) (h05 : EarlyMenuFields G g cm i)
    (hatom : ∀ m (E : C m) b,((G m E:Measure (ℝ × ℝ)).map Prod.snd) {b}=0)
    (hfields : ∀ m (E : C m),LiteralFields i (g m E))
    (hpsi : ∀ m (E : C m),
      (∫ p,PrefixRoot.sourcePsi i (g m E).rejectionRoot p.2 ∂(G m E:Measure (ℝ × ℝ)))=
        3*PrefixRoot.requiredDemand i) : Output G g cm i := by
  have hcommon := source_common_used G g cm i h05 hatom
  have hprefix := eventually_source_prefix G g cm i h05 hfields hpsi
  refine ⟨hcommon,?_,?_,?_,
    eventually_source_rank_chain G g cm i h05 hatom hfields hpsi,
    SourcePrimitiveStieltjes.eventually_source_primitive_stieltjes G g cm i h05 hatom hfields hpsi,
    eventually_source_stieltjes_IC G g cm i h05 hatom hfields hpsi⟩
  · filter_upwards [hprefix,eventually_ge_atTop (4:ℕ)] with m hp hm E
    exact LiteralRankIC.usedSet_sorted i hm (G m E:Measure (ℝ × ℝ))
      ((h05.permitted m E).mono fun _ h => h.1) (hatom m E)
      (g m E) (hp E).2.1 (cm m E) (ReceiptGap.cap i)
  · filter_upwards [hprefix,eventually_ge_atTop (4:ℕ)] with m hp hm E
    filter_upwards [hcommon m E] with p hused
    exact LiteralRankIC.source_rank_identity_on_usedSet i hm (G m E:Measure (ℝ × ℝ))
      (h05.value_marginal m E) (hatom m E) (g m E) (hp E).2.1
      (cm m E) (ReceiptGap.cap i) (hcommon m E) p hused
  · filter_upwards [hprefix,eventually_ge_atTop (4:ℕ)] with m hp hm E
    exact LiteralPureBid.source_exists_monotone_pure_bid i hm
      (G m E:Measure (ℝ × ℝ)) (h05.value_marginal m E) (hatom m E)
      (g m E) (hp E).2.1 (cm m E) (ReceiptGap.cap_bounds i).1.le
      (h05.permitted m E) (h05.all_action_IC m E)

end Family
end FCAppendix.Affine.Uniform06.SourceRankOutput
