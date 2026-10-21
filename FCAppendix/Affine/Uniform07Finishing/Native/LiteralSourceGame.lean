import FCAppendix.Affine.Uniform07Finishing.Native.CompleteSourceGame
import FCAppendix.Affine.Uniform07Finishing.Native.SourceGuards

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Classical
open StrictNative
variable {m : ℕ} [Nonempty (Fin m)]

def literalSourceAlpha (i : Uniform07.Row) (Λ z width ε : ℝ) :
    ClassifiedContext m→ unitInterval :=
  Weighted.sourceGuardAlpha (Uniform07.xi i) Λ (Early.nativeRadius i) (Early.demandRatio i)
    (Early.bidCap i) (Uniform07.cutoff i/1000) z (Uniform07.cutoff i) width ε (Uniform07.capacity m)

lemma source_guard_root_positive (i : Uniform07.Row) {Λ : ℝ}
    (hΛ:(54/100:ℝ)*Uniform07.cutoff i<Λ) : 0<Λ-Early.nativeRadius i := by
  have hh:=((Early.native_sampling_margin_guards i).2 Λ hΛ).1
  have ht:=Uniform07.cutoff_pos i
  have hm:((52/100:ℝ)*Uniform07.cutoff i)<Λ-Early.nativeRadius i :=
    (le_max_right _ _).trans_lt hh
  linarith

omit [Nonempty (Fin m)] in
lemma measurable_literalSourceAlpha (i : Uniform07.Row) {Λ : ℝ}
    (hΛ:(54/100:ℝ)*Uniform07.cutoff i<Λ) (z width ε : ℝ) :
    Measurable (literalSourceAlpha (m:=m) i Λ z width ε) :=
  Weighted.measurable_sourceGuardAlpha (Uniform07.xi_pos i)
    (Early.native_sampling_margin_guards i).1 (source_guard_root_positive i hΛ)
    (div_pos (Uniform07.cutoff_pos i) (by norm_num : (0:ℝ)<1000)) (Early.demandRatio i)
    (Early.bidCap i) z (Uniform07.cutoff i) width ε (Uniform07.capacity m)

lemma source_guard_multiplier_positive (i : Uniform07.Row) {Λ : ℝ}
    (hΛ:(54/100:ℝ)*Uniform07.cutoff i<Λ) : 0<Λ :=
  lt_trans (mul_pos (by norm_num : (0:ℝ)<54/100) (Uniform07.cutoff_pos i)) hΛ

def literalSourceNativeGame (i : Uniform07.Row) (hc:1≤ Uniform07.capacity m)
    (R Λ z width ε : ℝ) (hΛ:(54/100:ℝ)*Uniform07.cutoff i<Λ)
    (PL : ProbabilityMeasure (ℝ×JointAction 2)) :
    FiniteGame m 2 (Uniform07.capacity m) unitInterval :=
  completeSourceNativeGame i hc R Λ (source_guard_multiplier_positive i hΛ) PL
    (literalSourceAlpha i Λ z width ε) (measurable_literalSourceAlpha i hΛ z width ε)

variable (i : Uniform07.Row) (hm:2≤ m) (hc:1≤ Uniform07.capacity m)
  {R Λ z width ε : ℝ} (hR:0< R) (hUR:Early.bidCap i< R) (hRt:R< Uniform07.cutoff i)
  (hΛ:(54/100:ℝ)*Uniform07.cutoff i<Λ)
  (PL : ProbabilityMeasure (ℝ×JointAction 2))
  (hLvalue:(PL : Measure (ℝ×JointAction 2)).map Prod.fst=(sourceLowerValueLaw i : Measure ℝ))
  (hLroute:∀ᵐx∂(PL : Measure (ℝ×JointAction 2)),x.2.bid≤ Early.bidCap i ∧ x.2.routeCount=2)

include hm hR hRt hLvalue hLroute in
theorem literalSourceNativeGame_joint_law :
    (literalSourceNativeGame i hc R Λ z width ε hΛ PL).F⊗ₘ
      (literalSourceNativeGame i hc R Λ z width ε hΛ PL).σ=
        (sourcePopulation i m hc R PL : Measure (ℝ×JointAction 2)) :=
  completeSourceNativeGame_joint_law i hc R Λ (source_guard_multiplier_positive i hΛ) PL
    (literalSourceAlpha i Λ z width ε) (measurable_literalSourceAlpha i hΛ z width ε)
    hm hR hRt hLvalue hLroute

include hm hR hUR hRt hLvalue hLroute in

theorem literalSourceNativeGame_proposers :
    ∃B : PosteriorSystem (literalSourceNativeGame i hc R Λ z width ε hΛ PL),
      PosteriorProposerOptimal (literalSourceNativeGame i hc R Λ z width ε hΛ PL) B :=
  completeSourceNativeGame_proposer_optimal i hc R Λ (source_guard_multiplier_positive i hΛ) PL
    (literalSourceAlpha i Λ z width ε) (measurable_literalSourceAlpha i hΛ z width ε)
    hm hR hUR hRt hLvalue hLroute

include hm hR hΛ in

theorem literalSourceNativeGame_guarded_plan
    (hroot:Uniform07.kappa i*R<Λ-Early.nativeRadius i) (hε:0<ε)
    (X : ClassifiedContext m) (hX:NonnegativeList X.1)
    (hbid:∀k,entryBid (X.1 k)≤ R) (E : Finset (Fin m))
    (hE:Weighted.sourcePlan (Uniform07.xi i) Λ (Early.demandRatio i) (Early.bidCap i)
      (Uniform07.cutoff i/2) (Uniform07.capacity m) (sourceSeedMeasure i m hc R PL)
        (literalSourceAlpha i Λ z width ε) X=some E) :
    Weighted.ValidExclusive (Uniform07.xi i) X.1
      (Weighted.budget (Uniform07.capacity m) 0 X) (Weighted.budget (Uniform07.capacity m) 1 X) E :=
  Weighted.literal_sourcePlan_valid i hΛ hR hroot (by omega) hε (Uniform07.capacity m)
    (sourceSeedMeasure i m hc R PL) X hX hbid E hE

end FCAppendix.Affine.Uniform07Finishing
