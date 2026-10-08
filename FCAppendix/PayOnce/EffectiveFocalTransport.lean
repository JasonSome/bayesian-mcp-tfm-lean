import FCAppendix.PayOnce.DummyInterimKernel

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set
open PayOnce.CompactifiedBidLaws
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem focalDraw_effectiveRivals_measurePreserving (Γ : FiniteGame m n c Seed) (i : Fin m) :
    MeasurePreserving (fun d : UserProfile m n => (d i,effectiveRivalBids i d))
      (userProfileLaw Γ) ((userLaw Γ).prod
        (Measure.pi fun _ : Rival i => (PayOnce.BidScaling.realBidLaw Γ : Measure ℝ))) := by
  have hM : Measurable (fun d : UserProfile m n => (d i,effectiveRivalBids i d)) :=
    (measurable_pi_apply i).prodMk (measurable_effectiveRivalBids i)
  refine ⟨hM,?_⟩
  have hu : userProfileLaw Γ =
      ((userLaw Γ).prod (userProfileLaw Γ)).map (fun z : UserDraw n × UserProfile m n => Function.update z.2 i z.1) :=
    (Resample.map_update_eq (userLaw Γ) i).symm
  conv_lhs => rw [hu,Measure.map_map hM (Resample.measurable_update_pair i)]
  have he : (fun d : UserProfile m n => (d i,effectiveRivalBids i d)) ∘
      (fun z : UserDraw n × UserProfile m n => Function.update z.2 i z.1) =
      fun z : UserDraw n × UserProfile m n => (z.1,effectiveRivalBids i z.2) := by
    funext z
    simp only [Function.comp_apply,Function.update_self]
    congr 1
    funext j
    exact congrArg (fun d : UserDraw n => effectiveBid d.1.2) (Function.update_of_ne j.property z.1 z.2)
  rw [he]
  exact ((MeasurePreserving.id (userLaw Γ)).prod (effectiveRivalBids_measurePreserving Γ i)).map_eq

theorem focalAction_effectiveRivals_measurePreserving (Γ : FiniteGame m n c Seed) (i : Fin m) :
    MeasurePreserving (fun d : UserProfile m n => ((d i).1,effectiveRivalBids i d))
      (userProfileLaw Γ) ((Γ.F ⊗ₘ Γ.σ).prod
        (Measure.pi fun _ : Rival i => (PayOnce.BidScaling.realBidLaw Γ : Measure ℝ))) :=
  ((measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ) (ν := permLaw n)).prod
    (MeasurePreserving.id _)).comp (focalDraw_effectiveRivals_measurePreserving Γ i)

theorem effectiveFocalBid_rivals_measurePreserving (Γ : FiniteGame m n c Seed) (i : Fin m) :
    MeasurePreserving (fun d : UserProfile m n => (effectiveBid (d i).1.2,effectiveRivalBids i d))
      (userProfileLaw Γ) ((PayOnce.BidScaling.realBidLaw Γ : Measure ℝ).prod
        (Measure.pi fun _ : Rival i => (PayOnce.BidScaling.realBidLaw Γ : Measure ℝ))) := by
  have hbid : MeasurePreserving (fun x : ℝ × JointAction n => effectiveBid x.2)
      (Γ.F ⊗ₘ Γ.σ) (PayOnce.BidScaling.realBidLaw Γ : Measure ℝ) :=
    ⟨(measurable_effectiveBid n).comp measurable_snd,(realEffectiveBidLaw_eq_action_map Γ).symm⟩
  exact (hbid.prod (MeasurePreserving.id _)).comp (focalAction_effectiveRivals_measurePreserving Γ i)

end FCAppendix.Bayes
