import FCAppendix.PayOnce.KernelAgreement

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set
open scoped ProbabilityTheory BigOperators
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem focalDraw_rivalBids_measurePreserving (Γ : FiniteGame m n c Seed) (i : Fin m) :
    MeasurePreserving (fun d : UserProfile m n => (d i, rivalBids i d))
      (userProfileLaw Γ) ((userLaw Γ).prod (analyticalRivalLaw Γ i)) := by
  have hM : Measurable (fun d : UserProfile m n => (d i, rivalBids i d)) :=
    (measurable_pi_apply i).prodMk (measurable_rivalBids i)
  refine ⟨hM, ?_⟩
  have hu : (userProfileLaw Γ) =
      ((userLaw Γ).prod (userProfileLaw Γ)).map (fun z : UserDraw n × UserProfile m n => Function.update z.2 i z.1) :=
    (Resample.map_update_eq (userLaw Γ) i).symm
  conv_lhs => rw [hu, Measure.map_map hM (Resample.measurable_update_pair i)]
  have he : (fun d : UserProfile m n => (d i, rivalBids i d)) ∘
      (fun z : UserDraw n × UserProfile m n => Function.update z.2 i z.1) =
      fun z : UserDraw n × UserProfile m n => (z.1, rivalBids i z.2) := by
    funext z
    simp only [Function.comp_apply, Function.update_self]
    congr 1
    funext j
    exact congrArg (fun d : UserDraw n => d.1.2.bid) (Function.update_of_ne j.property z.1 z.2)
  rw [he]
  have hp := (MeasurePreserving.id (userLaw Γ)).prod
    (show MeasurePreserving (rivalBids (n := n) i) (userProfileLaw Γ) (analyticalRivalLaw Γ i) from
      ⟨measurable_rivalBids i, rfl⟩)
  exact hp.map_eq

theorem focalAction_rivalBids_measurePreserving (Γ : FiniteGame m n c Seed) (i : Fin m) :
    MeasurePreserving (fun d : UserProfile m n => ((d i).1, rivalBids i d))
      (userProfileLaw Γ) ((Γ.F ⊗ₘ Γ.σ).prod (analyticalRivalLaw Γ i)) := by
  exact ((measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ) (ν := permLaw n)).prod
    (MeasurePreserving.id (analyticalRivalLaw Γ i))).comp (focalDraw_rivalBids_measurePreserving Γ i)

theorem integral_profile_statistic_eq_type_rivals (Γ : FiniteGame m n c Seed)
    (i : Fin m) (f : (ℝ × JointAction n) × (Rival i → ℝ) → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : ∀ z, ‖f z‖ ≤ C)
    (bid : ℝ → ℝ) (hpure : ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v, a = safeFullBid n (bid v)) :
    (∫ d, f ((d i).1, rivalBids i d) ∂userProfileLaw Γ) =
      ∫ v, ∫ rivals, f ((v, safeFullBid n (bid v)), rivals) ∂analyticalRivalLaw Γ i ∂Γ.F := by
  have hpres := focalAction_rivalBids_measurePreserving Γ i
  have hi : Integrable f ((Γ.F ⊗ₘ Γ.σ).prod (analyticalRivalLaw Γ i)) :=
    Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  calc
    _ = ∫ z, f z ∂((Γ.F ⊗ₘ Γ.σ).prod (analyticalRivalLaw Γ i)) := by
      rw [← hpres.map_eq]
      exact (integral_map hpres.measurable.aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫ x, ∫ rivals, f (x,rivals) ∂analyticalRivalLaw Γ i ∂(Γ.F ⊗ₘ Γ.σ) := integral_prod _ hi
    _ = ∫ v, ∫ a, ∫ rivals, f ((v,a),rivals) ∂analyticalRivalLaw Γ i ∂Γ.σ v ∂Γ.F :=
      Measure.integral_compProd hi.integral_prod_left
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hpure] with v hv
      have he : (fun a : JointAction n => ∫ rivals, f ((v,a),rivals) ∂analyticalRivalLaw Γ i) =ᵐ[Γ.σ v]
          fun _ => ∫ rivals, f ((v,safeFullBid n (bid v)),rivals) ∂analyticalRivalLaw Γ i := by
        filter_upwards [hv] with a ha
        rw [ha]
      rw [integral_congr_ae he]
      simp only [integral_const, probReal_univ, one_smul]

end FCAppendix.Bayes

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set
open scoped ProbabilityTheory BigOperators
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem focalBid_rivalBids_measurePreserving (Γ : FiniteGame m n c Seed) (i : Fin m) :
    MeasurePreserving (fun d : UserProfile m n => ((d i).1.2.bid, rivalBids i d))
      (userProfileLaw Γ) ((realBidLaw Γ).prod (Measure.pi fun _ : Rival i => realBidLaw Γ)) := by
  rw [← analyticalRivalLaw_eq_pi Γ i]
  have hbid : MeasurePreserving (fun x : ℝ × JointAction n => x.2.bid)
      (Γ.F ⊗ₘ Γ.σ) (realBidLaw Γ) :=
    ⟨(measurable_bid n).comp measurable_snd, (realBidLaw_eq_action_map Γ).symm⟩
  exact (hbid.prod (MeasurePreserving.id (analyticalRivalLaw Γ i))).comp
    (focalAction_rivalBids_measurePreserving Γ i)

end FCAppendix.Bayes
