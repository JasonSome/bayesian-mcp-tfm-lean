import FCAppendix.PayOnce.PopulationSampling
import FCAppendix.PayOnce.DummyCovarianceOrder

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Filter Topology Set Game
open PayOnce PayOnce.CovarianceConcentration PayOnce.CompactifiedBidLaws
open scoped BigOperators ProbabilityTheory

theorem integral_sampled_effective_statistic
    {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (f : ℝ × ℝ → ℝ) (hf : Measurable f) {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C)
    (bid : ℝ → ℝ) (hpure : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), effectiveBid x.2 = bid x.1) :
    (∫ z : UserProfile m n × Fin m, f ((z.1 z.2).1.1,effectiveBid (z.1 z.2).1.2)
      ∂populationLaw (userProfileLaw Γ)) = ∫ v, f (v,bid v) ∂Γ.F := by
  letI : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  let f0 : ℝ × JointAction n → ℝ := fun x => f (x.1,effectiveBid x.2)
  have hf0 : Measurable f0 := hf.comp (measurable_fst.prodMk ((measurable_effectiveBid n).comp measurable_snd))
  have hm' i : Measurable (fun d : UserProfile m n => f0 (d i).1) :=
    hf0.comp (measurable_fst.comp (measurable_pi_apply i))
  have hi i : Integrable (fun d : UserProfile m n => f0 (d i).1) (userProfileLaw Γ) :=
    Integrable.of_bound (hm' i).aestronglyMeasurable C (Eventually.of_forall fun d => hb _)
  have he i : (∫ d : UserProfile m n, f0 (d i).1 ∂userProfileLaw Γ) = ∫ v, f (v,bid v) ∂Γ.F := by
    have hpres : MeasurePreserving (fun d : UserProfile m n => (d i).1)
        (userProfileLaw Γ) (Γ.F ⊗ₘ Γ.σ) :=
      (measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ) (ν := permLaw n)).comp
        (measurePreserving_eval (fun _ : Fin m => userLaw Γ) i)
    have htransport : (∫ d : UserProfile m n, f0 (d i).1 ∂userProfileLaw Γ) =
        ∫ x, f0 x ∂(Γ.F ⊗ₘ Γ.σ) := by
      rw [← hpres.map_eq]
      exact (integral_map hpres.measurable.aemeasurable hf0.aestronglyMeasurable).symm
    rw [htransport,Measure.integral_compProd
      (Integrable.of_bound hf0.aestronglyMeasurable C (Eventually.of_forall fun x => hb _))]
    apply integral_congr_ae
    filter_upwards [Measure.ae_ae_of_ae_compProd hpure] with v hv
    have hh : (fun a : JointAction n => f0 (v,a)) =ᵐ[Γ.σ v] fun _ => f (v,bid v) := by
      filter_upwards [hv] with a ha
      change f (v,effectiveBid a) = _
      rw [ha]
    rw [integral_congr_ae hh]
    simp only [integral_const,probReal_univ,one_smul]
  change (∫ z : UserProfile m n × Fin m, f0 (z.1 z.2).1 ∂populationLaw (userProfileLaw Γ)) = _
  rw [integral_populationLaw (userProfileLaw Γ) (fun (d : UserProfile m n) (i : Fin m) => f0 (d i).1)
    (integrable_populationLaw_of_bound _ _ hm' (fun d i => hb _)),integral_populationMean (userProfileLaw Γ) (fun (d : UserProfile m n) (i : Fin m) => f0 (d i).1) hi]
  simp only [populationMean,he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hm.ne')

end FCAppendix.Bayes
