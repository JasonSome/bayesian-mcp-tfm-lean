import FCAppendix.Affine.Tail04.NativePolicyFactor
import FCAppendix.Affine.Hybrid.ClassifiedReceipts

noncomputable section
namespace FCAppendix.Affine.Tail04.NativePosteriorIntegration
open MeasureTheory ProbabilityTheory Set Classical Filter Game Bayes
open NativeLocalPolicy Hybrid

local instance (α : Type*) : TopologicalSpace (Finset α) := ⊥
local instance (α : Type*) : DiscreteTopology (Finset α) := ⟨rfl⟩
local instance (α : Type*) : MeasurableSpace (Finset α) := ⊤
local instance (α : Type*) : BorelSpace (Finset α) := ⟨borel_eq_top_of_discrete.symm⟩

lemma first_seed_integral (j : Fin 2) (f : unitInterval → ℝ) (hf : Measurable f) :
    (∫ s : Fin 2 → Seed,f (s j).1 ∂Measure.pi (fun _ : Fin 2 => seedLaw))=
      ∫ u : unitInterval,f u ∂volume := by
  have hp := (measurePreserving_fst (μ:=(volume : Measure unitInterval))
    (ν:=(volume : Measure unitInterval))).comp
      (measurePreserving_eval (fun _ : Fin 2 => seedLaw) j)
  calc
    _=∫ u,f u ∂(Measure.pi (fun _ : Fin 2 => seedLaw)).map (fun s => (s j).1) :=
      (integral_map hp.measurable.aemeasurable hf.aestronglyMeasurable).symm
    _=_ := by erw [hp.map_eq]

lemma second_seed_integral (j : Fin 2) (f : unitInterval → ℝ) (hf : Measurable f) :
    (∫ s : Fin 2 → Seed,f (s j).2 ∂Measure.pi (fun _ : Fin 2 => seedLaw))=
      ∫ u : unitInterval,f u ∂volume := by
  have hp := (measurePreserving_snd (μ:=(volume : Measure unitInterval))
    (ν:=(volume : Measure unitInterval))).comp
      (measurePreserving_eval (fun _ : Fin 2 => seedLaw) j)
  calc
    _=∫ u,f u ∂(Measure.pi (fun _ : Fin 2 => seedLaw)).map (fun s => (s j).2) :=
      (integral_map hp.measurable.aemeasurable hf.aestronglyMeasurable).symm
    _=_ := by erw [hp.map_eq]

variable {m c : ℕ} (Γ : FiniteGame m 2 c Seed) (B : PosteriorSystem Γ)
  (hseed : Γ.seedLaw=seedLaw)

include hseed in
theorem sampler_posterior_mean {P Y α : Type*} [MeasurableSpace P]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [Fintype α] [DecidableEq α]
    (j : Fin 2) (L : LocalList m) (i : Fin m)
    (f : (P×Y) → unitInterval → Finset α)
    (hf : Measurable (Function.uncurry f)) (p : P)
    (row : UserProfile m 2 → Y) (hrow : Measurable row)
    (ρ : Measure Y) [IsProbabilityMeasure ρ]
    (hlaw : (B.posterior j L).map row=ρ) (a : α)
    (hfactor : ∀ᵐ d ∂B.posterior j L,∀ u : Seed,
      (i∈(Γ.policy (otherProposer j) (observe (drawsRealization d) (otherProposer j)) u).val ↔
        a∈f (p,row d) u.1)) :
    posteriorOtherMean Γ B j L i=LocalSamplerMean.mean f p ρ a := by
  rw [posteriorOtherMean_eq_profile_integral]
  have hinner : ∀ᵐ d ∂B.posterior j L,
      (∫ s : Fin 2 → Seed,((otherInclusionCount Γ j i (d,s)).val:ℝ)
        ∂Measure.pi (fun _ : Fin 2 => Γ.seedLaw))=
      ∫ u : unitInterval,if a∈f (p,row d) u then (1:ℝ) else 0 ∂volume := by
    filter_upwards [hfactor] with d hd
    have he (s : Fin 2 → Seed) : ((otherInclusionCount Γ j i (d,s)).val:ℝ)=
        if a∈f (p,row d) (s (otherProposer j)).1 then 1 else 0 := by
      rw [otherInclusionCount_two]
      simp only [allocation,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,hd]
    rw [integral_congr_ae (ae_of_all _ he),hseed]
    exact first_seed_integral (otherProposer j) _
      ((LocalSamplerMean.measurable_indicator f hf p a).comp (measurable_const.prodMk measurable_id))
  rw [integral_congr_ae hinner]
  have hm : Measurable (fun z : UserProfile m 2×unitInterval =>
      if a∈f (p,row z.1) z.2 then (1:ℝ) else 0) :=
    (LocalSamplerMean.measurable_indicator f hf p a).comp (hrow.prodMap measurable_id)
  have hi : Integrable (fun z : UserProfile m 2×unitInterval =>
      if a∈f (p,row z.1) z.2 then (1:ℝ) else 0) ((B.posterior j L).prod volume) :=
    Integrable.of_bound hm.aestronglyMeasurable 1
      (ae_of_all _ fun z => by split_ifs <;> norm_num)
  rw [←integral_prod _ hi]
  exact PrivateConditionalRows.sampler_mean_of_row_law f hf p (B.posterior j L)
    row hrow ρ hlaw a

include hseed in
theorem low_posterior_mean (D : Data m c) (j : Fin 2) (L : LocalList m) (i : Fin m)
    (hfactor : ∀ᵐ d ∂B.posterior j L,∀ u : Seed,
      (i∈(Γ.policy (otherProposer j) (observe (drawsRealization d) (otherProposer j)) u).val ↔
        i∈NativeExactLow.select D.ξ D.xi_pos D.xi_lt_one c (otherProposer j)
          (Observable.Regions.lowContext D.E j L) u.2)) :
    posteriorOtherMean Γ B j L i=
      NativeExactLow.acceptance D.ξ D.xi_pos D.xi_lt_one c (otherProposer j)
        (Observable.Regions.lowContext D.E j L) i := by
  let X := Observable.Regions.lowContext D.E j L
  let f : unitInterval → ℝ := fun u =>
    if i∈NativeExactLow.select D.ξ D.xi_pos D.xi_lt_one c (otherProposer j) X u then 1 else 0
  have hm : Measurable f := (measurable_of_countable (fun S : Finset (Fin m) =>
    if i∈S then (1:ℝ) else 0)).comp
      ((NativeExactLow.measurable_select D.ξ D.xi_pos D.xi_lt_one c (otherProposer j)).comp
        (measurable_const.prodMk measurable_id))
  rw [posteriorOtherMean_eq_profile_integral]
  have he : ∀ᵐ d ∂B.posterior j L,
      (∫ s : Fin 2 → Seed,((otherInclusionCount Γ j i (d,s)).val:ℝ)
        ∂Measure.pi (fun _ : Fin 2 => Γ.seedLaw))=∫ u,f u ∂volume := by
    filter_upwards [hfactor] with d hd
    have hs (s : Fin 2 → Seed) : ((otherInclusionCount Γ j i (d,s)).val:ℝ)=
        f (s (otherProposer j)).2 := by
      rw [otherInclusionCount_two]
      simp only [f,X,allocation,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,hd]
    rw [integral_congr_ae (ae_of_all _ hs),hseed]
    exact second_seed_integral (otherProposer j) f hm
  rw [integral_congr_ae he]
  simp [NativeExactLow.acceptance,f,X]

theorem private_posterior_mean (j : Fin 2) (L : LocalList m) (i : Fin m)
    (habsent : ∀ᵐ d ∂B.posterior j L,
      observe (drawsRealization d) (otherProposer j) i=none) :
    posteriorOtherMean Γ B j L i=0 := by
  rw [posteriorOtherMean_eq_profile_integral]
  apply integral_eq_zero_of_ae
  filter_upwards [habsent] with d hd
  apply integral_eq_zero_of_ae
  apply ae_of_all
  intro s
  have hn : i∉allocation (drawsRealization d) Γ.policy s (otherProposer j) := by
    intro hin
    exact (Γ.policy (otherProposer j) (observe (drawsRealization d) (otherProposer j))
      (s (otherProposer j))).property.2 i hin hd
  change ((otherInclusionCount Γ j i (d,s)).val:ℝ) = 0
  rw [otherInclusionCount_two,if_neg hn]
  norm_num

end FCAppendix.Affine.Tail04.NativePosteriorIntegration
