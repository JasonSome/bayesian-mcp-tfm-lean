import FCAppendix.Affine.Tail04.NativePosteriorIntegration
import FCAppendix.Affine.Tail04.PosteriorReceiptNormalization

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeKernelIntegration
open MeasureTheory ProbabilityTheory Set Classical Filter Game Bayes
open NativeLocalPolicy NativePosteriorIntegration Hybrid
open PosteriorReceiptNormalization

local instance (α : Type*) : TopologicalSpace (Finset α) := ⊥
local instance (α : Type*) : DiscreteTopology (Finset α) := ⟨rfl⟩
local instance (α : Type*) : MeasurableSpace (Finset α) := ⊤
local instance (α : Type*) : BorelSpace (Finset α) := ⟨borel_eq_top_of_discrete.symm⟩

variable {m c : ℕ} (Γ : FiniteGame m 2 c Seed)
    (κ : Fin 2 → Kernel (LocalList m) (UserProfile m 2)) [∀ j,IsMarkovKernel (κ j)]

def otherMean (j : Fin 2) (L : LocalList m) (i : Fin m) : ℝ :=
  (countBelief Γ κ j L i).expect (fun r => (r.val:ℝ))

lemma otherMean_integral (j : Fin 2) (L : LocalList m) (i : Fin m) :
    otherMean Γ κ j L i=
      ∫ d,∫ s : Fin 2 → Seed,((otherInclusionCount Γ j i (d,s)).val:ℝ)
        ∂Measure.pi (fun _ : Fin 2 => Γ.seedLaw) ∂κ j L := by
  rw [otherMean,countBelief,FiniteLaw.expect_ofMeasure]
  apply integral_prod
  have hm : Measurable (fun ω : Background m 2 Seed => ((otherInclusionCount Γ j i ω).val:ℝ)) :=
    (measurable_of_countable (fun r : Fin 2 => (r.val:ℝ))).comp (measurable_otherInclusionCount Γ j i)
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  exact ae_of_all _ (fun ω => by
    rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast Nat.le_of_lt_succ (otherInclusionCount Γ j i ω).isLt)

variable (hseed : Γ.seedLaw=seedLaw)

include hseed in
theorem sampler_mean {P Y α : Type*} [MeasurableSpace P]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [Fintype α] [DecidableEq α]
    (j : Fin 2) (L : LocalList m) (i : Fin m)
    (f : (P×Y) → unitInterval → Finset α)
    (hf : Measurable (Function.uncurry f)) (p : P)
    (row : UserProfile m 2 → Y) (hrow : Measurable row)
    (ρ : Measure Y) [IsProbabilityMeasure ρ] (hlaw : (κ j L).map row=ρ) (a : α)
    (hfactor : ∀ᵐ d ∂κ j L,∀ u : Seed,
      (i∈(Γ.policy (otherProposer j) (observe (drawsRealization d) (otherProposer j)) u).val ↔
        a∈f (p,row d) u.1)) :
    otherMean Γ κ j L i=LocalSamplerMean.mean f p ρ a := by
  rw [otherMean_integral]
  have hinner : ∀ᵐ d ∂κ j L,
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
      if a∈f (p,row z.1) z.2 then (1:ℝ) else 0) ((κ j L).prod volume) :=
    Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun z => by split_ifs <;> norm_num)
  rw [←integral_prod _ hi]
  exact PrivateConditionalRows.sampler_mean_of_row_law f hf p (κ j L) row hrow ρ hlaw a

include hseed in
theorem low_mean (D : Data m c) (j : Fin 2) (L : LocalList m) (i : Fin m)
    (hfactor : ∀ᵐ d ∂κ j L,∀ u : Seed,
      (i∈(Γ.policy (otherProposer j) (observe (drawsRealization d) (otherProposer j)) u).val ↔
        i∈NativeExactLow.select D.ξ D.xi_pos D.xi_lt_one c (otherProposer j)
          (Observable.Regions.lowContext D.E j L) u.2)) :
    otherMean Γ κ j L i=
      NativeExactLow.acceptance D.ξ D.xi_pos D.xi_lt_one c (otherProposer j)
        (Observable.Regions.lowContext D.E j L) i := by
  let X := Observable.Regions.lowContext D.E j L
  let f : unitInterval → ℝ := fun u =>
    if i∈NativeExactLow.select D.ξ D.xi_pos D.xi_lt_one c (otherProposer j) X u then 1 else 0
  have hm : Measurable f := (measurable_of_countable (fun S : Finset (Fin m) =>
    if i∈S then (1:ℝ) else 0)).comp
      ((NativeExactLow.measurable_select D.ξ D.xi_pos D.xi_lt_one c (otherProposer j)).comp
        (measurable_const.prodMk measurable_id))
  rw [otherMean_integral]
  have he : ∀ᵐ d ∂κ j L,
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

theorem zero_mean (j : Fin 2) (L : LocalList m) (i : Fin m)
    (habsent : ∀ᵐ d ∂κ j L,∀ u : Seed,
      i∉(Γ.policy (otherProposer j) (observe (drawsRealization d) (otherProposer j)) u).val) :
    otherMean Γ κ j L i=0 := by
  rw [otherMean_integral]
  apply integral_eq_zero_of_ae
  filter_upwards [habsent] with d hd
  apply integral_eq_zero_of_ae
  apply ae_of_all
  intro s
  have hn : i∉allocation (drawsRealization d) Γ.policy s (otherProposer j) := hd _
  change ((otherInclusionCount Γ j i (d,s)).val:ℝ) = 0
  rw [otherInclusionCount_two,if_neg hn]
  norm_num

lemma affine_receipts (η : ℝ) (hη0 : 0≤ η) (hη1 : η≤1)
    (hA : Γ.A=Schedule.affine 2 η hη0 hη1)
    (j : Fin 2) (L : LocalList m) (i : Fin m) :
    receipts Γ κ j L i=entryBid (L i)*(1-(1-η)/2*otherMean Γ κ j L i) := by
  cases he : L i with
  | none => simp [receipts,beliefReceipts,he,entryBid]
  | some b =>
    simp only [receipts,beliefReceipts,he,entryBid]
    rw [hA,Finite.conditionalReceipt]
    let ν := countBelief Γ κ j L i
    have hh (r : Fin 2) :
        b*(Schedule.affine 2 η hη0 hη1).charge (r.val+1)/((r.val:ℝ)+1)=
          b*(1-(1-η)/2*(r.val:ℝ)) := by
      fin_cases r
      · simp [Schedule.affine,successIndicator]
      · simp [Schedule.affine,successIndicator];ring
    rw [ν.expect_congr hh,FiniteLaw.expect_const_mul,FiniteLaw.expect_sub,
      FiniteLaw.expect_const,FiniteLaw.expect_const_mul]
    rfl

end FCAppendix.Affine.Tail04.NativeKernelIntegration
