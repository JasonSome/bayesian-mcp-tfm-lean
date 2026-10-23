import FCAppendix.CommonReserve.AnonymousRoutedSource
import FCAppendix.CommonReserve.BidTightness

noncomputable section
namespace FCAppendix.CommonReserve
open Game MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ProbabilityTheory

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def anonymousRoutedIndicator (Γ : Bayes.FiniteGame m n c Seed) (i : Fin m) (j : Fin n)
    (a : JointAction n) (τ : Equiv.Perm (Fin n)) (ω : Bayes.Background m n Seed) : ℝ :=
  if i ∈ Game.allocation (Bayes.deviated i a (ω, τ)) Γ.policy ω.2 j then 1 else 0

theorem measurable_anonymousRoutedIndicator (Γ : Bayes.FiniteGame m n c Seed)
    (i : Fin m) (j : Fin n) (a : JointAction n) (τ : Equiv.Perm (Fin n)) :
    Measurable (anonymousRoutedIndicator Γ i j a τ) := by
  classical
  have hm := (Bayes.measurable_allocation_deviated Γ i a j).comp
    (measurable_id.prodMk (measurable_const (a := τ)))
  exact Measurable.ite
    (hm (MeasurableSet.of_discrete : MeasurableSet {S : Finset (Fin m) | i ∈ S}))
    measurable_const measurable_const

theorem integrable_anonymousRoutedIndicator (Γ : Bayes.FiniteGame m n c Seed)
    (i : Fin m) (j : Fin n) (a : JointAction n) (τ : Equiv.Perm (Fin n)) :
    Integrable (anonymousRoutedIndicator Γ i j a τ) (Bayes.backgroundLaw Γ) := by
  apply Integrable.of_bound (measurable_anonymousRoutedIndicator Γ i j a τ).aestronglyMeasurable 1
  exact Eventually.of_forall fun ω => by
    unfold anonymousRoutedIndicator
    split <;> norm_num

theorem integral_routed_focalIndicator_seed (Γ : Bayes.FiniteGame m n c Seed)
    (r : ℝ) (hr : 0 ≤ r) (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (d : Fin m → Bayes.UserDraw n) (i : Fin m) (j : Fin n) (a : JointAction n)
    (τ : Equiv.Perm (Fin n)) :
    (∫ s, (routedSource Γ r hr).focalIndicator i j (routedAction r ((0, a), τ))
      (routedSample r (d, s)) ∂(Measure.pi fun _ : Fin n => Γ.seedLaw)) =
      ∫ s, anonymousRoutedIndicator Γ i j a τ (d, s)
        ∂(Measure.pi fun _ : Fin n => Γ.seedLaw) := by
  classical
  let L : Fin n → LocalList m := fun l =>
    Game.observe (Game.deviate (Bayes.drawsRealization d) i a.bid a.bid_nonneg
      (firstK τ a.routeCount)) l
  let H : (Fin n → Finset (Fin m)) → ℝ := fun S => if i ∈ S j then 1 else 0
  have hH : Measurable H := measurable_of_countable _
  have he (s : Fin n → Seed) :
      (routedSource Γ r hr).focalIndicator i j (routedAction r ((0, a), τ))
        (routedSample r (d, s)) =
        H (Bayes.selectionVector Γ (fun l => reserveList (L l) r) s) := by
    change (if i ∈ (Γ.policy j
      (observe (FiniteGame.deviated i (routedAction r ((0, a), τ))
        (routedSample r (d, s))) j) (s j)).val then (1 : ℝ) else 0) = _
    rw [observe_routed_deviated]
    rfl
  simp_rw [he]
  calc
    _ = ∫ S, H S ∂(Measure.pi fun _ : Fin n => Γ.seedLaw).map
        (Bayes.selectionVector Γ (fun l => reserveList (L l) r)) :=
      (integral_map_of_stronglyMeasurable
        (Bayes.measurable_selectionVector Γ _) hH.stronglyMeasurable).symm
    _ = ∫ S, H S ∂(Measure.pi fun _ : Fin n => Γ.seedLaw).map
        (Bayes.selectionVector Γ L) := by
      rw [selectionVector_map_reserveList Γ r hr hT L (fun l => anonymous_list_nonneg _ l)]
    _ = _ := integral_map_of_stronglyMeasurable
      (Bayes.measurable_selectionVector Γ L) hH.stronglyMeasurable

theorem integral_routed_focalIndicator_eq_anonymous (Γ : Bayes.FiniteGame m n c Seed)
    (r : ℝ) (hr : 0 ≤ r) (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (i : Fin m) (j : Fin n) (a : JointAction n) (τ : Equiv.Perm (Fin n)) :
    (∫ ω, (routedSource Γ r hr).focalIndicator i j (routedAction r ((0, a), τ)) ω
      ∂(routedSource Γ r hr).sampleLaw) =
      ∫ ω, anonymousRoutedIndicator Γ i j a τ ω ∂Bayes.backgroundLaw Γ := by
  let Γ' := routedSource Γ r hr
  let a' := routedAction r ((0, a), τ)
  have hp := routedSample_measurePreserving Γ r hr
  have hm : Measurable (Γ'.focalIndicator i j a') :=
    Measurable.of_uncurry_left (f := Γ'.focalIndicator i j) (x := a')
      (Γ'.measurable_focalIndicator_joint i j)
  have hi : Integrable (fun ω => Γ'.focalIndicator i j a' (routedSample r ω))
      (Bayes.backgroundLaw Γ) := by
    apply Integrable.of_bound (hm.comp hp.measurable).aestronglyMeasurable 1
    exact Eventually.of_forall fun ω => by
      simp only [Function.comp_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg (Γ'.focalIndicator_nonneg i j a' _)]
      exact Γ'.focalIndicator_le_one i j a' _
  calc
    _ = ∫ ω, Γ'.focalIndicator i j a' (routedSample r ω) ∂Bayes.backgroundLaw Γ := by
      calc
        _ = ∫ ω, Γ'.focalIndicator i j a' ω
            ∂(Bayes.backgroundLaw Γ).map (routedSample r) := by rw [hp.map_eq]
        _ = _ := integral_map_of_stronglyMeasurable hp.measurable hm.stronglyMeasurable
    _ = _ := by
      rw [show Bayes.backgroundLaw Γ =
          (Measure.pi fun _ : Fin m => Bayes.userLaw Γ).prod
            (Measure.pi fun _ : Fin n => Γ.seedLaw) from rfl,
        integral_prod _ hi, integral_prod _ (integrable_anonymousRoutedIndicator Γ i j a τ)]
      apply integral_congr_ae
      exact Eventually.of_forall fun d =>
        integral_routed_focalIndicator_seed Γ r hr hT d i j a τ

theorem anonymous_ae_positive_routed_acceptance (Γ : Bayes.FiniteGame m n c Seed)
    (r : ℝ) (hr : 0 ≤ r) (hc : 0 < c)
    (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r) (i : Fin m) :
    ∀ᵐ d ∂Bayes.userLaw Γ, ∀ j, r ≤ d.1.2.bid →
      j ∈ firstK d.2 d.1.2.routeCount → 0 < d.1.2.bid →
      0 < ∫ ω, anonymousRoutedIndicator Γ i j d.1.2 d.2 ω ∂Bayes.backgroundLaw Γ := by
  let Γ' := routedSource Γ r hr
  have hp : MeasurePreserving (routedDraw r) (Bayes.userLaw Γ) Γ'.userLaw :=
    ⟨measurable_routedDraw r, (routedSource_userLaw Γ r hr).symm⟩
  have ha := hp.quasiMeasurePreserving.ae
    (Γ'.ae_positive_coordinate_acceptance hc hT i)
  filter_upwards [ha] with d hd j hb hj hpos
  have hb' : 0 < Bayes.entryBid ((routedAction r d).val j) := by
    simp [routedAction, hb, hj, Bayes.entryBid, hpos]
  have hh := hd j hb'
  change 0 < ∫ ω, Γ'.focalIndicator i j (routedAction r ((0, d.1.2), d.2)) ω
    ∂Γ'.sampleLaw at hh
  rw [integral_routed_focalIndicator_eq_anonymous Γ r hr hT i j d.1.2 d.2] at hh
  exact hh

end FCAppendix.CommonReserve
