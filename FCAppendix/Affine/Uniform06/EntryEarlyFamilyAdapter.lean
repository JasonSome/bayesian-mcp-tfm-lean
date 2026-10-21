import FCAppendix.Affine.Uniform06.EntryCommonCarrier
import FCAppendix.Affine.Uniform06.EntryFullDominance

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryEarlyFamilyAdapter

open MeasureTheory ProbabilityTheory Set Filter Topology LowBody
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.ClippedResidual
open SourceEarlyFamily SourcePrefixConstructor EntryConstructedSource
open EntryEarlySourceLimits EntryFiniteConstructor EntryFullRestoration
open LiteralExperiment

variable {C : ℕ → Type*}
  (G : ∀ m,C m → ProbabilityMeasure (ℝ × ℝ))
  (g : ∀ m,C m → GuardData)
  (cm : ∀ m,C m → (Fin (m-1) → Fin 4) → ℝ)

structure RootFields (i : Row) : Prop where
  literal : ∀ m (E : C m),LiteralFields i (g m E)
  positive : ∀ m (E : C m),0<(g m E).multiplier
  clearing : ∀ m (E : C m),
    (∫ p,exposure (xi i) (g m E).multiplier p.2 ∂(G m E:Measure (ℝ × ℝ)))=
      PrefixRoot.requiredDemand i
  rejection : ∀ m (E : C m),
    (∫ p,PrefixRoot.sourcePsi i (g m E).rejectionRoot p.2 ∂(G m E:Measure (ℝ × ℝ)))=
      3*PrefixRoot.requiredDemand i
  population : ∀ m (E : C m),(g m E).population=(m:ℝ)
  margin : ∀ m (E : C m),(g m E).margin≤ epsilon i

def arrayLaw (n : ℕ → ℕ) (E : ∀ j,C (n j)) : Measure EntryCommonCarrier.Space :=
  EntryCommonCarrier.commonLaw (fun j => G (n j) (E j))
    ((G (n 0) (E 0):Measure (ℝ × ℝ)).map Prod.fst)

instance arrayLaw_probability (n : ℕ → ℕ) (E : ∀ j,C (n j)) :
    IsProbabilityMeasure (arrayLaw G n E) := by
  letI : IsProbabilityMeasure ((G (n 0) (E 0):Measure (ℝ × ℝ)).map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  unfold arrayLaw
  infer_instance

theorem arrayLaw_pair (i : Row) (h05 : EarlyMenuFields G g cm i)
    (n : ℕ → ℕ) (E : ∀ j,C (n j)) (j : ℕ) :
    (arrayLaw G n E).map
      (fun ω : EntryCommonCarrier.Space => (ω.1,ω.2 (j+1)))=
        (G (n j) (E j):Measure (ℝ × ℝ)) := by
  letI : IsProbabilityMeasure ((G (n 0) (E 0):Measure (ℝ × ℝ)).map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  exact EntryCommonCarrier.commonLaw_pair (fun j => G (n j) (E j)) _
    (fun j => (h05.value_marginal (n j) (E j)).trans
      (h05.value_marginal (n 0) (E 0)).symm) j

theorem pair_preserving (i : Row) (h05 : EarlyMenuFields G g cm i)
    (n : ℕ → ℕ) (E : ∀ j,C (n j)) (j : ℕ) :
    MeasurePreserving (fun ω : EntryCommonCarrier.Space => (ω.1,ω.2 (j+1)))
      (arrayLaw G n E) (G (n j) (E j):Measure (ℝ × ℝ)) :=
  ⟨measurable_fst.prodMk ((measurable_pi_apply _).comp measurable_snd),
    arrayLaw_pair G g cm i h05 n E j⟩

theorem common_all_action_IC (i : Row) (h05 : EarlyMenuFields G g cm i)
    (n : ℕ → ℕ) (E : ∀ j,C (n j)) :
    ∀ᵐ ω ∂arrayLaw G n E,∀ j : ℕ,
      ω.2 (j+1)∈Icc (LowChernoff.physicalFloor i ω.1) (min ω.1 (ReceiptGap.cap i)) ∧
      ∀ b∈Icc (LowChernoff.physicalFloor i ω.1) (min ω.1 (ReceiptGap.cap i)),
        Rank.payoff (eta i) ω.1 b
          (LiteralExperiment.sourceSuccess i (n j) (G (n j) (E j)) (g (n j) (E j)) (cm (n j) (E j)) b)
          (LiteralExperiment.sourceDuplicate i (n j) (G (n j) (E j)) (g (n j) (E j)) (cm (n j) (E j)) b) ≤
        Rank.payoff (eta i) ω.1 (ω.2 (j+1))
          (LiteralExperiment.sourceSuccess i (n j) (G (n j) (E j)) (g (n j) (E j)) (cm (n j) (E j)) (ω.2 (j+1)))
          (LiteralExperiment.sourceDuplicate i (n j) (G (n j) (E j)) (g (n j) (E j)) (cm (n j) (E j)) (ω.2 (j+1))) := by
  apply ae_all_iff.mpr
  intro j
  exact (pair_preserving G g cm i h05 n E j).quasiMeasurePreserving.ae
    ((h05.permitted (n j) (E j)).and (h05.all_action_IC (n j) (E j)))

def from_family (i : Row) (h05 : EarlyMenuFields G g cm i) (hr : RootFields G g i)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (E : ∀ j,C (n j)) :
    EarlyArray (arrayLaw G n E) i := by
  let μ := arrayLaw G n E
  let V : EntryCommonCarrier.Space → ℝ := Prod.fst
  let B : ℕ → EntryCommonCarrier.Space → ℝ := fun j ω => ω.2 (j+1)
  have hV : Measurable V := measurable_fst
  have hB (j : ℕ) : Measurable (B j) := (measurable_pi_apply _).comp measurable_snd
  have hpair (j : ℕ) : MeasurePreserving (fun ω => (V ω,B j ω)) μ
      (G (n j) (E j):Measure (ℝ × ℝ)) := pair_preserving G g cm i h05 n E j
  have hmenu (j : ℕ) : ∀ᵐ ω ∂μ,
      B j ω∈Icc (LowChernoff.physicalFloor i (V ω)) (min (V ω) (ReceiptGap.cap i)) :=
    (hpair j).quasiMeasurePreserving.ae (h05.permitted (n j) (E j))
  have hvalue : μ.map V=LowChernoff.conditionalValueLaw i := by
    have hh := congrArg (fun ν : Measure (ℝ × ℝ) => ν.map Prod.fst) (hpair 0).map_eq
    rw [Measure.map_map measurable_fst (hV.prodMk (hB 0))] at hh
    exact hh.trans (h05.value_marginal (n 0) (E 0))
  have hactive : ∀ a>(0:ℝ),∀ e>(0:ℝ),∀ᶠ j in atTop,∀ᵐ ω ∂μ,
      V ω∈Icc (entry i+a) (cutoff i) →
        |B j ω-ActiveGraphComponent.activeBid i (V ω)|< e := by
    intro a ha e he
    have hh := hn.eventually (source_early_active_closed G g cm i h05 a ha e he)
    filter_upwards [hh] with j hj
    exact (hpair j).quasiMeasurePreserving.ae (hj (E j))
  have hL : Tendsto (fun j => (g (n j) (E j)).multiplier) atTop (𝓝 (entry i)) := by
    apply Metric.tendsto_atTop.mpr
    intro e he
    have hh := hn.eventually (h05.root_limit e he)
    obtain ⟨J,hJ⟩ := eventually_atTop.mp hh
    exact ⟨J,fun j hj => by simpa only [Real.dist_eq] using hJ j hj (E j)⟩
  refine {
    value := V
    bid := B
    value_measurable := hV
    bid_measurable := hB
    value_law := hvalue
    admissible := fun j => (hmenu j).mono fun ω hh => hh.2.trans (min_le_left _ _)
    nonnegative := fun j => (hmenu j).mono fun ω hh => ?_
    bid_cap := fun j => (hmenu j).mono fun ω hh => hh.2.trans (min_le_right _ _)
    active_closed := hactive
    guards := fun j => g (n j) (E j)
    literal := fun j => hr.literal (n j) (E j)
    multiplier_pos := fun j => hr.positive (n j) (E j)
    multiplier_tendsto := hL
    root_equation := fun j => ?_
    rejection_equation := fun j => ?_
    population := n
    population_tendsto := hn
    population_eq := fun j => hr.population (n j) (E j)
    margin_small := fun j => hr.margin (n j) (E j) }
  · have hf : 0≤ LowChernoff.physicalFloor i (V ω) := by
      unfold LowChernoff.physicalFloor
      positivity
    exact hf.trans hh.1
  · have hm : Measurable (fun p : ℝ × ℝ => exposure (xi i) (g (n j) (E j)).multiplier p.2) :=
      ((continuous_exposure (xi_pos i) (hr.positive (n j) (E j))).measurable.comp measurable_snd)
    have he := hr.clearing (n j) (E j)
    rw [← (hpair j).map_eq,integral_map (hV.prodMk (hB j)).aemeasurable hm.aestronglyMeasurable] at he
    exact he
  · have hm : Measurable (fun p : ℝ × ℝ => PrefixRoot.sourcePsi i (g (n j) (E j)).rejectionRoot p.2) := by
      unfold PrefixRoot.sourcePsi PrefixRoot.psi
      fun_prop
    have he := hr.rejection (n j) (E j)
    rw [← (hpair j).map_eq,integral_map (hV.prodMk (hB j)).aemeasurable hm.aestronglyMeasurable] at he
    exact he

theorem from_family_jointLaw (i : Row) (h05 : EarlyMenuFields G g cm i) (hr : RootFields G g i)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (E : ∀ j,C (n j)) (j : ℕ) :
    (from_family G g cm i h05 hr n hn E).jointLaw j=(G (n j) (E j):Measure (ℝ × ℝ)) :=
  arrayLaw_pair G g cm i h05 n E j

end FCAppendix.Affine.Uniform06.EntryEarlyFamilyAdapter
