import FCAppendix.Affine.Tail04.TypicalCountLaws
import FCAppendix.Affine.Tail04.LocalSamplerMean
import FCAppendix.Affine.Tail04.EmpiricalStatistics

noncomputable section
namespace FCAppendix.Affine.Tail04
open MeasureTheory Set Classical
open scoped BigOperators

section FiniteProduct
variable {X Y A B : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [Fintype A] [Fintype B] [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSingletonClass A] [MeasurableSingletonClass B]

theorem original_finiteLaw_product (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : X → A) (g : Y → B) (hf : Measurable f) (hg : Measurable g) :
    FiniteLaw.ofMeasure (μ.prod ν) (Prod.map f g) (hf.prodMap hg) =
      (FiniteLaw.ofMeasure μ f hf).prod (FiniteLaw.ofMeasure ν g hg) := by
  apply FiniteLaw.ext
  rintro ⟨a,b⟩
  rw [FiniteLaw.ofMeasure_mass]
  have he : {z : X × Y | Prod.map f g z=(a,b)} =
      {x | f x=a} ×ˢ {y | g y=b} := by
    ext z
    simp [Prod.ext_iff]
  rw [he,Measure.prod_prod,ENNReal.toReal_mul]
  change _ = (FiniteLaw.ofMeasure μ f hf).mass a *
    (FiniteLaw.ofMeasure ν g hg).mass b
  rw [FiniteLaw.ofMeasure_mass,FiniteLaw.ofMeasure_mass]

end FiniteProduct

section OriginalLocal
variable {P X α : Type*} [MeasurableSpace P] [MeasurableSpace X]
  [Fintype α] [DecidableEq α]
local instance : MeasurableSpace (Finset α) := ⊤

def localAccept (f : (P × X) → unitInterval → Finset α) (p : P) (i : α)
    (z : X × unitInterval) : Bool := decide (i ∈ f (p,z.1) z.2)

theorem measurable_localAccept (f : (P × X) → unitInterval → Finset α)
    (hf : Measurable (Function.uncurry f)) (p : P) (i : α) :
    Measurable (localAccept f p i) :=
  (measurable_of_countable (fun S : Finset α => decide (i ∈ S))).comp
    (hf.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd))

def originalAcceptanceLaw (f : (P × X) → unitInterval → Finset α)
    (hf : Measurable (Function.uncurry f)) (p : P)
    (θ : Measure X) [IsProbabilityMeasure θ] (i : α) : FiniteLaw Bool :=
  FiniteLaw.ofMeasure (θ.prod volume) (localAccept f p i)
    (measurable_localAccept f hf p i)

theorem originalAcceptanceLaw_eq (f : (P × X) → unitInterval → Finset α)
    (hf : Measurable (Function.uncurry f)) (p : P)
    (θ : Measure X) [IsProbabilityMeasure θ] (i : α) :
    originalAcceptanceLaw f hf p θ i =
      IndependentCounts.bernoulli (LocalSamplerMean.mean f p θ i)
        (LocalSamplerMean.bounds f hf p θ i).1 (LocalSamplerMean.bounds f hf p θ i).2 := by
  let K := originalAcceptanceLaw f hf p θ i
  have ht : K.mass true=LocalSamplerMean.mean f p θ i := by
    rw [← FiniteLaw.expect_singleton K true]
    change (originalAcceptanceLaw f hf p θ i).expect (fun z => if z = true then 1 else 0) = _
    rw [originalAcceptanceLaw, FiniteLaw.expect_ofMeasure]
    simp only [localAccept,decide_eq_true_eq,LocalSamplerMean.mean]
  have hs : K.mass false + K.mass true = 1 := by
    simpa only [Fintype.sum_bool, add_comm] using K.total
  apply FiniteLaw.ext
  intro z
  cases z
  · change K.mass false=1-LocalSamplerMean.mean f p θ i
    linarith
  · exact ht

end OriginalLocal

section OriginalPair
variable {P X Y α β : Type*} [MeasurableSpace P]
  [MeasurableSpace X] [MeasurableSpace Y] [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]
local instance : MeasurableSpace (Finset α) := ⊤
local instance : MeasurableSpace (Finset β) := ⊤

def originalPairCount (f : (P × X) → unitInterval → Finset α)
    (g : (P × Y) → unitInterval → Finset β) (p : P) (i : α) (j : β)
    (z : (X × unitInterval) × (Y × unitInterval)) : Fin 3 :=
  boolPairCount (localAccept f p i z.1,localAccept g p j z.2)

theorem measurable_originalPairCount (f : (P × X) → unitInterval → Finset α)
    (g : (P × Y) → unitInterval → Finset β)
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (p : P) (i : α) (j : β) : Measurable (originalPairCount f g p i j) :=
  (measurable_of_countable boolPairCount).comp
    ((measurable_localAccept f hf p i).prodMap (measurable_localAccept g hg p j))

def originalIndependentCountLaw (f : (P × X) → unitInterval → Finset α)
    (g : (P × Y) → unitInterval → Finset β)
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (p : P) (θ0 : Measure X) (θ1 : Measure Y)
    [IsProbabilityMeasure θ0] [IsProbabilityMeasure θ1] (i : α) (j : β) : CountLaw 2 :=
  FiniteLaw.ofMeasure ((θ0.prod volume).prod (θ1.prod volume))
    (originalPairCount f g p i j) (measurable_originalPairCount f g hf hg p i j)

theorem originalIndependentCountLaw_eq (f : (P × X) → unitInterval → Finset α)
    (g : (P × Y) → unitInterval → Finset β)
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (p : P) (θ0 : Measure X) (θ1 : Measure Y)
    [IsProbabilityMeasure θ0] [IsProbabilityMeasure θ1] (i : α) (j : β) :
    originalIndependentCountLaw f g hf hg p θ0 θ1 i j =
      twoCoinCountLaw (LocalSamplerMean.mean f p θ0 i) (LocalSamplerMean.mean g p θ1 j)
        (LocalSamplerMean.bounds f hf p θ0 i).1 (LocalSamplerMean.bounds f hf p θ0 i).2
        (LocalSamplerMean.bounds g hg p θ1 j).1 (LocalSamplerMean.bounds g hg p θ1 j).2 := by
  have he : originalIndependentCountLaw f g hf hg p θ0 θ1 i j =
      ((originalAcceptanceLaw f hf p θ0 i).prod
        (originalAcceptanceLaw g hg p θ1 j)).map boolPairCount := by
    unfold originalAcceptanceLaw
    rw [← original_finiteLaw_product (θ0.prod volume) (θ1.prod volume)
      (localAccept f p i) (localAccept g p j)
      (measurable_localAccept f hf p i) (measurable_localAccept g hg p j)]
    rw [FiniteLaw.ofMeasure_map _ _ _ boolPairCount (measurable_of_countable _)]
    rfl
  rw [he,originalAcceptanceLaw_eq,originalAcceptanceLaw_eq]
  rfl

end OriginalPair

section CommonBranch
variable {X A : Type*} [MeasurableSpace X] [Fintype A]
  [MeasurableSpace A] [MeasurableSingletonClass A]

def strictBranchFlag (w u : unitInterval) : Bool := if u< w then true else false

theorem measurable_strictBranchFlag (w : unitInterval) : Measurable (strictBranchFlag w) := by
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
    measurable_const measurable_const

theorem strictBranchFlag_law (w : unitInterval) :
    FiniteLaw.ofMeasure (volume : Measure unitInterval) (strictBranchFlag w)
      (measurable_strictBranchFlag w) =
      IndependentCounts.bernoulli (w:ℝ) w.property.1 w.property.2 := by
  rw [← Empirical.uniform_flag_law w]
  apply FiniteLaw.ofMeasure_congr_ae
  have hn : ∀ᵐ u : unitInterval ∂volume, u≠w := by
    rw [ae_iff]
    simp
  filter_upwards [hn] with u hu
  by_cases h : u< w
  · simp [strictBranchFlag,Empirical.flag,h,le_of_lt h]
  · have hle : ¬u≤ w := fun hl => h (lt_of_le_of_ne hl hu)
    simp [strictBranchFlag,Empirical.flag,h,hle]

def seededBranchOutcome (w : unitInterval) (typical fallback : X → A)
    (z : unitInterval × X) : A := if z.1< w then typical z.2 else fallback z.2

omit [Fintype A] [MeasurableSingletonClass A] in
theorem measurable_seededBranchOutcome (w : unitInterval) (typical fallback : X → A)
    (ht : Measurable typical) (ha : Measurable fallback) :
    Measurable (seededBranchOutcome w typical fallback) :=
  Measurable.ite (measurableSet_lt measurable_fst measurable_const)
    (ht.comp measurable_snd) (ha.comp measurable_snd)

theorem original_sharedBranch_law (μ : Measure X) [IsProbabilityMeasure μ]
    (w : unitInterval) (typical fallback : X → A)
    (ht : Measurable typical) (ha : Measurable fallback) :
    FiniteLaw.ofMeasure ((volume : Measure unitInterval).prod μ)
      (seededBranchOutcome w typical fallback)
      (measurable_seededBranchOutcome w typical fallback ht ha) =
      FiniteLaw.mixture (FiniteLaw.ofMeasure μ typical ht) (FiniteLaw.ofMeasure μ fallback ha)
        (w:ℝ) w.property.1 w.property.2 := by
  let pair : X → A × A := fun x => (typical x,fallback x)
  have hpair : Measurable pair := ht.prodMk ha
  let pick : Bool × (A × A) → A := fun z => if z.1 then z.2.1 else z.2.2
  have hpick : Measurable pick := measurable_of_countable pick
  have he : FiniteLaw.ofMeasure ((volume : Measure unitInterval).prod μ)
      (seededBranchOutcome w typical fallback)
      (measurable_seededBranchOutcome w typical fallback ht ha) =
      ((FiniteLaw.ofMeasure volume (strictBranchFlag w) (measurable_strictBranchFlag w)).prod
        (FiniteLaw.ofMeasure μ pair hpair)).map pick := by
    rw [← original_finiteLaw_product volume μ (strictBranchFlag w) pair
      (measurable_strictBranchFlag w) hpair,
      FiniteLaw.ofMeasure_map _ _ _ pick hpick]
    apply FiniteLaw.ofMeasure_congr_ae
    exact ae_of_all _ fun z => by
      simp [seededBranchOutcome,strictBranchFlag,pick,pair]
  rw [he,strictBranchFlag_law]
  apply FiniteLaw.ext_expect
  intro f
  rw [FiniteLaw.expect_map,FiniteLaw.expect_prod,IndependentCounts.expect_bernoulli,
    FiniteLaw.expect_mixture]
  simp only [pick,Bool.false_eq_true,ite_false,ite_true]
  simp only [FiniteLaw.expect_ofMeasure,pair]
  ring

end CommonBranch
end FCAppendix.Affine.Tail04
