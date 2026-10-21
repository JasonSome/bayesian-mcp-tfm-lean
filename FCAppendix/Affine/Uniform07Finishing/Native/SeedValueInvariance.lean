import FCAppendix.Affine.Uniform07Finishing.Native.SourceGuards

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Weighted
open MeasureTheory ProbabilityTheory Game Bayes Set Classical
open FCAppendix.Affine StrictNative
open scoped BigOperators
variable {m : ℕ}

def SeedEquivalentContext (zs : ℝ) (X Y : ClassifiedContext m) : Prop :=
  X.2 = Y.2 ∧ ∀ i, X.1 i = Y.1 i ∨
    ∃ b b' : ℝ, X.1 i = some b ∧ Y.1 i = some b' ∧ b ≤ zs ∧ b' ≤ zs

lemma seedEquivalentContext_of_entryBid {zs : ℝ} {X Y : ClassifiedContext m}
    (hcounts : X.2 = Y.2)
    (hpres : ∀ i, X.1 i ≠ none ↔ Y.1 i ≠ none)
    (hseed : ∀ i, (entryBid (X.1 i) ≤ zs ∧ entryBid (Y.1 i) ≤ zs) ∨
      X.1 i = Y.1 i) : SeedEquivalentContext zs X Y := by
  refine ⟨hcounts,fun i => ?_⟩
  rcases hseed i with hs | he
  · cases hx : X.1 i with
    | none =>
        have hy : Y.1 i = none := by
          by_contra hn
          exact ((hpres i).mpr hn) hx
        exact Or.inl hy.symm
    | some b =>
        have hn : Y.1 i ≠ none := (hpres i).mp (by simp [hx])
        cases hy : Y.1 i with
        | none => exact (hn hy).elim
        | some b' => exact Or.inr ⟨b,b',rfl,rfl,by simpa [hx,entryBid] using hs.1,
            by simpa [hy,entryBid] using hs.2⟩
  · exact Or.inl he

lemma SeedEquivalentContext.symm {zs : ℝ} {X Y : ClassifiedContext m}
    (h : SeedEquivalentContext zs X Y) : SeedEquivalentContext zs Y X := by
  refine ⟨h.1.symm,fun i => ?_⟩
  rcases h.2 i with he | ⟨b,b',hb,hb',hz,hz'⟩
  · exact Or.inl he.symm
  · exact Or.inr ⟨b',b,hb',hb,hz',hz⟩

lemma seedEquivalent_presentSet {zs : ℝ} {X Y : ClassifiedContext m}
    (h : SeedEquivalentContext zs X Y) : presentSet X.1 = presentSet Y.1 := by
  ext i
  rcases h.2 i with he | ⟨b,b',hb,hb',_,_⟩
  · simp only [presentSet, Finset.mem_filter, Finset.mem_univ, true_and, he]
  · simp [presentSet,hb,hb']

lemma seedEquivalent_budget {zs : ℝ} {X Y : ClassifiedContext m}
    (h : SeedEquivalentContext zs X Y) (c : ℕ) (j : Fin 2) :
    budget c j X = budget c j Y := by
  unfold budget contextUpper
  rw [h.1,seedEquivalent_presentSet h]

lemma seedEquivalent_commonBudget {zs : ℝ} {X Y : ClassifiedContext m}
    (h : SeedEquivalentContext zs X Y) (c : ℕ) : commonBudget c X = commonBudget c Y := by
  simp only [commonBudget,seedEquivalent_budget h]

lemma seedEquivalent_sourceDemand {zs ξ z : ℝ} {X Y : ClassifiedContext m}
    (h : SeedEquivalentContext zs X Y) (hz : zs ≤ z) :
    sourceDemand ξ z X.1 = sourceDemand ξ z Y.1 := by
  apply Finset.sum_congr rfl
  intro i _
  rcases h.2 i with he | ⟨b,b',hb,hb',hs,hs'⟩
  · rw [he]
  · simp only [hb,hb',entryBid]
    rw [ClippedResidual.exposure_zero (hs.trans hz),
      ClippedResidual.exposure_zero (hs'.trans hz)]

lemma seedEquivalent_sourceWeights {zs ξ Λ r U : ℝ} {X Y : ClassifiedContext m}
    (h : SeedEquivalentContext zs X Y) (hr : 0 < r) (hz : zs ≤ Λ) :
    sourceWeights ξ Λ r U X.1 = sourceWeights ξ Λ r U Y.1 := by
  apply Subtype.ext
  funext i
  rcases h.2 i with he | ⟨b,b',hb,hb',hs,hs'⟩
  · simp only [sourceWeights,he]
  · rw [sourceWeights_seed ξ Λ r U zs b hr hz X.1 i hb hs,
      sourceWeights_seed ξ Λ r U zs b' hr hz Y.1 i hb' hs']

lemma sourcePsi_zero {d₀ z b : ℝ} (hb : b ≤ z) : sourcePsi d₀ z b = 0 := by
  simp only [sourcePsi,max_eq_left (sub_nonpos.mpr hb),zero_div]

lemma seedEquivalent_sourceRejectionDemand {zs d₀ z : ℝ} {X Y : ClassifiedContext m}
    (h : SeedEquivalentContext zs X Y) (hz : zs ≤ z) :
    sourceRejectionDemand d₀ z X.1 = sourceRejectionDemand d₀ z Y.1 := by
  apply Finset.sum_congr rfl
  intro i _
  rcases h.2 i with he | ⟨b,b',hb,hb',hs,hs'⟩
  · rw [he]
  · simp only [hb,hb',entryBid]
    rw [sourcePsi_zero (hs.trans hz),sourcePsi_zero (hs'.trans hz)]

lemma seedEquivalent_sourceCountMargin {zs t width : ℝ} {X Y : ClassifiedContext m}
    (h : SeedEquivalentContext zs X Y) :
    sourceCountMargin t width X = sourceCountMargin t width Y := by
  unfold sourceCountMargin
  rw [seedEquivalent_presentSet h,h.1]

lemma seedEquivalent_sourceCountSlacks {zs t width : ℝ} {X Y : ClassifiedContext m}
    (h : SeedEquivalentContext zs X Y) :
    sourceCountSlacks t width X = sourceCountSlacks t width Y := by
  unfold sourceCountSlacks
  rw [seedEquivalent_presentSet h,h.1]

lemma seedEquivalent_sourceSlacks {zs ξ Λ a r U d₀ z t width : ℝ}
    {X Y : ClassifiedContext m} (h : SeedEquivalentContext zs X Y)
    (hr : 0 < r) (ha : 0 ≤ a) (hzΛ : zs ≤ Λ-a) (hzz : zs ≤ z) (c : ℕ) :
    sourceSlacks ξ Λ a r U d₀ z t width c X =
      sourceSlacks ξ Λ a r U d₀ z t width c Y := by
  have hzΛ' : zs ≤ Λ := by linarith
  have hzhi : zs ≤ Λ+a := by linarith
  simp only [sourceSlacks,seedEquivalent_commonBudget h,seedEquivalent_budget h,
    seedEquivalent_sourceDemand h hzΛ,seedEquivalent_sourceDemand h hzhi,
    seedEquivalent_sourceWeights h hr hzΛ',seedEquivalent_sourceRejectionDemand h hzz,
    seedEquivalent_sourceCountMargin h]

lemma seedEquivalent_sourceGuardAlpha {zs ξ Λ a r U d₀ z t width ε : ℝ}
    {X Y : ClassifiedContext m} (h : SeedEquivalentContext zs X Y)
    (hr : 0 < r) (ha : 0 ≤ a) (hzΛ : zs ≤ Λ-a) (hzz : zs ≤ z) (c : ℕ) :
    sourceGuardAlpha ξ Λ a r U d₀ z t width ε c X =
      sourceGuardAlpha ξ Λ a r U d₀ z t width ε c Y := by
  apply Subtype.ext
  simp only [sourceGuardAlpha,sourcePolicySlacks,
    seedEquivalent_sourceSlacks h hr ha hzΛ hzz c,seedEquivalent_sourceCountSlacks h]

lemma seedEquivalent_exceptionalSet {zs U : ℝ} {X Y : ClassifiedContext m}
    (h : SeedEquivalentContext zs X Y) (hzU : zs ≤ U) :
    exceptionalSet U X.1 = exceptionalSet U Y.1 := by
  ext i
  rcases h.2 i with he | ⟨b,b',hb,hb',hs,hs'⟩
  · simp only [exceptionalSet,Finset.mem_filter,Finset.mem_univ,true_and,he]
  · have hbU : ¬U < b := not_lt.mpr (hs.trans hzU)
    have hbU' : ¬U < b' := not_lt.mpr (hs'.trans hzU)
    simp [exceptionalSet,hb,hb',entryBid,hbU,hbU']

variable [Nonempty (Fin m)]

def sourcePlanFromSeed (ξ Λ r U : ℝ) (c : ℕ)
    (α : ClassifiedContext m → unitInterval) (X : ClassifiedContext m)
    (seed : Option unitInterval) : Option (Finset (Fin m)) :=
  let Δ := max (budget c 0 X) (budget c 1 X)-commonBudget c X
  let w := sourceWeights ξ Λ r U X.1
  if (exceptionalSet U X.1).card ≤ 1 ∧ (Δ : ℝ) < WeightedSampling.totalWeight w then
    sampleSeedOption Δ (α X,w) seed
  else none

lemma sourcePlan_eq_fromSeed (ξ Λ r U zs : ℝ) (c : ℕ) (μseed : Measure ℝ)
    (α : ClassifiedContext m → unitInterval) (X : ClassifiedContext m) :
    sourcePlan ξ Λ r U zs c μseed α X =
      sourcePlanFromSeed ξ Λ r U c α X (sourceSeed μseed zs X) := rfl

lemma seedEquivalent_sourcePlanFromSeed {zs ξ Λ a r U d₀ z t width ε : ℝ}
    {X Y : ClassifiedContext m} (h : SeedEquivalentContext zs X Y)
    (hr : 0 < r) (ha : 0 ≤ a) (hzΛ : zs ≤ Λ-a) (hzz : zs ≤ z)
    (hzU : zs ≤ U) (c : ℕ) (seed : Option unitInterval) :
    sourcePlanFromSeed ξ Λ r U c (sourceGuardAlpha ξ Λ a r U d₀ z t width ε c) X seed =
      sourcePlanFromSeed ξ Λ r U c (sourceGuardAlpha ξ Λ a r U d₀ z t width ε c) Y seed := by
  have hzΛ' : zs ≤ Λ := by linarith
  unfold sourcePlanFromSeed
  rw [seedEquivalent_budget h c 0,seedEquivalent_budget h c 1,
    seedEquivalent_commonBudget h c,seedEquivalent_sourceWeights h hr hzΛ',
    seedEquivalent_exceptionalSet h hzU,seedEquivalent_sourceGuardAlpha h hr ha hzΛ hzz c]

end FCAppendix.Affine.Uniform07Finishing.Weighted
