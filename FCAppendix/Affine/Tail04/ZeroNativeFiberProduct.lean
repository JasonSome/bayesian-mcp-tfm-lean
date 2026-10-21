import FCAppendix.Affine.Tail04.OriginalFiberProduct
import FCAppendix.Affine.Tail04.OriginalMovingLow
import FCAppendix.Affine.Tail04.ZeroNativeCategories

noncomputable section
namespace FCAppendix.Affine.Tail04.ZeroNativeFiberProduct
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Hybrid NativeFlag Existence.Distributional OriginalValues OriginalPopulation
open NativeZeroNoiseSource SourceTailNoisyFixedPoint ZeroNativeCategories OriginalFiberProduct

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (hdR : P.d0< D.R) (H : ℝ) (hUH : D.U< H)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht)
  (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀ v,t< v → H≤ upperBid v) (N : ℕ)

local notation "E" => regions D P hdR H hUH
local notation "z" => activeMass P.theta*P.zeta*powerTail P.M 10 t
local notation "m" => N+1
variable (hrare : (1-D.ξ)*D.U+D.ξ*D.U*((N+1:ℝ)*
  ((activeMass P.theta*P.zeta*powerTail P.M 10 t)/
    (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t)))≤ D.R)

private lemma castMarketRare {N : ℕ} {x y p q : ℝ}
    (h : x+y*((N+1:ℝ)*p)≤q) : x+y*((((N+1:ℕ):ℝ))*p)≤q := by
  simpa only [Nat.cast_add,Nat.cast_one] using h
local notation "Γ" => game D P t ht hdR H hUH πL π upperBid hupperBid hfloor m (castMarketRare hrare)
local notation "μ" => userLaw Γ
local notation "ρA" => CompactSourceBidLaws.bidMarginal (Subtype.val (active D P t ht π))
local notation "ρP" => OriginalPrivateSource.originalEntryLaw E P rfl t ht.le πL
  («partial» D P t ht π) (active D P t ht π) upperBid hupperBid hfloor

abbrev RestSeeds := (Fin 2 → NativeLocalPolicy.Seed) × Equiv.Perm (Fin 2)

def restSeedLaw : Measure RestSeeds :=
  (Measure.pi (fun _ : Fin 2 => (Γ).seedLaw)).prod (permLaw 2)

instance restSeedLaw_probability : IsProbabilityMeasure
    (restSeedLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare) := by
  unfold restSeedLaw
  infer_instance

def commonProjection (x : UserDraw 2) : Icc (1:ℝ) (E).U := OriginalCommonLaw.commonDecode E x.1
def privateProjection (x : UserDraw 2) : Ici (E).H ⊕ Icc (E).R (E).Rp := LocalCoordinates.decode E x.1.2.bid

lemma measurable_commonProjection : Measurable (commonProjection D P hdR H hUH) :=
  (OriginalCommonLaw.measurable_commonDecode E).comp measurable_fst

lemma measurable_privateProjection : Measurable (privateProjection D P hdR H hUH) :=
  (LocalCoordinates.measurable_decode E).comp ((measurable_bid 2).comp measurable_fst.snd)

include N in
theorem common_projection_law :
    (cond μ ((E).coarseTag ⁻¹' {(1:Fin 4)})).map (commonProjection D P hdR H hUH)=
      (ProbabilityMeasure.toMeasure ρA) :=
  OriginalCommonLaw.native_original_common_bid E P rfl t ht.le πL
    («partial» D P t ht π) (active D P t ht π) upperBid hupperBid hfloor Γ
    (game_original_joint D P t ht hdR H hUH πL π upperBid hupperBid hfloor m (castMarketRare hrare))

include N in
theorem private_projection_law (j : Fin 2) :
    (cond μ ((E).coarseTag ⁻¹' {NativeContinuation.upperTag j})).map
      (privateProjection D P hdR H hUH)=(ProbabilityMeasure.toMeasure ρP) :=
  OriginalPrivateSource.native_originalEntryLaw E P rfl t ht.le πL
    («partial» D P t ht π) (active D P t ht π) upperBid hupperBid hfloor Γ
    (game_original_joint D P t ht hdR H hUH πL π upperBid hupperBid hfloor m (castMarketRare hrare)) j

variable (kind : Fin N → Fin 4) (A H0 H1 : ℕ)
  (ea : Fin A ≃ Common kind) (e0 : Fin H0 ≃ Zero kind) (e1 : Fin H1 ≃ One kind)

local notation "ω" => restSeedLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
local notation "rows" => OriginalFiberProduct.fiberRows kind A H0 H1 ea e0 e1
  (commonProjection D P hdR H hUH) (privateProjection D P hdR H hUH)

def associate : OriginalFiniteFibers.DeletedSample N NativeLocalPolicy.Seed →
    (Fin N → UserDraw 2) × RestSeeds := MeasurableEquiv.prodAssoc

lemma measurable_associate : Measurable (associate N) := MeasurableEquiv.prodAssoc.measurable

theorem fiber_associate_law :
    (fiberMeasure D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare kind).map
      (associate N)=OriginalFiberProduct.fiberLaw μ (E).coarseTag kind ω := by
  haveI (i : Fin N) : IsProbabilityMeasure (cond μ ((E).coarseTag ⁻¹' {kind i})) :=
    cond_isProbabilityMeasure (native_source_category_ne_zero D P t ht hdR H hUH πL π
      upperBid hupperBid hfloor Γ
      (game_original_joint D P t ht hdR H hUH πL π upperBid hupperBid hfloor m (castMarketRare hrare)) (kind i))
  exact (measurePreserving_prodAssoc
    (Measure.pi (fun i => cond μ ((E).coarseTag ⁻¹' {kind i})))
    (Measure.pi (fun _ : Fin 2 => (Γ).seedLaw)) (permLaw 2)).map_eq

theorem native_numerical_fibers :
    (fiberMeasure D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare kind).map
      (rows ∘ associate N)=
      (OriginalFiberProduct.numericalLaw A H0 H1 (ProbabilityMeasure.toMeasure ρA) (ProbabilityMeasure.toMeasure ρP)).prod ω := by
  have hp0 := private_projection_law D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare 0
  have hp1 := private_projection_law D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare 1
  simp only [NativeContinuation.upperTag] at hp0 hp1
  rw [←Measure.map_map (OriginalFiberProduct.measurable_fiberRows kind A H0 H1 ea e0 e1
      _ _ (measurable_commonProjection D P hdR H hUH) (measurable_privateProjection D P hdR H hUH))
    (measurable_associate N),fiber_associate_law]
  exact OriginalFiberProduct.fiberRows_law μ (E).coarseTag kind
    (fun i => native_source_category_ne_zero D P t ht hdR H hUH πL π upperBid hupperBid hfloor Γ
      (game_original_joint D P t ht hdR H hUH πL π upperBid hupperBid hfloor m (castMarketRare hrare)) (kind i))
    A H0 H1 ea e0 e1 _ _ (measurable_commonProjection D P hdR H hUH)
    (measurable_privateProjection D P hdR H hUH) (ProbabilityMeasure.toMeasure ρA) (ProbabilityMeasure.toMeasure ρP)
    (common_projection_law D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare) hp0 hp1 ω

variable (n : ℕ) (el : Fin (n+1) ≃ {i : Fin N // kind i=0})

theorem native_seed_numerical_fibers
    (hlow : ∀ b,nativeLowBidLaw Γ E {b}=0) :
    (fiberMeasure D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare kind).map
      ((OriginalFiberProduct.seedRows μ (E).coarseTag kind A H0 H1 ea e0 e1
        (commonProjection D P hdR H hUH) (privateProjection D P hdR H hUH)
        NativeFlag.nativeBid n el) ∘ associate N)=
      (volume : Measure unitInterval).prod
        ((OriginalFiberProduct.numericalLaw A H0 H1 (ProbabilityMeasure.toMeasure ρA) (ProbabilityMeasure.toMeasure ρP)).prod ω) := by
  have hp0 := private_projection_law D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare 0
  have hp1 := private_projection_law D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare 1
  simp only [NativeContinuation.upperTag] at hp0 hp1
  rw [←Measure.map_map (OriginalFiberProduct.measurable_seedRows μ (E).coarseTag kind
      A H0 H1 ea e0 e1 _ _ (measurable_commonProjection D P hdR H hUH)
      (measurable_privateProjection D P hdR H hUH) NativeFlag.nativeBid
      NativeFlag.measurable_nativeBid n el) (measurable_associate N),fiber_associate_law]
  exact OriginalFiberProduct.seedRows_law μ (E).coarseTag (E).measurable_coarseTag kind
    (fun i => native_source_category_ne_zero D P t ht hdR H hUH πL π upperBid hupperBid hfloor Γ
      (game_original_joint D P t ht hdR H hUH πL π upperBid hupperBid hfloor m (castMarketRare hrare)) (kind i))
    A H0 H1 ea e0 e1 _ _ (measurable_commonProjection D P hdR H hUH)
    (measurable_privateProjection D P hdR H hUH) (ProbabilityMeasure.toMeasure ρA) (ProbabilityMeasure.toMeasure ρP)
    (common_projection_law D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare)
    hp0 hp1 ω NativeFlag.nativeBid NativeFlag.measurable_nativeBid hlow n el

theorem native_low_singletons_of_C2 (cats : FiniteLaw (Fin 4))
    (L : LowBody.ActualAtomlessLowLimit N P.d0 D.ξ D.c cats P.originalLowLaw)
    (hL : πL=L.joint) : ∀ b,nativeLowBidLaw Γ E {b}=0 := by
  apply OriginalLowConditional.native_low_atomless_of_C2 E Γ
    (lowMass P.theta) (activeMass P.theta-z) (partialMass+z) P.low_mass_pos
    cats P.originalLowLaw L
  have hr := native_original_exact_low_row E P rfl t ht.le πL
    («partial» D P t ht π) (active D P t ht π) upperBid hupperBid hfloor Γ
    (game_original_joint D P t ht hdR H hUH πL π upperBid hupperBid hfloor m (castMarketRare hrare))
  simpa only [hL] using hr

theorem native_seed_numerical_fibers_of_C2 (cats : FiniteLaw (Fin 4))
    (L : LowBody.ActualAtomlessLowLimit N P.d0 D.ξ D.c cats P.originalLowLaw)
    (hL : πL=L.joint) :
    (fiberMeasure D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare kind).map
      ((OriginalFiberProduct.seedRows μ (E).coarseTag kind A H0 H1 ea e0 e1
        (commonProjection D P hdR H hUH) (privateProjection D P hdR H hUH)
        NativeFlag.nativeBid n el) ∘ associate N)=
      (volume : Measure unitInterval).prod
        ((OriginalFiberProduct.numericalLaw A H0 H1 (ProbabilityMeasure.toMeasure ρA) (ProbabilityMeasure.toMeasure ρP)).prod ω) :=
  native_seed_numerical_fibers D P t ht hdR H hUH πL π upperBid hupperBid hfloor
    N hrare kind A H0 H1 ea e0 e1 n el
    (native_low_singletons_of_C2 D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
      cats L hL)

end FCAppendix.Affine.Tail04.ZeroNativeFiberProduct
