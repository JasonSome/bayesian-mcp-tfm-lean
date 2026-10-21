import FCAppendix.Affine.Tail04.OriginalFiberProduct

noncomputable section
namespace FCAppendix.Affine.Tail04.NoisyNativeFiberProduct
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Hybrid NativeFlag Existence.Distributional OriginalValues OriginalPopulation
open NativeNoisySource SourceTailNoisyFixedPoint NoisyNativeCategories OriginalFiberProduct

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht)
  (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀ v,t< v → H≤ upperBid v) (N : ℕ)

variable (hrare : (1-D.ξ)*D.B+D.ξ*D.B*((N+1:ℝ)*((activeMass P.theta*P.zeta*powerTail P.M 10 t)/(partialMass+(activeMass P.theta*P.zeta*powerTail P.M 10 t))))≤ D.R)

abbrev RestSeeds := (Fin 2 → NativeLocalPolicy.Seed) × Equiv.Perm (Fin 2)

def restSeedLaw : Measure RestSeeds :=
  (Measure.pi (fun _ : Fin 2 => (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare)).seedLaw)).prod (permLaw 2)

instance restSeedLaw_probability : IsProbabilityMeasure
    (restSeedLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) := by
  unfold restSeedLaw
  infer_instance

def commonProjection (x : UserDraw 2) : Icc (1:ℝ) D.B := OriginalCommonLaw.commonDecode (regions D P hdR H hBH) x.1
def privateProjection (x : UserDraw 2) : Ici H ⊕ Icc D.R D.V := LocalCoordinates.decode (regions D P hdR H hBH) x.1.2.bid

def privateRowLaw : ProbabilityMeasure (Ici H ⊕ Icc D.R D.V) := by
  exact OriginalPrivateSource.originalEntryLaw (regions D P hdR H hBH) P rfl t ht.le πL
    (partialPhysical D P t ht π) (activePhysical D P t ht π) upperBid hupperBid hfloor

lemma measurable_commonProjection : Measurable (commonProjection D P hdR H hBH) :=
  (OriginalCommonLaw.measurable_commonDecode (regions D P hdR H hBH)).comp measurable_fst

lemma measurable_privateProjection : Measurable (privateProjection D P hdR H hBH) :=
  (LocalCoordinates.measurable_decode (regions D P hdR H hBH)).comp ((measurable_bid 2).comp measurable_fst.snd)

include N in
theorem common_projection_law :
    (cond (userLaw (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare))) ((regions D P hdR H hBH).coarseTag ⁻¹' {(1:Fin 4)})).map (commonProjection D P hdR H hBH)=
      ((CompactSourceBidLaws.bidMarginal (Subtype.val (activePhysical D P t ht π))) : Measure (Icc (1:ℝ) D.B)) :=
  OriginalCommonLaw.native_original_common_bid (regions D P hdR H hBH) P rfl t ht.le πL
    (partialPhysical D P t ht π) (activePhysical D P t ht π) upperBid hupperBid hfloor (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare))
    (game_original_joint D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare))

include N in
theorem private_projection_law (j : Fin 2) :
    (cond (userLaw (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare))) ((regions D P hdR H hBH).coarseTag ⁻¹' {NativeContinuation.upperTag j})).map
      (privateProjection D P hdR H hBH)=((privateRowLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor) : Measure (Ici H ⊕ Icc D.R D.V)) :=
  OriginalPrivateSource.native_originalEntryLaw (regions D P hdR H hBH) P rfl t ht.le πL
    (partialPhysical D P t ht π) (activePhysical D P t ht π) upperBid hupperBid hfloor (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare))
    (game_original_joint D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare)) j

variable (kind : Fin N → Fin 4) (A H0 H1 : ℕ)
  (ea : Fin A ≃ Common kind) (e0 : Fin H0 ≃ Zero kind) (e1 : Fin H1 ≃ One kind)

def associate : OriginalFiniteFibers.DeletedSample N NativeLocalPolicy.Seed →
    (Fin N → UserDraw 2) × RestSeeds := MeasurableEquiv.prodAssoc

lemma measurable_associate : Measurable (associate N) := MeasurableEquiv.prodAssoc.measurable

theorem fiber_associate_law :
    (fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind).map
      (associate N)=OriginalFiberProduct.fiberLaw (userLaw (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare))) (regions D P hdR H hBH).coarseTag kind (restSeedLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) := by
  haveI (i : Fin N) : IsProbabilityMeasure (cond (userLaw (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare))) ((regions D P hdR H hBH).coarseTag ⁻¹' {kind i})) :=
    cond_isProbabilityMeasure (native_source_category_ne_zero D P t ht hdR H hBH πL π
      upperBid hupperBid hfloor (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare))
      (game_original_joint D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare)) (kind i))
  exact (measurePreserving_prodAssoc
    (Measure.pi (fun i => cond (userLaw (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare))) ((regions D P hdR H hBH).coarseTag ⁻¹' {kind i})))
    (Measure.pi (fun _ : Fin 2 => (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare)).seedLaw)) (permLaw 2)).map_eq

theorem native_numerical_fibers :
    (fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind).map
      ((OriginalFiberProduct.fiberRows kind A H0 H1 ea e0 e1 (commonProjection D P hdR H hBH) (privateProjection D P hdR H hBH)) ∘ associate N)=
      (OriginalFiberProduct.numericalLaw A H0 H1 ((CompactSourceBidLaws.bidMarginal (Subtype.val (activePhysical D P t ht π))) : Measure (Icc (1:ℝ) D.B)) ((privateRowLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor) : Measure (Ici H ⊕ Icc D.R D.V))).prod (restSeedLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) := by
  have hp0 := private_projection_law D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare 0
  have hp1 := private_projection_law D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare 1
  rw [show NativeContinuation.upperTag (0:Fin 2)=(2:Fin 4) by decide] at hp0
  rw [show NativeContinuation.upperTag (1:Fin 2)=(3:Fin 4) by decide] at hp1
  rw [←Measure.map_map (OriginalFiberProduct.measurable_fiberRows kind A H0 H1 ea e0 e1
      _ _ (measurable_commonProjection D P hdR H hBH) (measurable_privateProjection D P hdR H hBH))
    (measurable_associate N),fiber_associate_law]
  exact OriginalFiberProduct.fiberRows_law (userLaw (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare))) (regions D P hdR H hBH).coarseTag kind
    (fun i => native_source_category_ne_zero D P t ht hdR H hBH πL π upperBid hupperBid hfloor (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare))
      (game_original_joint D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare)) (kind i))
    A H0 H1 ea e0 e1 _ _ (measurable_commonProjection D P hdR H hBH)
    (measurable_privateProjection D P hdR H hBH) ((CompactSourceBidLaws.bidMarginal (Subtype.val (activePhysical D P t ht π))) : Measure (Icc (1:ℝ) D.B)) ((privateRowLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor) : Measure (Ici H ⊕ Icc D.R D.V))
    (common_projection_law D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) hp0 hp1 (restSeedLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare)

variable (n : ℕ) (el : Fin (n+1) ≃ {i : Fin N // kind i=0})

theorem native_seed_numerical_fibers
    (hlow : ∀ b,nativeLowBidLaw (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare)) (regions D P hdR H hBH) {b}=0) :
    (fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind).map
      ((OriginalFiberProduct.seedRows (userLaw (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare))) (regions D P hdR H hBH).coarseTag kind A H0 H1 ea e0 e1
        (commonProjection D P hdR H hBH) (privateProjection D P hdR H hBH)
        NativeFlag.nativeBid n el) ∘ associate N)=
      (volume : Measure unitInterval).prod
        ((OriginalFiberProduct.numericalLaw A H0 H1 ((CompactSourceBidLaws.bidMarginal (Subtype.val (activePhysical D P t ht π))) : Measure (Icc (1:ℝ) D.B)) ((privateRowLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor) : Measure (Ici H ⊕ Icc D.R D.V))).prod (restSeedLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare)) := by
  have hp0 := private_projection_law D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare 0
  have hp1 := private_projection_law D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare 1
  rw [show NativeContinuation.upperTag (0:Fin 2)=(2:Fin 4) by decide] at hp0
  rw [show NativeContinuation.upperTag (1:Fin 2)=(3:Fin 4) by decide] at hp1
  rw [←Measure.map_map (OriginalFiberProduct.measurable_seedRows (userLaw (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare))) (regions D P hdR H hBH).coarseTag kind
      A H0 H1 ea e0 e1 _ _ (measurable_commonProjection D P hdR H hBH)
      (measurable_privateProjection D P hdR H hBH) NativeFlag.nativeBid
      NativeFlag.measurable_nativeBid n el) (measurable_associate N),fiber_associate_law]
  exact OriginalFiberProduct.seedRows_law (userLaw (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare))) (regions D P hdR H hBH).coarseTag (regions D P hdR H hBH).measurable_coarseTag kind
    (fun i => native_source_category_ne_zero D P t ht hdR H hBH πL π upperBid hupperBid hfloor (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare))
      (game_original_joint D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare)) (kind i))
    A H0 H1 ea e0 e1 _ _ (measurable_commonProjection D P hdR H hBH)
    (measurable_privateProjection D P hdR H hBH) ((CompactSourceBidLaws.bidMarginal (Subtype.val (activePhysical D P t ht π))) : Measure (Icc (1:ℝ) D.B)) ((privateRowLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor) : Measure (Ici H ⊕ Icc D.R D.V))
    (common_projection_law D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare)
    hp0 hp1 (restSeedLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) NativeFlag.nativeBid NativeFlag.measurable_nativeBid hlow n el

theorem native_low_singletons_of_C2 (cats : FiniteLaw (Fin 4))
    (L : LowBody.ActualAtomlessLowLimit N P.d0 D.ξ D.c cats P.originalLowLaw)
    (hL : πL=L.joint) : ∀ b,nativeLowBidLaw (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare)) (regions D P hdR H hBH) {b}=0 := by
  subst πL
  exact OriginalLowConditional.native_low_atomless_of_C2 (regions D P hdR H hBH) (game D P t ht hdR H hBH L.joint π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare))
    (lowMass P.theta) (activeMass P.theta-(activeMass P.theta*P.zeta*powerTail P.M 10 t)) (partialMass+(activeMass P.theta*P.zeta*powerTail P.M 10 t)) P.low_mass_pos
    cats P.originalLowLaw L
    (native_original_exact_low_row (regions D P hdR H hBH) P rfl t ht.le L.joint
      (partialPhysical D P t ht π) (activePhysical D P t ht π) upperBid hupperBid hfloor (game D P t ht hdR H hBH L.joint π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare))
      (game_original_joint D P t ht hdR H hBH L.joint π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare)))

theorem native_seed_numerical_fibers_of_C2 (cats : FiniteLaw (Fin 4))
    (L : LowBody.ActualAtomlessLowLimit N P.d0 D.ξ D.c cats P.originalLowLaw)
    (hL : πL=L.joint) :
    (fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind).map
      ((OriginalFiberProduct.seedRows (userLaw (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hrare))) (regions D P hdR H hBH).coarseTag kind A H0 H1 ea e0 e1
        (commonProjection D P hdR H hBH) (privateProjection D P hdR H hBH)
        NativeFlag.nativeBid n el) ∘ associate N)=
      (volume : Measure unitInterval).prod
        ((OriginalFiberProduct.numericalLaw A H0 H1 ((CompactSourceBidLaws.bidMarginal (Subtype.val (activePhysical D P t ht π))) : Measure (Icc (1:ℝ) D.B)) ((privateRowLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor) : Measure (Ici H ⊕ Icc D.R D.V))).prod (restSeedLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare)) :=
  native_seed_numerical_fibers D P t ht hdR H hBH πL π upperBid hupperBid hfloor
    N hrare kind A H0 H1 ea e0 e1 n el
    (native_low_singletons_of_C2 D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
      cats L hL)

end FCAppendix.Affine.Tail04.NoisyNativeFiberProduct
