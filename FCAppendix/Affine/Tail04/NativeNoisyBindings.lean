import FCAppendix.Affine.Tail04.NativeMenuReports
import FCAppendix.Affine.Tail04.NoisyNativeFiberProduct
import FCAppendix.Affine.Tail04.PartialNativeCoordinates

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeNoisyBindings
open MeasureTheory ProbabilityTheory Set Classical Game Bayes Filter
open Existence.Distributional OriginalValues OriginalPopulation
open SourceTailNoisyFixedPoint NativeNoisySource NativeLocalPolicy
open NoisyNativeCategories NativeDeletedCounts OriginalFiniteFibers

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht)
  (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀ v,t< v → H≤ upperBid v) (N : ℕ)

variable (hrare : (1-D.ξ)*D.B+D.ξ*D.B*(((N+1):ℝ)*((activeMass P.theta*P.zeta*powerTail P.M 10 t)/(partialMass+(activeMass P.theta*P.zeta*powerTail P.M 10 t))))≤ D.R)

include hrare in
lemma rare_cast : (1-D.ξ)*D.B+D.ξ*D.B*(((N+1:ℕ):ℝ)*
    ((activeMass P.theta*P.zeta*powerTail P.M 10 t)/
      (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t)))≤ D.R := by
  simpa only [Nat.cast_add,Nat.cast_one] using hrare

def localData : NativeLocalPolicy.Data (N+1) D.c :=
  NativeSourcePolicy.data (regions D P hdR H hBH) P rfl t ht.le πL
    (partialPhysical D P t ht π) (activePhysical D P t ht π)
    upperBid hupperBid hfloor (N+1) D.c D.ξ D.width D.regimeShare D.eA D.eR D.F
    D.hξ D.hξ1 D.hw D.regimeShare.2.1 D.regimeShare.2.2 (by simpa only [regions,Nat.cast_add,Nat.cast_one] using hrare) (duplicate_gap D)

def publicData : PublicScenario.Data :=
  NativeSourcePolicy.publicData (regions D P hdR H hBH) P rfl t ht.le πL
    (partialPhysical D P t ht π) (activePhysical D P t ht π)
    upperBid hupperBid hfloor D.c D.ξ D.regimeShare D.eA D.eR D.F
    D.regimeShare.2.1 D.regimeShare.2.2

def coreGame : FiniteGame (N+1) 2 D.c Seed :=
  NativeSourcePosterior.game (regions D P hdR H hBH) P rfl t ht.le πL
    (partialPhysical D P t ht π) (activePhysical D P t ht π)
    upperBid hupperBid hfloor (N+1) D.c D.ξ D.width D.regimeShare D.eA D.eR D.F
    D.hξ D.hξ1 D.hw D.regimeShare.2.1 D.regimeShare.2.2 (by simpa only [regions,Nat.cast_add,Nat.cast_one] using hrare)
    (duplicate_gap D) D.eta D.heta0 D.heta1

@[simp] theorem localData_regions : (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).E=(regions D P hdR H hBH) := rfl
@[simp] theorem coreGame_policy : (coreGame D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).policy=(localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).completedPolicy := rfl
@[simp] theorem sourceGame_seed : (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (rare_cast D P t N hrare)).seedLaw=NativeLocalPolicy.seedLaw := rfl
@[simp] theorem sourceGame_schedule :
    (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (rare_cast D P t N hrare)).A=Schedule.affine 2 D.eta D.heta0 D.heta1 := rfl

theorem sourceGame_focalCount (i : Fin (N+1)) (a : JointAction 2) (ω : Sample (N+1) 2 Seed) :
    focalCount (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (rare_cast D P t N hrare)) i a ω=focalCount (coreGame D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i a ω :=
  FeasibleListNormalization.focalCount_eq (coreGame D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i a ω

theorem sourceGame_problem (i : Fin (N+1)) : problem (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (rare_cast D P t N hrare)) i=problem (coreGame D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i :=
  FeasibleListNormalization.problem_eq (coreGame D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i

theorem localData_signalLaw (h : Fin ((N+1)+1)) :
    WeakProbability.toMeasure ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).signalLaw h)=
      ProbabilityMeasure.toMeasure ((installOriginal D P t ht).privateBayes h.val
        (CompactSourceBidLaws.bidMarginal (π 2).1)) := by
  rw [←(localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).signalLaw_exact]
  exact NoisyNativeRowLaws.original_sorted_private_signal D P t ht hdR H hBH
    πL π upperBid hupperBid hfloor h.val

theorem localData_signalProbability (h : Fin ((N+1)+1)) :
    ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).signalLaw h).val=(installOriginal D P t ht).privateBayes h.val
      (CompactSourceBidLaws.bidMarginal (π 2).1) := by
  apply ProbabilityMeasure.toMeasure_injective
  exact localData_signalLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare h

theorem localData_marksLaw (h : Fin ((N+1)+1)) :
    (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).marksLaw h=(installOriginal D P t ht).marksLaw h.val := by
  apply FiniteLaw.ext
  intro r
  have hm := NoisyNativeRowLaws.original_sorted_marks D P t ht hdR H hBH
    πL π upperBid hupperBid hfloor h.val
  have hk := (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).marksLaw_exact h
  have he := congrArg (fun μ : Measure (EqualPrivateSignal.Marks h.val) => (μ {r}).toReal)
    (hk.symm.trans hm)
  simpa only [FiniteLaw.probabilityMeasure_singleton,
    ENNReal.toReal_ofReal ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).marksLaw h |>.nonneg r),
    ENNReal.toReal_ofReal ((installOriginal D P t ht).marksLaw h.val |>.nonneg r)] using he

@[simp] theorem publicData_marksLaw (h : Fin ((N+1)+1)) : (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor).marksLaw h.val=(localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).marksLaw h := rfl

@[simp] theorem localData_publicChoice (A : ℕ) :
    (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).publicChoice A=PublicScenario.localChoice (regions D P hdR H hBH) (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor) (LowBody.realLowBidLaw πL.1) A := rfl

theorem source_lowBidLaw :
    NativeFlag.nativeLowBidLaw (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (rare_cast D P t N hrare)) (regions D P hdR H hBH)=(LowBody.realLowBidLaw πL.1 : Measure ℝ) := by
  exact OriginalLowConditional.native_lowBidLaw_eq (regions D P hdR H hBH) (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (rare_cast D P t N hrare)) (lowMass P.theta)
    (activeMass P.theta-(activeMass P.theta*P.zeta*powerTail P.M 10 t)) (partialMass+(activeMass P.theta*P.zeta*powerTail P.M 10 t)) P.low_mass_pos _
    (native_original_exact_low_row (regions D P hdR H hBH) P rfl t ht.le πL
      (partialPhysical D P t ht π) (activePhysical D P t ht π)
      upperBid hupperBid hfloor (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (rare_cast D P t N hrare))
      (game_original_joint D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (rare_cast D P t N hrare)))

theorem source_user_bands :
    ∀ᵐ x ∂userLaw (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (rare_cast D P t N hrare)),sourceBands P (regions D P hdR H hBH) t x.1 := by
  rw [game_original_user]
  have hband : ∀ᵐ x ∂(joint D P t ht πL π upperBid hupperBid : Measure (ℝ×JointAction 2)),
      sourceBands P (regions D P hdR H hBH) t x :=
    originalJoint_sourceBands P (regions D P hdR H hBH) rfl t ht.le πL
      (partialPhysical D P t ht π) (activePhysical D P t ht π)
      upperBid hupperBid hfloor
  exact (measurePreserving_fst
    (μ:=(joint D P t ht πL π upperBid hupperBid : Measure (ℝ×JointAction 2)))
    (ν:=permLaw 2)).quasiMeasurePreserving.ae hband

theorem conditional_user_bands (k : Fin 4) :
    ∀ᵐ x ∂cond (userLaw (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (rare_cast D P t N hrare))) ((regions D P hdR H hBH).coarseTag ⁻¹' {k}),
      sourceBands P (regions D P hdR H hBH) t x.1 ∧ (regions D P hdR H hBH).coarseTag x=k := by
  have hband : ∀ᵐ x ∂cond (userLaw (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (rare_cast D P t N hrare))) ((regions D P hdR H hBH).coarseTag ⁻¹' {k}),
      sourceBands P (regions D P hdR H hBH) t x.1 := ProbabilityTheory.cond_absolutelyContinuous.ae_le
    (source_user_bands D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare)
  have htag : ∀ᵐ x ∂cond (userLaw (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (rare_cast D P t N hrare))) ((regions D P hdR H hBH).coarseTag ⁻¹' {k}),(regions D P hdR H hBH).coarseTag x=k := by
    unfold ProbabilityTheory.cond
    exact Measure.ae_smul_measure
      (ae_restrict_mem ((measurableSet_singleton k).preimage (regions D P hdR H hBH).measurable_coarseTag)) _
  exact hband.and htag

theorem fiber_support (kind : Fin N → Fin 4) :
    ∀ᵐ w ∂fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind,
      ∀ r,sourceBands P (regions D P hdR H hBH) t (w.1.1 r).1 ∧ (regions D P hdR H hBH).coarseTag (w.1.1 r)=kind r := by
  haveI (r : Fin N) : IsProbabilityMeasure
      (cond (userLaw (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (rare_cast D P t N hrare))) ((regions D P hdR H hBH).coarseTag ⁻¹' {kind r})) :=
    cond_isProbabilityMeasure (native_source_category_ne_zero D P t ht hdR H hBH
      πL π upperBid hupperBid hfloor (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (rare_cast D P t N hrare))
      (game_original_joint D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (rare_cast D P t N hrare)) (kind r))
  have hp : ∀ᵐ w ∂Measure.pi (fun r : Fin N =>
      cond (userLaw (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (rare_cast D P t N hrare))) ((regions D P hdR H hBH).coarseTag ⁻¹' {kind r})),
      ∀ r,sourceBands P (regions D P hdR H hBH) t (w r).1 ∧ (regions D P hdR H hBH).coarseTag (w r)=kind r :=
    ae_all_iff.mpr (fun r => (measurePreserving_eval
      (fun r : Fin N => cond (userLaw (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (rare_cast D P t N hrare))) ((regions D P hdR H hBH).coarseTag ⁻¹' {kind r})) r).quasiMeasurePreserving.ae
      (conditional_user_bands D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare (kind r)))
  let μrow : Measure (Fin N→ UserDraw 2) :=
    Measure.pi (fun r : Fin N => cond (userLaw (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (rare_cast D P t N hrare))) ((regions D P hdR H hBH).coarseTag ⁻¹' {kind r}))
  let νseed := Measure.pi (fun _ : Fin 2 => (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (rare_cast D P t N hrare)).seedLaw)
  have hmp : MeasurePreserving (fun w : DeletedSample N Seed => w.1.1)
      ((μrow.prod νseed).prod (permLaw 2)) μrow :=
    (measurePreserving_fst (μ:=μrow) (ν:=νseed)).comp
      (measurePreserving_fst (μ:=μrow.prod νseed) (ν:=permLaw 2))
  exact hmp.quasiMeasurePreserving.ae hp

lemma restoreUsers_succAbove (i : Fin (N+1)) (r : Fin N → UserDraw 2) (j : Fin N) :
    restoreUsers i r (i.succAbove j)=r j := by
  have he := congrArg (fun pair : UserDraw 2×(Fin N → UserDraw 2) => pair.2 j)
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) => UserDraw 2) i).apply_symm_apply
      (dummyDraw,r))
  exact he

lemma restored_source_rivals (i : Fin (N+1)) (w : DeletedSample N Seed)
    (hw : ∀ r,sourceBands P (regions D P hdR H hBH) t (w.1.1 r).1) :
    ∀ l,l≠i → sourceBands P (regions D P hdR H hBH) t ((restoreSample i w).1.1 l).1 := by
  intro l hl
  obtain ⟨r,rfl⟩ := Fin.exists_succAbove_eq hl
  simpa only [restoreSample,restoreUsers_succAbove] using hw r

lemma restored_kind (i : Fin (N+1)) (w : DeletedSample N Seed) (kind : Fin N → Fin 4)
    (hw : ∀ r,(regions D P hdR H hBH).coarseTag (w.1.1 r)=kind r) :
    PartialNativeCoordinates.rivalKinds (regions D P hdR H hBH) i (restoreSample i w).1=kind := by
  funext r
  simpa only [PartialNativeCoordinates.rivalKinds,restoreSample,restoreUsers_succAbove] using hw r

theorem source_active_count (i : Fin (N+1)) (b : Icc (1:ℝ) (regions D P hdR H hBH).U)
    (ω : Sample (N+1) 2 Seed) (hr : ∀ l,l≠i → sourceBands P (regions D P hdR H hBH) t (ω.1.1 l).1) :
    let a := RawRoutes.action b ((by norm_num : (0:ℝ)≤1).trans b.2.1) 2
    let L := observe (deviated i a ω) 0
    let hi := NativeMenuReports.active_focal_present (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i b ω 0
    focalCount (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (rare_cast D P t N hrare)) i a ω=
      originalPairCount
        ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).zeroSampler (LocalCoordinates.ids (regions D P hdR H hBH) 1 L).card ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (LocalCoordinates.ids (regions D P hdR H hBH) 2 L))
          ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (LocalCoordinates.ids (regions D P hdR H hBH) 3 L)))
        ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).oneSampler (LocalCoordinates.ids (regions D P hdR H hBH) 1 L).card ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (LocalCoordinates.ids (regions D P hdR H hBH) 2 L))
          ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (LocalCoordinates.ids (regions D P hdR H hBH) 3 L)))
        ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).parameter (LocalCoordinates.ids (regions D P hdR H hBH) 1 L) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (LocalCoordinates.ids (regions D P hdR H hBH) 2 L))
          ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).finiteCount (LocalCoordinates.ids (regions D P hdR H hBH) 3 L)) L)
        (Sum.inl (SortedCoordinates.rankFin (LocalCoordinates.ids (regions D P hdR H hBH) 1 L) (LocalCoordinates.bidVector L) ⟨i,hi⟩))
        (Sum.inl (SortedCoordinates.rankFin (LocalCoordinates.ids (regions D P hdR H hBH) 1 L) (LocalCoordinates.bidVector L) ⟨i,hi⟩))
        ((LocalCoordinates.privateRow (regions D P hdR H hBH) (LocalCoordinates.ids (regions D P hdR H hBH) 2 L) L,(ω.1.2 0).1),
          (LocalCoordinates.privateRow (regions D P hdR H hBH) (LocalCoordinates.ids (regions D P hdR H hBH) 3 L) (observe (deviated i a ω) 1),
            (ω.1.2 1).1)) := by
  dsimp only
  rw [sourceGame_focalCount]
  exact NativeMenuReports.native_active_focal_count (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) P t (coreGame D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) rfl i b ω hr

theorem source_partial_count (i : Fin (N+1)) (b : Icc (regions D P hdR H hBH).R (regions D P hdR H hBH).Rp) (k : Fin 3)
    (ω : Sample (N+1) 2 Seed) (hr : ∀ l,l≠i → sourceBands P (regions D P hdR H hBH) t (ω.1.1 l).1) :
    focalCount (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (rare_cast D P t N hrare)) i (RawRoutes.action b (((regions D P hdR H hBH).d_nonneg.trans (regions D P hdR H hBH).d_lt_R.le).trans b.2.1) k) ω=
      boolPairCount
        ((if (0:Fin 2)∈firstK ω.2 k.val then NativeMenuReports.privateZeroAccept (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i b ω.1 else false),
          (if (1:Fin 2)∈firstK ω.2 k.val then NativeMenuReports.privateOneAccept (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) i b ω.1 else false)) := by
  rw [sourceGame_focalCount]
  exact NativeMenuReports.native_partial_focal_count (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) P t (coreGame D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) rfl i b k ω hr

end FCAppendix.Affine.Tail04.NativeNoisyBindings
