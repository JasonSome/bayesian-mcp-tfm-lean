import FCAppendix.Affine.Tail04.NativeMenuReports
import FCAppendix.Affine.Tail04.ZeroNativeFiberProduct
import FCAppendix.Affine.Tail04.PartialNativeCoordinates
import FCAppendix.Affine.Tail04.ZeroNativeRowLaws

noncomputable section
namespace FCAppendix.Affine.Tail04.ZeroNativeBindings
open MeasureTheory ProbabilityTheory Set Classical Game Bayes Filter
open Existence.Distributional OriginalValues OriginalPopulation
open SourceTailNoisyFixedPoint NativeZeroNoiseSource NativeLocalPolicy
open ZeroNativeCategories NativeDeletedCounts OriginalFiniteFibers

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (hdR : P.d0< D.R) (H : ℝ) (hUH : D.U< H)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht)
  (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀ v,t< v → H≤ upperBid v) (N : ℕ)

local notation "E" => regions D P hdR H hUH
local notation "z" => activeMass P.theta*P.zeta*powerTail P.M 10 t
local notation "m" => N+1
variable (hrare : (1-D.ξ)*D.U+D.ξ*D.U*(((N+1:ℕ):ℝ)*
  ((activeMass P.theta*P.zeta*powerTail P.M 10 t)/
    (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t)))≤ D.R)

include hrare in
private lemma fiberRare : (1-D.ξ)*D.U+D.ξ*D.U*(((N:ℝ)+1)*
    ((activeMass P.theta*P.zeta*powerTail P.M 10 t)/
      (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t)))≤ D.R := by
  simpa only [Nat.cast_add,Nat.cast_one] using hrare

local notation "Γ" => game D P t ht hdR H hUH πL π upperBid hupperBid hfloor m hrare

def localData : NativeLocalPolicy.Data m D.c :=
  NativeSourcePolicy.data E P rfl t ht.le πL
    («partial» D P t ht π) (active D P t ht π)
    upperBid hupperBid hfloor m D.c D.ξ D.width D.regimeShare D.eA D.eR D.F
    D.hξ D.hξ1 D.hw D.regimeShare.2.1 D.regimeShare.2.2 hrare (base_duplicate_gap D)

def publicData : PublicScenario.Data :=
  NativeSourcePolicy.publicData E P rfl t ht.le πL
    («partial» D P t ht π) (active D P t ht π)
    upperBid hupperBid hfloor D.c D.ξ D.regimeShare D.eA D.eR D.F
    D.regimeShare.2.1 D.regimeShare.2.2

def coreGame : FiniteGame m 2 D.c Seed :=
  NativeSourcePosterior.game E P rfl t ht.le πL
    («partial» D P t ht π) (active D P t ht π)
    upperBid hupperBid hfloor m D.c D.ξ D.width D.regimeShare D.eA D.eR D.F
    D.hξ D.hξ1 D.hw D.regimeShare.2.1 D.regimeShare.2.2 hrare
    (base_duplicate_gap D) D.eta D.heta0 D.heta1

local notation "K" => localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
local notation "Q" => publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor
local notation "Γ₀" => coreGame D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare

@[simp] theorem localData_regions : (K).E=E := rfl
@[simp] theorem coreGame_policy : (Γ₀).policy=(K).completedPolicy := rfl
@[simp] theorem sourceGame_seed : (Γ).seedLaw=NativeLocalPolicy.seedLaw := rfl
@[simp] theorem sourceGame_schedule :
    (Γ).A=Schedule.affine 2 D.eta D.heta0 D.heta1 := rfl

theorem sourceGame_focalCount (i : Fin m) (a : JointAction 2) (ω : Sample m 2 Seed) :
    focalCount Γ i a ω=focalCount Γ₀ i a ω :=
  FeasibleListNormalization.focalCount_eq Γ₀ i a ω

theorem sourceGame_problem (i : Fin m) : problem Γ i=problem Γ₀ i :=
  FeasibleListNormalization.problem_eq Γ₀ i

theorem localData_signalLaw (h : Fin (m+1)) :
    WeakProbability.toMeasure ((K).signalLaw h)=
      WeakProbability.toMeasure (ZeroNoiseFiniteGame.privateBayes (installOriginal D P t ht) h.val
        (CompactSourceBidLaws.bidMarginal (π 2).1)) := by
  rw [←(K).signalLaw_exact]
  exact ZeroNativeRowLaws.original_sorted_private_signal D P t ht hdR H hUH
    πL π upperBid hupperBid hfloor h.val

theorem localData_signalProbability (h : Fin (m+1)) :
    ((K).signalLaw h).val=(ZeroNoiseFiniteGame.privateBayes (installOriginal D P t ht) h.val
      (CompactSourceBidLaws.bidMarginal (π 2).1)).val := by
  apply ProbabilityMeasure.toMeasure_injective
  exact localData_signalLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare h

theorem localData_signal (h : Fin (m+1)) :
    (K).signalLaw h=ZeroNoiseFiniteGame.privateBayes (installOriginal D P t ht) h.val
      (CompactSourceBidLaws.bidMarginal (π 2).1) := by
  cases he : (K).signalLaw h
  cases he' : ZeroNoiseFiniteGame.privateBayes (installOriginal D P t ht) h.val
      (CompactSourceBidLaws.bidMarginal (π 2).1)
  congr 1
  simpa only [he,he'] using
    localData_signalProbability D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare h

theorem localData_marksLaw (h : Fin (m+1)) :
    (K).marksLaw h=(installOriginal D P t ht).marksLaw h.val := by
  apply FiniteLaw.ext
  intro r
  have hm := ZeroNativeRowLaws.original_sorted_marks D P t ht hdR H hUH
    πL π upperBid hupperBid hfloor h.val
  have hm' := ((K).marksLaw_exact h).symm.trans hm
  have he := congrArg (fun μ : Measure (EqualPrivateSignal.Marks h.val) => (μ {r}).toReal) hm'
  simpa only [FiniteLaw.probabilityMeasure_singleton,
    ENNReal.toReal_ofReal ((K).marksLaw h |>.nonneg r),
    ENNReal.toReal_ofReal ((installOriginal D P t ht).marksLaw h.val |>.nonneg r)] using he

@[simp] theorem publicData_marksLaw (h : Fin (m+1)) : (Q).marksLaw h.val=(K).marksLaw h := rfl

@[simp] theorem localData_publicChoice (A : ℕ) :
    (K).publicChoice A=PublicScenario.localChoice E Q (LowBody.realLowBidLaw πL.1) A := rfl

include N in
theorem source_lowBidLaw :
    NativeFlag.nativeLowBidLaw Γ E=(LowBody.realLowBidLaw πL.1 : Measure ℝ) := by
  exact OriginalLowConditional.native_lowBidLaw_eq E Γ (lowMass P.theta)
    (activeMass P.theta-z) (partialMass+z) P.low_mass_pos _
    (native_original_exact_low_row E P rfl t ht.le πL
      («partial» D P t ht π) (active D P t ht π)
      upperBid hupperBid hfloor Γ
      (game_original_joint D P t ht hdR H hUH πL π upperBid hupperBid hfloor m hrare))

theorem source_user_bands :
    ∀ᵐ x ∂userLaw Γ,sourceBands P E t x.1 := by
  rw [game_original_user]
  exact (measurePreserving_fst (ν:=permLaw 2)).quasiMeasurePreserving.ae
    (originalJoint_sourceBands P E rfl t ht.le πL
      («partial» D P t ht π) (active D P t ht π)
      upperBid hupperBid hfloor)

include N in
theorem conditional_user_bands (k : Fin 4) :
    ∀ᵐ x ∂cond (userLaw Γ) ((E).coarseTag ⁻¹' {k}),
      sourceBands P E t x.1 ∧ (E).coarseTag x=k := by
  have hband : ∀ᵐ x ∂cond (userLaw Γ) ((E).coarseTag ⁻¹' {k}),
      sourceBands P E t x.1 := ProbabilityTheory.cond_absolutelyContinuous.ae_le
    (source_user_bands D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare)
  have htag : ∀ᵐ x ∂cond (userLaw Γ) ((E).coarseTag ⁻¹' {k}),(E).coarseTag x=k := by
    unfold ProbabilityTheory.cond
    exact Measure.ae_smul_measure
      (ae_restrict_mem ((measurableSet_singleton k).preimage (E).measurable_coarseTag)) _
  exact hband.and htag

theorem fiber_support (kind : Fin N → Fin 4) :
    ∀ᵐ w ∂fiberMeasure D P t ht hdR H hUH πL π upperBid hupperBid hfloor N
      (fiberRare D P t N hrare) kind,
      ∀ r,sourceBands P E t (w.1.1 r).1 ∧ (E).coarseTag (w.1.1 r)=kind r := by
  haveI (r : Fin N) : IsProbabilityMeasure
      (cond (userLaw Γ) ((E).coarseTag ⁻¹' {kind r})) :=
    cond_isProbabilityMeasure (native_source_category_ne_zero D P t ht hdR H hUH
      πL π upperBid hupperBid hfloor Γ
      (game_original_joint D P t ht hdR H hUH πL π upperBid hupperBid hfloor m hrare) (kind r))
  have hp : ∀ᵐ w ∂Measure.pi (fun r : Fin N =>
      cond (userLaw Γ) ((E).coarseTag ⁻¹' {kind r})),
      ∀ r,sourceBands P E t (w r).1 ∧ (E).coarseTag (w r)=kind r :=
    ae_all_iff.mpr (fun r => (measurePreserving_eval (fun s : Fin N =>
      ProbabilityTheory.cond (userLaw Γ) ((E).coarseTag ⁻¹' {kind s})) r).quasiMeasurePreserving.ae
      (conditional_user_bands D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare (kind r)))
  have hp' := (measurePreserving_fst
    (ν:=Measure.pi (fun _ : Fin 2=>(Γ).seedLaw))).quasiMeasurePreserving.ae hp
  exact (measurePreserving_fst (ν:=permLaw 2)).quasiMeasurePreserving.ae hp'

lemma restoreUsers_succAbove (i : Fin m) (r : Fin N → UserDraw 2) (j : Fin N) :
    restoreUsers i r (i.succAbove j)=r j := by
  have he := congrArg (fun pair : UserDraw 2×(Fin N → UserDraw 2) => pair.2 j)
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin m => UserDraw 2) i).apply_symm_apply
      (dummyDraw,r))
  exact he

lemma restored_source_rivals (i : Fin m) (w : DeletedSample N Seed)
    (hw : ∀ r,sourceBands P E t (w.1.1 r).1) :
    ∀ l,l≠i → sourceBands P E t ((restoreSample i w).1.1 l).1 := by
  intro l hl
  obtain ⟨r,rfl⟩ := Fin.exists_succAbove_eq hl
  simpa only [restoreSample,restoreUsers_succAbove] using hw r

lemma restored_kind (i : Fin m) (w : DeletedSample N Seed) (kind : Fin N → Fin 4)
    (hw : ∀ r,(E).coarseTag (w.1.1 r)=kind r) :
    PartialNativeCoordinates.rivalKinds E i (restoreSample i w).1=kind := by
  funext r
  simpa only [PartialNativeCoordinates.rivalKinds,restoreSample,restoreUsers_succAbove] using hw r

include ht πL π upperBid hupperBid hfloor N hrare in
theorem source_active_count (i : Fin m) (b : Icc (1:ℝ) (E).U)
    (ω : Sample m 2 Seed) (hr : ∀ l,l≠i → sourceBands P E t (ω.1.1 l).1) :
    let a := RawRoutes.action b ((by norm_num : (0:ℝ)≤1).trans b.2.1) 2
    let L := observe (deviated i a ω) 0
    let hi := NativeMenuReports.active_focal_present K i b ω 0
    focalCount Γ i a ω=
      originalPairCount
        ((K).zeroSampler (LocalCoordinates.ids E 1 L).card ((K).finiteCount (LocalCoordinates.ids E 2 L))
          ((K).finiteCount (LocalCoordinates.ids E 3 L)))
        ((K).oneSampler (LocalCoordinates.ids E 1 L).card ((K).finiteCount (LocalCoordinates.ids E 2 L))
          ((K).finiteCount (LocalCoordinates.ids E 3 L)))
        ((K).parameter (LocalCoordinates.ids E 1 L) ((K).finiteCount (LocalCoordinates.ids E 2 L))
          ((K).finiteCount (LocalCoordinates.ids E 3 L)) L)
        (Sum.inl (SortedCoordinates.rankFin (LocalCoordinates.ids E 1 L) (LocalCoordinates.bidVector L) ⟨i,hi⟩))
        (Sum.inl (SortedCoordinates.rankFin (LocalCoordinates.ids E 1 L) (LocalCoordinates.bidVector L) ⟨i,hi⟩))
        ((LocalCoordinates.privateRow E (LocalCoordinates.ids E 2 L) L,(ω.1.2 0).1),
          (LocalCoordinates.privateRow E (LocalCoordinates.ids E 3 L) (observe (deviated i a ω) 1),
            (ω.1.2 1).1)) := by
  dsimp only
  rw [sourceGame_focalCount]
  exact NativeMenuReports.native_active_focal_count K P t Γ₀ rfl i b ω hr

theorem source_partial_count (i : Fin m) (b : Icc (E).R (E).Rp) (k : Fin 3)
    (ω : Sample m 2 Seed) (hr : ∀ l,l≠i → sourceBands P E t (ω.1.1 l).1) :
    focalCount Γ i (RawRoutes.action b (((E).d_nonneg.trans (E).d_lt_R.le).trans b.2.1) k) ω=
      boolPairCount
        ((if (0:Fin 2)∈firstK ω.2 k.val then NativeMenuReports.privateZeroAccept K i b ω.1 else false),
          (if (1:Fin 2)∈firstK ω.2 k.val then NativeMenuReports.privateOneAccept K i b ω.1 else false)) := by
  rw [sourceGame_focalCount]
  exact NativeMenuReports.native_partial_focal_count K P t Γ₀ rfl i b k ω hr

end FCAppendix.Affine.Tail04.ZeroNativeBindings
