import FCAppendix.Affine.Tail04.NativeMenuReports
import FCAppendix.Affine.Tail04.OrderedNoisyNativeCategories
import FCAppendix.Affine.Tail04.OrderedNativeCommonCount
import FCAppendix.Affine.Tail04.OrderedNativePrivateCount
import FCAppendix.Affine.Tail04.NoisyNativeFiberProduct
import FCAppendix.Affine.Tail04.PartialNativeCoordinates

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedNativePayoffBindings
open MeasureTheory ProbabilityTheory Set Classical Game Bayes Filter
open Existence.Distributional OriginalValues OriginalPopulation
open SourceTailNoisyFixedPoint OrderedNativeNoisySource NativeLocalPolicy
open OrderedNoisyNativeCategories NativeDeletedCounts OriginalFiniteFibers

private lemma castMarketRare {N : ℕ} {x y p q : ℝ}
    (h : x+y*((N+1:ℝ)*p)≤q) : x+y*((((N+1:ℕ):ℝ))*p)≤q := by
  simpa only [Nat.cast_add,Nat.cast_one] using h

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht)
  (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀ v,t< v → H≤ upperBid v) (N : ℕ)

local notation "E" => regions D P hdR H hBH
local notation "z" => activeMass P.theta*P.zeta*powerTail P.M 10 t
local notation "m" => N+1
variable (hrare : (1-D.ξ)*D.B+D.ξ*D.B*((N+1:ℝ)*
  ((activeMass P.theta*P.zeta*powerTail P.M 10 t)/
    (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t)))≤ D.R)
local notation "Γ" => game D P t ht hdR H hBH πL π upperBid hupperBid hfloor m (castMarketRare hrare)

def localData : NativeLocalPolicy.Data m D.c :=
  NativeSourcePolicy.data E P rfl t ht.le πL
    (partialPhysical D P t ht π) (activePhysical D P t ht π)
    upperBid hupperBid hfloor m D.c D.ξ D.width D.regimeShare D.eA D.eR D.F
    D.hξ D.hξ1 D.hw D.regimeShare.2.1 D.regimeShare.2.2 (castMarketRare hrare) (duplicate_gap D)

def publicData : PublicScenario.Data :=
  NativeSourcePolicy.publicData E P rfl t ht.le πL
    (partialPhysical D P t ht π) (activePhysical D P t ht π)
    upperBid hupperBid hfloor D.c D.ξ D.regimeShare D.eA D.eR D.F
    D.regimeShare.2.1 D.regimeShare.2.2

def coreGame : FiniteGame m 2 D.c Seed :=
  OrderedNativeSourcePosterior.game E P rfl t ht.le πL
    (partialPhysical D P t ht π) (activePhysical D P t ht π)
    upperBid hupperBid hfloor m D.c D.ξ D.width D.regimeShare D.eA D.eR D.F
    D.hξ D.hξ1 D.hw D.regimeShare.2.1 D.regimeShare.2.2 (castMarketRare hrare)
    (duplicate_gap D) D.eta D.heta0 D.heta1

local notation "K" => localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
local notation "Q" => publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor
local notation "Γ₀" => coreGame D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare

@[simp] theorem localData_regions : (K).E=E := rfl
@[simp] theorem coreGame_policy : (Γ₀).policy=OrderedNativePolicy.policy K := rfl
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
      ProbabilityMeasure.toMeasure ((installOriginal D P t ht).privateBayes h.val
        (CompactSourceBidLaws.bidMarginal (π 2).1)) := by
  rw [←(K).signalLaw_exact]
  exact NoisyNativeRowLaws.original_sorted_private_signal D P t ht hdR H hBH
    πL π upperBid hupperBid hfloor h.val

theorem localData_signalProbability (h : Fin (m+1)) :
    ((K).signalLaw h).val=(installOriginal D P t ht).privateBayes h.val
      (CompactSourceBidLaws.bidMarginal (π 2).1) := by
  apply ProbabilityMeasure.toMeasure_injective
  exact localData_signalLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare h

theorem localData_marksLaw (h : Fin (m+1)) :
    (K).marksLaw h=(installOriginal D P t ht).marksLaw h.val := by
  apply FiniteLaw.ext
  intro r
  have hm := NoisyNativeRowLaws.original_sorted_marks D P t ht hdR H hBH
    πL π upperBid hupperBid hfloor h.val
  have hm' := ((K).marksLaw_exact h).symm.trans hm
  have he := congrArg (fun μ : Measure (EqualPrivateSignal.Marks h.val) => (μ {r}).toReal) hm'
  simpa only [FiniteLaw.probabilityMeasure_singleton,
    ENNReal.toReal_ofReal ((K).marksLaw h |>.nonneg r),
    ENNReal.toReal_ofReal ((installOriginal D P t ht).marksLaw h.val |>.nonneg r)] using he

@[simp] theorem publicData_marksLaw (h : Fin (m+1)) : (Q).marksLaw h.val=(K).marksLaw h := rfl

@[simp] theorem localData_publicChoice (A : ℕ) :
    (K).publicChoice A=PublicScenario.localChoice E Q (LowBody.realLowBidLaw πL.1) A := rfl

theorem source_lowBidLaw :
    NativeFlag.nativeLowBidLaw Γ E=(LowBody.realLowBidLaw πL.1 : Measure ℝ) := by
  exact OriginalLowConditional.native_lowBidLaw_eq E Γ (lowMass P.theta)
    (activeMass P.theta-z) (partialMass+z) P.low_mass_pos _
    (native_original_exact_low_row E P rfl t ht.le πL
      (partialPhysical D P t ht π) (activePhysical D P t ht π)
      upperBid hupperBid hfloor Γ
      (game_original_joint D P t ht hdR H hBH πL π upperBid hupperBid hfloor m (castMarketRare hrare)))

theorem source_user_bands :
    ∀ᵐ x ∂userLaw Γ,sourceBands P E t x.1 := by
  rw [game_original_user]
  exact (measurePreserving_fst (ν:=permLaw 2)).quasiMeasurePreserving.ae
    (originalJoint_sourceBands P E rfl t ht.le πL
      (partialPhysical D P t ht π) (activePhysical D P t ht π)
      upperBid hupperBid hfloor)

theorem conditional_user_bands (k : Fin 4) :
    ∀ᵐ x ∂cond (userLaw Γ) ((E).coarseTag ⁻¹' {k}),
      sourceBands P E t x.1 ∧ (E).coarseTag x=k := by
  have hband : ∀ᵐ x ∂cond (userLaw Γ) ((E).coarseTag ⁻¹' {k}),
      sourceBands P E t x.1 := ProbabilityTheory.cond_absolutelyContinuous.ae_le
    (source_user_bands D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare)
  have htag : ∀ᵐ x ∂cond (userLaw Γ) ((E).coarseTag ⁻¹' {k}),(E).coarseTag x=k := by
    unfold ProbabilityTheory.cond
    exact Measure.ae_smul_measure
      (ae_restrict_mem ((measurableSet_singleton k).preimage (E).measurable_coarseTag)) _
  exact hband.and htag

theorem fiber_support (kind : Fin N → Fin 4) :
    ∀ᵐ w ∂fiberMeasure D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare kind,
      ∀ r,sourceBands P E t (w.1.1 r).1 ∧ (E).coarseTag (w.1.1 r)=kind r := by
  haveI (r : Fin N) : IsProbabilityMeasure
      (cond (userLaw Γ) ((E).coarseTag ⁻¹' {kind r})) :=
    cond_isProbabilityMeasure (native_source_category_ne_zero D P t ht hdR H hBH
      πL π upperBid hupperBid hfloor Γ
      (game_original_joint D P t ht hdR H hBH πL π upperBid hupperBid hfloor m (castMarketRare hrare)) (kind r))
  have hp : ∀ᵐ w ∂Measure.pi (fun r : Fin N =>
      cond (userLaw Γ) ((E).coarseTag ⁻¹' {kind r})),
      ∀ r,sourceBands P E t (w r).1 ∧ (E).coarseTag (w r)=kind r :=
    ae_all_iff.mpr (fun r => (measurePreserving_eval (fun s : Fin N =>
      ProbabilityTheory.cond (userLaw Γ) ((E).coarseTag ⁻¹' {kind s})) r).quasiMeasurePreserving.ae
      (conditional_user_bands D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare (kind r)))
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

theorem source_active_count (i : Fin m) (b : Icc (1:ℝ) (E).U)
    (ω : Sample m 2 Seed) (hr : ∀ l,l≠i → sourceBands P E t (ω.1.1 l).1) :
    let a := RawRoutes.action b ((by norm_num : (0:ℝ)≤1).trans b.2.1) 2
    let L := observe (deviated i a ω) 0
    let O := observe (deviated i a ω) 1
    focalCount Γ i a ω=
      NativeCountCoordinates.listPairCount K
        (OrderedNativeCountCoordinates.zeroList K L O)
        (OrderedNativeCountCoordinates.oneList K L O) i
        (OrderedNativeCountCoordinates.zeroSeed K L (ω.1.2 0) (ω.1.2 1))
        (OrderedNativeCountCoordinates.oneSeed K L (ω.1.2 0) (ω.1.2 1)) := by
  dsimp only
  rw [sourceGame_focalCount D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare]
  change Game.boundedCount _ (Γ₀).policy _ _=_
  rw [coreGame_policy,OrderedNativeCountCoordinates.boundedCount_eq_pair]
  exact OrderedNativeCountCoordinates.pair_eq_restored K
    (NativeMenuReports.compatible_deviation E i _ ω
      (NativeMenuReports.active_report_menu K b)
      (fun l hl => NativeMenuReports.source_menu E P t _ (hr l hl))) i
      (ω.1.2 0) (ω.1.2 1)

def privateAccept (i : Fin m) (b : Icc (E).R (E).Rp)
    (ω : Background m 2 Seed) (j : Fin 2) : Bool :=
  OrderedNativePrivateCount.privateDecision K j (presentList ω i b j) i (ω.2 j)

lemma privateAccept_eq (i : Fin m) (b : Icc (E).R (E).Rp)
    (ω : Background m 2 Seed)
    (hr : ∀ l,l≠i → sourceBands P E t (ω.1 l).1) (j : Fin 2) :
    privateAccept D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare i b ω j=
      decide (i∈(OrderedNativePolicy.policy K j (presentList ω i b j) (ω.2 j)).val) :=
  OrderedNativePrivateCount.privateDecision_eq K j _
    (NativeMenuReports.onMenu_present_partial K P t i b ω hr j) i
    (Or.inl (NativeMenuReports.partial_present_ids K i b ω j)) (ω.2 j)

theorem source_partial_count (i : Fin m) (b : Icc (E).R (E).Rp) (k : Fin 3)
    (ω : Sample m 2 Seed) (hr : ∀ l,l≠i → sourceBands P E t (ω.1.1 l).1) :
    focalCount Γ i (RawRoutes.action b (((E).d_nonneg.trans (E).d_lt_R.le).trans b.2.1) k) ω=
      boolPairCount
        ((if (0:Fin 2)∈firstK ω.2 k.val then
          privateAccept D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
            i b ω.1 0 else false),
         (if (1:Fin 2)∈firstK ω.2 k.val then
          privateAccept D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
            i b ω.1 1 else false)) := by
  rw [sourceGame_focalCount D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare]
  rw [privateAccept_eq D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
      i b ω.1 hr 0,
    privateAccept_eq D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
      i b ω.1 hr 1]
  apply Fin.ext
  simp only [focalCount,Game.boundedCount,inclusionCount_eq_sum,Fin.sum_univ_two,
    boolPairCount]
  simp only [mem_allocation_deviated_iff Γ₀ i _ ω 0,
    mem_allocation_deviated_iff Γ₀ i _ ω 1]
  simp only [Accepts,coreGame_policy,RawRoutes.action]
  by_cases h0 : (0:Fin 2)∈firstK ω.2 k.val <;>
    by_cases h1 : (1:Fin 2)∈firstK ω.2 k.val <;>
      simp [h0,h1]

end FCAppendix.Affine.Tail04.OrderedNativePayoffBindings
