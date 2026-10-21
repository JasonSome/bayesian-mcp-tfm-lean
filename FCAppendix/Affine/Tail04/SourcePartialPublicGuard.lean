import FCAppendix.Affine.Tail04.PartialSortedCompression
import FCAppendix.Affine.Tail04.NativeSourcePolicy
import FCAppendix.Affine.Tail04.PartialNativeGuardIntegration
import FCAppendix.Affine.Tail04.PartialNativeRegime
import FCAppendix.Affine.Tail04.OriginalLowConditional

noncomputable section
namespace FCAppendix.Affine.Tail04.SourcePartialPublicGuard
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation OriginalPrivateSource
open MenuError NativeTypicalCount EqualPrivateSignal Hybrid
open SourceMenuPopulation SourceMenuError SourceMomentRectangle
open NativeLocalPolicy NativeActiveFiberCoordinates PartialNativePublicWeight
open PartialSortedCompression OriginalFlagCompression OriginalNoiseProduct JoinedHighPolicy
open PartialNativeEvents PartialNativeCategoryBounds PartialNativeGuardIntegration
open scoped BigOperators
open Filter Topology

abbrev RowSpace (N : ℕ) := (Fin N→ UserDraw 2)×(Fin N→ unitInterval)

def rowLaw {m c N : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) : Measure (RowSpace N) :=
  (Measure.pi (fun _ : Fin N => userLaw Γ)).prod
    (Measure.pi (fun _ : Fin N => (volume : Measure unitInterval)))

instance {m c N : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) : IsProbabilityMeasure (rowLaw (N:=N) Γ) := by
  unfold rowLaw;infer_instance

def bad {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (P : ValueParameters) (E : Observable.Regions)
    (ξ : ℝ) (N : ℕ) (reg : Bool) : Set (RowSpace N) :=
  sourceFiveBad (userLaw Γ) N (zipRow N)
    (categoryFlag E 1) (categoryFlag E 2) (categoryFlag E 3)
    (nativeFlag P ξ reg) nativeBid (radius ξ (centerMoment P reg))

lemma measurableSet_bad {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (P : ValueParameters) (E : Observable.Regions)
    (ξ : ℝ) (N : ℕ) (reg : Bool) : MeasurableSet (bad Γ P E ξ N reg) :=
  measurableSet_sourceFiveBad (userLaw Γ) (rowLaw Γ) N (zipRow N)
    (zipRow_preserves (userLaw Γ) (volume : Measure unitInterval) N)
    (categoryFlag E 1) (categoryFlag E 2) (categoryFlag E 3)
    (measurable_categoryFlag E 1) (measurable_categoryFlag E 2) (measurable_categoryFlag E 3)
    (nativeFlag P ξ reg) (measurable_nativeFlag P ξ reg) nativeBid measurable_nativeBid _

def error (P : ValueParameters) (ξ : ℝ) (N : ℕ) : ℝ :=
  (1-P.theta)*(10*Real.exp (-(N:ℝ)*(radius ξ (centerMoment P false))^2/50))+
    P.theta*(10*Real.exp (-(N:ℝ)*(radius ξ (centerMoment P true))^2/50))

lemma error_nonnegative (P : ValueParameters) (ξ : ℝ) (N : ℕ) : 0≤ error P ξ N := by
  have ht := P.theta_small
  have ht0 := P.theta_pos
  have ht1 : 0 ≤ 1-P.theta := by linarith
  unfold error
  positivity

def badBound (P : ValueParameters) (ξ : ℝ) (N : ℕ) : ℝ :=
  (75/2:ℝ)/Real.sqrt N+2*error P ξ N+
    Real.exp (-(N:ℝ)*(lowMass P.theta)^2/2)

lemma badBound_nonnegative (P : ValueParameters) (ξ : ℝ) (N : ℕ) : 0≤ badBound P ξ N := by
  have he := error_nonnegative P ξ N
  unfold badBound
  positivity

lemma exponential_tendsto_zero {d : ℝ} (hd : 0< d) :
    Tendsto (fun N : ℕ => Real.exp (-(N:ℝ)*d)) atTop (𝓝 0) := by
  have hn : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  convert! Real.tendsto_exp_neg_atTop_nhds_zero.comp (hn.const_mul_atTop hd) using 1
  funext N
  congr 1
  ring

lemma guard_radius_positive (P : ValueParameters) {ξ : ℝ} (hξ : 0< ξ) (reg : Bool) :
    0< radius ξ (centerMoment P reg) := by
  have hm := centerMoment_pos P reg
  unfold radius γ
  positivity

theorem badBound_tendsto_zero (P : ValueParameters) {ξ : ℝ} (hξ : 0< ξ) :
    Tendsto (badBound P ξ) atTop (𝓝 0) := by
  have hn : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hs : Tendsto (fun N : ℕ => (75/2:ℝ)/Real.sqrt N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hn)
  have he (reg : Bool) : Tendsto
      (fun N : ℕ => 10*Real.exp (-(N:ℝ)*(radius ξ (centerMoment P reg))^2/50)) atTop (𝓝 0) := by
    have hd : 0<(radius ξ (centerMoment P reg))^2/50 := by
      exact div_pos (sq_pos_of_pos (guard_radius_positive P hξ reg)) (by norm_num)
    have hh := (exponential_tendsto_zero hd).const_mul 10
    convert! hh using 1
    · funext N
      congr 2
      ring
    · simp
  have hlow : 0<(lowMass P.theta)^2/2 :=
    div_pos (sq_pos_of_pos P.low_mass_pos) (by norm_num)
  have hl : Tendsto (fun N : ℕ => Real.exp (-(N:ℝ)*(lowMass P.theta)^2/2)) atTop (𝓝 0) := by
    convert! exponential_tendsto_zero hlow using 1
    funext N
    congr 1
    ring
  have hh := (hs.add ((((he false).const_mul (1-P.theta)).add
    ((he true).const_mul P.theta)).const_mul 2)).add hl
  change Tendsto (fun N : ℕ => (75/2:ℝ)/Real.sqrt N+2*error P ξ N+
    Real.exp (-(N:ℝ)*(lowMass P.theta)^2/2)) atTop (𝓝 0)
  simpa only [error,mul_zero,add_zero] using hh

theorem eventually_room (P : ValueParameters) {ξ : ℝ} (hξ : 0< ξ) :
    ∀ᶠ N : ℕ in atTop,∀ reg,8/(N:ℝ)≤ radius ξ (centerMoment P reg) := by
  have hn : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have he : Tendsto (fun N : ℕ => (8:ℝ)/N) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hn
  have h0 := he.eventually (gt_mem_nhds (guard_radius_positive P hξ false))
  have h1 := he.eventually (gt_mem_nhds (guard_radius_positive P hξ true))
  filter_upwards [h0,h1] with N hN0 hN1
  intro reg
  cases reg
  · exact hN0.le
  · exact hN1.le

section Source
variable {N : ℕ} (P : ValueParameters) (E : Observable.Regions) (hd : E.d=P.d0)
  (t : ℝ) (ht : P.M< t) (u : ℝ) (hu : 0≤ u) (huE : 1+u≤ E.U)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (πP : Law (A:=Icc E.R E.Rp) P.originalPartialLaw)
  (πB : Law (A:=Icc (1:ℝ) (1+u)) P.originalBulkLaw)
  (πT : Law (A:=Icc (1:ℝ) E.U) (P.originalTruncatedTailLaw t ht))
  (upperBid : ℝ→ℝ) (hupper : Measurable upperBid)
  (hfloor : ∀ v,t< v → E.H≤ upperBid v)
  (ξ width : ℝ) (hξ : 0< ξ) (hξh : ξ<1/2) (hw : 0< width)
  (hrare : (1-ξ)*E.U+ξ*E.U*(((N+1:ℕ):ℝ)*(upperMass P t/(partialMass+upperMass P t)))≤ E.R)
  (hdup : (1-ξ)*E.U<1)

variable (Γ : FiniteGame (N+1) 2 (iidCapacity (99/200) N) NativeLocalPolicy.Seed)
  (hjoint : Γ.F⊗ₘΓ.σ=(originalJoint P t ht.le E.R E.Rp E.U
    (E.d_nonneg.trans E.d_lt_R.le) πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper : Measure _))
  (hN : 0< N) (huB : 1+u< Central.B ξ) (hEB : E.U≤ Central.B ξ)
  (hR : E.R=Central.R ξ) (hRp : E.Rp≤ Central.R ξ+ξ/1000)
  (hsmall : relativeError P.zeta u (Central.B ξ)≤ ξ/1000)
  (hmSmall : upperMass P t≤ Central.mixedR (P.theta^2)/1000)
  (hwγ : width≤ γ ξ)
  (hroom : ∀ reg,8/(N:ℝ)≤ radius ξ (centerMoment P reg))

theorem source_marks_mean (reg : Bool) (H : Fin (N+2)) :
    privateMean H.val reg ((NativeSourcePolicy.data E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor (N+1) (iidCapacity (99/200) N) ξ width P.theta (SourceNoisyData.eA P) (SourceNoisyData.eR P) (Central.B ξ) hξ (by linarith) hw P.theta_pos.le (by linarith [P.theta_small]) hrare hdup).marksLaw H)=keptShare P t reg*H.val := by
  have hcount := originalPrivateRow_countMean E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT)
    upperBid hupper hfloor H.val
  have hm := privateMean_regime_of_countMean H.val reg ((NativeSourcePolicy.data E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor (N+1) (iidCapacity (99/200) N) ξ width P.theta (SourceNoisyData.eA P) (SourceNoisyData.eR P) (Central.B ξ) hξ (by linarith) hw P.theta_pos.le (by linarith [P.theta_small]) hrare hdup).marksLaw H)
    (upperMass P t/(partialMass+upperMass P t)) hcount
  rw [hm]
  cases reg <;> simp only [keptShare,Bool.false_eq_true,if_false,if_true,one_mul]
  ring

include hd u hu huE πL πP πB πT upperBid hupper hfloor hξ hξh hw hjoint hN huB hEB hR hRp hsmall hmSmall hwγ hroom in
theorem source_common_guard (reg : Bool) :
    (rowLaw Γ).real (bad Γ P E ξ N reg)≤
      10*Real.exp (-(N:ℝ)*(radius ξ (centerMoment P reg))^2/50) ∧
    ∀ z,z∉bad Γ P E ξ N reg → ∀ target : RowSpace N→ Fin (N+1),∀ side : Fin 2,
      partialGuardWeight N (zipRow N) target
        (categoryFlag E 1) (categoryFlag E 2) (categoryFlag E 3)
        (nativeFlag P ξ reg) nativeBid ξ (keptShare P t reg) (99/200)
        E.U E.R E.Rp width (keptShare_bounds P t ht.le reg).1 reg side z=1 := by
  have h := native_partial_common_guard Γ P E hd t ht u hu huE πL πP πB πT
    upperBid hupper hfloor hjoint ξ hξ hξh huB hEB hR hRp hsmall hmSmall
    (rowLaw Γ) N hN (zipRow N)
    (zipRow_preserves (userLaw Γ) (volume : Measure unitInterval) N)
    width hw hwγ reg (hroom reg)
  exact h.2

lemma fiberWeight_eq_draw_weight (i : Fin (N+1)) (kind : Fin N→ Fin 4)
    (side : Fin 2) (r : Fin N→ UserDraw 2) (z : unitInterval) :
    fiberWeight (NativeSourcePolicy.data E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor (N+1) (iidCapacity (99/200) N) ξ width P.theta (SourceNoisyData.eA P) (SourceNoisyData.eR P) (Central.B ξ) hξ (by linarith) hw P.theta_pos.le (by linarith [P.theta_small]) hrare hdup) (NativeSourcePolicy.publicData E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor (iidCapacity (99/200) N) ξ P.theta (SourceNoisyData.eA P) (SourceNoisyData.eR P) (Central.B ξ) P.theta_pos.le (by linarith [P.theta_small])) i kind side (r,z)=
      PublicWeightLaw.weight (NativeSourcePolicy.publicData E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor (iidCapacity (99/200) N) ξ P.theta (SourceNoisyData.eA P) (SourceNoisyData.eR P) (Central.B ξ) P.theta_pos.le (by linarith [P.theta_small])) (commonSize i kind)
        ((partialPrivateFin (NativeSourcePolicy.data E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor (N+1) (iidCapacity (99/200) N) ξ width P.theta (SourceNoisyData.eA P) (SourceNoisyData.eR P) (Central.B ξ) hξ (by linarith) hw P.theta_pos.le (by linarith [P.theta_small]) hrare hdup) i kind side 0).val,(partialPrivateFin (NativeSourcePolicy.data E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor (N+1) (iidCapacity (99/200) N) ξ width P.theta (SourceNoisyData.eA P) (SourceNoisyData.eR P) (Central.B ξ) hξ (by linarith) hw P.theta_pos.le (by linarith [P.theta_small]) hrare hdup) i kind side 1).val)
        E.U E.R E.Rp width
        (TypicalGuard.bids (SortedAllNoise.sortedBox (commonRow E i kind r)))
        (PublicScenario.draw (NativeSourcePolicy.publicData E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor (iidCapacity (99/200) N) ξ P.theta (SourceNoisyData.eA P) (SourceNoisyData.eR P) (Central.B ξ) P.theta_pos.le (by linarith [P.theta_small])) (commonSize i kind)
          (TypicalGuard.bids (SortedAllNoise.sortedBox (commonRow E i kind r)),
            ((partialPrivateFin (NativeSourcePolicy.data E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor (N+1) (iidCapacity (99/200) N) ξ width P.theta (SourceNoisyData.eA P) (SourceNoisyData.eR P) (Central.B ξ) hξ (by linarith) hw P.theta_pos.le (by linarith [P.theta_small]) hrare hdup) i kind side 0).val,(partialPrivateFin (NativeSourcePolicy.data E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor (N+1) (iidCapacity (99/200) N) ξ width P.theta (SourceNoisyData.eA P) (SourceNoisyData.eR P) (Central.B ξ) hξ (by linarith) hw P.theta_pos.le (by linarith [P.theta_small]) hrare hdup) i kind side 1).val)) z).1 := rfl

include hu hξh hjoint hN huB hEB hR hRp hsmall hmSmall hwγ hroom in
theorem source_public_failure_bound (i : Fin (N+1)) (kind : Fin N→ Fin 4)
    (r : Fin N→ UserDraw 2) (hk : ∀ j,E.coarseTag (r j)=kind j)
    (hr : ∀ j,NativeMenuReports.MenuAction E (r j).1.2) (side : Fin 2) :
    (volume : Measure unitInterval).real {z | fiberWeight (NativeSourcePolicy.data E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor (N+1) (iidCapacity (99/200) N) ξ width P.theta (SourceNoisyData.eA P) (SourceNoisyData.eR P) (Central.B ξ) hξ (by linarith) hw P.theta_pos.le (by linarith [P.theta_small]) hrare hdup) (NativeSourcePolicy.publicData E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor (iidCapacity (99/200) N) ξ P.theta (SourceNoisyData.eA P) (SourceNoisyData.eR P) (Central.B ξ) P.theta_pos.le (by linarith [P.theta_small])) i kind side (r,z)≠1}≤
      (1-P.theta)*(Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))).real
        {z | (r,z)∈bad Γ P E ξ N false}+
      P.theta*(Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))).real
        {z | (r,z)∈bad Γ P E ξ N true} := by
  simp_rw [fiberWeight_eq_draw_weight P E hd t ht u huE πL πP πB πT upperBid hupper hfloor
    ξ width hξ hξh hw hrare hdup]
  apply PublicWeightLaw.draw_weight_failure_le_full_flags (NativeSourcePolicy.publicData E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor (iidCapacity (99/200) N) ξ P.theta (SourceNoisyData.eA P) (SourceNoisyData.eR P) (Central.B ξ) P.theta_pos.le (by linarith [P.theta_small])) (commonSize i kind)
    ((partialPrivateFin (NativeSourcePolicy.data E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor (N+1) (iidCapacity (99/200) N) ξ width P.theta (SourceNoisyData.eA P) (SourceNoisyData.eR P) (Central.B ξ) hξ (by linarith) hw P.theta_pos.le (by linarith [P.theta_small]) hrare hdup) i kind side 0).val,(partialPrivateFin (NativeSourcePolicy.data E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor (N+1) (iidCapacity (99/200) N) ξ width P.theta (SourceNoisyData.eA P) (SourceNoisyData.eR P) (Central.B ξ) hξ (by linarith) hw P.theta_pos.le (by linarith [P.theta_small]) hrare hdup) i kind side 1).val)
    E.U E.R E.Rp width
    (TypicalGuard.bids (SortedAllNoise.sortedBox (commonRow E i kind r)))
    (fun j : Fin N => categoryFlag E 1 (r j)) (sortedActiveEquiv E i kind r hk)
    (fun reg j => nativeFlag P ξ reg (r j))
    (fun reg j => source_flags (NativeSourcePolicy.data E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor (N+1) (iidCapacity (99/200) N) ξ width P.theta (SourceNoisyData.eA P) (SourceNoisyData.eR P) (Central.B ξ) hξ (by linarith) hw P.theta_pos.le (by linarith [P.theta_small]) hrare hdup) (NativeSourcePolicy.publicData E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor (iidCapacity (99/200) N) ξ P.theta (SourceNoisyData.eA P) (SourceNoisyData.eR P) (Central.B ξ) P.theta_pos.le (by linarith [P.theta_small])) P rfl (fun reg => rfl) i kind r hk hr reg j)
    (fun reg => {z | (r,z)∈bad Γ P E ξ N reg})
    (fun reg => (measurableSet_bad Γ P E ξ N reg).preimage (measurable_const.prodMk measurable_id))
  intro reg z hz
  have hg := (source_common_guard P E hd t ht u hu huE πL πP πB πT upperBid hupper hfloor
    ξ width hξ hξh hw Γ hjoint hN huB hEB hR hRp hsmall hmSmall hwγ hroom reg).2 (r,z) hz
  constructor
  · have hp := active_positive_of_weight_one (zipRow N) (fun _ : RowSpace N => 0)
      (categoryFlag E 1) (categoryFlag E 2) (categoryFlag E 3) (nativeFlag P ξ reg) nativeBid
      ξ (keptShare P t reg) (99/200) E.U E.R E.Rp width
      (keptShare_bounds P t ht.le reg).1 reg side (r,z) (hg (fun _ => 0) side)
    change 0< boolCount (fun j : Fin N => categoryFlag E 1 (r j)) at hp
    rw [active_card _ (sortedActiveEquiv E i kind r hk)] at hp
    exact hp
  · intro target
    erw [source_partial_phi (NativeSourcePolicy.data E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor (N+1) (iidCapacity (99/200) N) ξ width P.theta (SourceNoisyData.eA P) (SourceNoisyData.eR P) (Central.B ξ) hξ (by linarith) hw P.theta_pos.le (by linarith [P.theta_small]) hrare hdup) (NativeSourcePolicy.publicData E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor (iidCapacity (99/200) N) ξ P.theta (SourceNoisyData.eA P) (SourceNoisyData.eR P) (Central.B ξ) P.theta_pos.le (by linarith [P.theta_small])) rfl rfl (fun _ => rfl) rfl P t ht.le
      (source_marks_mean P E hd t ht u huE πL πP πB πT upperBid hupper hfloor
        ξ width hξ hξh hw hrare hdup) i kind r hk hr hN side reg z target]
    exact hg (fun _ => ((sortedActiveEquiv E i kind r hk target).val).succ) side

include P hd t ht u huE πL πP πB πT upperBid hupper hfloor hjoint in
lemma source_menu : ∀ᵐ x ∂Γ.F⊗ₘΓ.σ,NativeMenuReports.MenuAction E x.2 := by
  rw [hjoint]
  exact (originalJoint_sourceBands P E hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor).mono
    fun x hx => NativeMenuReports.source_menu E P t x hx

include P hd t ht u huE πL πP πB πT upperBid hupper hfloor hjoint in
lemma source_category_nonzero (k : Fin 4) :
    (userLaw Γ) (E.coarseTag ⁻¹' {k})≠0 := by
  have hz := P.tailMass_nonneg t ht.le
  change 0 ≤ upperMass P t at hz
  have ha := P.movingActiveMass_positive t ht.le
  have hsum : lowMass P.theta+(activeMass P.theta-upperMass P t)+(partialMass+upperMass P t)=1 := by
    have hh := mass_sum P.theta
    linarith
  have hrow := native_original_exact_low_row E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor Γ hjoint
  have hm := original_category_mean Γ E (lowMass P.theta) (activeMass P.theta-upperMass P t)
    (partialMass+upperMass P t) P.low_mass_pos.le ha.le
    (by norm_num [partialMass];linarith) hsum
    (LowBody.realLowBidLaw πL.1 : Measure ℝ) hrow k
  have he : (∫ x,indicator (categoryFlag E k) x ∂userLaw Γ)=
      (userLaw Γ).real (E.coarseTag ⁻¹' {k}) := by
    simp only [categoryFlag_indicator]
    simpa only [Set.indicator,Set.mem_preimage,Set.mem_singleton_iff,Pi.one_apply] using
      integral_indicator_one (μ:=userLaw Γ) (E.measurable_coarseTag (measurableSet_singleton k))
  rw [he] at hm
  have hpos : 0 < (userLaw Γ).real (E.coarseTag ⁻¹' {k}) := by
    rw [hm]
    fin_cases k
    · exact P.low_mass_pos
    · exact ha
    · norm_num [partialMass];linarith
    · norm_num [partialMass];linarith
  intro heq
  rw [measureReal_def,heq,ENNReal.toReal_zero] at hpos
  exact lt_irrefl _ hpos

include hd t ht u huE πP πB πT upperBid hupper hfloor hjoint in
theorem source_low_bid_law : NativeFlag.nativeLowBidLaw Γ E=
    (LowBody.realLowBidLaw πL.1 : Measure ℝ) := by
  have hrow := native_original_exact_low_row E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor Γ hjoint
  exact OriginalLowConditional.native_lowBidLaw_eq E Γ (lowMass P.theta)
    (activeMass P.theta-upperMass P t) (partialMass+upperMass P t)
    P.low_mass_pos _ hrow

include hjoint in
theorem source_native_public : ∀ n z,(NativeSourcePolicy.data E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor (N+1) (iidCapacity (99/200) N) ξ width P.theta (SourceNoisyData.eA P) (SourceNoisyData.eR P) (Central.B ξ) hξ (by linarith) hw P.theta_pos.le (by linarith [P.theta_small]) hrare hdup).publicChoice n z=
    PublicScenario.localChoice E (NativeSourcePolicy.publicData E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor (iidCapacity (99/200) N) ξ P.theta (SourceNoisyData.eA P) (SourceNoisyData.eR P) (Central.B ξ) P.theta_pos.le (by linarith [P.theta_small])) (NativeFlag.nativeLowBidLaw Γ E) n z := by
  intro n z
  rw [source_low_bid_law P E hd t ht u huE πL πP πB πT upperBid hupper hfloor Γ hjoint]
  rfl

variable (cats : FiniteLaw (Fin 4))
  (L : LowBody.ActualAtomlessLowLimit N P.d0 ξ (iidCapacity (99/200) N) cats P.originalLowLaw)
  (hL : πL=L.joint)

include P hd t ht u huE πL πP πB πT upperBid hupper hfloor hjoint cats L hL in
theorem source_low_singletons : ∀ b,NativeFlag.nativeLowBidLaw Γ E {b}=0 := by
  have hrow := native_original_exact_low_row E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor Γ hjoint
  apply OriginalLowConditional.native_low_atomless_of_C2 E Γ (lowMass P.theta)
    (activeMass P.theta-upperMass P t) (partialMass+upperMass P t) P.low_mass_pos
    cats P.originalLowLaw L
  simpa only [hL,upperMass] using! hrow

include hξh hjoint cats L hL in
theorem source_serviceProb (i : Fin (N+1)) :
    1-P.theta≤ NativePartialDeviation.serviceProb (NativeSourcePolicy.data E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor (N+1) (iidCapacity (99/200) N) ξ width P.theta (SourceNoisyData.eA P) (SourceNoisyData.eR P) (Central.B ξ) hξ (by linarith) hw P.theta_pos.le (by linarith [P.theta_small]) hrare hdup) Γ i :=
  PartialNativeRegime.serviceProb_lower Γ (NativeSourcePolicy.data E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor (N+1) (iidCapacity (99/200) N) ξ width P.theta (SourceNoisyData.eA P) (SourceNoisyData.eR P) (Central.B ξ) hξ (by linarith) hw P.theta_pos.le (by linarith [P.theta_small]) hrare hdup) (NativeSourcePolicy.publicData E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor (iidCapacity (99/200) N) ξ P.theta (SourceNoisyData.eA P) (SourceNoisyData.eR P) (Central.B ξ) P.theta_pos.le (by linarith [P.theta_small]))
    (source_native_public P E hd t ht u huE πL πP πB πT upperBid hupper hfloor
      ξ width hξ hξh hw hrare hdup Γ hjoint)
    (source_category_nonzero P E hd t ht u huE πL πP πB πT upperBid hupper hfloor Γ hjoint)
    (source_low_singletons P E hd t ht u huE πL πP πB πT upperBid hupper hfloor
      ξ Γ hjoint cats L hL)
    (source_menu P E hd t ht u huE πL πP πB πT upperBid hupper hfloor Γ hjoint) i

include hu hξh hjoint hN huB hEB hR hRp hsmall hmSmall hwγ hroom cats L hL in
theorem source_guard_off_noLow (i : Fin (N+1)) (side : Fin 2) :
    (backgroundLaw Γ).real (guardEvent (NativeSourcePolicy.data E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor (N+1) (iidCapacity (99/200) N) ξ width P.theta (SourceNoisyData.eA P) (SourceNoisyData.eR P) (Central.B ξ) hξ (by linarith) hw P.theta_pos.le (by linarith [P.theta_small]) hrare hdup) i side\noLow E i)≤ error P ξ N := by
  have hh := native_guard_off_noLow_le Γ (NativeSourcePolicy.data E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor (N+1) (iidCapacity (99/200) N) ξ width P.theta (SourceNoisyData.eA P) (SourceNoisyData.eR P) (Central.B ξ) hξ (by linarith) hw P.theta_pos.le (by linarith [P.theta_small]) hrare hdup) (NativeSourcePolicy.publicData E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor (iidCapacity (99/200) N) ξ P.theta (SourceNoisyData.eA P) (SourceNoisyData.eR P) (Central.B ξ) P.theta_pos.le (by linarith [P.theta_small]))
    (source_native_public P E hd t ht u huE πL πP πB πT upperBid hupper hfloor
      ξ width hξ hξh hw hrare hdup Γ hjoint)
    (source_category_nonzero P E hd t ht u huE πL πP πB πT upperBid hupper hfloor Γ hjoint)
    (source_low_singletons P E hd t ht u huE πL πP πB πT upperBid hupper hfloor
      ξ Γ hjoint cats L hL)
    (source_menu P E hd t ht u huE πL πP πB πT upperBid hupper hfloor Γ hjoint)
    i side (bad Γ P E ξ N) (measurableSet_bad Γ P E ξ N)
    (fun kind r hk hr => source_public_failure_bound P E hd t ht u hu huE πL πP πB πT
      upperBid hupper hfloor ξ width hξ hξh hw hrare hdup Γ hjoint hN huB hEB hR hRp
      hsmall hmSmall hwγ hroom i kind r hk hr side)
  have h0 := (source_common_guard P E hd t ht u hu huE πL πP πB πT upperBid hupper hfloor
    ξ width hξ hξh hw Γ hjoint hN huB hEB hR hRp hsmall hmSmall hwγ hroom false).1
  have h1 := (source_common_guard P E hd t ht u hu huE πL πP πB πT upperBid hupper hfloor
    ξ width hξ hξh hw Γ hjoint hN huB hEB hR hRp hsmall hmSmall hwγ hroom true).1
  exact hh.trans (add_le_add
    (mul_le_mul_of_nonneg_left h0 (by change 0 ≤ 1-P.theta; linarith [P.theta_small]))
    (mul_le_mul_of_nonneg_left h1 P.theta_pos.le))

include hu hξh hjoint hN huB hEB hR hRp hsmall hmSmall hwγ hroom cats L hL in
theorem source_badMass (i : Fin (N+1)) :
    NativePartialDeviation.badMass (NativeSourcePolicy.data E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor (N+1) (iidCapacity (99/200) N) ξ width P.theta (SourceNoisyData.eA P) (SourceNoisyData.eR P) (Central.B ξ) hξ (by linarith) hw P.theta_pos.le (by linarith [P.theta_small]) hrare hdup) Γ i≤
      (75/2:ℝ)/Real.sqrt N+2*error P ξ N+
        Real.exp (-(N:ℝ)*(lowMass P.theta)^2/2) := by
  have hh := badMass_refined_union_bound Γ (NativeSourcePolicy.data E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor (N+1) (iidCapacity (99/200) N) ξ width P.theta (SourceNoisyData.eA P) (SourceNoisyData.eR P) (Central.B ξ) hξ (by linarith) hw P.theta_pos.le (by linarith [P.theta_small]) hrare hdup) (NativeSourcePolicy.publicData E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor (iidCapacity (99/200) N) ξ P.theta (SourceNoisyData.eA P) (SourceNoisyData.eR P) (Central.B ξ) P.theta_pos.le (by linarith [P.theta_small]))
    (source_native_public P E hd t ht u huE πL πP πB πT upperBid hupper hfloor
      ξ width hξ hξh hw hrare hdup Γ hjoint)
    (source_category_nonzero P E hd t ht u huE πL πP πB πT upperBid hupper hfloor Γ hjoint)
    (source_low_singletons P E hd t ht u huE πL πP πB πT upperBid hupper hfloor
      ξ Γ hjoint cats L hL)
    (source_menu P E hd t ht u huE πL πP πB πT upperBid hupper hfloor Γ hjoint) i
  have ht0 := source_tie_bound Γ (NativeSourcePolicy.data E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor (N+1) (iidCapacity (99/200) N) ξ width P.theta (SourceNoisyData.eA P) (SourceNoisyData.eR P) (Central.B ξ) hξ (by linarith) hw P.theta_pos.le (by linarith [P.theta_small]) hrare hdup) P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor hjoint i hN 0
  have ht1 := source_tie_bound Γ (NativeSourcePolicy.data E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor (N+1) (iidCapacity (99/200) N) ξ width P.theta (SourceNoisyData.eA P) (SourceNoisyData.eR P) (Central.B ξ) hξ (by linarith) hw P.theta_pos.le (by linarith [P.theta_small]) hrare hdup) P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor hjoint i hN 1
  have hg0 := source_guard_off_noLow P E hd t ht u hu huE πL πP πB πT upperBid hupper hfloor
    ξ width hξ hξh hw hrare hdup Γ hjoint hN huB hEB hR hRp hsmall hmSmall hwγ hroom cats L hL i 0
  have hg1 := source_guard_off_noLow P E hd t ht u hu huE πL πP πB πT upperBid hupper hfloor
    ξ width hξ hξh hw hrare hdup Γ hjoint hN huB hEB hR hRp hsmall hmSmall hwγ hroom cats L hL i 1
  have hn := source_noLow_bound Γ (NativeSourcePolicy.data E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor (N+1) (iidCapacity (99/200) N) ξ width P.theta (SourceNoisyData.eA P) (SourceNoisyData.eR P) (Central.B ξ) hξ (by linarith) hw P.theta_pos.le (by linarith [P.theta_small]) hrare hdup) P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor hjoint i hN
  have hsum : (75/4:ℝ)/Real.sqrt N+(75/4:ℝ)/Real.sqrt N=(75/2:ℝ)/Real.sqrt N := by ring
  simp only [NativeSourcePolicy.data] at hh ht0 ht1 hg0 hg1 hn ⊢
  linarith

end Source
end FCAppendix.Affine.Tail04.SourcePartialPublicGuard
