import FCAppendix.Affine.Tail04.OrderedAtomTwoFocalGuard
import FCAppendix.Affine.Tail04.OrderedAtomTwoFocalCompression
import FCAppendix.Affine.Tail04.TwoFocalFlagExpectation
import FCAppendix.Affine.Tail04.PartialSortedCompression

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomTwoFocalExpectation
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation OriginalPrivateSource
open MenuError SourceMenuPopulation SourceMenuError SourceMomentRectangle OrderedAtomTwoFocalGuard
open EqualPrivateSignal NativeTypicalCount OriginalFlagCompression TwoFocalCompression
open OriginalFlagMeasure TwoFocalFlagExpectation PartialNativeGuardIntegration OriginalNoiseProduct
open ActualActiveFiniteGain ActualFallbackPromotion

def markZero {N : ℕ} (r : Fin N→ UserDraw 2) : Fin N→ UserDraw 2×unitInterval :=
  fun j => (r j,0)

def prefixActive (E : Observable.Regions) {N : ℕ} (r : Fin N→ UserDraw 2) : Fin (N+2)→ Bool :=
  fullActive (markZero r) (categoryFlag E 1)

def prefixBid {N : ℕ} (r : Fin N→ UserDraw 2) (bid : UserDraw 2→ℝ) (b0 b1 : ℝ) : Fin (N+2)→ℝ :=
  fullBid (markZero r) bid b0 b1

def prefixProbability (P : ValueParameters) (ξ : ℝ) (reg : Bool) {N : ℕ}
    (r : Fin N→ UserDraw 2) (b0 b1 : ℝ) : Fin (N+2)→ unitInterval :=
  Fin.cases (sourceProbability (baseFlag P reg) (Central.B ξ) b0)
    (Fin.cases (sourceProbability (baseFlag P reg) (Central.B ξ) b1)
      (fun j : Fin N => nativeFlag P ξ reg (r j)))

def privateSize (E : Observable.Regions) {N : ℕ} (r : Fin N→ UserDraw 2) (k : Fin 4) : ℕ :=
  privateCount N (fun _ : Unit => markZero r) (categoryFlag E k) ()

def lowPresent (E : Observable.Regions) {N : ℕ} (r : Fin N→ UserDraw 2) : Bool :=
  decide (∃ j,E.coarseTag (r j)=0)

def noLow (E : Observable.Regions) (N : ℕ) : Set (Fin N→ UserDraw 2) :=
  {r | ∀ j,E.coarseTag (r j)≠0}

lemma measurableSet_noLow (E : Observable.Regions) (N : ℕ) :
    MeasurableSet (noLow E N) := by
  have h : noLow E N = ⋂ j : Fin N, {r : Fin N → UserDraw 2 | E.coarseTag (r j)=0}ᶜ := by
    ext r
    simp only [noLow, mem_setOf_eq, mem_iInter, mem_compl_iff]
  rw [h]
  exact MeasurableSet.iInter (fun j =>
    (measurableSet_eq_fun (E.measurable_coarseTag.comp (measurable_pi_apply j)) measurable_const).compl)

lemma low_indicator (E : Observable.Regions) {N : ℕ} (r : Fin N→ UserDraw 2) :
    (if lowPresent E r then (0:ℝ) else 1)=(if r∈noLow E N then 1 else 0) := by
  simp only [lowPresent,noLow,mem_setOf_eq,decide_eq_true_eq]
  by_cases h : ∃ j,E.coarseTag (r j)=0
  · have hn : ¬∀ j,E.coarseTag (r j)≠0 := by
      obtain ⟨j,hj⟩ := h
      exact fun h => h j hj
    simp only [if_pos h,if_neg hn]
  · have hn : ∀ j,E.coarseTag (r j)≠0 := by simpa only [not_exists] using h
    simp only [if_neg h,if_pos hn]

lemma prefix_probability_exact (P : ValueParameters) (ξ : ℝ) (reg : Bool)
    {N : ℕ} (r : Fin N→ UserDraw 2) (b0 b1 : ℝ) (j : Fin (N+2)) :
    (sourceProbability (baseFlag P reg) (Central.B ξ)
      (prefixBid r nativeBid b0 b1 j):ℝ)=(prefixProbability P ξ reg r b0 b1 j:ℝ) := by
  refine Fin.cases rfl (fun k => ?_) j
  exact Fin.cases rfl (fun _ => rfl) k

lemma prefix_flags_exact (P : ValueParameters) (ξ : ℝ) (reg : Bool)
    {N : ℕ} (r : Fin N→ UserDraw 2) (b0 b1 : ℝ) (z : Fin (N+2)→ unitInterval) :
    flags (prefixProbability P ξ reg r b0 b1) z=
      fullFlags (zipRow N (r,suffix N z)) (nativeFlag P ξ reg)
        (Empirical.flag (prefixProbability P ξ reg r b0 b1 0) (z 0))
        (Empirical.flag (prefixProbability P ξ reg r b0 b1 (Fin.succ 0)) (z (Fin.succ 0))) := by
  funext j
  refine Fin.cases rfl (fun k => ?_) j
  exact Fin.cases rfl (fun _ => rfl) k

section Source
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
  (Γ : FiniteGame m 2 c Seed) (P : ValueParameters) (E : Observable.Regions) (hd : E.d=P.d0)
  (t : ℝ) (ht : P.M< t) (u : ℝ) (hu : 0≤ u) (huE : 1+u≤ E.U)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (πP : Law (A:=Icc E.R E.Rp) P.originalPartialLaw)
  (πB : Law (A:=Icc (1:ℝ) (1+u)) P.originalBulkLaw)
  (πT : Law (A:=Icc (1:ℝ) E.U) (P.originalTruncatedTailLaw t ht))
  (upperBid : ℝ→ℝ) (hupper : Measurable upperBid)
  (hfloor : ∀ v,t< v → E.H≤ upperBid v)

local notation "πA" => ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT
variable (hjoint : Γ.F⊗ₘΓ.σ=(originalJoint P t ht.le E.R E.Rp E.U
  (E.d_nonneg.trans E.d_lt_R.le) πL πP
    (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper : Measure _))
  (ξ : ℝ) (hξ : 0< ξ) (hξh : ξ<1/2)
  (huB : 1+u< Central.B ξ) (hEB : E.U≤ Central.B ξ)
  (hR : E.R=Central.R ξ) (hRp : E.Rp≤ Central.R ξ+ξ/1000)
  (hsmall : relativeError P.zeta u (Central.B ξ)≤ ξ/1000)
  (hmSmall : upperMass P t≤ Central.mixedR (P.theta^2)/1000)
  (N : ℕ) (hN : 0< N)
  (width : ℝ) (hw : 0< width) (hwγ : width≤ γ ξ) (reg : Bool)
  (hroom : 32/(N:ℝ)≤ radius ξ (centerMoment P reg))

local notation "μsrc" => userLaw Γ
local notation "Row" => Fin N→ UserDraw 2
local notation "Ur" => Fin N→ unitInterval
local notation "μr" => Measure.pi (fun _ : Fin N => μsrc)
local notation "μu" => Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))
local notation "δ" => radius ξ (centerMoment P reg)
local notation "νH" => originalMarks P E hd t ht u huE πL πP πB πT upperBid hupper hfloor

def bad : Set (Row×Ur) :=
  sourceFiveBad μsrc N (zipRow N) (categoryFlag E 1) (categoryFlag E 2) (categoryFlag E 3)
    (nativeFlag P ξ reg) nativeBid (δ/2)

def actualPhi (r : Row) (A : ℕ) : ℕ→ℝ→ unitInterval :=
  TypicalGuardStatistics.phi A ((min (privateSize E r 2) (privateSize E r 3))) ((max (privateSize E r 2) (privateSize E r 3)))
    (twoCapacity (99/200) N) ξ E.U E.R E.Rp width reg
      (νH ((min (privateSize E r 2) (privateSize E r 3)))) (νH ((max (privateSize E r 2) (privateSize E r 3))))

include hd t ht u huE πL πP πB πT upperBid hupper hfloor hjoint in
lemma source_low_mass : (μsrc).real (E.coarseTag ⁻¹' {0})=lowMass P.theta := by
  have hm := mass_sum P.theta
  have hsum : lowMass P.theta+(activeMass P.theta-upperMass P t)+(partialMass+upperMass P t)=1 := by
    linarith
  have hrow := native_original_exact_low_row E P hd t ht.le πL πP πA upperBid hupper hfloor Γ hjoint
  have hh := original_category_mean Γ E (lowMass P.theta) (activeMass P.theta-upperMass P t)
    (partialMass+upperMass P t) P.low_mass_pos.le (P.movingActiveMass_positive t ht.le).le
    (by norm_num [partialMass];linarith [upperMass_nonnegative P t ht.le]) hsum
    (LowBody.realLowBidLaw πL.1 : Measure ℝ) hrow 0
  simp only [categoryFlag_indicator,Matrix.cons_val_zero] at hh
  have hi := integral_indicator_one (μ:=μsrc) (E.measurable_coarseTag (measurableSet_singleton 0))
  have he : (∫ x,if E.coarseTag x=0 then (1:ℝ) else 0 ∂μsrc)=(μsrc).real (E.coarseTag ⁻¹' {0}) := by
    simpa only [Set.indicator,mem_preimage,mem_singleton_iff,Pi.one_apply] using hi
  exact he.symm.trans hh

include hd t ht u huE πL πP πB πT upperBid hupper hfloor hjoint hN in
lemma source_noLow_probability : (μr).real (noLow E N)≤ Real.exp (-(N:ℝ)*(lowMass P.theta)^2/2) := by
  have hh := NativeFlag.iid_bulk_count_lower_tail μsrc (E.coarseTag ⁻¹' {0})
    (E.measurable_coarseTag (measurableSet_singleton 0)) N hN P.low_mass_pos
    (source_low_mass Γ P E hd t ht u huE πL πP πB πT upperBid hupper hfloor hjoint).ge
  apply (measureReal_mono (μ:=μr) ?_).trans hh
  intro r hr
  have hz : Probability.sampleCount (E.coarseTag ⁻¹' {0}) r=0 := by
    unfold Probability.sampleCount
    have he : (Finset.univ.filter fun j => r j∈E.coarseTag ⁻¹' {0})=∅ := by
      ext j
      simp [hr j]
    rw [he,Finset.card_empty]
  change (Probability.sampleCount (E.coarseTag ⁻¹' {0}) r:ℝ)<lowMass P.theta*(N:ℝ)/2
  rw [hz,Nat.cast_zero]
  exact (div_pos (mul_pos P.low_mass_pos (Nat.cast_pos.mpr hN)) (by norm_num))

include P hd t ht u huE πL πP πB πT upperBid hupper hfloor hjoint in
lemma source_row_menu : ∀ᵐ r ∂μr,∀ j,NativeMenuReports.MenuAction E (r j).1.2 := by
  have hJ : ∀ᵐ x ∂Γ.F⊗ₘΓ.σ,NativeMenuReports.MenuAction E x.2 := by
    rw [hjoint]
    exact (originalJoint_sourceBands P E hd t ht.le πL πP πA upperBid hupper hfloor).mono
      fun x hx => NativeMenuReports.source_menu E P t x hx
  have hx : ∀ᵐ x ∂μsrc,NativeMenuReports.MenuAction E x.1.2 :=
    (measurePreserving_fst (μ:=Γ.F⊗ₘΓ.σ) (ν:=permLaw 2)).quasiMeasurePreserving.ae hJ
  exact ae_all_iff.mpr (fun j => (measurePreserving_eval (fun _ : Fin N => μsrc) j).quasiMeasurePreserving.ae hx)

include hu hjoint hξ hξh huB hEB hR hRp hsmall hmSmall hN hw hwγ hroom in
lemma source_guard : MeasurableSet (bad Γ P E ξ N reg) ∧
    ((μr).prod μu).real (bad Γ P E ξ N reg)≤10*Real.exp (-(N:ℝ)*δ^2/200) ∧
      ∀ z,z∉bad Γ P E ξ N reg → ∀ bid' : UserDraw 2→ℝ,
      (∀ j,categoryFlag E 1 (z.1 j)=true → 1≤ nativeBid (z.1 j) ∧ 1≤ bid' (z.1 j)) →
      (∀ j,categoryFlag E 1 (z.1 j)=true → |nativeBid (z.1 j)-bid' (z.1 j)|≤ δ/2) →
      ∀ b0 b1 : ℝ,1≤ b0 → 1≤ b1 → ∀ f0 f1 : Bool,∀ target : Row×Ur→ Fin (N+2),
      let A := twoActiveCount N (zipRow N) (categoryFlag E 1) z
      let M := twoMixedCount N (zipRow N) (categoryFlag E 1) (nativeFlag P ξ reg) f0 f1 target z
      let H0 := (min (privateSize E z.1 2) (privateSize E z.1 3))
      let H1 := (max (privateSize E z.1 2) (privateSize E z.1 3))
      let Q := clampedOwner (A-M) (keptShare P t reg*H0) (keptShare P t reg*H1)
      TypicalGuardStatistics.weight H0 H1 (twoCapacity (99/200) N) Q (A-M-Q) M
        ξ E.U E.R E.Rp width reg (νH H0) (νH H1)
        ((N:ℝ)*twoReciprocal N (zipRow N) (categoryFlag E 1) (nativeFlag P ξ reg)
          bid' b0 b1 f0 f1 target z)=1 :=
  native_robust_guard Γ P E hd t ht u hu huE πL πP πB πT upperBid hupper hfloor
    hjoint ξ hξ hξh huB hEB hR hRp hsmall hmSmall ((μr).prod μu) N hN (zipRow N)
    (zipRow_preserves μsrc (volume : Measure unitInterval) N) width hw hwγ reg hroom

include hu hjoint hξ hξh huB hEB hR hRp hsmall hmSmall hN hw hwγ hroom in
theorem row_failure_bound (r : Row) (A : ℕ) (e : Fin A≃Active (prefixActive E r))
    (bid' : UserDraw 2→ℝ)
    (hbox : ∀ j,categoryFlag E 1 (r j)=true → 1≤ nativeBid (r j) ∧ 1≤ bid' (r j))
    (hnear : ∀ j,categoryFlag E 1 (r j)=true → |nativeBid (r j)-bid' (r j)|≤ δ/2)
    (b0 b1 : ℝ) (hb0 : 1≤ b0) (hb1 : 1≤ b1) :
    failure (prefixActive E r) e (prefixProbability P ξ reg r b0 b1)
      (effectivePhi (lowPresent E r)
        (actualPhi P E hd t ht u huE πL πP πB πT upperBid hupper hfloor ξ N width reg r A))
      (compressedBids (prefixActive E r) e (prefixBid r bid' b0 b1))≤
        sectionMass μu (bad Γ P E ξ N reg) r+(if r∈noLow E N then 1 else 0) := by
  have hs := source_guard Γ P E hd t ht u hu huE πL πP πB πT upperBid hupper hfloor
    hjoint ξ hξ hξh huB hEB hR hRp hsmall hmSmall N hN width hw hwγ reg hroom
  have hh := effective_failure_le (prefixActive E r) e (prefixProbability P ξ reg r b0 b1)
    (lowPresent E r) (actualPhi P E hd t ht u huE πL πP πB πT upperBid hupper hfloor ξ N width reg r A)
    (compressedBids (prefixActive E r) e (prefixBid r bid' b0 b1))
    {z : Ur | (r,z)∈bad Γ P E ξ N reg}
    (hs.1.preimage (measurable_const.prodMk measurable_id)) (by
      intro z hz target
      rw [prefix_flags_exact]
      let row := zipRow N (r,suffix N z)
      let f0 := Empirical.flag (prefixProbability P ξ reg r b0 b1 0) (z 0)
      let f1 := Empirical.flag (prefixProbability P ξ reg r b0 b1 (Fin.succ 0)) (z (Fin.succ 0))
      have hphi := OrderedAtomTwoFocalCompression.two_phi_exact row (categoryFlag E 1) (nativeFlag P ξ reg) bid' e target
        hN (categoryFlag E 2) (categoryFlag E 3) b0 b1 f0 f1 ξ (keptShare P t reg)
        (99/200) E.U E.R E.Rp width reg (νH ((min (privateSize E r 2) (privateSize E r 3)))) (νH ((max (privateSize E r 2) (privateSize E r 3))))
        (originalMarks_mean P E hd t ht u huE πL πP πB πT upperBid hupper hfloor reg _)
        (originalMarks_mean P E hd t ht u huE πL πP πB πT upperBid hupper hfloor reg _)
        (fun j hj => (hbox j hj).2)
      exact hphi.trans (hs.2.2 (r,suffix N z) hz bid' hbox hnear b0 b1 hb0 hb1 f0 f1
        (fun _ => (e target).val)))
  rw [low_indicator E r] at hh
  exact hh

include hu hjoint hξ hξh huB hEB hR hRp hsmall hmSmall hN hw hwγ hroom in
theorem original_flag_loss (A : Row→ℕ) (e : ∀ r,Fin (A r)≃Active (prefixActive E r))
    (bid' : UserDraw 2→ℝ)
    (hbox : ∀ x,NativeMenuReports.MenuAction E x.1.2 → categoryFlag E 1 x=true → 1≤ bid' x)
    (hnear : ∀ x,NativeMenuReports.MenuAction E x.1.2 → categoryFlag E 1 x=true → |nativeBid x-bid' x|≤ δ/2)
    (b0 b1 : ℝ) (hb0 : 1≤ b0) (hb1 : 1≤ b1) :
    (∫ r : Row,failure (prefixActive E r) (e r) (prefixProbability P ξ reg r b0 b1)
      (effectivePhi (lowPresent E r)
        (actualPhi P E hd t ht u huE πL πP πB πT upperBid hupper hfloor ξ N width reg r (A r)))
      (compressedBids (prefixActive E r) (e r) (prefixBid r bid' b0 b1)) ∂μr)≤
        10*Real.exp (-(N:ℝ)*δ^2/200)+Real.exp (-(N:ℝ)*(lowMass P.theta)^2/2) := by
  have hs := source_guard Γ P E hd t ht u hu huE πL πP πB πT upperBid hupper hfloor
    hjoint ξ hξ hξh huB hEB hR hRp hsmall hmSmall N hN width hw hwγ reg hroom
  let g : Row→ℝ := fun r => sectionMass μu (bad Γ P E ξ N reg) r+
    (if r∈noLow E N then 1 else 0)
  have hNo : Integrable (fun r : Row => if r∈noLow E N then (1:ℝ) else 0) μr :=
    Integrable.of_bound
      (Measurable.ite (measurableSet_noLow E N) measurable_const measurable_const).aestronglyMeasurable
      1 (ae_of_all _ fun r => by split_ifs <;> norm_num)
  have hg : Integrable g μr := (integrable_sectionMass μu (bad Γ P E ξ N reg) hs.1 μr).add hNo
  have hh := integral_mono_of_nonneg (μ:=μr)
    (f:=fun r => failure (prefixActive E r) (e r) (prefixProbability P ξ reg r b0 b1)
      (effectivePhi (lowPresent E r)
        (actualPhi P E hd t ht u huE πL πP πB πT upperBid hupper hfloor ξ N width reg r (A r)))
      (compressedBids (prefixActive E r) (e r) (prefixBid r bid' b0 b1)))
    (g:=g) (ae_of_all _ fun r => (failure_bounds _ _ _ _ _).1) hg (by
      filter_upwards [source_row_menu Γ P E hd t ht u huE πL πP πB πT upperBid hupper hfloor hjoint N] with r hr
      exact row_failure_bound Γ P E hd t ht u hu huE πL πP πB πT upperBid hupper hfloor
        hjoint ξ hξ hξh huB hEB hR hRp hsmall hmSmall N hN width hw hwγ reg hroom r (A r) (e r) bid'
        (fun j hj => ⟨(PartialSortedCompression.menu_active_box E (r j) (hr j) hj).1,hbox (r j) (hr j) hj⟩)
        (fun j hj => hnear (r j) (hr j) hj) b0 b1 hb0 hb1)
  have hgi : (∫ r : Row,g r ∂μr)=((μr).prod μu).real (bad Γ P E ξ N reg)+(μr).real (noLow E N) := by
    change (∫ r : Row,sectionMass μu (bad Γ P E ξ N reg) r+
      (if r∈noLow E N then (1:ℝ) else 0) ∂μr)=_
    rw [integral_add (integrable_sectionMass μu (bad Γ P E ξ N reg) hs.1 μr) hNo,
      ←product_real_eq_integral μu (bad Γ P E ξ N reg) hs.1 μr]
    congr 1
    simpa only [Set.indicator,Pi.one_apply] using integral_indicator_one (μ:=μr) (measurableSet_noLow E N)
  rw [hgi] at hh
  exact hh.trans (add_le_add hs.2.1
    (source_noLow_probability Γ P E hd t ht u huE πL πP πB πT upperBid hupper hfloor hjoint N hN))

include hu hjoint hξ hξh huB hEB hR hRp hsmall hmSmall hN hw hwγ hroom in
theorem actual_two_focal_loss (A : Row→ℕ) (e : ∀ r,Fin (A r)≃Active (prefixActive E r))
    (b0 b1 : ℝ) (hb0 : 1≤ b0) (hb1 : 1≤ b1) :
    (∫ r : Row,badWeightProbability
      (effectivePhi (lowPresent E r)
        (actualPhi P E hd t ht u huE πL πP πB πT upperBid hupper hfloor ξ N width reg r (A r)))
      (baseFlag P reg) (Central.B ξ)
      (compressedBids (prefixActive E r) (e r) (prefixBid r nativeBid b0 b1)) ∂μr)≤
        10*Real.exp (-(N:ℝ)*δ^2/200)+Real.exp (-(N:ℝ)*(lowMass P.theta)^2/2) := by
  have hh := original_flag_loss Γ P E hd t ht u hu huE πL πP πB πT upperBid hupper hfloor
    hjoint ξ hξ hξh huB hEB hR hRp hsmall hmSmall N hN width hw hwγ reg hroom A e nativeBid
    (fun x hx ha => (PartialSortedCompression.menu_active_box E x hx ha).1)
    (fun x _ _ => by
      have hM := centerMoment_pos P reg
      simp only [sub_self,abs_zero]
      unfold radius γ
      positivity)
    b0 b1 hb0 hb1
  convert! hh using 1
  apply integral_congr_ae
  exact ae_of_all _ fun r => (failure_eq_actual (prefixActive E r) (e r)
    (prefixProbability P ξ reg r b0 b1)
    (effectivePhi (lowPresent E r)
      (actualPhi P E hd t ht u huE πL πP πB πT upperBid hupper hfloor ξ N width reg r (A r)))
    (compressedBids (prefixActive E r) (e r) (prefixBid r nativeBid b0 b1))
    (baseFlag P reg) (Central.B ξ)
    (fun j => prefix_probability_exact P ξ reg r b0 b1 (e r j).val)).symm

include hu hjoint hξ hξh huB hEB hR hRp hsmall hmSmall hN hw hwγ hroom in
theorem changed_flag_loss (A : Row→ℕ) (e : ∀ r,Fin (A r)≃Active (prefixActive E r))
    (bid' : UserDraw 2→ℝ)
    (hbox : ∀ x,NativeMenuReports.MenuAction E x.1.2 → categoryFlag E 1 x=true → 1≤ bid' x)
    (hnear : ∀ x,NativeMenuReports.MenuAction E x.1.2 → categoryFlag E 1 x=true → |nativeBid x-bid' x|≤ δ/2)
    (b0 b1 : ℝ) (hb0 : 1≤ b0) (hb1 : 1≤ b1) (εflag : ℝ)
    (hvariation : ∀ᵐ r ∂μr,
      CompactPromotionErrors.flagVariation (baseFlag P reg) (Central.B ξ)
        (compressedBids (prefixActive E r) (e r) (prefixBid r bid' b0 b1))
        (compressedBids (prefixActive E r) (e r) (prefixBid r nativeBid b0 b1))≤ εflag) :
    (∫ r : Row,badWeightProbability
      (effectivePhi (lowPresent E r)
        (actualPhi P E hd t ht u huE πL πP πB πT upperBid hupper hfloor ξ N width reg r (A r)))
      (baseFlag P reg) (Central.B ξ)
      (compressedBids (prefixActive E r) (e r) (prefixBid r bid' b0 b1)) ∂μr)≤
        10*Real.exp (-(N:ℝ)*δ^2/200)+Real.exp (-(N:ℝ)*(lowMass P.theta)^2/2)+εflag := by
  have hs := source_guard Γ P E hd t ht u hu huE πL πP πB πT upperBid hupper hfloor
    hjoint ξ hξ hξh huB hEB hR hRp hsmall hmSmall N hN width hw hwγ reg hroom
  let g : Row→ℝ := fun r => sectionMass μu (bad Γ P E ξ N reg) r+
    (if r∈noLow E N then 1 else 0)+εflag
  have hNo : Integrable (fun r : Row => if r∈noLow E N then (1:ℝ) else 0) μr :=
    Integrable.of_bound
      (Measurable.ite (measurableSet_noLow E N) measurable_const measurable_const).aestronglyMeasurable
      1 (ae_of_all _ fun r => by split_ifs <;> norm_num)
  have hg : Integrable g μr :=
    ((integrable_sectionMass μu (bad Γ P E ξ N reg) hs.1 μr).add hNo).add (integrable_const εflag)
  have hh := integral_mono_of_nonneg (μ:=μr)
    (f:=fun r => badWeightProbability
      (effectivePhi (lowPresent E r)
        (actualPhi P E hd t ht u huE πL πP πB πT upperBid hupper hfloor ξ N width reg r (A r)))
      (baseFlag P reg) (Central.B ξ)
      (compressedBids (prefixActive E r) (e r) (prefixBid r bid' b0 b1)))
    (g:=g) (ae_of_all _ fun _ => FiniteLaw.prob_nonneg _ _) hg (by
      filter_upwards [source_row_menu Γ P E hd t ht u huE πL πP πB πT upperBid hupper hfloor hjoint N,
        hvariation] with r hr hv
      let old := compressedBids (prefixActive E r) (e r) (prefixBid r nativeBid b0 b1)
      let new := compressedBids (prefixActive E r) (e r) (prefixBid r bid' b0 b1)
      let cut := effectivePhi (lowPresent E r)
        (actualPhi P E hd t ht u huE πL πP πB πT upperBid hupper hfloor ξ N width reg r (A r))
      have hDifference := (abs_le.mp (CompactPromotionErrors.flag_probability_difference
        (baseFlag P reg) (Central.B ξ) new old (fun z => ¬WeightFlags cut new z))).2
      have hl := compressedLaw_eq_source (prefixActive E r) (e r)
        (prefixProbability P ξ reg r b0 b1) old (baseFlag P reg) (Central.B ξ)
        (fun j => prefix_probability_exact P ξ reg r b0 b1 (e r j).val)
      rw [←hl] at hDifference
      change badWeightProbability cut (baseFlag P reg) (Central.B ξ) new-
        failure (prefixActive E r) (e r) (prefixProbability P ξ reg r b0 b1) cut new≤_ at hDifference
      have hb := row_failure_bound Γ P E hd t ht u hu huE πL πP πB πT upperBid hupper hfloor
        hjoint ξ hξ hξh huB hEB hR hRp hsmall hmSmall N hN width hw hwγ reg hroom r (A r) (e r) bid'
        (fun j hj => ⟨(PartialSortedCompression.menu_active_box E (r j) (hr j) hj).1,hbox (r j) (hr j) hj⟩)
        (fun j hj => hnear (r j) (hr j) hj) b0 b1 hb0 hb1
      change badWeightProbability cut (baseFlag P reg) (Central.B ξ) new≤_
      dsimp only [g]
      linarith)
  have hgi : (∫ r : Row,g r ∂μr)=
      ((μr).prod μu).real (bad Γ P E ξ N reg)+(μr).real (noLow E N)+εflag := by
    change (∫ r : Row,(sectionMass μu (bad Γ P E ξ N reg) r+
      (if r∈noLow E N then (1:ℝ) else 0))+εflag ∂μr)=_
    rw [integral_add (f:=fun r : Row => sectionMass μu (bad Γ P E ξ N reg) r+
        (if r∈noLow E N then (1:ℝ) else 0)) (g:=fun _ => εflag)
        ((integrable_sectionMass μu (bad Γ P E ξ N reg) hs.1 μr).add hNo) (integrable_const εflag),
      integral_add (integrable_sectionMass μu (bad Γ P E ξ N reg) hs.1 μr) hNo,
      ←product_real_eq_integral μu (bad Γ P E ξ N reg) hs.1 μr]
    rw [show (∫ r : Row,if r∈noLow E N then (1:ℝ) else 0 ∂μr)=(μr).real (noLow E N) by
      simpa only [Set.indicator,Pi.one_apply] using integral_indicator_one (μ:=μr) (measurableSet_noLow E N)]
    simp only [integral_const,probReal_univ,one_smul]
  rw [hgi] at hh
  exact hh.trans (add_le_add (add_le_add hs.2.1
    (source_noLow_probability Γ P E hd t ht u huE πL πP πB πT upperBid hupper hfloor hjoint N hN)) (le_refl εflag))

end Source
end FCAppendix.Affine.Tail04.OrderedAtomTwoFocalExpectation
