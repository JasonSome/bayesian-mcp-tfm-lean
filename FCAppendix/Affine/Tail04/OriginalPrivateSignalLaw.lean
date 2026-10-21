import FCAppendix.Affine.Tail04.OriginalPrivateSource
import FCAppendix.Affine.Tail04.NoisyPrivateLaws
import FCAppendix.Affine.Tail04.ActiveJointMerge

noncomputable section
namespace FCAppendix.Affine.Tail04.OriginalPrivateSignalLaw
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation
open OriginalPrivateEntry OriginalPrivateSource EqualPrivateSignal EqualPrivateUpper Hybrid
open CompactSourceBidLaws

variable (E : Observable.Regions)

def residualDecode (x : ℝ×JointAction 2) : Unit⊕Icc E.R E.Rp :=
  signalEntry (jointDecode E x)

lemma measurable_residualDecode : Measurable (residualDecode E) :=
  continuous_signalEntry.measurable.comp (measurable_jointDecode E)

lemma decode_partial (b : Icc E.R E.Rp) : LocalCoordinates.decode E (b:ℝ)=Sum.inr b := by
  have hn : ¬E.H≤(b:ℝ) := not_le.mpr (b.2.2.trans_lt E.Rp_lt_H)
  simp only [LocalCoordinates.decode,if_neg hn]
  congr 1
  apply Subtype.ext
  exact LocalCoordinates.clamp_eq b.2

include E in
lemma bandJoint_residual {vL vU : ℝ} (μ : Measure (Icc vL vU)) [IsProbabilityMeasure μ]
    (πP : Law (A:=Icc E.R E.Rp) μ) :
    (bandJoint (E.d_nonneg.trans E.d_lt_R.le) 1 (by norm_num) μ πP : Measure _).map
      (residualDecode E)=((bidMarginal πP.1 : ProbabilityMeasure (Icc E.R E.Rp)) : Measure _).map Sum.inr := by
  have hf : Measurable (fun x : Icc vL vU×Icc E.R E.Rp =>
      ((x.1:ℝ),bandAction (E.d_nonneg.trans E.d_lt_R.le) 1 (by norm_num) x.2)) :=
    measurable_fst.subtype_val.prodMk
      ((measurable_bandAction (E.d_nonneg.trans E.d_lt_R.le) 1 (by norm_num)).comp measurable_snd)
  change ((πP.1 : Measure (Icc vL vU × Icc E.R E.Rp)).map _).map (residualDecode E)=
    ((πP.1 : Measure (Icc vL vU × Icc E.R E.Rp)).map Prod.snd).map Sum.inr
  erw [Measure.map_map (measurable_residualDecode E) hf,
    Measure.map_map measurable_inr measurable_snd]
  congr 1
  funext x
  simp only [Function.comp_apply,residualDecode,jointDecode,bandAction,decode_partial,signalEntry]

lemma upperJoint_residual (FH : ProbabilityMeasure ℝ) (b : ℝ → ℝ) (hb : Measurable b)
    (hfloor : ∀ᵐ v ∂(FH : Measure ℝ),E.H≤ b v) :
    (upperJoint FH b hb : Measure (ℝ × JointAction 2)).map (residualDecode E)=Measure.dirac (Sum.inl ()) := by
  have hs := (upperJoint_support FH b hb E.H hfloor).mono (fun x hx => hx.1)
  have he : (upperJoint FH b hb : Measure (ℝ × JointAction 2)).map (residualDecode E)=
      (upperJoint FH b hb : Measure (ℝ × JointAction 2)).map (fun _ => (Sum.inl () : Unit⊕Icc E.R E.Rp)) := by
    apply Measure.map_congr
    filter_upwards [hs] with x hx
    simp only [residualDecode,jointDecode,LocalCoordinates.decode,if_pos hx,signalEntry]
  rw [he,Measure.map_const,measure_univ,one_smul]

variable (P : ValueParameters) (hd : E.d=P.d0) (t : ℝ) (ht : P.M≤ t)
local instance : IsProbabilityMeasure (P.originalMovingActiveLaw t ht) :=
  P.originalMovingActiveLaw_probability t ht
variable (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
    (πP : Law (A:=Icc E.R E.Rp) P.originalPartialLaw)
    (πA : Law (A:=Icc (1:ℝ) E.U) (P.originalMovingActiveLaw t ht))
    (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)
    (hfloor : ∀ v,t< v → E.H≤ upperBid v)

local notation "hR" => E.d_nonneg.trans E.d_lt_R.le
local notation "z" => activeMass P.theta*P.zeta*powerTail P.M 10 t
local notation "J" => originalJoint P t ht E.R E.Rp E.U hR πL πP πA upperBid hupperBid
local notation "ρ" => originalEntryLaw E P hd t ht πL πP πA upperBid hupperBid hfloor

def privateShare (P : ValueParameters) (t : ℝ) (ht : P.M≤ t) : unitInterval :=
  ⟨activeMass P.theta*P.zeta*powerTail P.M 10 t/
      (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t),by
    have hh : 0< partialMass := by norm_num [partialMass]
    have hz := P.tailMass_nonneg t ht
    exact ⟨div_nonneg hz (add_pos_of_pos_of_nonneg hh hz).le,
      (div_le_one (add_pos_of_pos_of_nonneg hh hz)).mpr (le_add_of_nonneg_left hh.le)⟩⟩

theorem weighted_original_signal :
    ENNReal.ofReal (partialMass+z) • (ρ : Measure (Ici E.H ⊕ Icc E.R E.Rp)).map signalEntry=
      ENNReal.ofReal partialMass • ((bidMarginal πP.1 : ProbabilityMeasure (Icc E.R E.Rp)) : Measure _).map Sum.inr+
      ENNReal.ofReal z • Measure.dirac (Sum.inl ()) := by
  have hL : ∀ᵐ x ∂(lowJoint P.originalLowLaw πL : Measure (ℝ×JointAction 2)),x.2.bid≤ E.d := by
    apply (ae_map_iff (measurable_fst.subtype_val.prodMk
      ((measurable_lowBroadcast P.d0).comp measurable_snd)).aemeasurable
      (measurableSet_le ((measurable_bid 2).comp measurable_snd) measurable_const)).mpr
    exact ae_of_all _ fun x => by
      change (x.2:ℝ)≤ E.d
      rw [hd]
      exact x.2.2.2
  have hP := (bandJoint_support hR 1 (by norm_num) P.originalPartialLaw πP).mono
    (fun _ hx => (Or.inl hx.2.1 : _∈E.privateBids))
  have hA := (bandJoint_support (by norm_num : (0:ℝ)≤1) 2 le_rfl
    (P.originalMovingActiveLaw t ht) πA).mono (fun x hx =>
      (show x.2.bid∉E.privateBids from by
        rintro (hp | hp)
        · linarith [hp.2,hx.2.1.1,E.Rp_lt_one]
        · have hp' : E.H≤x.2.bid := hp
          linarith [hp',hx.2.1.2,E.U_lt_H]))
  let FH : ProbabilityMeasure ℝ := ⟨P.originalMovingUpperLaw t,P.originalMovingUpperLaw_probability t⟩
  have hf : ∀ᵐ v ∂(FH : Measure ℝ),E.H≤ upperBid v :=
    (P.originalMovingUpperLaw_support t).mono (fun v hv => hfloor v hv)
  have hH := (upperJoint_support FH upperBid hupperBid E.H hf).mono
    (fun _ hx => (Or.inr hx.1 : _∈E.privateBids))
  have hres := private_restriction E (lowMass P.theta) partialMass (activeMass P.theta-z) z
    _ _ _ _ hL hP hA hH
  have hmass : ENNReal.ofReal (partialMass+z)=(J : Measure _ ) E.privateJointEvent := by
    rw [←original_private_mass E P hd t ht πL πP πA upperBid hupperBid hfloor,
      ofReal_measureReal]
  change (J : Measure (ℝ × JointAction 2)).restrict E.privateJointEvent = _ at hres
  change ENNReal.ofReal (partialMass+z) •
    ((cond (J : Measure _) E.privateJointEvent).map (jointDecode E)).map signalEntry=_
  rw [Measure.map_map continuous_signalEntry.measurable (measurable_jointDecode E),
    ←Measure.map_smul,hmass,measure_smul_cond,hres]
  change Measure.map (residualDecode E) _ = _
  rw [Measure.map_add _ _ (measurable_residualDecode E),Measure.map_smul,Measure.map_smul,
    bandJoint_residual E P.originalPartialLaw πP,upperJoint_residual E FH upperBid hupperBid hf]

theorem original_signal_law :
    (ρ : Measure (Ici E.H ⊕ Icc E.R E.Rp)).map signalEntry=
      (NoisyPrivateLaws.residualEntryLaw (privateShare P t ht) (bidMarginal πP.1) : Measure (Unit⊕Icc E.R E.Rp)) := by
  have hh : 0< partialMass := by norm_num [partialMass]
  have hz := P.tailMass_nonneg t ht
  have hs : 0< partialMass+z := add_pos_of_pos_of_nonneg hh hz
  apply ActiveJointMerge.measure_smul_cancel hs
  rw [weighted_original_signal E P hd t ht πL πP πA upperBid hupperBid hfloor]
  change _=ENNReal.ofReal (partialMass+z) •
    (ENNReal.ofReal (privateShare P t ht:ℝ) • Measure.dirac (Sum.inl ())+
      ENNReal.ofReal (1-(privateShare P t ht:ℝ)) •
        (((bidMarginal πP.1).map (f:=(Sum.inr : Icc E.R E.Rp → Unit⊕Icc E.R E.Rp)) measurable_inr.aemeasurable : ProbabilityMeasure (Unit⊕Icc E.R E.Rp)) : Measure (Unit⊕Icc E.R E.Rp)))
  rw [smul_add,smul_smul,smul_smul,←ENNReal.ofReal_mul hs.le,←ENNReal.ofReal_mul hs.le]
  have h0 : (partialMass+z)*(privateShare P t ht:ℝ)=z := by
    dsimp [privateShare]
    field_simp [hs.ne']
  have h1 : (partialMass+z)*(1-(privateShare P t ht:ℝ))=partialMass := by
    dsimp [privateShare]
    field_simp [hs.ne']
    ring
  rw [h0,h1,add_comm]
  rfl

theorem original_rawRow_signal_law (H : ℕ) :
    (PrivateRowSorting.originalIid E H ρ : Measure (Row H E.R E.Rp E.H)).map signal=
      (rowLaw H (NoisyPrivateLaws.residualEntryLaw (privateShare P t ht)
        (bidMarginal πP.1)) : Measure (Signal H E.R E.Rp)) := by
  change (Measure.pi fun _ : Fin H => (ρ : Measure (Ici E.H ⊕ Icc E.R E.Rp))).map
    (fun row i => signalEntry (row i))=_
  rw [Measure.pi_map_pi (fun _ => continuous_signalEntry.measurable.aemeasurable),rowLaw_eq_pi]
  simp only [original_signal_law E P hd t ht πL πP πA upperBid hupperBid hfloor]

theorem original_sortedRow_signal_law (H : ℕ) :
    (originalPrivateRow E P hd t ht πL πP πA upperBid hupperBid hfloor H : Measure (Row H E.R E.Rp E.H)).map signal=
      (rowLaw H (NoisyPrivateLaws.residualEntryLaw (privateShare P t ht)
        (bidMarginal πP.1)) : Measure (Signal H E.R E.Rp)).map (PrivateRowSorting.sortSignal E H) := by
  rw [originalPrivateRow,PrivateRowSorting.sortedOriginalIid,PrivateRowSorting.sorted_signal_law,
    original_rawRow_signal_law E P hd t ht πL πP πA upperBid hupperBid hfloor]

end FCAppendix.Affine.Tail04.OriginalPrivateSignalLaw
