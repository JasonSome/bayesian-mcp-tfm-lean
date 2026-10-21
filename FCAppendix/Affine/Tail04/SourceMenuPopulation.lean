import FCAppendix.Affine.Tail04.SourceNativeMoments

noncomputable section
namespace FCAppendix.Affine.Tail04.SourceMenuPopulation
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation MenuError
open SourceMomentRectangle SourceNativeMoments Hybrid

def baseFlag (P : ValueParameters) (reg : Bool) : ℝ :=
  if reg then SourceNoisyData.eR P else SourceNoisyData.eA P

def centerMoment (P : ValueParameters) (reg : Bool) : ℝ :=
  if reg then Central.mixedR (P.theta^2) else Central.mixedA (P.theta^2)

def upperMass (P : ValueParameters) (t : ℝ) : ℝ :=
  activeMass P.theta*P.zeta*powerTail P.M 10 t

def keptShare (P : ValueParameters) (t : ℝ) (reg : Bool) : ℝ :=
  if reg then upperMass P t/(partialMass+upperMass P t) else 1

theorem baseFlag_bounds (P : ValueParameters) (reg : Bool) :
    baseFlag P reg∈Ioo (0:ℝ) 1 := by
  cases reg
  · exact SourceNoisyData.eA_bounds P
  · exact SourceNoisyData.eR_bounds P

theorem centerMoment_eq (P : ValueParameters) (reg : Bool) :
    activeMass P.theta*baseFlag P reg=centerMoment P reg := by
  have ha : activeMass P.theta≠0 := P.active_mass_pos.ne'
  cases reg <;>
    simp only [baseFlag,centerMoment,Bool.false_eq_true,ite_false,ite_true]
  · unfold SourceNoisyData.eA Central.mixedA
    field_simp [ha]
  · unfold SourceNoisyData.eR Central.mixedR Central.h partialMass
    field_simp [ha]

theorem centerMoment_pos (P : ValueParameters) (reg : Bool) :
    0< centerMoment P reg := by
  rw [←centerMoment_eq]
  exact mul_pos P.active_mass_pos (baseFlag_bounds P reg).1

theorem upperMass_nonnegative (P : ValueParameters) (t : ℝ) (ht : P.M≤ t) :
    0≤ upperMass P t := P.tailMass_nonneg t ht

theorem keptShare_bounds (P : ValueParameters) (t : ℝ) (ht : P.M≤ t) (reg : Bool) :
    keptShare P t reg∈Icc (0:ℝ) 1 ∧ lowerShare reg≤ keptShare P t reg := by
  have hh := upperMass_nonnegative P t ht
  have hd : 0< partialMass+upperMass P t := by norm_num [partialMass];linarith
  cases reg
  · norm_num [keptShare,lowerShare]
  · simp only [keptShare,lowerShare,ite_true]
    exact ⟨⟨div_nonneg hh hd.le,(div_le_one hd).mpr (by norm_num [partialMass])⟩,
      div_nonneg hh hd.le⟩

structure GuardInterior (ξ share ρ B R Rp γ δ abar mbar hbar wbar : ℝ) (reg : Bool) : Prop where
  share_mem : share∈Icc (0:ℝ) 1
  share_lower : lowerShare reg≤ share
  radius_pos : 0< δ
  radius_mixed : δ≤ mbar/2
  radius_reciprocal : δ≤ wbar/2
  radius_capacity : 4*δ≤ ρ-(abar-mbar)/2-hbar
  radius_margin : 10*δ≤ γ*wbar
  lower_endpoint : (1-ξ)*B+2*γ≤ populationNumerator ξ ρ abar mbar hbar (lowerShare reg)/wbar
  upper_endpoint : populationNumerator ξ ρ abar mbar hbar 1/wbar+2*γ≤1
  private_mean : if reg then Rp+2*γ≤ populationNumerator ξ ρ abar mbar hbar share/wbar
    else populationNumerator ξ ρ abar mbar hbar share/wbar+2*γ≤ R

theorem GuardInterior.mean_margins {ξ share ρ B R Rp γ δ abar mbar hbar wbar : ℝ} {reg : Bool}
    (G : GuardInterior ξ share ρ B R Rp γ δ abar mbar hbar wbar reg)
    (hξ : 0≤ ξ) (hhbar : 0≤ hbar) :
    0< wbar ∧ (1-ξ)*B+2*γ≤ populationNumerator ξ ρ abar mbar hbar share/wbar ∧
      populationNumerator ξ ρ abar mbar hbar share/wbar+2*γ≤1 := by
  have hW : 0< wbar := by linarith [G.radius_pos,G.radius_reciprocal]
  have hl := div_le_div_of_nonneg_right
    (populationNumerator_mono (ρ:=ρ) (abar:=abar) (mbar:=mbar) hξ hhbar G.share_lower) hW.le
  have hu := div_le_div_of_nonneg_right
    (populationNumerator_mono (ρ:=ρ) (abar:=abar) (mbar:=mbar) hξ hhbar G.share_mem.2) hW.le
  exact ⟨hW,G.lower_endpoint.trans hl,by linarith [G.upper_endpoint]⟩

theorem population_full_private (P : ValueParameters) (ξ M hm : ℝ) :
    populationNumerator ξ (99/200) (activeMass P.theta-hm) M ((partialMass+hm)/2) 1=
      (1-ξ/2)*M-ξ*(P.theta^2)/2 := by
  unfold populationNumerator activeMass partialMass delta
  ring

theorem population_zero_private (P : ValueParameters) (ξ M hm : ℝ) :
    populationNumerator ξ (99/200) (activeMass P.theta-hm) M ((partialMass+hm)/2) 0=
      (1-ξ/2)*M-ξ*(partialMass+P.theta^2+hm)/2 := by
  unfold populationNumerator activeMass partialMass delta
  ring

theorem population_reject_mean (P : ValueParameters) (ξ M hm : ℝ) (hhm : 0≤ hm) :
    populationNumerator ξ (99/200) (activeMass P.theta-hm) M ((partialMass+hm)/2)
      (hm/(partialMass+hm))=(1-ξ/2)*M-ξ*(partialMass+P.theta^2)/2 := by
  have he : populationNumerator ξ (99/200) (activeMass P.theta-hm) M ((partialMass+hm)/2)
      (hm/(partialMass+hm))=(1-ξ/2)*M-ξ*(99/200)+(ξ/2)*(activeMass P.theta-hm)+
      ξ*(hm/(partialMass+hm))*((partialMass+hm)/2) := by
    unfold populationNumerator
    ring
  rw [he,source_numerator_reject P ξ M hm hhm]
  unfold delta
  ring

theorem source_interior (P : ValueParameters) {ξ t B R Rp M W : ℝ}
    (ht : P.M≤ t) (hξ : 0< ξ) (hξh : ξ<1/2)
    (hB : B≤ Central.B ξ) (hR : R=Central.R ξ) (hRp : Rp≤ Central.R ξ+ξ/1000)
    (hmSmall : upperMass P t≤ Central.mixedR (P.theta^2)/1000)
    (reg : Bool)
    (hM : |M-centerMoment P reg|≤ ξ*centerMoment P reg/1000)
    (hW : |W-centerMoment P reg|≤ ξ*centerMoment P reg/1000) :
    GuardInterior ξ (keptShare P t reg) (99/200) B R Rp (γ ξ)
      (radius ξ (centerMoment P reg)) (activeMass P.theta-upperMass P t)
      M ((partialMass+upperMass P t)/2) W reg := by
  have hh := upperMass_nonnegative P t ht
  have hs := keptShare_bounds P t ht reg
  have hr := radius_guards (hm:=upperMass P t) hξ hξh (centerMoment_pos P reg)
    (sq_nonneg P.theta) (source_sum P) hM hW
  have hb : (1-ξ)*B+2*γ ξ≤(1-ξ)*Central.B ξ+2*γ ξ := by
    exact add_le_add (mul_le_mul_of_nonneg_left hB (by linarith : 0≤1-ξ)) (le_refl _)
  refine ⟨hs.1,hs.2,hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2,?_,?_,?_⟩
  · cases reg
    · have h := accept_population_guards P hξ hξh hM hW
      simpa only [lowerShare,Bool.false_eq_true,ite_false,population_full_private] using hb.trans h.1
    · have h := reject_population_guards P hξ hξh hh hmSmall hRp hM hW
      simpa only [lowerShare,ite_true,population_zero_private] using hb.trans h.1
  · cases reg
    · simpa only [population_full_private] using
        (accept_population_guards P hξ hξh hM hW).2.1
    · simpa only [population_full_private] using
        (reject_population_guards P hξ hξh hh hmSmall hRp hM hW).2.1
  · cases reg
    · simp only [keptShare,Bool.false_eq_true,ite_false,population_full_private,hR]
      exact (accept_population_guards P hξ hξh hM hW).2.2
    · simp only [keptShare,ite_true]
      rw [population_reject_mean P ξ M (upperMass P t) hh]
      exact (reject_population_guards P hξ hξh hh hmSmall hRp hM hW).2.2

section Native
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
  (Γ : FiniteGame m 2 c Seed) (P : ValueParameters) (E : Observable.Regions) (hd : E.d=P.d0)
  (t : ℝ) (ht : P.M< t) (u : ℝ)
  (hu : 0≤ u) (huE : 1+u≤ E.U)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (πP : Law (A:=Icc E.R E.Rp) P.originalPartialLaw)
  (πB : Law (A:=Icc (1:ℝ) (1+u)) P.originalBulkLaw)
  (πT : Law (A:=Icc (1:ℝ) E.U) (P.originalTruncatedTailLaw t ht))
  (upperBid : ℝ→ℝ) (hupper : Measurable upperBid)
  (hfloor : ∀ v,t< v → E.H≤ upperBid v)

local notation "πA" => ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT
local notation "J" => originalJoint P t ht.le E.R E.Rp E.U
  (E.d_nonneg.trans E.d_lt_R.le) πL πP πA upperBid hupper
variable (hjoint : Γ.F⊗ₘΓ.σ=(originalJoint P t ht.le E.R E.Rp E.U
  (E.d_nonneg.trans E.d_lt_R.le) πL πP
  (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT)
  upperBid hupper : Measure (ℝ×JointAction 2)))

include hd ht u huE πL πP πB πT upperBid hupper hfloor hjoint in
theorem native_private_means :
    (∫ x,indicator (categoryFlag E 2) x ∂userLaw Γ)=(partialMass+upperMass P t)/2 ∧
    (∫ x,indicator (categoryFlag E 3) x ∂userLaw Γ)=(partialMass+upperMass P t)/2 := by
  have hrow := native_original_exact_low_row E P hd t ht.le πL πP πA upperBid hupper hfloor Γ hjoint
  have hsum : lowMass P.theta+(activeMass P.theta-upperMass P t)+(partialMass+upperMass P t)=1 := by
    have hh := mass_sum P.theta
    linarith
  have hpriv : 0≤ partialMass+upperMass P t := by
    have hh := upperMass_nonnegative P t ht.le
    norm_num [partialMass]
    linarith
  have hc := original_category_mean Γ E (lowMass P.theta) (activeMass P.theta-upperMass P t)
    (partialMass+upperMass P t) P.low_mass_pos.le (P.movingActiveMass_positive t ht.le).le
    hpriv hsum (LowBody.realLowBidLaw πL.1 : Measure ℝ) hrow
  exact ⟨by simpa using hc 2,by simpa using hc 3⟩

include hd ht hu huE πL πP πB πT upperBid hupper hfloor hjoint in
theorem native_guard_interior (ξ : ℝ) (hξ : 0< ξ) (hξh : ξ<1/2)
    (huB : 1+u< Central.B ξ) (hEB : E.U≤ Central.B ξ)
    (hR : E.R=Central.R ξ) (hRp : E.Rp≤ Central.R ξ+ξ/1000)
    (hsmall : relativeError P.zeta u (Central.B ξ)≤ ξ/1000)
    (hmSmall : upperMass P t≤ Central.mixedR (P.theta^2)/1000) (reg : Bool) :
    GuardInterior ξ (keptShare P t reg) (99/200) E.U E.R E.Rp (γ ξ)
      (radius ξ (centerMoment P reg))
      (∫ x,indicator (categoryFlag E 1) x ∂userLaw Γ)
      (∫ x,(sourceProbability (baseFlag P reg) (Central.B ξ) x.1.2.bid:ℝ)*
        indicator (categoryFlag E 1) x ∂userLaw Γ)
      (∫ x,indicator (categoryFlag E 2) x ∂userLaw Γ)
      (∫ x,(sourceProbability (baseFlag P reg) (Central.B ξ) x.1.2.bid:ℝ)*
        reciprocalWeight (categoryFlag E 1) (fun y : UserDraw 2 => y.1.2.bid) x ∂userLaw Γ) reg := by
  have he := baseFlag_bounds P reg
  have hm := native_two_moment_small Γ P E hd t ht u (baseFlag P reg) (Central.B ξ)
    hu huE huB hEB he.1 he.2.le πL πP πB πT upperBid hupper hfloor hjoint hsmall
  rw [centerMoment_eq] at hm
  have hg := source_interior P ht.le hξ hξh hEB hR hRp hmSmall reg hm.1 hm.2
  have ha := native_active_mean Γ P E hd t ht u huE πL πP πB πT
    upperBid hupper hfloor hjoint
  have hp := native_private_means Γ P E hd t ht u huE πL πP πB πT
    upperBid hupper hfloor hjoint
  rw [ha,hp.1]
  simpa only [upperMass,mixedWeight_eq_marked,originalReciprocalWeight_eq_marked] using hg

include hd ht hu huE πL πP πB πT upperBid hupper hfloor hjoint in
theorem native_nominal_guard_interior (ξ : ℝ) (hξ : 0< ξ) (hξh : ξ<1/2)
    (huB : 1+u< Central.B ξ) (hEB : E.U≤ Central.B ξ)
    (hR : E.R=Central.R ξ) (hRp : E.Rp≤ Central.R ξ+ξ/1000)
    (hsmall : relativeError P.zeta u (Central.B ξ)≤ ξ/1000)
    (hmSmall : upperMass P t≤ Central.mixedR (P.theta^2)/1000) (reg : Bool) :
    GuardInterior ξ (keptShare P t reg) (99/200) (Central.B ξ) E.R E.Rp (γ ξ)
      (radius ξ (centerMoment P reg))
      (∫ x,indicator (categoryFlag E 1) x ∂userLaw Γ)
      (∫ x,(sourceProbability (baseFlag P reg) (Central.B ξ) x.1.2.bid:ℝ)*
        indicator (categoryFlag E 1) x ∂userLaw Γ)
      (∫ x,indicator (categoryFlag E 2) x ∂userLaw Γ)
      (∫ x,(sourceProbability (baseFlag P reg) (Central.B ξ) x.1.2.bid:ℝ)*
        reciprocalWeight (categoryFlag E 1) (fun y : UserDraw 2 => y.1.2.bid) x ∂userLaw Γ) reg := by
  have he := baseFlag_bounds P reg
  have hm := native_two_moment_small Γ P E hd t ht u (baseFlag P reg) (Central.B ξ)
    hu huE huB hEB he.1 he.2.le πL πP πB πT upperBid hupper hfloor hjoint hsmall
  rw [centerMoment_eq] at hm
  have hg := source_interior P ht.le hξ hξh (B:=Central.B ξ) le_rfl hR hRp hmSmall reg hm.1 hm.2
  have ha := native_active_mean Γ P E hd t ht u huE πL πP πB πT upperBid hupper hfloor hjoint
  have hp := native_private_means Γ P E hd t ht u huE πL πP πB πT upperBid hupper hfloor hjoint
  rw [ha,hp.1]
  simpa only [upperMass,mixedWeight_eq_marked,originalReciprocalWeight_eq_marked] using hg

end Native
end FCAppendix.Affine.Tail04.SourceMenuPopulation
