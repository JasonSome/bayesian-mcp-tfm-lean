import FCAppendix.Affine.Tail04.OriginalMenuMoments
import FCAppendix.Affine.Tail04.TypicalGuardError
import FCAppendix.Affine.Tail04.SourceNoisyData

noncomputable section
namespace FCAppendix.Affine.Tail04.SourceMomentRectangle
open MeasureTheory ProbabilityTheory Set Classical
open MenuError OriginalValues

def relativeError (ζ u B0 : ℝ) : ℝ := ζ+u*(1+2/(B0-1))

lemma relativeError_nonnegative {ζ u B0 : ℝ}
    (hζ : 0≤ ζ) (hu : 0≤ u) (hB : 1< B0) : 0≤ relativeError ζ u B0 := by
  unfold relativeError
  positivity

lemma bulk_reciprocal_bound {a e0 ζ u B0 : ℝ}
    (ha : 0≤ a) (he : 0≤ e0) (hζ : ζ∈Icc (0:ℝ) 1)
    (hu : 0≤ u) (huB : 1+u< B0) :
    a*e0*(1-relativeError ζ u B0)≤
      a*(1-ζ)*bulkReciprocalConstant e0 B0 (1+u) := by
  let s := u/(B0-1)
  have hD : 0< B0-1 := by linarith
  have hs : 0≤ s := div_nonneg hu hD.le
  have hsp : 1+u>0 := by linarith
  have hr : (B0-(1+u))/(B0-1)=1-s := by
    dsimp [s]
    field_simp [hD.ne']
    ring
  have hcore : 1-2*s-u≤(1-s)^2/(1+u) := by
    apply (le_div_iff₀ hsp).mpr
    nlinarith [sq_nonneg s,sq_nonneg u,mul_nonneg hs hu]
  have hmult := mul_le_mul_of_nonneg_left hcore (mul_nonneg (mul_nonneg ha (sub_nonneg.mpr hζ.2)) he)
  have hζerr : 0≤ ζ*(2*s+u) := mul_nonneg hζ.1 (by positivity)
  have hid : a*e0*(1-relativeError ζ u B0)=a*e0*(1-ζ-2*s-u) := by
    unfold relativeError
    dsimp [s]
    ring
  rw [hid]
  unfold bulkReciprocalConstant
  rw [hr]
  calc
    _ ≤ a*(1-ζ)*e0*(1-2*s-u) := by
      have h := mul_nonneg (mul_nonneg ha he) hζerr
      nlinarith
    _ ≤ a*(1-ζ)*e0*((1-s)^2/(1+u)) := hmult
    _ = _ := by ring

lemma two_moment_error {a e0 ζ u B0 mixed reciprocal : ℝ}
    (ha : 0< a) (he : 0< e0) (hζ : ζ∈Icc (0:ℝ) 1)
    (hu : 0≤ u) (huB : 1+u< B0)
    (hbulk : a*(1-ζ)*bulkReciprocalConstant e0 B0 (1+u)≤ reciprocal)
    (hWM : reciprocal≤ mixed) (hM : mixed≤ a*e0) :
    |mixed-a*e0|≤ a*e0*relativeError ζ u B0 ∧
      |reciprocal-a*e0|≤ a*e0*relativeError ζ u B0 := by
  have hl := (bulk_reciprocal_bound ha.le he.le hζ hu huB).trans hbulk
  constructor
  · rw [abs_of_nonpos (sub_nonpos.mpr hM)]
    nlinarith
  · rw [abs_of_nonpos (sub_nonpos.mpr (hWM.trans hM))]
    nlinarith

lemma moment_lower {M W M0 ξ : ℝ} (hM0 : 0< M0) (hξ : ξ∈Icc (0:ℝ) (1/2))
    (hM : |M-M0|≤ ξ*M0/1000) (hW : |W-M0|≤ ξ*M0/1000) :
    M0/2≤ M ∧ M0/2≤ W := by
  have heM := (abs_le.mp hM).1
  have heW := (abs_le.mp hW).1
  have hx := mul_le_mul_of_nonneg_right hξ.2 hM0.le
  constructor <;> nlinarith

lemma moment_ratio {ξ M W M0 d : ℝ}
    (hξ : ξ∈Icc (0:ℝ) (1/2)) (hM0 : 0< M0)
    (hM : |M-M0|≤ ξ*M0/1000) (hW : |W-M0|≤ ξ*M0/1000)
    (hn : |(1-ξ/2)*M0-ξ*d/2|≤ M0) :
    |((1-ξ/2)*M-ξ*d/2)/W-((1-ξ/2)*M0-ξ*d/2)/M0|≤ ξ/250 := by
  have hl := moment_lower hM0 hξ hM hW
  have hk : (1-ξ/2)∈Icc (0:ℝ) 1 := ⟨by linarith [hξ.2],by linarith [hξ.1]⟩
  have hnum : |((1-ξ/2)*M-ξ*d/2)-((1-ξ/2)*M0-ξ*d/2)|≤ ξ*M0/1000 := by
    rw [show ((1-ξ/2)*M-ξ*d/2)-((1-ξ/2)*M0-ξ*d/2)=(1-ξ/2)*(M-M0) by ring,
      abs_mul,abs_of_nonneg hk.1]
    exact (mul_le_mul_of_nonneg_left hM hk.1).trans
      (by
        have h0 : 0≤ ξ*M0/1000 := div_nonneg (mul_nonneg hξ.1 hM0.le) (by norm_num)
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hk.2 h0)
  have hr := Central.ratio_error (half_pos hM0) hl.2 hM0 hn hnum hW
  have he : (ξ*M0/1000+ξ*M0/1000)/(M0/2)=ξ/250 := by
    field_simp [hM0.ne']
    ring
  exact hr.trans_eq he

def γ (ξ : ℝ) : ℝ := ξ/1000
def radius (ξ M0 : ℝ) : ℝ := γ ξ*M0/40

lemma radius_guards {ξ M W M0 δ a h hm : ℝ}
    (hξ : 0< ξ) (hξh : ξ<1/2) (hM0 : 0< M0) (hδ : 0≤ δ)
    (hsum : a+h=99/100-δ)
    (hM : |M-M0|≤ ξ*M0/1000) (hW : |W-M0|≤ ξ*M0/1000) :
    0< radius ξ M0 ∧ radius ξ M0≤ M/2 ∧ radius ξ M0≤ W/2 ∧
      4*radius ξ M0≤99/200-((a-hm)-M)/2-(h+hm)/2 ∧
      10*radius ξ M0≤ γ ξ*W := by
  have hl := moment_lower hM0 ⟨hξ.le,hξh.le⟩ hM hW
  have hg : 0< γ ξ := div_pos hξ (by norm_num)
  have hg1 : γ ξ≤1 := by unfold γ;linarith
  have hgm : γ ξ*M0≤ M0 := by nlinarith
  have hgw := mul_le_mul_of_nonneg_left hl.2 hg.le
  unfold radius
  refine ⟨by positivity,?_,?_,?_,?_⟩ <;> nlinarith

lemma source_sum (P : ValueParameters) : activeMass P.theta+partialMass=99/100-P.theta^2 := by
  unfold activeMass partialMass delta
  ring

lemma central_ratio_bounds {ξ q M0 d : ℝ}
    (hξ : ξ∈Icc (0:ℝ) (1/2)) (hq : q∈Icc (0:ℝ) 1) (hM0 : 0< M0)
    (he : ((1-ξ/2)*M0-ξ*d/2)/M0=1-ξ*q) :
    |(1-ξ/2)*M0-ξ*d/2|≤ M0 := by
  have hu : (1-ξ*q)∈Icc (0:ℝ) 1 := by
    have hh := mul_le_mul hξ.2 hq.2 hq.1 (by norm_num : (0:ℝ)≤1/2)
    exact ⟨by nlinarith,by nlinarith [mul_nonneg hξ.1 hq.1]⟩
  have hnum : (1-ξ/2)*M0-ξ*d/2=M0*(1-ξ*q) := by
    have h := (div_eq_iff hM0.ne').mp he
    simpa only [mul_comm] using h
  rw [hnum,abs_mul,abs_of_pos hM0,abs_of_nonneg hu.1]
  nlinarith [hu.2]

lemma accept_center (P : ValueParameters) (ξ : ℝ) :
    ((1-ξ/2)*Central.mixedA (P.theta^2)-ξ*(P.theta^2)/2)/Central.mixedA (P.theta^2)=
      Central.lamA ξ := by
  have ht : P.theta^2≠0 := pow_ne_zero 2 P.theta_pos.ne'
  unfold Central.mixedA Central.lamA
  field_simp [ht,P.theta_pos.ne']
  ring

lemma reject_center (P : ValueParameters) (ξ : ℝ) :
    ((1-ξ/2)*Central.mixedR (P.theta^2)-ξ*(partialMass+P.theta^2)/2)/
      Central.mixedR (P.theta^2)=Central.lamR ξ := by
  have hh : partialMass+P.theta^2≠0 := by
    have := sq_nonneg P.theta
    norm_num [partialMass] at *
    linarith
  unfold Central.mixedR Central.h Central.lamR partialMass at *
  field_simp [hh]
  ring

theorem accept_population_guards (P : ValueParameters) {ξ M W : ℝ}
    (hξ : 0< ξ) (hξh : ξ<1/2)
    (hM : |M-Central.mixedA (P.theta^2)|≤ ξ*Central.mixedA (P.theta^2)/1000)
    (hW : |W-Central.mixedA (P.theta^2)|≤ ξ*Central.mixedA (P.theta^2)/1000) :
    let L := ((1-ξ/2)*M-ξ*(P.theta^2)/2)/W
    (1-ξ)*Central.B ξ+2*γ ξ≤ L ∧ L+2*γ ξ≤1 ∧ L+2*γ ξ≤ Central.R ξ := by
  dsimp only
  have hm : 0< Central.mixedA (P.theta^2) := by
    have htheta := P.theta_pos
    unfold Central.mixedA
    positivity
  have he := accept_center P ξ
  have hn := central_ratio_bounds ⟨hξ.le,hξh.le⟩ (by norm_num : (19/20:ℝ)∈Icc (0:ℝ) 1)
    hm (he.trans (by unfold Central.lamA;ring))
  have hr := moment_ratio ⟨hξ.le,hξh.le⟩ hm hM hW hn
  rw [he] at hr
  have hl := (abs_le.mp hr).1
  have hh := (abs_le.mp hr).2
  have hc := Central.receipt_margins ξ hξ hξh
  unfold γ
  exact ⟨by linarith [hc.1],by linarith [hc.2.2.2.1],by linarith [hc.2.1]⟩

theorem reject_population_guards (P : ValueParameters) {ξ M W hm Up : ℝ}
    (hξ : 0< ξ) (hξh : ξ<1/2) (hhm : 0≤ hm)
    (hsmall : hm≤ Central.mixedR (P.theta^2)/1000)
    (hUp : Up≤ Central.R ξ+ξ/1000)
    (hM : |M-Central.mixedR (P.theta^2)|≤ ξ*Central.mixedR (P.theta^2)/1000)
    (hW : |W-Central.mixedR (P.theta^2)|≤ ξ*Central.mixedR (P.theta^2)/1000) :
    (1-ξ)*Central.B ξ+2*γ ξ≤((1-ξ/2)*M-ξ*(partialMass+P.theta^2+hm)/2)/W ∧
      ((1-ξ/2)*M-ξ*(P.theta^2)/2)/W+2*γ ξ≤1 ∧
      Up+2*γ ξ≤((1-ξ/2)*M-ξ*(partialMass+P.theta^2)/2)/W := by
  let M0 := Central.mixedR (P.theta^2)
  have hM0 : 0< M0 := by dsimp [M0,Central.mixedR,Central.h];positivity
  have he := reject_center P ξ
  have hn := central_ratio_bounds ⟨hξ.le,hξh.le⟩ (by norm_num : (9/10:ℝ)∈Icc (0:ℝ) 1)
    hM0 (he.trans (by unfold Central.lamR;ring))
  have hr := moment_ratio ⟨hξ.le,hξh.le⟩ hM0 hM hW hn
  rw [he] at hr
  have hl := (abs_le.mp hr).1
  have hh := (abs_le.mp hr).2
  have hWlo := (moment_lower hM0 ⟨hξ.le,hξh.le⟩ hM hW).2
  have hW0 : 0< W := (half_pos hM0).trans_le hWlo
  have hshift : ξ*hm/(2*W)≤ ξ/1000 := by
    apply (div_le_iff₀ (by positivity : 0<2*W)).mpr
    have ht := mul_le_mul_of_nonneg_left hsmall hξ.le
    nlinarith
  have hid : ((1-ξ/2)*M-ξ*(partialMass+P.theta^2+hm)/2)/W=
      ((1-ξ/2)*M-ξ*(partialMass+P.theta^2)/2)/W-ξ*hm/(2*W) := by ring
  have hupperCenter : ((1-ξ/2)*M0-ξ*(P.theta^2)/2)/M0≤1-ξ/2 := by
    apply (div_le_iff₀ hM0).mpr
    nlinarith [sq_nonneg P.theta]
  have hupperNonneg : 0≤(1-ξ/2)*M0-ξ*(P.theta^2)/2 := by
    have hh0 := (abs_le.mp hn).1
    have hc : 0≤((1-ξ/2)*M0-ξ*(partialMass+P.theta^2)/2) := by
      have hp : 0≤ Central.lamR ξ := by unfold Central.lamR;linarith
      have hd := (le_div_iff₀ hM0).mp (he.symm ▸ hp)
      simpa using hd
    have hp : 0≤ partialMass := by norm_num [partialMass]
    nlinarith
  have hupperBound : |(1-ξ/2)*M0-ξ*(P.theta^2)/2|≤ M0 := by
    rw [abs_of_nonneg hupperNonneg]
    have hc := (div_le_iff₀ hM0).mp hupperCenter
    nlinarith
  have hupperError := moment_ratio ⟨hξ.le,hξh.le⟩ hM0 hM hW hupperBound
  have hupper := (abs_le.mp hupperError).2
  have hc := Central.receipt_margins ξ hξ hξh
  refine ⟨?_,?_,?_⟩
  · rw [hid]
    unfold γ Central.lamR Central.B at *
    nlinarith [sq_nonneg ξ]
  · unfold γ
    linarith
  · unfold γ
    linarith [hc.2.2.1]

end FCAppendix.Affine.Tail04.SourceMomentRectangle
