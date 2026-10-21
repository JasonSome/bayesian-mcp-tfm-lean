import FCAppendix.Affine.Hybrid.Multiple03.ScalarLogs
import FCAppendix.Affine.LowBody.CategoricalRateGuards

noncomputable section
namespace FCAppendix.Affine.Hybrid.Multiple03
open Set Filter Topology
open FCAppendix.Affine.Uniform07

inductive RateCase where | multiple335 | multiple665 | tailLower | tailUpper
  deriving DecidableEq, Fintype

def rateActiveQ : RateCase→ℚ
  | .multiple335 => 67/200 | .multiple665 => 133/200
  | .tailLower => 8/25 | .tailUpper => 67/100
def rateUpperQ : RateCase→ℚ
  | .multiple335 => 13/20 | .multiple665 => 8/25
  | .tailLower => 67/100 | .tailUpper => 8/25
def rateLowQ : RateCase→ℚ
  | .multiple335 | .multiple665 => 3/200
  | .tailLower | .tailUpper => 1/100
def tiltQ : RateCase→ℚ
  | .multiple335 => 250141/1250000 | .multiple665 => 1463303/10000000
  | .tailLower => 4/25 | .tailUpper => 3/25
def certifiedGapQ : RateCase→ℚ
  | .multiple335 => 139/1250 | .multiple665 => 3617/100000
  | .tailLower => 1397/10000 | .tailUpper => 1101/10000
def mgfQ (i : RateCase) : ℚ :=
  rateActiveQ i*(tiltQ i)^2+rateUpperQ i*tiltQ i+rateLowQ i
def klFirstQ (i : RateCase) : ℚ := (99/200)/(1-rateUpperQ i/2)
def klSecondQ (i : RateCase) : ℚ := (101/200)/(rateUpperQ i/2)

def tiltLog : (i : RateCase)→ LogCertificate (tiltQ i)
  | .multiple335 => log_335_z | .multiple665 => log_665_z
  | .tailLower => log_tail_lower_z | .tailUpper => log_tail_upper_z

def reindexLog {q r : ℚ} (c : LogCertificate q) (h : r=q) : LogCertificate r where
  lo := c.lo
  hi := c.hi
  n := c.n
  q_pos := h.symm ▸ c.q_pos
  lo_small := c.lo_small
  hi_small := c.hi_small
  lower_check := h.symm ▸ c.lower_check
  upper_check := h.symm ▸ c.upper_check

def mgfLog (i : RateCase) : LogCertificate (mgfQ i) := by
  cases i
  · exact reindexLog log_335_mgf (by norm_num [mgfQ,rateActiveQ,rateUpperQ,rateLowQ,tiltQ])
  · exact reindexLog log_665_mgf (by norm_num [mgfQ,rateActiveQ,rateUpperQ,rateLowQ,tiltQ])
  · exact reindexLog log_tail_lower_mgf (by norm_num [mgfQ,rateActiveQ,rateUpperQ,rateLowQ,tiltQ])
  · exact reindexLog log_tail_upper_mgf (by norm_num [mgfQ,rateActiveQ,rateUpperQ,rateLowQ,tiltQ])
def klFirstLog (i : RateCase) : LogCertificate (klFirstQ i) := by
  cases i
  · exact reindexLog log_335_kl1 (by norm_num [klFirstQ,rateUpperQ])
  · exact reindexLog log_665_kl1 (by norm_num [klFirstQ,rateUpperQ])
  · exact reindexLog log_tail_lower_kl1 (by norm_num [klFirstQ,rateUpperQ])
  · exact reindexLog log_tail_upper_kl1 (by norm_num [klFirstQ,rateUpperQ])
def klSecondLog (i : RateCase) : LogCertificate (klSecondQ i) := by
  cases i
  · exact reindexLog log_335_kl2 (by norm_num [klSecondQ,rateUpperQ])
  · exact reindexLog log_665_kl2 (by norm_num [klSecondQ,rateUpperQ])
  · exact reindexLog log_tail_lower_kl2 (by norm_num [klSecondQ,rateUpperQ])
  · exact reindexLog log_tail_upper_kl2 (by norm_num [klSecondQ,rateUpperQ])

def witnessGap (s a h z : ℝ) : ℝ :=
  (99/100)*Real.log z-Real.log (a*z^2+h*z+s)-
    (99/100)*Real.log ((99/200)/(1-h/2))-
    (101/100)*Real.log ((101/200)/(h/2))

def rateGapBox (i : RateCase) : Box :=
  Box.sub (Box.sub (Box.sub (Box.scale (99/100) (tiltLog i).box)
    (mgfLog i).box) (Box.scale (99/100) (klFirstLog i).box))
    (Box.scale (101/100) (klSecondLog i).box)

theorem rateGapBox_ok (i : RateCase) : (rateGapBox i).Holds
    (witnessGap (rateLowQ i) (rateActiveQ i) (rateUpperQ i) (tiltQ i)) := by
  have h := Box.sub_ok (Box.sub_ok (Box.sub_ok
    (Box.scale_ok (99/100) (tiltLog i).correct) (mgfLog i).correct)
    (Box.scale_ok (99/100) (klFirstLog i).correct))
    (Box.scale_ok (101/100) (klSecondLog i).correct)
  simpa [rateGapBox,witnessGap,mgfQ,klFirstQ,klSecondQ] using h

theorem rational_witness_gap (i : RateCase) :
    (certifiedGapQ i:ℝ)<
      witnessGap (rateLowQ i) (rateActiveQ i) (rateUpperQ i) (tiltQ i) := by
  apply Box.lower_real (rateGapBox_ok i)
  cases i <;> norm_num [rateGapBox,certifiedGapQ,tiltLog,mgfLog,klFirstLog,klSecondLog,
    reindexLog,LogCertificate.box,Box.sub,Box.add,Box.neg,Box.scale,Box.mul,Box.point,
    log_335_z,log_335_mgf,log_335_kl1,log_335_kl2,
    log_665_z,log_665_mgf,log_665_kl1,log_665_kl2,
    log_tail_lower_z,log_tail_lower_mgf,log_tail_lower_kl1,log_tail_lower_kl2,
    log_tail_upper_z,log_tail_upper_mgf,log_tail_upper_kl1,log_tail_upper_kl2]

theorem jointObjective_log_tilt {s a h z : ℝ} (hz : 0< z) :
    FCAppendix.Affine.LowBody.jointObjective s a h (99/200) (Real.log z)-
      2*FCAppendix.Ample.binaryKL (99/200) (1-h/2)=witnessGap s a h z := by
  have he : Real.exp (2*Real.log z)=z^2 := by
    rw [two_mul,Real.exp_add,Real.exp_log hz]
    ring
  simp only [FCAppendix.Affine.LowBody.jointObjective,he,Real.exp_log hz,
    FCAppendix.Ample.binaryKL,witnessGap]
  norm_num
  ring

theorem jointObjective_le_jointRate {s a h rho t : ℝ}
    (hs : 0< s) (ha : 0≤ a) (hh : 0≤ h) (hrho : 0≤ rho) (ht : t<0) :
    FCAppendix.Affine.LowBody.jointObjective s a h rho t≤
      FCAppendix.Affine.LowBody.jointRate s a h rho := by
  have hb : BddAbove (FCAppendix.Affine.LowBody.jointObjective s a h rho '' Iio 0) := by
    refine ⟨-Real.log s,?_⟩
    rintro _ ⟨u,hu,rfl⟩
    have hz : s≤ a*Real.exp (2*u)+h*Real.exp u+s := by
      have hA := mul_nonneg ha (Real.exp_pos (2*u)).le
      have hH := mul_nonneg hh (Real.exp_pos u).le
      linarith
    have hl := Real.log_le_log hs hz
    have ht' : 2*rho*u≤0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hu.le
    dsimp [FCAppendix.Affine.LowBody.jointObjective]
    linarith
  exact le_csSup hb ⟨t,ht,rfl⟩

theorem source_rate_gap_of_witness {s a h z c : ℝ}
    (hs : 0< s) (ha : 0≤ a) (hh : 0≤ h) (hz0 : 0< z) (hz1 : z<1)
    (hc : c< witnessGap s a h z) :
    2*FCAppendix.Ample.binaryKL (99/200) (1-h/2)+c<
      FCAppendix.Affine.LowBody.jointRate s a h (99/200) := by
  have ht : Real.log z<0 := Real.log_neg hz0 hz1
  have hm := jointObjective_le_jointRate hs ha hh (by norm_num : (0:ℝ)≤99/200) ht
  have he := jointObjective_log_tilt (s:=s) (a:=a) (h:=h) hz0
  linarith

theorem certified_source_rate_gap (i : RateCase) :
    2*FCAppendix.Ample.binaryKL (99/200) (1-(rateUpperQ i:ℝ)/2)+
      (certifiedGapQ i:ℝ)<
      FCAppendix.Affine.LowBody.jointRate (rateLowQ i) (rateActiveQ i)
        (rateUpperQ i) (99/200) := by
  exact source_rate_gap_of_witness
    (by cases i <;> norm_num [rateLowQ])
    (by cases i <;> norm_num [rateActiveQ])
    (by cases i <;> norm_num [rateUpperQ])
    (by cases i <;> norm_num [tiltQ])
    (by cases i <;> norm_num [tiltQ]) (rational_witness_gap i)

def rootLoQ : Bool→ℚ | false => 2001127/10000000 | true => 1463302/10000000
def rootHiQ : Bool→ℚ | false => 2001128/10000000 | true => 1463303/10000000
def multipleRateCase : Bool→ RateCase | false => .multiple335 | true => .multiple665
def chernoffPolynomial (i : Bool) (z : ℝ) : ℝ :=
  (rateActiveQ (multipleRateCase i):ℝ)*(101/200)*z^2+
    (rateUpperQ (multipleRateCase i):ℝ)*(1/200)*z-
    (99/200)*(rateLowQ (multipleRateCase i):ℝ)

theorem positive_chernoff_quadratic_root_enclosure (i : Bool) :
    ∃ z : ℝ, z∈Ioo (rootLoQ i:ℝ) (rootHiQ i:ℝ) ∧
      0< z ∧ z<1 ∧ chernoffPolynomial i z=0 ∧
      ∀ w : ℝ,0< w→ chernoffPolynomial i w=0→ w=z := by
  have hab : (rootLoQ i:ℝ)≤ rootHiQ i := by cases i <;> norm_num [rootLoQ,rootHiQ]
  have hlo : chernoffPolynomial i (rootLoQ i)<0 := by
    cases i <;> norm_num [chernoffPolynomial,multipleRateCase,rateActiveQ,
      rateUpperQ,rateLowQ,rootLoQ]
  have hhi : 0< chernoffPolynomial i (rootHiQ i) := by
    cases i <;> norm_num [chernoffPolynomial,multipleRateCase,rateActiveQ,
      rateUpperQ,rateLowQ,rootHiQ]
  obtain ⟨z,hz,hzero⟩ := intermediate_value_Icc hab
    (show ContinuousOn (chernoffPolynomial i) (Icc (rootLoQ i:ℝ) (rootHiQ i:ℝ)) by
      unfold chernoffPolynomial
      fun_prop) ⟨hlo.le,hhi.le⟩
  have hzlo : (rootLoQ i:ℝ)< z := by
    apply lt_of_le_of_ne hz.1
    intro he
    have := hzero
    rw [←he] at this
    linarith
  have hzhi : z<(rootHiQ i:ℝ) := by
    apply lt_of_le_of_ne hz.2
    intro he
    rw [he] at hzero
    linarith
  have hzp : 0< z := lt_trans (by cases i <;> norm_num [rootLoQ]) hzlo
  refine ⟨z,⟨hzlo,hzhi⟩,hzp,hzhi.trans (by cases i <;> norm_num [rootHiQ]),hzero,?_⟩
  intro w hwp hw
  have ha : 0<(rateActiveQ (multipleRateCase i):ℝ) := by
    cases i <;> norm_num [rateActiveQ,multipleRateCase]
  have hh : 0<(rateUpperQ (multipleRateCase i):ℝ) := by
    cases i <;> norm_num [rateUpperQ,multipleRateCase]
  have hp : 0<(rateActiveQ (multipleRateCase i):ℝ)*(101/200)*(w+z)+
      (rateUpperQ (multipleRateCase i):ℝ)*(1/200) := by positivity
  have he : (w-z)*((rateActiveQ (multipleRateCase i):ℝ)*(101/200)*(w+z)+
      (rateUpperQ (multipleRateCase i):ℝ)*(1/200))=0 := by
    dsimp [chernoffPolynomial] at hw hzero
    nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hp.ne')

end FCAppendix.Affine.Hybrid.Multiple03
