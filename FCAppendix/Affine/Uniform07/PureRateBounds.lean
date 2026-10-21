import FCAppendix.Affine.Uniform07.SourceRateBounds

namespace FCAppendix.Affine.Uniform07

def pureParameterBox (i : Row) (z : ℚ) : Box :=
  Box.sub (Box.scale (1/2) (Box.add (Box.point 1) (cutoffBox i)))
    (Box.scale z (cutoffBox i))

theorem pureParameterBox_ok (i : Row) (z : ℚ) :
    (pureParameterBox i z).Holds (pureParameter i (z:ℝ)) := by
  simpa [pureParameterBox,pureParameter,div_eq_mul_inv,mul_comm] using
    Box.sub_ok (Box.scale_ok (1/2) (Box.add_ok (Box.point_ok 1) (cutoffBox_ok i)))
      (Box.scale_ok z (cutoffBox_ok i))

def first_pure_lowPBox : Box := pureParameterBox .first (739/1000)
def first_pure_lowRatio1 : Box := Box.div (Box.point (999/2000)) first_pure_lowPBox
def first_pure_lowRatio2 : Box := Box.div (Box.point (1001/2000)) (Box.sub (Box.point 1) first_pure_lowPBox)
theorem first_pure_lowRatio1_ok : first_pure_lowRatio1.Holds (rho/pureParameter .first (739/1000)) := by
  have h := Box.div_ok (a:=Box.point (999/2000))
    (b:=first_pure_lowPBox) (by norm_num [first_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ])
    (Box.point_ok (999/2000)) (pureParameterBox_ok .first (739/1000))
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at h
  simpa only [rho,first_pure_lowRatio1] using h

theorem first_pure_lowRatio2_ok : first_pure_lowRatio2.Holds ((1-rho)/(1-pureParameter .first (739/1000))) := by
  have h := Box.div_ok (a:=Box.point (1001/2000))
    (b:=Box.sub (Box.point 1) first_pure_lowPBox)
    (by norm_num [first_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ])
    (Box.point_ok (1001/2000)) (Box.sub_ok (Box.point_ok 1) (pureParameterBox_ok .first (739/1000)))
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] at h
  convert h using 1 <;> norm_num [rho,first_pure_lowRatio2]

def first_pure_lowL1lo : LogCertificate first_pure_lowRatio1.lo where
  lo := (-487230531124819527178633833/1000000000000000000000000000000)
  hi := (-48723053112481952717863383/100000000000000000000000000000)
  n := 32
  q_pos := by norm_num [first_pure_lowRatio1,first_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  lo_small := by norm_num [first_pure_lowRatio1,first_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  hi_small := by norm_num [first_pure_lowRatio1,first_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  lower_check := by norm_num [first_pure_lowRatio1,first_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  upper_check := by norm_num [first_pure_lowRatio1,first_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]

def first_pure_lowL1hi : LogCertificate first_pure_lowRatio1.hi where
  lo := (-487230531124819527178633833/1000000000000000000000000000000)
  hi := (-48723053112481952717863383/100000000000000000000000000000)
  n := 32
  q_pos := by norm_num [first_pure_lowRatio1,first_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  lo_small := by norm_num [first_pure_lowRatio1,first_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  hi_small := by norm_num [first_pure_lowRatio1,first_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  lower_check := by norm_num [first_pure_lowRatio1,first_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  upper_check := by norm_num [first_pure_lowRatio1,first_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]

def first_pure_lowL2lo : LogCertificate first_pure_lowRatio2.lo where
  lo := (60811730171407262922933497/125000000000000000000000000000)
  hi := (486493841371258103383467979/1000000000000000000000000000000)
  n := 32
  q_pos := by norm_num [first_pure_lowRatio2,first_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  lo_small := by norm_num [first_pure_lowRatio2,first_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  hi_small := by norm_num [first_pure_lowRatio2,first_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  lower_check := by norm_num [first_pure_lowRatio2,first_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  upper_check := by norm_num [first_pure_lowRatio2,first_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]

def first_pure_lowL2hi : LogCertificate first_pure_lowRatio2.hi where
  lo := (60811730171407262922933497/125000000000000000000000000000)
  hi := (486493841371258103383467979/1000000000000000000000000000000)
  n := 32
  q_pos := by norm_num [first_pure_lowRatio2,first_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  lo_small := by norm_num [first_pure_lowRatio2,first_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  hi_small := by norm_num [first_pure_lowRatio2,first_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  lower_check := by norm_num [first_pure_lowRatio2,first_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  upper_check := by norm_num [first_pure_lowRatio2,first_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]

def first_pure_lowBox : Box := Box.add
  (Box.scale (999/2000) (logBox first_pure_lowRatio1 first_pure_lowL1lo first_pure_lowL1hi))
  (Box.scale (1001/2000) (logBox first_pure_lowRatio2 first_pure_lowL2lo first_pure_lowL2hi))
theorem first_pure_lowBox_ok : first_pure_lowBox.Holds (pureRate .first (739/1000)) := by
  have h := Box.add_ok
    (Box.scale_ok (999/2000) (logBox_ok first_pure_lowL1lo first_pure_lowL1hi first_pure_lowRatio1_ok))
    (Box.scale_ok (1001/2000) (logBox_ok first_pure_lowL2lo first_pure_lowL2hi first_pure_lowRatio2_ok))
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at h
  convert h using 1 <;> norm_num [pureRate,rho,first_pure_lowBox]
theorem first_pure_low : pureRate .first (739/1000) < ((2962933/25000000000000):ℝ) := by
  apply Box.upper_real first_pure_lowBox_ok
  norm_num [first_pure_lowBox,Box.add,Box.mul,Box.scale,Box.point,
    logBox,first_pure_lowL1lo,first_pure_lowL1hi,first_pure_lowL2lo,first_pure_lowL2hi]

def first_pure_entryPBox : Box := pureParameterBox .first (3/4)
def first_pure_entryRatio1 : Box := Box.div (Box.point (999/2000)) first_pure_entryPBox
def first_pure_entryRatio2 : Box := Box.div (Box.point (1001/2000)) (Box.sub (Box.point 1) first_pure_entryPBox)
theorem first_pure_entryRatio1_ok : first_pure_entryRatio1.Holds (rho/pureParameter .first (3/4)) := by
  have h := Box.div_ok (a:=Box.point (999/2000))
    (b:=first_pure_entryPBox) (by norm_num [first_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ])
    (Box.point_ok (999/2000)) (pureParameterBox_ok .first (3/4))
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at h
  simpa only [rho,first_pure_entryRatio1] using h

theorem first_pure_entryRatio2_ok : first_pure_entryRatio2.Holds ((1-rho)/(1-pureParameter .first (3/4))) := by
  have h := Box.div_ok (a:=Box.point (1001/2000))
    (b:=Box.sub (Box.point 1) first_pure_entryPBox)
    (by norm_num [first_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ])
    (Box.point_ok (1001/2000)) (Box.sub_ok (Box.point_ok 1) (pureParameterBox_ok .first (3/4)))
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] at h
  convert h using 1 <;> norm_num [rho,first_pure_entryRatio2]

def first_pure_entryL1lo : LogCertificate first_pure_entryRatio1.lo where
  lo := (-28975055749995147858344527/62500000000000000000000000000)
  hi := (-463600891999922365733512429/1000000000000000000000000000000)
  n := 32
  q_pos := by norm_num [first_pure_entryRatio1,first_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  lo_small := by norm_num [first_pure_entryRatio1,first_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  hi_small := by norm_num [first_pure_entryRatio1,first_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  lower_check := by norm_num [first_pure_entryRatio1,first_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  upper_check := by norm_num [first_pure_entryRatio1,first_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]

def first_pure_entryL1hi : LogCertificate first_pure_entryRatio1.hi where
  lo := (-28975055749995147858344527/62500000000000000000000000000)
  hi := (-463600891999922365733512429/1000000000000000000000000000000)
  n := 32
  q_pos := by norm_num [first_pure_entryRatio1,first_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  lo_small := by norm_num [first_pure_entryRatio1,first_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  hi_small := by norm_num [first_pure_entryRatio1,first_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  lower_check := by norm_num [first_pure_entryRatio1,first_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  upper_check := by norm_num [first_pure_entryRatio1,first_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]

def first_pure_entryL2lo : LogCertificate first_pure_entryRatio2.lo where
  lo := (28930562364567658747175363/62500000000000000000000000000)
  hi := (462888997833082539954805811/1000000000000000000000000000000)
  n := 32
  q_pos := by norm_num [first_pure_entryRatio2,first_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  lo_small := by norm_num [first_pure_entryRatio2,first_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  hi_small := by norm_num [first_pure_entryRatio2,first_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  lower_check := by norm_num [first_pure_entryRatio2,first_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  upper_check := by norm_num [first_pure_entryRatio2,first_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]

def first_pure_entryL2hi : LogCertificate first_pure_entryRatio2.hi where
  lo := (28930562364567658747175363/62500000000000000000000000000)
  hi := (462888997833082539954805811/1000000000000000000000000000000)
  n := 32
  q_pos := by norm_num [first_pure_entryRatio2,first_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  lo_small := by norm_num [first_pure_entryRatio2,first_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  hi_small := by norm_num [first_pure_entryRatio2,first_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  lower_check := by norm_num [first_pure_entryRatio2,first_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  upper_check := by norm_num [first_pure_entryRatio2,first_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]

def first_pure_entryBox : Box := Box.add
  (Box.scale (999/2000) (logBox first_pure_entryRatio1 first_pure_entryL1lo first_pure_entryL1hi))
  (Box.scale (1001/2000) (logBox first_pure_entryRatio2 first_pure_entryL2lo first_pure_entryL2hi))
theorem first_pure_entryBox_ok : first_pure_entryBox.Holds (pureRate .first (3/4)) := by
  have h := Box.add_ok
    (Box.scale_ok (999/2000) (logBox_ok first_pure_entryL1lo first_pure_entryL1hi first_pure_entryRatio1_ok))
    (Box.scale_ok (1001/2000) (logBox_ok first_pure_entryL2lo first_pure_entryL2hi first_pure_entryRatio2_ok))
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at h
  convert h using 1 <;> norm_num [pureRate,rho,first_pure_entryBox]
theorem first_pure_entry : ((5364893/50000000000000):ℝ) < pureRate .first (3/4) := by
  apply Box.lower_real first_pure_entryBox_ok
  norm_num [first_pure_entryBox,Box.add,Box.mul,Box.scale,Box.point,
    logBox,first_pure_entryL1lo,first_pure_entryL1hi,first_pure_entryL2lo,first_pure_entryL2hi]

def second_pure_lowPBox : Box := pureParameterBox .second (691/1000)
def second_pure_lowRatio1 : Box := Box.div (Box.point (999/2000)) second_pure_lowPBox
def second_pure_lowRatio2 : Box := Box.div (Box.point (1001/2000)) (Box.sub (Box.point 1) second_pure_lowPBox)
theorem second_pure_lowRatio1_ok : second_pure_lowRatio1.Holds (rho/pureParameter .second (691/1000)) := by
  have h := Box.div_ok (a:=Box.point (999/2000))
    (b:=second_pure_lowPBox) (by norm_num [second_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ])
    (Box.point_ok (999/2000)) (pureParameterBox_ok .second (691/1000))
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at h
  simpa only [rho,second_pure_lowRatio1] using h

theorem second_pure_lowRatio2_ok : second_pure_lowRatio2.Holds ((1-rho)/(1-pureParameter .second (691/1000))) := by
  have h := Box.div_ok (a:=Box.point (1001/2000))
    (b:=Box.sub (Box.point 1) second_pure_lowPBox)
    (by norm_num [second_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ])
    (Box.point_ok (1001/2000)) (Box.sub_ok (Box.point_ok 1) (pureParameterBox_ok .second (691/1000)))
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] at h
  convert h using 1 <;> norm_num [rho,second_pure_lowRatio2]

def second_pure_lowL1lo : LogCertificate second_pure_lowRatio1.lo where
  lo := (-115131298499055624945909879/200000000000000000000000000000)
  hi := (-35978530780954882795596837/62500000000000000000000000000)
  n := 32
  q_pos := by norm_num [second_pure_lowRatio1,second_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  lo_small := by norm_num [second_pure_lowRatio1,second_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  hi_small := by norm_num [second_pure_lowRatio1,second_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  lower_check := by norm_num [second_pure_lowRatio1,second_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  upper_check := by norm_num [second_pure_lowRatio1,second_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]

def second_pure_lowL1hi : LogCertificate second_pure_lowRatio1.hi where
  lo := (-115131298499055624945909879/200000000000000000000000000000)
  hi := (-35978530780954882795596837/62500000000000000000000000000)
  n := 32
  q_pos := by norm_num [second_pure_lowRatio1,second_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  lo_small := by norm_num [second_pure_lowRatio1,second_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  hi_small := by norm_num [second_pure_lowRatio1,second_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  lower_check := by norm_num [second_pure_lowRatio1,second_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  upper_check := by norm_num [second_pure_lowRatio1,second_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]

def second_pure_lowL2lo : LogCertificate second_pure_lowRatio2.lo where
  lo := (114967381527765180086398937/200000000000000000000000000000)
  hi := (8981826681856654694249917/15625000000000000000000000000)
  n := 32
  q_pos := by norm_num [second_pure_lowRatio2,second_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  lo_small := by norm_num [second_pure_lowRatio2,second_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  hi_small := by norm_num [second_pure_lowRatio2,second_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  lower_check := by norm_num [second_pure_lowRatio2,second_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  upper_check := by norm_num [second_pure_lowRatio2,second_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]

def second_pure_lowL2hi : LogCertificate second_pure_lowRatio2.hi where
  lo := (114967381527765180086398937/200000000000000000000000000000)
  hi := (8981826681856654694249917/15625000000000000000000000000)
  n := 32
  q_pos := by norm_num [second_pure_lowRatio2,second_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  lo_small := by norm_num [second_pure_lowRatio2,second_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  hi_small := by norm_num [second_pure_lowRatio2,second_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  lower_check := by norm_num [second_pure_lowRatio2,second_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  upper_check := by norm_num [second_pure_lowRatio2,second_pure_lowPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]

def second_pure_lowBox : Box := Box.add
  (Box.scale (999/2000) (logBox second_pure_lowRatio1 second_pure_lowL1lo second_pure_lowL1hi))
  (Box.scale (1001/2000) (logBox second_pure_lowRatio2 second_pure_lowL2lo second_pure_lowL2hi))
theorem second_pure_lowBox_ok : second_pure_lowBox.Holds (pureRate .second (691/1000)) := by
  have h := Box.add_ok
    (Box.scale_ok (999/2000) (logBox_ok second_pure_lowL1lo second_pure_lowL1hi second_pure_lowRatio1_ok))
    (Box.scale_ok (1001/2000) (logBox_ok second_pure_lowL2lo second_pure_lowL2hi second_pure_lowRatio2_ok))
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at h
  convert h using 1 <;> norm_num [pureRate,rho,second_pure_lowBox]
theorem second_pure_low : pureRate .second (691/1000) < ((4136357/25000000000000):ℝ) := by
  apply Box.upper_real second_pure_lowBox_ok
  norm_num [second_pure_lowBox,Box.add,Box.mul,Box.scale,Box.point,
    logBox,second_pure_lowL1lo,second_pure_lowL1hi,second_pure_lowL2lo,second_pure_lowL2hi]

def second_pure_entryPBox : Box := pureParameterBox .second (7/10)
def second_pure_entryRatio1 : Box := Box.div (Box.point (999/2000)) second_pure_entryPBox
def second_pure_entryRatio2 : Box := Box.div (Box.point (1001/2000)) (Box.sub (Box.point 1) second_pure_entryPBox)
theorem second_pure_entryRatio1_ok : second_pure_entryRatio1.Holds (rho/pureParameter .second (7/10)) := by
  have h := Box.div_ok (a:=Box.point (999/2000))
    (b:=second_pure_entryPBox) (by norm_num [second_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ])
    (Box.point_ok (999/2000)) (pureParameterBox_ok .second (7/10))
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at h
  simpa only [rho,second_pure_entryRatio1] using h

theorem second_pure_entryRatio2_ok : second_pure_entryRatio2.Holds ((1-rho)/(1-pureParameter .second (7/10))) := by
  have h := Box.div_ok (a:=Box.point (1001/2000))
    (b:=Box.sub (Box.point 1) second_pure_entryPBox)
    (by norm_num [second_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ])
    (Box.point_ok (1001/2000)) (Box.sub_ok (Box.point_ok 1) (pureParameterBox_ok .second (7/10)))
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] at h
  convert h using 1 <;> norm_num [rho,second_pure_entryRatio2]

def second_pure_entryL1lo : LogCertificate second_pure_entryRatio1.lo where
  lo := (-138908304813832727390527217/250000000000000000000000000000)
  hi := (-111126643851066181912421773/200000000000000000000000000000)
  n := 32
  q_pos := by norm_num [second_pure_entryRatio1,second_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  lo_small := by norm_num [second_pure_entryRatio1,second_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  hi_small := by norm_num [second_pure_entryRatio1,second_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  lower_check := by norm_num [second_pure_entryRatio1,second_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  upper_check := by norm_num [second_pure_entryRatio1,second_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]

def second_pure_entryL1hi : LogCertificate second_pure_entryRatio1.hi where
  lo := (-138908304813832727390527217/250000000000000000000000000000)
  hi := (-111126643851066181912421773/200000000000000000000000000000)
  n := 32
  q_pos := by norm_num [second_pure_entryRatio1,second_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  lo_small := by norm_num [second_pure_entryRatio1,second_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  hi_small := by norm_num [second_pure_entryRatio1,second_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  lower_check := by norm_num [second_pure_entryRatio1,second_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  upper_check := by norm_num [second_pure_entryRatio1,second_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]

def second_pure_entryL2lo : LogCertificate second_pure_entryRatio2.lo where
  lo := (554831037504945998266092083/1000000000000000000000000000000)
  hi := (277415518752472999133046043/500000000000000000000000000000)
  n := 32
  q_pos := by norm_num [second_pure_entryRatio2,second_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  lo_small := by norm_num [second_pure_entryRatio2,second_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  hi_small := by norm_num [second_pure_entryRatio2,second_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  lower_check := by norm_num [second_pure_entryRatio2,second_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  upper_check := by norm_num [second_pure_entryRatio2,second_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]

def second_pure_entryL2hi : LogCertificate second_pure_entryRatio2.hi where
  lo := (554831037504945998266092083/1000000000000000000000000000000)
  hi := (277415518752472999133046043/500000000000000000000000000000)
  n := 32
  q_pos := by norm_num [second_pure_entryRatio2,second_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  lo_small := by norm_num [second_pure_entryRatio2,second_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  hi_small := by norm_num [second_pure_entryRatio2,second_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  lower_check := by norm_num [second_pure_entryRatio2,second_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]
  upper_check := by norm_num [second_pure_entryRatio2,second_pure_entryPBox,pureParameterBox,Box.sub,Box.add,Box.neg,Box.mul,Box.div,Box.inv,Box.point,Box.scale,
    cutoffBox,cutoffDenBox,logX,log_first_x,log_second_x,LogCertificate.box,xQ,xiQ,etaQ,expBox,expPolyQ,expErrorQ,Box.inflate,Finset.sum_range_succ,Nat.factorial]

def second_pure_entryBox : Box := Box.add
  (Box.scale (999/2000) (logBox second_pure_entryRatio1 second_pure_entryL1lo second_pure_entryL1hi))
  (Box.scale (1001/2000) (logBox second_pure_entryRatio2 second_pure_entryL2lo second_pure_entryL2hi))
theorem second_pure_entryBox_ok : second_pure_entryBox.Holds (pureRate .second (7/10)) := by
  have h := Box.add_ok
    (Box.scale_ok (999/2000) (logBox_ok second_pure_entryL1lo second_pure_entryL1hi second_pure_entryRatio1_ok))
    (Box.scale_ok (1001/2000) (logBox_ok second_pure_entryL2lo second_pure_entryL2hi second_pure_entryRatio2_ok))
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at h
  convert h using 1 <;> norm_num [pureRate,rho,second_pure_entryBox]
theorem second_pure_entry : ((123313/800000000000):ℝ) < pureRate .second (7/10) := by
  apply Box.lower_real second_pure_entryBox_ok
  norm_num [second_pure_entryBox,Box.add,Box.mul,Box.scale,Box.point,
    logBox,second_pure_entryL1lo,second_pure_entryL1hi,second_pure_entryL2lo,second_pure_entryL2hi]

end FCAppendix.Affine.Uniform07
