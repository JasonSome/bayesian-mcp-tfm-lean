import FCAppendix.Affine.Hybrid.Multiple03.LogRemainder

set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
namespace FCAppendix.Affine.Hybrid.Multiple03
open FCAppendix.Affine.Uniform07

def log_band1 : LogCertificate (1901/1899) where
  lo := (1052631676143281/1000000000000000000)
  hi := (263157919035821/250000000000000000)
  n := 48
  q_pos := by norm_num
  lo_small := by norm_num
  hi_small := by norm_num
  lower_check := by norm_num [expBox,expErrorQ,expPolyQ,Box.inflate,Box.point,Finset.sum_range_succ]
  upper_check := by norm_num [expBox,expErrorQ,expPolyQ,Box.inflate,Box.point,Finset.sum_range_succ]

def log_band2 : LogCertificate (2101/2099) where
  lo := (952381024367427/1000000000000000000)
  hi := (95238102436743/100000000000000000)
  n := 48
  q_pos := by norm_num
  lo_small := by norm_num
  hi_small := by norm_num
  lower_check := by norm_num [expBox,expErrorQ,expPolyQ,Box.inflate,Box.point,Finset.sum_range_succ]
  upper_check := by norm_num [expBox,expErrorQ,expPolyQ,Box.inflate,Box.point,Finset.sum_range_succ]

def log_335_z : LogCertificate (250141/1250000) where
  lo := (-1608874071422323613/1000000000000000000)
  hi := (-160887407142232361/100000000000000000)
  n := 48
  q_pos := by norm_num
  lo_small := by norm_num
  hi_small := by norm_num
  lower_check := by norm_num [expBox,expErrorQ,expPolyQ,Box.inflate,Box.point,Finset.sum_range_succ]
  upper_check := by norm_num [expBox,expErrorQ,expPolyQ,Box.inflate,Box.point,Finset.sum_range_succ]

def log_335_mgf : LogCertificate (49527637332027/312500000000000) where
  lo := (-1842073625470040883/1000000000000000000)
  hi := (-23025920318375511/12500000000000000)
  n := 48
  q_pos := by norm_num
  lo_small := by norm_num
  hi_small := by norm_num
  lower_check := by norm_num [expBox,expErrorQ,expPolyQ,Box.inflate,Box.point,Finset.sum_range_succ]
  upper_check := by norm_num [expBox,expErrorQ,expPolyQ,Box.inflate,Box.point,Finset.sum_range_succ]

def log_335_kl1 : LogCertificate (11/15) where
  lo := (-310154928303839523/1000000000000000000)
  hi := (-1938468301898997/6250000000000000)
  n := 48
  q_pos := by norm_num
  lo_small := by norm_num
  hi_small := by norm_num
  lower_check := by norm_num [expBox,expErrorQ,expPolyQ,Box.inflate,Box.point,Finset.sum_range_succ]
  upper_check := by norm_num [expBox,expErrorQ,expPolyQ,Box.inflate,Box.point,Finset.sum_range_succ]

def log_335_kl2 : LogCertificate (101/65) where
  lo := (440733246945622339/1000000000000000000)
  hi := (220366623472811171/500000000000000000)
  n := 48
  q_pos := by norm_num
  lo_small := by norm_num
  hi_small := by norm_num
  lower_check := by norm_num [expBox,expErrorQ,expPolyQ,Box.inflate,Box.point,Finset.sum_range_succ]
  upper_check := by norm_num [expBox,expErrorQ,expPolyQ,Box.inflate,Box.point,Finset.sum_range_succ]

def log_665_z : LogCertificate (1463303/10000000) where
  lo := (-1921888883719307587/1000000000000000000)
  hi := (-30029513808114181/15625000000000000)
  n := 48
  q_pos := by norm_num
  lo_small := by norm_num
  hi_small := by norm_num
  lower_check := by norm_num [expBox,expErrorQ,expPolyQ,Box.inflate,Box.point,Finset.sum_range_succ]
  upper_check := by norm_num [expBox,expErrorQ,expPolyQ,Box.inflate,Box.point,Finset.sum_range_succ]

def log_665_mgf : LogCertificate (1521300924084597/20000000000000000) where
  lo := (-1257893766423999/488281250000000)
  hi := (-2576166433636349949/1000000000000000000)
  n := 48
  q_pos := by norm_num
  lo_small := by norm_num
  hi_small := by norm_num
  lower_check := by norm_num [expBox,expErrorQ,expPolyQ,Box.inflate,Box.point,Finset.sum_range_succ]
  upper_check := by norm_num [expBox,expErrorQ,expPolyQ,Box.inflate,Box.point,Finset.sum_range_succ]

def log_665_kl1 : LogCertificate (33/56) where
  lo := (-528844129268668999/1000000000000000000)
  hi := (-132211032317167249/250000000000000000)
  n := 48
  q_pos := by norm_num
  lo_small := by norm_num
  hi_small := by norm_num
  lower_check := by norm_num [expBox,expErrorQ,expPolyQ,Box.inflate,Box.point,Finset.sum_range_succ]
  upper_check := by norm_num [expBox,expErrorQ,expPolyQ,Box.inflate,Box.point,Finset.sum_range_succ]

def log_665_kl2 : LogCertificate (101/32) where
  lo := (574692307020766451/500000000000000000)
  hi := (229876922808306581/200000000000000000)
  n := 48
  q_pos := by norm_num
  lo_small := by norm_num
  hi_small := by norm_num
  lower_check := by norm_num [expBox,expErrorQ,expPolyQ,Box.inflate,Box.point,Finset.sum_range_succ]
  upper_check := by norm_num [expBox,expErrorQ,expPolyQ,Box.inflate,Box.point,Finset.sum_range_succ]

def log_tail_lower_z : LogCertificate (4/25) where
  lo := (-458145365937077533/250000000000000000)
  hi := (-1832581463748310129/1000000000000000000)
  n := 48
  q_pos := by norm_num
  lo_small := by norm_num
  hi_small := by norm_num
  lower_check := by norm_num [expBox,expErrorQ,expPolyQ,Box.inflate,Box.point,Finset.sum_range_succ]
  upper_check := by norm_num [expBox,expErrorQ,expPolyQ,Box.inflate,Box.point,Finset.sum_range_succ]

def log_tail_lower_mgf : LogCertificate (7837/62500) where
  lo := (-2076310448671628269/1000000000000000000)
  hi := (-1038155224335814133/500000000000000000)
  n := 48
  q_pos := by norm_num
  lo_small := by norm_num
  hi_small := by norm_num
  lower_check := by norm_num [expBox,expErrorQ,expPolyQ,Box.inflate,Box.point,Finset.sum_range_succ]
  upper_check := by norm_num [expBox,expErrorQ,expPolyQ,Box.inflate,Box.point,Finset.sum_range_succ]

def log_tail_lower_kl1 : LogCertificate (99/133) where
  lo := (-922591494022387/3125000000000000)
  hi := (-295229278087163837/1000000000000000000)
  n := 48
  q_pos := by norm_num
  lo_small := by norm_num
  hi_small := by norm_num
  lower_check := by norm_num [expBox,expErrorQ,expPolyQ,Box.inflate,Box.point,Finset.sum_range_succ]
  upper_check := by norm_num [expBox,expErrorQ,expPolyQ,Box.inflate,Box.point,Finset.sum_range_succ]

def log_tail_lower_kl2 : LogCertificate (101/67) where
  lo := (41042789745029339/100000000000000000)
  hi := (410427897450293393/1000000000000000000)
  n := 48
  q_pos := by norm_num
  lo_small := by norm_num
  hi_small := by norm_num
  lower_check := by norm_num [expBox,expErrorQ,expPolyQ,Box.inflate,Box.point,Finset.sum_range_succ]
  upper_check := by norm_num [expBox,expErrorQ,expPolyQ,Box.inflate,Box.point,Finset.sum_range_succ]

def log_tail_upper_z : LogCertificate (3/25) where
  lo := (-2120263536200091059/1000000000000000000)
  hi := (-132516471012505691/62500000000000000)
  n := 48
  q_pos := by norm_num
  lo_small := by norm_num
  hi_small := by norm_num
  lower_check := by norm_num [expBox,expErrorQ,expPolyQ,Box.inflate,Box.point,Finset.sum_range_succ]
  upper_check := by norm_num [expBox,expErrorQ,expPolyQ,Box.inflate,Box.point,Finset.sum_range_succ]

def log_tail_upper_mgf : LogCertificate (907/15625) where
  lo := (-1423242512244732823/500000000000000000)
  hi := (-2846485024489465643/1000000000000000000)
  n := 48
  q_pos := by norm_num
  lo_small := by norm_num
  hi_small := by norm_num
  lower_check := by norm_num [expBox,expErrorQ,expPolyQ,Box.inflate,Box.point,Finset.sum_range_succ]
  upper_check := by norm_num [expBox,expErrorQ,expPolyQ,Box.inflate,Box.point,Finset.sum_range_succ]

def log_tail_upper_kl1 : LogCertificate (33/56) := log_665_kl1

def log_tail_upper_kl2 : LogCertificate (101/32) := log_665_kl2

theorem rational_interval_certificate_for_bands :
    log_band1.box.Holds (Real.log (1901/1899:ℝ)) ∧
    log_band2.box.Holds (Real.log (2101/2099:ℝ)) :=
  ⟨by simpa using log_band1.correct,by simpa using log_band2.correct⟩

end FCAppendix.Affine.Hybrid.Multiple03
