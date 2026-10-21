import FCAppendix.Affine.Uniform07Finishing.Early.Definitions

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Early
open FCAppendix.Affine.Uniform07 MeasureTheory Set

set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
def floorLog : LogCertificate (4577 / 3600) where
  lo := (120054958104720358277967 / 500000000000000000000000)
  hi := (240109916209440716555939 / 1000000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def lowLeftFirstLog : LogCertificate (3 / 4) where
  lo := (-143841036225890463719611 / 500000000000000000000000)
  hi := (-287682072451780927439217 / 1000000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def lowLeftSecondLog : LogCertificate (167 / 230) where
  lo := (-80021374126610066891249 / 250000000000000000000000)
  hi := (-320085496506440267564991 / 1000000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def lowRightLog : LogCertificate (199 / 200) where
  lo := (-626567727943035255387 / 125000000000000000000000)
  hi := (-5012541823544282043091 / 1000000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

end FCAppendix.Affine.Uniform07Finishing.Early
