import FCAppendix.Exclusive.NarrowExistenceCalculus
import FCAppendix.Exclusive.NarrowExistenceTransport

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Existence
open Set
open scoped BigOperators

def actualCross (r a W v g z : ℝ) (S' S'' T' T'' H' H'' : ℝ → ℝ) : ℝ :=
  crossCoefficient r (1-logAllocation r a W z) (logShare r W z) (Real.exp z)
    (v*S' (logAllocation r a W z)-Real.exp z*T' (logAllocation r a W z)-
      g*H' (logAllocation r a W z))
    (v*S'' (logAllocation r a W z)-Real.exp z*T'' (logAllocation r a W z)-
      g*H'' (logAllocation r a W z))
    (T' (logAllocation r a W z))

theorem hasDerivAt_score_logRivalSum (r a v g z t : ℝ) (hr : r ≠ 0)
    (S' S'' T T' T'' H' H'' : ℝ → ℝ)
    (hS : HasDerivAt S' (S'' (logAllocation r a (Real.exp t) z))
      (logAllocation r a (Real.exp t) z))
    (hT : HasDerivAt T (T' (logAllocation r a (Real.exp t) z))
      (logAllocation r a (Real.exp t) z))
    (hT' : HasDerivAt T' (T'' (logAllocation r a (Real.exp t) z))
      (logAllocation r a (Real.exp t) z))
    (hH : HasDerivAt H' (H'' (logAllocation r a (Real.exp t) z))
      (logAllocation r a (Real.exp t) z)) :
    HasDerivAt (fun s : ℝ => score r a (Real.exp s) v g S' T T' H' z)
      (-actualCross r a (Real.exp t) v g z S' S'' T' T'' H' H''/r) t := by
  have h := (hasDerivAt_score_rivalSum r a (Real.exp t) v g z (Real.exp_pos t).le
    S' S'' T T' T'' H' H'' hS hT hT' hH).comp t (Real.hasDerivAt_exp t)
  have hc := cross_eq_rivalSumDerivative r a (Real.exp t) z (Real.exp z)
    (v*S' (logAllocation r a (Real.exp t) z)-
      Real.exp z*T' (logAllocation r a (Real.exp t) z)-g*H' (logAllocation r a (Real.exp t) z))
    (v*S'' (logAllocation r a (Real.exp t) z)-
      Real.exp z*T'' (logAllocation r a (Real.exp t) z)-g*H'' (logAllocation r a (Real.exp t) z))
    (T' (logAllocation r a (Real.exp t) z)) (Real.exp_pos t).le
  apply h.congr_deriv
  apply (eq_div_iff hr).2
  dsimp [actualCross]
  nlinarith only [hc]

theorem score_logRivalSum_bound (r a v g z Wlo Whi K : ℝ)
    (hr : 0 < r) (hlo : 0 < Wlo)
    (S' S'' T T' T'' H' H'' : ℝ → ℝ)
    (hS : ∀ p, HasDerivAt S' (S'' p) p)
    (hT : ∀ p, HasDerivAt T (T' p) p)
    (hT' : ∀ p, HasDerivAt T' (T'' p) p)
    (hH : ∀ p, HasDerivAt H' (H'' p) p)
    (hcross : ∀ W ∈ Icc Wlo Whi, |actualCross r a W v g z S' S'' T' T'' H' H''| ≤ K)
    (x y : ℝ) (hx : x ∈ Icc (Real.log Wlo) (Real.log Whi))
    (hy : y ∈ Icc (Real.log Wlo) (Real.log Whi)) (hhi : 0 < Whi) :
    |score r a (Real.exp x) v g S' T T' H' z-
      score r a (Real.exp y) v g S' T T' H' z| ≤ (K/r)*|x-y| := by
  have he : ∀ t ∈ Icc (Real.log Wlo) (Real.log Whi), Real.exp t ∈ Icc Wlo Whi := by
    intro t ht
    constructor
    · simpa only [Real.exp_log hlo] using Real.exp_le_exp.mpr ht.1
    · simpa only [Real.exp_log hhi] using Real.exp_le_exp.mpr ht.2
  have hd (t : ℝ) := hasDerivAt_score_logRivalSum r a v g z t hr.ne'
    S' S'' T T' T'' H' H'' (hS _) (hT _) (hT' _) (hH _)
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hd t).hasDerivWithinAt)
    (fun t ht => by
      simp only [Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hr]
      exact div_le_div_of_nonneg_right (hcross (Real.exp t) (he t ht)) hr.le)
    (convex_Icc (Real.log Wlo) (Real.log Whi)) hy hx
  simpa only [Real.norm_eq_abs] using hmv

theorem actual_profile_score_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (r a v g z Wlo Whi K delta : ℝ) (hr : 0 < r) (hlo : 0 < Wlo) (hK : 0 ≤ K)
    (S' S'' T T' T'' H' H'' : ℝ → ℝ)
    (hS : ∀ p, HasDerivAt S' (S'' p) p)
    (hT : ∀ p, HasDerivAt T (T' p) p)
    (hT' : ∀ p, HasDerivAt T' (T'' p) p)
    (hH : ∀ p, HasDerivAt H' (H'' p) p)
    (hcross : ∀ W ∈ Icc Wlo Whi, |actualCross r a W v g z S' S'' T' T'' H' H''| ≤ K)
    (u w : ι → ℝ) (huw : ∀ i, |u i-w i| ≤ delta)
    (hu : Exclusive.Existence.inverseLogBidSum r u ∈ Icc Wlo Whi)
    (hw : Exclusive.Existence.inverseLogBidSum r w ∈ Icc Wlo Whi) :
    |score r a (Exclusive.Existence.inverseLogBidSum r u) v g S' T T' H' z-
      score r a (Exclusive.Existence.inverseLogBidSum r w) v g S' T T' H' z| ≤ K*delta := by
  have hup := Exclusive.Existence.inverseLogBidSum_pos r u
  have hwp := Exclusive.Existence.inverseLogBidSum_pos r w
  have hhi : 0 < Whi := hup.trans_le hu.2
  have hlu : Real.log (Exclusive.Existence.inverseLogBidSum r u) ∈
      Icc (Real.log Wlo) (Real.log Whi) :=
    ⟨Real.log_le_log hlo hu.1, Real.log_le_log hup hu.2⟩
  have hlw : Real.log (Exclusive.Existence.inverseLogBidSum r w) ∈
      Icc (Real.log Wlo) (Real.log Whi) :=
    ⟨Real.log_le_log hlo hw.1, Real.log_le_log hwp hw.2⟩
  have hs := score_logRivalSum_bound r a v g z Wlo Whi K hr hlo
    S' S'' T T' T'' H' H'' hS hT hT' hH hcross _ _ hlu hlw hhi
  rw [Real.exp_log hup, Real.exp_log hwp] at hs
  calc
    _ ≤ (K/r)*|Real.log (Exclusive.Existence.inverseLogBidSum r u)-
        Real.log (Exclusive.Existence.inverseLogBidSum r w)| := hs
    _ ≤ (K/r)*(r*delta) := mul_le_mul_of_nonneg_left
      (Exclusive.Existence.abs_log_inverseLogBidSum_sub_le hr.le u w huw)
      (div_nonneg hK hr.le)
    _ = K*delta := by field_simp

end FCAppendix.Exclusive.Narrow.Existence
