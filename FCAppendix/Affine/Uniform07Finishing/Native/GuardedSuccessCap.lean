import FCAppendix.Affine.Uniform07Finishing.Native.GuardedCorrespondence
import FCAppendix.Affine.Uniform07Finishing.Native.ConditionalSuccessCap

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Weighted

open MeasureTheory ProbabilityTheory Bayes Game Set Classical
open FCAppendix.Affine
open StrictNative
open Existence.PayOnceBounded (listBids)
open scoped BigOperators

def lowerMarginalCap (ξ lo Rhi : ℝ) : ℝ := max 0 ((1 - lo / Rhi) / ξ)

lemma lowerMarginalCap_nonneg (ξ lo Rhi : ℝ) :
    0 ≤ lowerMarginalCap ξ lo Rhi := le_max_left _ _

lemma lowerMarginalCap_antitone_root {ξ lo₀ lo₁ Rhi : ℝ}
    (hξ : 0 < ξ) (hRhi : 0 < Rhi) (hlo : lo₀ ≤ lo₁) :
    lowerMarginalCap ξ lo₁ Rhi ≤ lowerMarginalCap ξ lo₀ Rhi := by
  apply max_le_max le_rfl
  exact div_le_div_of_nonneg_right
    (sub_le_sub_left (div_le_div_of_nonneg_right hlo hRhi.le) 1) hξ.le

lemma lowerMarginalCap_lt_one {ξ lo Rhi : ℝ}
    (hξ : 0 < ξ) (hRhi : 0 < Rhi) (hguard : (1 - ξ) * Rhi < lo) :
    lowerMarginalCap ξ lo Rhi < 1 := by
  have hg : 1 - ξ < lo / Rhi := (lt_div_iff₀ hRhi).mpr hguard
  have hraw : (1 - lo / Rhi) / ξ < 1 := (div_lt_one hξ).mpr (by linarith)
  exact max_lt (by norm_num) hraw

theorem clipped_exposure_le_lowerMarginalCap {ξ lo Rhi z b : ℝ}
    (hξ : 0 < ξ) (hlo : 0 < lo) (_hRhi : 0 < Rhi)
    (hz : lo ≤ z) (hb : b ≤ Rhi) :
    ClippedResidual.exposure ξ z b ≤ lowerMarginalCap ξ lo Rhi := by
  have hz0 : 0 < z := hlo.trans_le hz
  by_cases hbz : b ≤ z
  · rw [ClippedResidual.exposure_zero hbz]
    exact lowerMarginalCap_nonneg ξ lo Rhi
  · have hzb : z < b := lt_of_not_ge hbz
    have hb0 : 0 < b := hz0.trans hzb
    have hratio : lo / Rhi ≤ z / b :=
      (div_le_div_of_nonneg_left hlo.le hb0 hb).trans
        (div_le_div_of_nonneg_right hz hb0.le)
    have hraw : (b - z) / (ξ * b) = (1 - z / b) / ξ := by
      field_simp [hξ.ne', hb0.ne']
    rw [ClippedResidual.exposure, max_eq_left hzb.le,
      max_eq_right (sub_pos.mpr hzb).le, hraw]
    exact (min_le_right _ _).trans
      ((div_le_div_of_nonneg_right (sub_le_sub_left hratio 1) hξ.le).trans
        (le_max_right _ _))

section FiniteVector
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem canonical_marginal_le_lowerMarginalCap {ξ lo R Rhi z : ℝ}
    (b : ι → ℝ) (d : ℕ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hlo : 0 < lo) (hRhi : 0 < Rhi) (hRRhi : R ≤ Rhi)
    (hz : lo ≤ z) (hguard : (1 - ξ) * R ≤ lo)
    (hb : ∀ i, b i ≤ R)
    (hroot : (∑ i, ClippedResidual.exposure ξ z (b i)) = (d : ℝ)) :
    ∀ i, EqualCapacity.positiveMarginal ξ d b i ≤ lowerMarginalCap ξ lo Rhi := by
  have he := canonical_eq_clipped_at_root b d hξ hξ1 (hlo.trans_le hz)
    (hguard.trans hz) hb hroot
  intro i
  rw [he]
  exact clipped_exposure_le_lowerMarginalCap hξ hlo hRhi hz ((hb i).trans hRRhi)

end FiniteVector

section NativeContext
variable {m : ℕ} [Nonempty (Fin m)]

theorem acceptance_equal_le_lowerMarginalCap {ξ lo R Rhi z : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (plan : ClassifiedContext m → Option (Finset (Fin m)))
    (X : ClassifiedContext m) (he : budget c 0 X = budget c 1 X)
    (hlo : 0 < lo) (hRhi : 0 < Rhi) (hRRhi : R ≤ Rhi)
    (hz : lo ≤ z) (hguard : (1 - ξ) * R ≤ lo)
    (hb : ∀ i, entryBid (X.1 i) ≤ R)
    (hroot : (∑ i, ClippedResidual.exposure ξ z (entryBid (X.1 i))) =
      (budget c 0 X : ℝ)) :
    ∀ j i, acceptance ξ hξ hξ1 c plan j X i ≤ lowerMarginalCap ξ lo Rhi := by
  intro j i
  rw [acceptance_equal ξ hξ hξ1 c plan j X he]
  apply canonical_marginal_le_lowerMarginalCap (listBids X.1) (budget c 0 X)
    hξ hξ1 hlo hRhi hRRhi hz hguard
  · intro k
    simpa only [listBids_eq_entry] using hb k
  · simpa only [listBids_eq_entry] using hroot

theorem acceptance_weighted_le_lowerMarginalCap {ξ lo R Rhi z : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (plan : ClassifiedContext m → Option (Finset (Fin m)))
    (X : ClassifiedContext m) (he : budget c 0 X ≠ budget c 1 X)
    (hu : usable ξ c plan X) (hR : 0 < R)
    (hlo : 0 < lo) (hRhi : 0 < Rhi) (hRRhi : R ≤ Rhi)
    (hz : lo ≤ z) (hguard : (1 - ξ) * R ≤ lo)
    (hb : ∀ i, entryBid (X.1 i) ≤ R)
    (hroot : ClippedResidual.remainingDemand ξ (fun i => entryBid (X.1 i))
      (candidate plan X) z = (commonBudget c X : ℝ)) :
    ∀ i, i ∉ candidate plan X →
      ∀ j, acceptance ξ hξ hξ1 c plan j X i ≤ lowerMarginalCap ξ lo Rhi := by
  have hz0 : 0 < z := hlo.trans_le hz
  have hsum : (∑ i, ClippedResidual.exposure ξ z
      (listBids (remainder X.1 (candidate plan X)) i)) = (commonBudget c X : ℝ) := by
    calc
      _ = ClippedResidual.remainingDemand ξ (fun i => entryBid (X.1 i))
          (candidate plan X) z := by
        unfold ClippedResidual.remainingDemand
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : k ∈ candidate plan X
        · simp [remainder_bid, hk, ClippedResidual.exposure_zero hz0.le]
        · simp only [listBids_eq_entry,remainder_entry,if_neg hk]
      _ = _ := hroot
  have hb' : ∀ k, listBids (remainder X.1 (candidate plan X)) k ≤ R := by
    intro k
    rw [listBids_eq_entry, remainder_entry]
    split_ifs
    · exact hR.le
    · exact hb k
  have hcap := canonical_marginal_le_lowerMarginalCap
    (listBids (remainder X.1 (candidate plan X))) (commonBudget c X)
    hξ hξ1 hlo hRhi hRRhi hz hguard hb' hsum
  intro i hi j
  rw [acceptance_weighted ξ hξ hξ1 c plan j X he hu]
  simpa only [hi, and_false, if_false] using hcap i

theorem source_U4_acceptance_le_lowerMarginalCap {ξ lo hi slack R Rhi : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (plan : ClassifiedContext m → Option (Finset (Fin m)))
    (X : ClassifiedContext m) (hX : NonnegativeList X.1)
    (E : Finset (Fin m)) (hplan : plan X = some E)
    (hR : 0 < R) (hlo : 0 < lo) (hlh : lo < hi)
    (hRhi : 0 < Rhi) (hRRhi : R ≤ Rhi)
    (hguard : (1 - ξ) * R < lo)
    (hb : ∀ k, entryBid (X.1 k) ≤ R)
    (hd : 0 < min (budget c 0 X) (budget c 1 X)) (hslack : 0 < slack)
    (hcard : E.card = max (budget c 0 X) (budget c 1 X) -
      min (budget c 0 X) (budget c 1 X))
    (hlow : (min (budget c 0 X) (budget c 1 X) : ℝ) + E.card + slack <
      ∑ k, ClippedResidual.exposure ξ lo (entryBid (X.1 k)))
    (hhigh : (∑ k, ClippedResidual.exposure ξ hi (entryBid (X.1 k))) <
      (min (budget c 0 X) (budget c 1 X) : ℝ) - slack)
    (hE : ∀ k ∈ E, hi ≤ entryBid (X.1 k)) :
    ∃ z ∈ Icc lo hi,
      ClippedResidual.remainingDemand ξ (fun k => entryBid (X.1 k)) E z =
        (commonBudget c X : ℝ) ∧
      ∀ k, k ∉ E → ∀ j,
        acceptance ξ hξ hξ1 c plan j X k ≤ lowerMarginalCap ξ lo Rhi := by
  obtain ⟨hvalid, z, hz, hr, hpc⟩ := source_U4_passes_native_test X.1 hX
    (budget c 0 X) (budget c 1 X) E hξ hξ1 hR hlo hlh hguard hb
    hd hslack hcard (by simpa only [Nat.cast_min] using hlow)
    (by simpa only [Nat.cast_min] using hhigh) hE
  have hcand : candidate plan X = E := by simp [candidate, hplan]
  refine ⟨z, hz, hr, ?_⟩
  intro k hk j
  by_cases he : budget c 0 X = budget c 1 X
  · have hE0 : E = ∅ := by
      apply Finset.card_eq_zero.mp
      simpa only [he, max_self, min_self, Nat.sub_self] using hcard
    have hsum : (∑ l, ClippedResidual.exposure ξ z (entryBid (X.1 l))) =
        (budget c 0 X : ℝ) := by
      simpa only [hE0, ClippedResidual.remainingDemand, Finset.notMem_empty,
        if_false, he, min_self] using hr
    exact acceptance_equal_le_lowerMarginalCap hξ hξ1 c plan X he
      hlo hRhi hRRhi hz.1 hguard.le hb hsum j k
  · have hu : usable ξ c plan X := by
      refine ⟨?_, ?_⟩
      · simp [hplan]
      · simpa only [hcand] using hvalid
    have hroot : ClippedResidual.remainingDemand ξ (fun l => entryBid (X.1 l))
        (candidate plan X) z = (commonBudget c X : ℝ) := by
      simpa only [hcand, commonBudget] using hr
    exact acceptance_weighted_le_lowerMarginalCap hξ hξ1 c plan X he hu hR
      hlo hRhi hRRhi hz.1 hguard.le hb hroot k (by simpa only [hcand] using hk) j

end NativeContext
end FCAppendix.Affine.Uniform07Finishing.Weighted
