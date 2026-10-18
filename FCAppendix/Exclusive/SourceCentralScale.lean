import FCAppendix.Exclusive.SourceLowTypeConstants
import FCAppendix.Exclusive.NarrowExistenceTariffJets

noncomputable section
namespace FCAppendix.Bayes.ExclusiveSource
open MeasureTheory Game Exclusive Exclusive.Narrow Set
open Exclusive.Narrow.Existence

theorem referenceBidScale_unique_eq_one (d : ℕ) (p : ℝ) (hp1 : p < 1) :
    referenceBidScale d .unique p = 1 := by
  have hq : (1-p)^d ≠ 0 := (pow_pos (sub_pos.mpr hp1) d).ne'
  simp [referenceBidScale,fTariff,fUnique,hq]

theorem exists_referenceBidScale_bounds (d : ℕ) (hd : 1 ≤ d) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p < 1) :
    ∃ scaleLo cap : ℝ, 0 < scaleLo ∧ scaleLo ≤ cap ∧
      ∀ a : UserTariff, a.Allowed → referenceBidScale d a p ∈ Icc scaleLo cap := by
  obtain ⟨Fmin,Fmax,_Dmin,_Dmax,hmin,hminmax,_hDmin,_hDminmax,hbounds⟩ :=
    source_tariff_uniform_bounds d hd hp0 le_rfl hp1
  let scaleLo := (1/Fmax)/(1-p)^d
  let cap := (1/Fmin)/(1-p)^d
  have hmax : 0 < Fmax := hmin.trans_le hminmax
  have hQ : 0 < (1-p)^d := pow_pos (sub_pos.mpr hp1) d
  have hlo : 0 < scaleLo := div_pos (one_div_pos.mpr hmax) hQ
  have hb (a : UserTariff) (ha : a.Allowed) : referenceBidScale d a p ∈ Icc scaleLo cap := by
    have hf := (hbounds a ha p ⟨le_rfl,le_rfl⟩).1
    have hfpos : 0 < fTariff d a p := hmin.trans_le hf.1
    exact ⟨div_le_div_of_nonneg_right (one_div_le_one_div_of_le hfpos hf.2) hQ.le,
      div_le_div_of_nonneg_right (one_div_le_one_div_of_le hmin hf.1) hQ.le⟩
  have hu := hb .unique trivial
  exact ⟨scaleLo,cap,hlo,hu.1.trans hu.2,hb⟩

theorem exists_scaled_referenceBidScale_bounds (d : ℕ) (hd : 1 ≤ d) (p H : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p < 1) (hH : 0 < H) :
    ∃ scaleLo cap : ℝ, 0 < scaleLo ∧ scaleLo ≤ cap ∧
      ∀ a : UserTariff, a.Allowed → H*referenceBidScale d a p ∈ Icc scaleLo cap := by
  obtain ⟨lo,cap,hlo,hlocap,hb⟩ := exists_referenceBidScale_bounds d hd p hp0 hp1
  exact ⟨H*lo,H*cap,mul_pos hH hlo,mul_le_mul_of_nonneg_left hlocap hH.le,
    fun a ha => ⟨mul_le_mul_of_nonneg_left (hb a ha).1 hH.le,
      mul_le_mul_of_nonneg_left (hb a ha).2 hH.le⟩⟩

theorem scarce_source_price_separation (d : ℕ) (hd : 1 ≤ d) (p : ℝ)
    (hp1 : p < 1) (hscarce : 1/((d+1:ℕ):ℝ) < p) :
    0 < (1-p)^d ∧ (1-p)^d < (1-1/((d+1:ℕ):ℝ))^d := by
  refine ⟨pow_pos (sub_pos.mpr hp1) d,?_⟩
  exact pow_lt_pow_left₀ (by linarith : 1-p < 1-1/((d+1:ℕ):ℝ))
    (sub_nonneg.mpr hp1.le) (by omega)

theorem exists_scarce_lowMarketConstants (d : ℕ) (hd : 1 ≤ d) (scaleLo p : ℝ)
    (hscaleLo : 0 < scaleLo) (hp1 : p < 1) (hscarce : 1/((d+1:ℕ):ℝ) < p) :
    Nonempty (LowMarketConstants (d+1) scaleLo ((1-p)^d)) := by
  have hp := scarce_source_price_separation d hd p hp1 hscarce
  apply exists_lowMarketConstants (d+1) (by omega) scaleLo ((1-p)^d) hscaleLo hp.1
  simpa only [Nat.add_sub_cancel] using hp.2

end FCAppendix.Bayes.ExclusiveSource
