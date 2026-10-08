import FCAppendix.Exclusive.NarrowCalculus
import FCAppendix.Exclusive.NarrowFiniteClassification

namespace FCAppendix.Exclusive.Narrow
open MeasureTheory Filter Topology Set

noncomputable def bidCoordinateScale (d : ℕ) (b p : ℝ) : ℝ := (d : ℝ) * b / (1 - p)

noncomputable def successSlope (d : ℕ) (p : ℝ) : ℝ :=
  ((d + 1 : ℕ) : ℝ) * (1 - p) ^ d

noncomputable def finiteCostTarget (d : ℕ) (a : UserTariff)
    (G : Schedule (d + 1)) (g b p : ℝ) : ℝ :=
  bidCoordinateScale d b p * binomialPolynomial (d + 1) a.charge p +
    b * binomialPolynomialDerivative (d + 1) a.charge p +
    g * binomialPolynomialDerivative (d + 1) G.charge p

theorem hasDerivAt_referenceBid_scale (d : ℕ) (hd : 1 ≤ d)
    (lam p : ℝ) (hp : p < 1) :
    HasDerivAt (referenceBid d lam) (bidCoordinateScale d (referenceBid d lam p) p) p := by
  convert hasDerivAt_referenceBid d hd lam p hp using 1
  dsimp [bidCoordinateScale, referenceBid]
  rw [pow_succ]
  field_simp [(sub_pos.mpr hp).ne', pow_ne_zero d (sub_pos.mpr hp).ne']

theorem finiteCostTarget_eq_source (d : ℕ) (hd : 1 ≤ d)
    (a : UserTariff) (G : Schedule (d + 1)) (g lam p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) :
    finiteCostTarget d a G g (referenceBid d lam p) p =
      (lam * fTariff d a p + g * baseMarginalCost d G p) * successSlope d p := by
  have he : referenceBidCost d a lam =ᶠ[𝓝 p]
      (fun x => referenceBid d lam x * binomialPolynomial (d + 1) a.charge x) := by
    filter_upwards [Ioo_mem_nhds hp0 hp1] with x hx
    rw [referenceBidCost_eq_actual d a lam x hx.1.le hx.2,
      binomialPolynomial_eq_expect (d + 1) a.charge x hx.1.le hx.2.le]
    rfl
  have hder := (hasDerivAt_referenceBid_scale d hd lam p hp1).mul
    (hasDerivAt_binomialPolynomial (d + 1) a.charge p)
  have hcost := hder.congr_of_eventuallyEq he
  have hid := hcost.unique (hasDerivAt_referenceBidCost d hd a lam p hp1)
  have hS : successSlope d p ≠ 0 := by
    dsimp [successSlope]
    exact mul_ne_zero (by positivity) (pow_ne_zero _ (sub_pos.mpr hp1).ne')
  have hbase : baseMarginalCost d G p * successSlope d p =
      binomialPolynomialDerivative (d + 1) G.charge p := by
    exact div_mul_cancel₀ _ hS
  unfold finiteCostTarget
  change bidCoordinateScale d (referenceBid d lam p) p *
      binomialPolynomial (d + 1) a.charge p + referenceBid d lam p *
      binomialPolynomialDerivative (d + 1) a.charge p +
      g * binomialPolynomialDerivative (d + 1) G.charge p = _
  have hid' : bidCoordinateScale d (referenceBid d lam p) p *
      binomialPolynomial (d + 1) a.charge p + referenceBid d lam p *
      binomialPolynomialDerivative (d + 1) a.charge p =
      lam * fTariff d a p * successSlope d p := by
    simpa only [successSlope] using hid
  rw [hid']
  rw [← hbase]
  ring

theorem source_residual_of_finite_derivatives (d : ℕ) (hd : 1 ≤ d)
    (a : UserTariff) (G : Schedule (d + 1))
    {g lam p b v A' C' eA eC : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hb : b = referenceBid d lam p) (hFOC : v * A' = C')
    (hA : |bidCoordinateScale d b p * A' - successSlope d p| ≤ eA)
    (hC : |bidCoordinateScale d b p * C' - finiteCostTarget d a G g b p| ≤ eC) :
    |v - (lam * fTariff d a p + g * baseMarginalCost d G p)| * successSlope d p ≤
      |v| * eA + eC := by
  have ht := finiteCostTarget_eq_source d hd a G g lam p hp0 hp1
  rw [hb, ht] at hC
  have hs : 0 ≤ successSlope d p := by
    dsimp [successSlope]
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (sub_pos.mpr hp1).le _)
  let D := bidCoordinateScale d b p
  let S := successSlope d p
  let V := lam * fTariff d a p + g * baseMarginalCost d G p
  have hid : (v - V) * S = v * (S - D * A') + (D * C' - V * S) := by
    rw [← hFOC]
    ring
  have hca : |D * C' - V * S| ≤ eC := by simpa [D, S, V, hb] using hC
  have haa : |S - D * A'| ≤ eA := by simpa [D, S, abs_sub_comm] using hA
  calc
    _ = |(v - V) * S| := by rw [abs_mul, abs_of_nonneg hs]
    _ = |v * (S - D * A') + (D * C' - V * S)| := congrArg abs hid
    _ ≤ |v * (S - D * A')| + |D * C' - V * S| := abs_add_le _ _
    _ ≤ |v| * eA + eC := by
      rw [abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left haa (abs_nonneg v)) hca

theorem source_residual_uniform (d : ℕ) (hd : 1 ≤ d)
    (a : UserTariff) (G : Schedule (d + 1))
    {g lam p b v A' C' err V Smin : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hb : b = referenceBid d lam p)
    (hFOC : v * A' = C') (hV : |v| ≤ V) (hSmin : 0 < Smin)
    (hS : Smin ≤ successSlope d p) (herr : 0 ≤ err)
    (hA : |bidCoordinateScale d b p * A' - successSlope d p| ≤ err)
    (hC : |bidCoordinateScale d b p * C' - finiteCostTarget d a G g b p| ≤ err) :
    |v - (lam * fTariff d a p + g * baseMarginalCost d G p)| ≤ (V + 1) * err / Smin := by
  have h := source_residual_of_finite_derivatives d hd a G hp0 hp1 hb hFOC hA hC
  have h1 := mul_le_mul_of_nonneg_left hS (abs_nonneg
    (v - (lam * fTariff d a p + g * baseMarginalCost d G p)))
  have h2 := mul_le_mul_of_nonneg_right hV herr
  apply (le_div_iff₀ hSmin).mpr
  nlinarith

theorem bid_tendsto_of_reference (d : ℕ) (lam p b : ℕ → ℝ) (lamInf pInf : ℝ)
    (hpInf : pInf < 1) (hlam : Tendsto lam atTop (𝓝 lamInf))
    (hp : Tendsto p atTop (𝓝 pInf))
    (hformula : ∀ᶠ t in atTop, b t = referenceBid d (lam t) (p t)) :
    Tendsto b atTop (𝓝 (referenceBid d lamInf pInf)) := by
  have ht : Tendsto (fun t => referenceBid d (lam t) (p t)) atTop
      (𝓝 (referenceBid d lamInf pInf)) :=
    hlam.div ((tendsto_const_nhds.sub hp).pow d)
      (pow_ne_zero _ (sub_pos.mpr hpInf).ne')
  exact ht.congr' (hformula.mono fun _ h => h.symm)

theorem unique_once_source_bid (d : ℕ) (lam p v g : ℝ) (hp : p < 1)
    (heq : v = lam * fTariff d .unique p + g * baseMarginalCost d (Schedule.once (d + 1)) p) :
    referenceBid d lam p = v - g := by
  exact reference_unique_once_bid d hp heq

end FCAppendix.Exclusive.Narrow

namespace FCAppendix.Bayes
open MeasureTheory Set Game Exclusive Exclusive.Narrow

variable {m c d : ℕ} {Seed : Type*} [MeasurableSpace Seed]

structure FiniteBroadcastDerivativeCorrection (Γ : FiniteGame m (d + 1) c Seed)
    (a : UserTariff) (i : Fin m) (lo hi l u K : ℝ)
    (A' C' : ℝ → ℝ)
    (P share : ℝ → UserProfile m (d + 1) → ℝ) : Prop where
  coefficient_nonneg : 0 ≤ K
  success : ∀ b ∈ Ioo lo hi, ∀ p ∈ Icc l u,
    |bidCoordinateScale d b p * A' b - successSlope d p| ≤
      K * ((∫ z, |P b z - p| ∂userProfileLaw Γ) + ∫ z, share b z ∂userProfileLaw Γ)
  cost : ∀ b ∈ Ioo lo hi, ∀ p ∈ Icc l u,
    |bidCoordinateScale d b p * C' b - finiteCostTarget d a Γ.G Γ.g b p| ≤
      K * ((∫ z, |P b z - p| ∂userProfileLaw Γ) + ∫ z, share b z ∂userProfileLaw Γ)

end FCAppendix.Bayes
