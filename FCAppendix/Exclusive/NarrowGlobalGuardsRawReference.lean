import FCAppendix.Exclusive.NarrowGlobalGuardsTransport

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Global
open Set

lemma referenceRouteUtility_eq_raw_response (n k : ℕ) (hn : 1 ≤ n) (hk : 0 < k)
    (a : UserTariff) (lam v b p : ℝ) (hp1 : p < 1)
    (hprice : b*(1-p)^(n-1)=lam) :
    referenceRouteUtility n k a lam v (-(k:ℝ)*Real.log (1-p)) =
      v*PayOnce.success k p-b*binomialPolynomial k a.charge p := by
  let A : ℝ := -(k:ℝ)*Real.log (1-p)
  have hkR : (k:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hq : 0 < 1-p := sub_pos.mpr hp1
  have hdiv : A/(k:ℝ) = -Real.log (1-p) := by dsimp [A]; field_simp
  have he : 1-Real.exp (-(A/(k:ℝ)))=p := by
    rw [hdiv,neg_neg,Real.exp_log hq]
    ring
  have hb : lam*Real.exp ((n-1:ℕ)*(A/(k:ℝ)))=b := by
    rw [← referenceBid_exp (n-1) lam (A/(k:ℝ)),he]
    unfold referenceBid
    exact (div_eq_iff (pow_pos hq _).ne').mpr hprice.symm
  change referenceRouteUtility n k a lam v A = _
  unfold referenceRouteUtility bidCostAtSuccess
  have hnR : ((n-1:ℕ):ℝ)=(n:ℝ)-1 := by simpa only [Nat.cast_one] using (Nat.cast_sub hn : ((n-1:ℕ):ℝ)=(n:ℝ)-(1:ℕ))
  rw [← prescribed_success k hk A,he,← hnR,hb]

theorem pricedPayoff_lower_route_strict_global (d k : ℕ) (hd : 1 ≤ d)
    (hk : 0 < k) (hkn : k < d+1) (a : UserTariff) (ha : a.Allowed)
    (lam v p0 : ℝ) (hlam : 0 < lam) (hp0 : 0 < p0) (hp1 : p0 < 1)
    (hFOC : v=lam*fTariff d a p0) (b : ℝ) :
    pricedPayoff (d+1) k a b lam < referenceUtility d a lam v p0+(1-v)*
      PayOnce.success k (menuMarginal (d+1) b lam) := by
  let p := menuMarginal (d+1) b lam
  have hpr := menuMarginal_bounds (d+1) b lam hlam
  have hplt : p < 1 := demand_lt_one _ (hlam.trans_le (le_max_right _ _)) hlam
  have hpactive : p=activeDemand (d+1) b lam :=
    menuMarginal_eq_activeDemand _ (by omega) b lam hlam
  by_cases hz : p=0
  · have hpos := referenceUtility_pos d hd a ha lam v p0 hlam hp0 hp1 hFOC
    have hzcharge : a.charge 0=0 := by cases a <;> simp [UserTariff.charge,successIndicator]
    change PayOnce.success k p-b*binomialPolynomial k a.charge p <
      referenceUtility d a lam v p0+(1-v)*PayOnce.success k p
    simpa only [hz,PayOnce.success,sub_zero,one_pow,sub_self,mul_zero,
      binomialPolynomial_at_zero,hzcharge,zero_mul,add_zero] using hpos
  · have hpp : 0 < p := lt_of_le_of_ne hpr.1 (Ne.symm hz)
    have hb : 0 < b := by
      by_contra hn
      have hh : activeDemand (d+1) b lam=0 := by simp [activeDemand,hn]
      exact hz (hpactive.trans hh)
    have hbl : lam < b := (demand_pos_iff (d+1) (by omega) hb hlam.le).mp (by
      simpa only [p,hpactive,activeDemand,if_pos hb] using hpp)
    have hprice : b*(1-p)^((d+1)-1)=lam := by
      rw [hpactive,activeDemand,if_pos hb,demand_receipt (d+1) (by omega) hb hlam,
        min_eq_right hbl.le]
    have hA : 0 ≤ -(k:ℝ)*Real.log (1-p) := by
      have hl : Real.log (1-p) ≤ 0 := Real.log_nonpos (sub_nonneg.mpr hplt.le) (by linarith [hpr.1])
      have hh := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg k) hl
      nlinarith only [hh]
    have hr := referenceRouteUtility_strict_global d k hd hk hkn a ha lam v p0
      hlam hp0 hp1 hFOC (-(k:ℝ)*Real.log (1-p)) hA
    rw [referenceRouteUtility_eq_raw_response (d+1) k (by omega) hk a lam v b p hplt hprice] at hr
    dsimp [pricedPayoff]
    change PayOnce.success k p-b*binomialPolynomial k a.charge p < _
    linarith

def referenceRawGap (d k : ℕ) (a : UserTariff) (p0 b : ℝ) : ℝ :=
  referenceUtility d a (normalizedPrice d a p0) 1 p0-
    pricedPayoff (d+1) k a b (normalizedPrice d a p0)

lemma referenceRawGap_pos (d k : ℕ) (hd : 1 ≤ d) (hk : 0 < k) (hkn : k < d+1)
    (a : UserTariff) (ha : a.Allowed) (p0 b : ℝ) (hp0 : 0 < p0) (hp1 : p0 < 1) :
    0 < referenceRawGap d k a p0 b := by
  have hf := (fTariff_pos_and_derivative_pos d hd a ha hp0.le hp1).1
  have hlam : 0 < normalizedPrice d a p0 := one_div_pos.mpr hf
  have hFOC : 1=normalizedPrice d a p0*fTariff d a p0 := (one_div_mul_cancel hf.ne').symm
  have hh := pricedPayoff_lower_route_strict_global d k hd hk hkn a ha
    _ 1 p0 hlam hp0 hp1 hFOC b
  simp only [sub_self,zero_mul,add_zero] at hh
  exact sub_pos.mpr hh

lemma continuousOn_normalizedPrice_affine (d : ℕ) (hd : 1 ≤ d)
    (p0 : ℝ) (hp0 : 0 ≤ p0) (hp1 : p0 < 1) :
    ContinuousOn (fun eta : ℝ => normalizedPrice d (.affine eta) p0) (Icc 0 1) := by
  unfold normalizedPrice fTariff
  apply continuousOn_const.div
  · fun_prop
  · intro eta heta
    exact (fTariff_pos_and_derivative_pos d hd (.affine eta) heta hp0 hp1).1.ne'

lemma continuousOn_referenceRawGap_affine (d k : ℕ) (hd : 1 ≤ d)
    (p0 : ℝ) (hp0 : 0 ≤ p0) (hp1 : p0 < 1) :
    ContinuousOn (fun x : ℝ×ℝ => referenceRawGap d k (.affine x.1) p0 x.2)
      (Icc (0:ℝ) 1 ×ˢ univ) := by
  let P : ℝ → ℝ := fun eta => normalizedPrice d (.affine eta) p0
  have hP : ContinuousOn P (Icc 0 1) := continuousOn_normalizedPrice_affine d hd p0 hp0 hp1
  have hPpos : ∀ eta ∈ Icc (0:ℝ) 1, 0 < P eta := fun eta heta =>
    one_div_pos.mpr (fTariff_pos_and_derivative_pos d hd (.affine eta) heta hp0 hp1).1
  have hPc : ContinuousOn (fun x : ℝ×ℝ => P x.1) (Icc (0:ℝ) 1 ×ˢ univ) :=
    hP.comp continuous_fst.continuousOn (fun _ hx => hx.1)
  have hPair : ContinuousOn (fun x : ℝ×ℝ => (x.2,P x.1)) (Icc (0:ℝ) 1 ×ˢ univ) :=
    continuous_snd.continuousOn.prodMk hPc
  have h0 := (continuousOn_pricedPayoff (d+1) k (by omega) (.affine 0)).comp hPair
    (fun x hx => hPpos x.1 hx.1)
  have h1 := (continuousOn_pricedPayoff (d+1) k (by omega) (.affine 1)).comp hPair
    (fun x hx => hPpos x.1 hx.1)
  have hpay : ContinuousOn (fun x : ℝ×ℝ => pricedPayoff (d+1) k (.affine x.1) x.2 (P x.1))
      (Icc (0:ℝ) 1 ×ˢ univ) := by
    apply ContinuousOn.congr (((continuousOn_const.sub continuous_fst.continuousOn).mul h0).add
      (continuous_fst.continuousOn.mul h1))
    intro x hx
    exact pricedPayoff_affine (d+1) k x.1 x.2 (P x.1) (hPpos x.1 hx.1)
  have hopt : ContinuousOn
      (fun x : ℝ×ℝ => referenceUtility d (.affine x.1) (P x.1) 1 p0)
      (Icc (0:ℝ) 1 ×ˢ univ) := by
    have hBid := hPc.div_const ((1-p0)^d)
    have hcost0 : ContinuousOn (fun x : ℝ×ℝ =>
        (1-x.1)*(P x.1/(1-p0)^d*PayOnce.success (d+1) p0))
        (Icc (0:ℝ) 1 ×ˢ univ) :=
      (continuousOn_const.sub continuous_fst.continuousOn).mul (hBid.mul continuousOn_const)
    have hcost1 : ContinuousOn (fun x : ℝ×ℝ =>
        x.1*(P x.1/(1-p0)^d*((d+1:ℕ)*p0)))
        (Icc (0:ℝ) 1 ×ˢ univ) :=
      continuous_fst.continuousOn.mul (hBid.mul continuousOn_const)
    exact continuousOn_const.sub (hcost0.add hcost1)
  exact hopt.sub hpay

lemma continuous_pricedPayoff_fixedPrice (n k : ℕ) (hn : 2 ≤ n)
    (a : UserTariff) (lam : ℝ) (hlam : 0 < lam) :
    Continuous (fun b : ℝ => pricedPayoff n k a b lam) := by
  rw [← continuousOn_univ]
  exact (continuousOn_pricedPayoff n k hn a).comp'
    (f := fun b : ℝ => (b,lam))
    (s := (univ : Set ℝ)) (t := {x : ℝ×ℝ | 0 < x.2})
    (continuous_id.prodMk continuous_const).continuousOn (fun _ _ => hlam)

theorem referenceRawGap_uniform_compact (d k : ℕ) (hd : 1 ≤ d)
    (hk : 0 < k) (hkn : k < d+1) (p0 B : ℝ)
    (hp0 : 0 < p0) (hp1 : p0 < 1) (hB : 0 ≤ B) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ a : UserTariff, a.Allowed → ∀ b ∈ Icc (0:ℝ) B,
      gap ≤ referenceRawGap d k a p0 b := by
  let K : Set (ℝ×ℝ) := Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) B
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKn : K.Nonempty := ⟨(0,0),⟨⟨le_refl _,zero_le_one⟩,⟨le_refl _,hB⟩⟩⟩
  have hcont := (continuousOn_referenceRawGap_affine d k hd p0 hp0.le hp1).mono
    (show K ⊆ Icc (0:ℝ) 1 ×ˢ univ from fun _ hx => ⟨hx.1,mem_univ _⟩)
  obtain ⟨x,hx,hmin⟩ := hK.exists_isMinOn hKn hcont
  have hga : 0 < referenceRawGap d k (.affine x.1) p0 x.2 :=
    referenceRawGap_pos d k hd hk hkn (.affine x.1) hx.1 p0 x.2 hp0 hp1
  have hprice : 0 < normalizedPrice d .unique p0 := one_div_pos.mpr
    (fTariff_pos_and_derivative_pos d hd .unique trivial hp0.le hp1).1
  have hpay := (continuous_pricedPayoff_fixedPrice (d+1) k (by omega) .unique
    (normalizedPrice d .unique p0) hprice).continuousOn (s := Icc (0:ℝ) B)
  have hcontu : ContinuousOn (referenceRawGap d k .unique p0) (Icc (0:ℝ) B) := by
    change ContinuousOn (fun b => referenceUtility d .unique (normalizedPrice d .unique p0) 1 p0-
      pricedPayoff (d+1) k .unique b (normalizedPrice d .unique p0)) (Icc (0:ℝ) B)
    exact continuousOn_const.sub hpay
  obtain ⟨bu,hbu,hminu⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) B)).exists_isMinOn
    (show (Icc (0:ℝ) B).Nonempty from ⟨0,le_refl _,hB⟩) hcontu
  have hgu : 0 < referenceRawGap d k .unique p0 bu :=
    referenceRawGap_pos d k hd hk hkn .unique trivial p0 bu hp0 hp1
  refine ⟨min (referenceRawGap d k .unique p0 bu)
    (referenceRawGap d k (.affine x.1) p0 x.2),lt_min hgu hga,?_⟩
  intro a ha b hb
  cases a with
  | unique => exact (min_le_left _ _).trans (hminu hb)
  | affine eta => exact (min_le_right _ _).trans (hmin (show (eta,b) ∈ K from ⟨ha,hb⟩))

end FCAppendix.Exclusive.Narrow.Global
