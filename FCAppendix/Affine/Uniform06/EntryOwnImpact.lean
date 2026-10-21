import FCAppendix.Affine.ClippedResidualContinuity

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryOwnImpact
open Set Filter Topology
open FCAppendix.Affine.ClippedResidual
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma exposure_antitone_price {ξ z₁ z₂ b : ℝ} (hξ : 0 < ξ)
    (hz₁ : 0 < z₁) (hz : z₁ ≤ z₂) : exposure ξ z₂ b ≤ exposure ξ z₁ b := by
  by_cases hb₂ : b ≤ z₂
  · rw [exposure_zero hb₂]
    exact exposure_nonneg hξ hz₁
  · have hb₂' : z₂ < b := lt_of_not_ge hb₂
    have hb₁ : z₁ < b := hz.trans_lt hb₂'
    have hb : 0 < b := hz₁.trans hb₁
    have hden : 0 < ξ*b := mul_pos hξ hb
    simp only [exposure, max_eq_left hb₂'.le, max_eq_left hb₁.le,
      max_eq_right (sub_nonneg.mpr hb₂'.le), max_eq_right (sub_nonneg.mpr hb₁.le)]
    exact min_le_min le_rfl (div_le_div_of_nonneg_right (by linarith) hden.le)

lemma remainingDemand_antitone_price (ξ : ℝ) (B : ι → ℝ) (E : Finset ι)
    {z₁ z₂ : ℝ} (hξ : 0 < ξ) (hz₁ : 0 < z₁) (hz : z₁ ≤ z₂) :
    remainingDemand ξ B E z₂ ≤ remainingDemand ξ B E z₁ := by
  unfold remainingDemand
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ E
  · simp [hi]
  · simpa only [hi,if_false] using exposure_antitone_price hξ hz₁ hz (b := B i)

def IsLargestPositiveRoot (ξ : ℝ) (B : ι → ℝ) (E : Finset ι) (d L : ℝ) : Prop :=
  0 < L ∧ remainingDemand ξ B E L = d ∧
    ∀ z, 0 < z → remainingDemand ξ B E z = d → z ≤ L

theorem exists_largest_positive_root {ξ U lo hi d slack : ℝ}
    (B : ι → ℝ) (E : Finset ι)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hU : 0 < U)
    (hlo : 0 < lo) (hlh : lo < hi) (hguard : (1-ξ)*U ≤ lo)
    (hBU : ∀ i, B i ≤ U) (hd : 0 < d) (heps : 0 < slack)
    (hlow : d+(E.card : ℝ)+slack < ∑ i, exposure ξ lo (B i))
    (hhigh : (∑ i, exposure ξ hi (B i)) < d-slack) :
    ∃ L ∈ Ioo lo hi, IsLargestPositiveRoot ξ B E d L := by
  obtain ⟨L,hL,hunique⟩ := exists_unique_balanced_root B E hξ hξ1 hU
    hlo hlh hguard hBU hd heps hlow hhigh
  have hDl : d < remainingDemand ξ B E lo := by
    have hr := (removal_changes_demand_by_at_most_card ξ lo B hξ hlo E).1
    linarith
  have hDh : remainingDemand ξ B E hi < d := by
    have hr := (removal_changes_demand_by_at_most_card ξ hi B hξ (hlo.trans hlh) E).2
    linarith
  have hLlo : lo < L := by
    apply lt_of_le_of_ne hL.1.1
    intro he
    rw [he] at hDl
    linarith [hL.2]
  have hLhi : L < hi := by
    apply lt_of_le_of_ne hL.1.2
    intro he
    rw [← he] at hDh
    linarith [hL.2]
  refine ⟨L,⟨hLlo,hLhi⟩,hlo.trans hLlo,hL.2,?_⟩
  intro z hz hroot
  by_contra hnot
  have hLz : L < z := lt_of_not_ge hnot
  by_cases hzh : z ≤ hi
  · have he := hunique z ⟨⟨hL.1.1.trans hLz.le,hzh⟩,hroot⟩
    linarith
  · have hhz : hi ≤ z := (lt_of_not_ge hzh).le
    have hm := remainingDemand_antitone_price ξ B E hξ (hlo.trans hlh) hhz
    rw [hroot] at hm
    linarith

def leftSecant (ξ : ℝ) (B : ι → ℝ) (E : Finset ι) (L Λ : ℝ) : ℝ :=
  if L < Λ then ξ * (remainingDemand ξ B E L-remainingDemand ξ B E Λ)/(Λ-L) else 0

def rightSecant (ξ : ℝ) (B : ι → ℝ) (E : Finset ι) (Λ b : ℝ) : ℝ :=
  if Λ < b then ξ * (remainingDemand ξ B E Λ-remainingDemand ξ B E b)/(b-Λ) else 0

lemma leftSecant_identity (ξ : ℝ) (B : ι → ℝ) (E : Finset ι)
    {L Λ : ℝ} (hLΛ : L < Λ) :
    (Λ-L)*leftSecant ξ B E L Λ =
      ξ*(remainingDemand ξ B E L-remainingDemand ξ B E Λ) := by
  simp only [leftSecant,if_pos hLΛ]
  field_simp [(sub_pos.mpr hLΛ).ne']

lemma rightSecant_identity (ξ : ℝ) (B : ι → ℝ) (E : Finset ι)
    {Λ b : ℝ} (hΛb : Λ < b) :
    (b-Λ)*rightSecant ξ B E Λ b =
      ξ*(remainingDemand ξ B E Λ-remainingDemand ξ B E b) := by
  simp only [rightSecant,if_pos hΛb]
  field_simp [(sub_pos.mpr hΛb).ne']

lemma leftSecant_nonneg {ξ L Λ : ℝ} (B : ι → ℝ) (E : Finset ι)
    (hξ : 0 < ξ) (hL : 0 < L) : 0 ≤ leftSecant ξ B E L Λ := by
  by_cases h : L < Λ
  · rw [leftSecant,if_pos h]
    exact div_nonneg (mul_nonneg hξ.le (sub_nonneg.mpr
      (remainingDemand_antitone_price ξ B E hξ hL h.le))) (sub_nonneg.mpr h.le)
  · simp [leftSecant,h]

lemma rightSecant_nonneg {ξ Λ b : ℝ} (B : ι → ℝ) (E : Finset ι)
    (hξ : 0 < ξ) (hΛ : 0 < Λ) : 0 ≤ rightSecant ξ B E Λ b := by
  by_cases h : Λ < b
  · rw [rightSecant,if_pos h]
    exact div_nonneg (mul_nonneg hξ.le (sub_nonneg.mpr
      (remainingDemand_antitone_price ξ B E hξ hΛ h.le))) (sub_nonneg.mpr h.le)
  · simp [rightSecant,h]

theorem focal_left_secant {ξ b L Λ p d : ℝ} (B : ι → ℝ) (E : Finset ι)
    (hξ : 0 < ξ) (hb : 0 < b) (hL : 0 < L) (hLΛ : L < Λ)
    (hroot : remainingDemand ξ B E L = d)
    (hfocal : remainingDemand ξ B E Λ+p=d)
    (hprice : Λ=b*(1-ξ*p)) :
    p=(b-L)*leftSecant ξ B E L Λ /
      (ξ*(1+b*leftSecant ξ B E L Λ)) := by
  let k := leftSecant ξ B E L Λ
  have hk : 0 ≤ k := leftSecant_nonneg B E hξ hL
  have hden : 0 < ξ*(1+b*k) := by positivity
  have hsec : (Λ-L)*k=ξ*p := by
    rw [leftSecant_identity ξ B E hLΛ,hroot]
    nlinarith [hfocal]
  apply (eq_div_iff hden.ne').2
  rw [hprice] at hsec
  nlinarith [hsec]

theorem focal_left_reciprocal {ξ b L Λ p d : ℝ} (B : ι → ℝ) (E : Finset ι)
    (hξ : 0 < ξ) (hb : 0 < b) (hL : 0 < L) (hLΛ : L < Λ)
    (hk : 0 < leftSecant ξ B E L Λ)
    (hroot : remainingDemand ξ B E L = d)
    (hfocal : remainingDemand ξ B E Λ+p=d)
    (hprice : Λ=b*(1-ξ*p)) :
    p=(b-L)/(ξ*(b+1/leftSecant ξ B E L Λ)) := by
  rw [focal_left_secant B E hξ hb hL hLΛ hroot hfocal hprice]
  field_simp [hξ.ne',hk.ne']
  ring

theorem focal_right_deficit {ξ b Λ p d : ℝ} (B : ι → ℝ) (E : Finset ι)
    (hξ : 0 < ξ) (hb : 0 < b) (hΛ : 0 < Λ) (hp : 0 < p)
    (hfocal : remainingDemand ξ B E Λ+p=d)
    (hprice : Λ=b*(1-ξ*p)) :
    p=(d-remainingDemand ξ B E b)/(1+b*rightSecant ξ B E Λ b) := by
  have hΛb : Λ < b := by
    have ht := mul_pos hb (mul_pos hξ hp)
    nlinarith [hprice]
  have hsec := rightSecant_identity ξ B E hΛb
  have hk := rightSecant_nonneg (b := b) B E hξ hΛ
  have hden : 0 < 1+b*rightSecant ξ B E Λ b := by positivity
  apply (eq_div_iff hden.ne').2
  have hbl : b-Λ = b*ξ*p := by nlinarith [hprice]
  rw [hbl] at hsec
  have hz : ξ*(p*(1+b*rightSecant ξ B E Λ b)-(d-remainingDemand ξ B E b))=0 := by
    nlinarith [hsec, congrArg (fun x => ξ*x) hfocal]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hξ.ne')

theorem ownImpact_relative_error {b b0 k k0 ξ a : ℝ}
    (hb0 : 0 < b0) (hb : b0 ≤ b) (hk0 : 0 < k0) (hk : k0 ≤ k)
    (hξ : 0 < ξ) (ha : 0 ≤ a) :
    0 ≤ a/(ξ*b) - a*k/(ξ*(1+b*k)) ∧
    a/(ξ*b) - a*k/(ξ*(1+b*k)) ≤ (a/(ξ*b))/(1+b0*k0) := by
  have hb' : 0 < b := hb0.trans_le hb
  have hk' : 0 < k := hk0.trans_le hk
  have hD : 0 < 1+b*k := by positivity
  have hD0 : 0 < 1+b0*k0 := by positivity
  have he : a/(ξ*b) - a*k/(ξ*(1+b*k)) = (a/(ξ*b))/(1+b*k) := by
    field_simp [hξ.ne',hb'.ne',hD.ne']
    ring
  rw [he]
  refine ⟨by positivity,?_⟩
  apply div_le_div_of_nonneg_left (by positivity) hD0
  have hm := mul_le_mul hb hk hk0.le hb'.le
  linarith

def faceMarginal (ξ d nActive K b : ℝ) : ℝ :=
  (ξ*d-nActive+b*K)/(ξ*(1+b*K))

theorem faceMarginal_eq_of_equations {ξ d nActive K b p Λ : ℝ}
    (hξ : 0 < ξ) (hb : 0 < b) (hK : 0 ≤ K)
    (hroot : (nActive-Λ*K)/ξ+p=d)
    (hprice : Λ=b*(1-ξ*p)) : p=faceMarginal ξ d nActive K b := by
  have hden : 0 < ξ*(1+b*K) := by positivity
  have hr : nActive-Λ*K+ξ*p=ξ*d := by
    have hm := (div_eq_iff hξ.ne').mp (show (nActive-Λ*K)/ξ=d-p by linarith)
    nlinarith [hm]
  unfold faceMarginal
  apply (eq_div_iff hden.ne').2
  rw [hprice] at hr
  nlinarith [hr]

theorem hasDerivAt_faceMarginal {ξ d nActive K b : ℝ}
    (hξ : 0 < ξ) (hb : 0 < b) (hK : 0 ≤ K) :
    HasDerivAt (faceMarginal ξ d nActive K)
      ((1-ξ*faceMarginal ξ d nActive K b)*K/(ξ*(1+b*K))) b := by
  have hden : ξ*(1+b*K) ≠ 0 := by positivity
  have hn : HasDerivAt (fun x : ℝ => ξ*d-nActive+x*K) K b := by
    convert! (hasDerivAt_const b (ξ*d-nActive)).add ((hasDerivAt_id b).mul_const K) using 1; ring
  have hd : HasDerivAt (fun x : ℝ => ξ*(1+x*K)) (ξ*K) b := by
    convert! ((hasDerivAt_const b 1).add ((hasDerivAt_id b).mul_const K)).const_mul ξ using 1; ring
  have hh := hn.div hd hden
  convert! hh using 1
  unfold faceMarginal
  field_simp [hξ.ne',hden]

end FCAppendix.Affine.Uniform06.EntryOwnImpact
