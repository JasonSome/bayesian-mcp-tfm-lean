import FCAppendix.Affine.Tail04.TypicalGuardStatistics

noncomputable section
namespace FCAppendix.Affine.Tail04.TypicalGuardEndpoints
open MeasureTheory Set Classical
open EqualPrivateSignal NativeTypicalCount
open scoped BigOperators

def lambda (c ell M : ℕ) (ξ W kept : ℝ) : ℝ :=
  ((M:ℝ)-ξ*((c:ℝ)-(ell:ℝ)-kept))/W

def lowerPrivateCount (H : ℕ) (reg : Bool) : ℕ := if reg then 0 else H

lemma kept_count_bounds (H : ℕ) (reg : Bool) (z : Marks H) :
    lowerPrivateCount H reg≤(if reg then upperCount z else H) ∧
      (if reg then upperCount z else H)≤ H := by
  cases reg
  · simp [lowerPrivateCount]
  · simp only [lowerPrivateCount,ite_true]
    have hh : upperCount z ≤ H := by
      simpa only [upperCount,Fintype.card_fin] using
        (Finset.card_le_univ (Finset.univ.filter (fun j : Fin H => z j=true)))
    exact ⟨Nat.zero_le _,hh⟩

lemma multiplier_eq_lambda (H c ell M : ℕ) (ξ : ℝ) (reg : Bool) (W : ℝ)
    (hcap : ell+H≤ c) (z : Marks H) :
    TypicalGuardStatistics.multiplier H c ell M ξ reg W z =
      lambda c ell M ξ W (((if reg then upperCount z else H):ℕ):ℝ) := by
  have hle : ell+(if reg then upperCount z else H)≤ c := by
    have hh := (kept_count_bounds H reg z).2
    omega
  unfold TypicalGuardStatistics.multiplier lambda
  rw [Nat.cast_sub hle,Nat.cast_add]
  congr 2
  ring

lemma lambda_mono (c ell M : ℕ) {ξ W k l : ℝ}
    (hξ : 0≤ ξ) (hW : 0< W) (hkl : k≤ l) :
    lambda c ell M ξ W k≤ lambda c ell M ξ W l := by
  apply div_le_div_of_nonneg_right _ hW.le
  have hh := mul_le_mul_of_nonneg_left hkl hξ
  nlinarith

lemma multiplier_endpoint_bounds (H c ell M : ℕ) {ξ W : ℝ} (reg : Bool)
    (hξ : 0≤ ξ) (hW : 0< W) (hcap : ell+H≤ c) (z : Marks H) :
    lambda c ell M ξ W (lowerPrivateCount H reg)≤
      TypicalGuardStatistics.multiplier H c ell M ξ reg W z ∧
    TypicalGuardStatistics.multiplier H c ell M ξ reg W z≤ lambda c ell M ξ W H := by
  rw [multiplier_eq_lambda H c ell M ξ reg W hcap z]
  have hk := kept_count_bounds H reg z
  exact ⟨lambda_mono c ell M hξ hW (by exact_mod_cast hk.1),
    lambda_mono c ell M hξ hW (by exact_mod_cast hk.2)⟩

theorem realizationMargin_ge (H c ell M : ℕ) {ξ W B γ : ℝ} (reg : Bool)
    (hξ : 0≤ ξ) (hW : 0< W) (hcap : ell+H≤ c) (hγ1 : γ≤1)
    (hlo : (1-ξ)*B+γ≤ lambda c ell M ξ W (lowerPrivateCount H reg))
    (hhi : lambda c ell M ξ W H+γ≤1) :
    γ≤ TypicalGuardStatistics.realizationMargin H c ell M ξ B reg W := by
  apply TypicalGuard.le_finiteMinimum _ γ hγ1
  intro z
  obtain ⟨hl,hu⟩ := multiplier_endpoint_bounds H c ell M reg hξ hW hcap z
  apply le_min <;> linarith

theorem meanMultiplier_eq_lambda (H c ell M : ℕ) (ξ : ℝ) (reg : Bool)
    (ν : FiniteLaw (Marks H)) (W : ℝ) (hcap : ell+H≤ c) :
    TypicalGuardStatistics.meanMultiplier H c ell M ξ reg ν W =
      lambda c ell M ξ W (privateMean H reg ν) := by
  change ν.expect (fun z => TypicalGuardStatistics.multiplier H c ell M ξ reg W z) = _
  simp_rw [multiplier_eq_lambda H c ell M ξ reg W hcap]
  unfold lambda privateMean
  simp only [div_eq_mul_inv,FiniteLaw.expect_mul_const,FiniteLaw.expect_sub,
    FiniteLaw.expect_const,FiniteLaw.expect_const_mul]

theorem meanMultiplier_congr_privateMean (H c ell M : ℕ) (ξ : ℝ) (reg : Bool)
    (ν ν' : FiniteLaw (Marks H)) (W : ℝ) (hcap : ell+H≤ c)
    (hmean : privateMean H reg ν=privateMean H reg ν') :
    TypicalGuardStatistics.meanMultiplier H c ell M ξ reg ν W=
      TypicalGuardStatistics.meanMultiplier H c ell M ξ reg ν' W := by
  rw [meanMultiplier_eq_lambda H c ell M ξ reg ν W hcap,
    meanMultiplier_eq_lambda H c ell M ξ reg ν' W hcap,hmean]

theorem margin_ge (H0 H1 c ell0 ell1 M : ℕ) {ξ W B R Rp γ : ℝ} (reg : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hξ : 0≤ ξ) (hW : 0< W) (hcap0 : ell0+H0≤ c) (hcap1 : ell1+H1≤ c) (hγ1 : γ≤1)
    (hlo0 : (1-ξ)*B+γ≤ lambda c ell0 M ξ W (lowerPrivateCount H0 reg))
    (hhi0 : lambda c ell0 M ξ W H0+γ≤1)
    (hlo1 : (1-ξ)*B+γ≤ lambda c ell1 M ξ W (lowerPrivateCount H1 reg))
    (hhi1 : lambda c ell1 M ξ W H1+γ≤1)
    (hp : if reg then
      Rp+γ≤ lambda c ell0 M ξ W (privateMean H0 reg ν0) ∧
        Rp+γ≤ lambda c ell1 M ξ W (privateMean H1 reg ν1)
      else lambda c ell0 M ξ W (privateMean H0 reg ν0)+γ≤ R ∧
        lambda c ell1 M ξ W (privateMean H1 reg ν1)+γ≤ R) :
    γ≤ TypicalGuardStatistics.margin H0 H1 c ell0 ell1 M ξ B R Rp reg ν0 ν1 W := by
  refine le_min (le_min (realizationMargin_ge H0 c ell0 M reg hξ hW hcap0 hγ1 hlo0 hhi0)
    (realizationMargin_ge H1 c ell1 M reg hξ hW hcap1 hγ1 hlo1 hhi1)) ?_
  unfold TypicalGuardStatistics.partialMargin
  rw [meanMultiplier_eq_lambda H0 c ell0 M ξ reg ν0 W hcap0,
    meanMultiplier_eq_lambda H1 c ell1 M ξ reg ν1 W hcap1]
  cases reg <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hp ⊢ <;>
    exact le_min (by linarith [hp.1]) (by linarith [hp.2])

theorem scalar_weight_eq_one (H0 H1 c ell0 ell1 M : ℕ) {ξ W B R Rp γ width : ℝ}
    (reg : Bool) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hξ : 0≤ ξ) (hW : 0< W) (hcap0 : ell0+H0≤ c) (hcap1 : ell1+H1≤ c) (hM : 0< M)
    (hw : 0< width) (hwγ : width≤ γ) (hγ1 : γ≤1)
    (hlo0 : (1-ξ)*B+γ≤ lambda c ell0 M ξ W (lowerPrivateCount H0 reg))
    (hhi0 : lambda c ell0 M ξ W H0+γ≤1)
    (hlo1 : (1-ξ)*B+γ≤ lambda c ell1 M ξ W (lowerPrivateCount H1 reg))
    (hhi1 : lambda c ell1 M ξ W H1+γ≤1)
    (hp : if reg then
      Rp+γ≤ lambda c ell0 M ξ W (privateMean H0 reg ν0) ∧
        Rp+γ≤ lambda c ell1 M ξ W (privateMean H1 reg ν1)
      else lambda c ell0 M ξ W (privateMean H0 reg ν0)+γ≤ R ∧
        lambda c ell1 M ξ W (privateMean H1 reg ν1)+γ≤ R) :
    TypicalGuardStatistics.weight H0 H1 c ell0 ell1 M ξ B R Rp width reg ν0 ν1 W=1 := by
  have hm := margin_ge H0 H1 c ell0 ell1 M reg ν0 ν1 hξ hW hcap0 hcap1 hγ1
    hlo0 hhi0 hlo1 hhi1 hp
  have hratio : 1≤ TypicalGuardStatistics.margin H0 H1 c ell0 ell1 M ξ B R Rp reg ν0 ν1 W/width :=
    (le_div_iff₀ hw).mpr (by simpa using hwγ.trans hm)
  have hs : TypicalGuardStatistics.Structural H0 H1 c ell0 ell1 M := ⟨hcap0,hcap1,hM⟩
  simp only [TypicalGuardStatistics.weight,if_pos hs,probabilityClip]
  exact min_eq_left (hratio.trans (le_max_right _ _))

theorem actual_weight_eq_one (N H0 H1 c : ℕ) {ξ W B R Rp γ width : ℝ}
    (reg : Bool) (I O0 O1 : Finset (Fin N)) (b : Fin N → ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hO : Disjoint O0 O1) (hI : Disjoint I (O0∪O1)) (hcover : I∪(O0∪O1)=Finset.univ)
    (hWeq : W=mixedReciprocalSum I b)
    (hξ : 0≤ ξ) (hW : 0< W) (hcap0 : O0.card+H0≤ c) (hcap1 : O1.card+H1≤ c)
    (hM : I.Nonempty) (hw : 0< width) (hwγ : width≤ γ) (hγ1 : γ≤1)
    (hlo0 : (1-ξ)*B+γ≤ lambda c O0.card I.card ξ W (lowerPrivateCount H0 reg))
    (hhi0 : lambda c O0.card I.card ξ W H0+γ≤1)
    (hlo1 : (1-ξ)*B+γ≤ lambda c O1.card I.card ξ W (lowerPrivateCount H1 reg))
    (hhi1 : lambda c O1.card I.card ξ W H1+γ≤1)
    (hp : if reg then
      Rp+γ≤ lambda c O0.card I.card ξ W (privateMean H0 reg ν0) ∧
        Rp+γ≤ lambda c O1.card I.card ξ W (privateMean H1 reg ν1)
      else lambda c O0.card I.card ξ W (privateMean H0 reg ν0)+γ≤ R ∧
        lambda c O1.card I.card ξ W (privateMean H1 reg ν1)+γ≤ R) :
    TypicalGuard.weight N H0 H1 c ξ B R Rp width reg I O0 O1 b ν0 ν1=1 := by
  rw [TypicalGuardStatistics.actual_weight N H0 H1 c ξ B R Rp width reg I O0 O1 b ν0 ν1
    hO hI hcover,← hWeq]
  exact scalar_weight_eq_one H0 H1 c O0.card O1.card I.card reg ν0 ν1 hξ hW hcap0 hcap1
    (Finset.card_pos.mpr hM) hw hwγ hγ1 hlo0 hhi0 hlo1 hhi1 hp

theorem scalar_weight_congr_privateMeans (H0 H1 c ell0 ell1 M : ℕ)
    (ξ B R Rp width W : ℝ) (reg : Bool)
    (ν0 ν0' : FiniteLaw (Marks H0)) (ν1 ν1' : FiniteLaw (Marks H1))
    (h0 : privateMean H0 reg ν0=privateMean H0 reg ν0')
    (h1 : privateMean H1 reg ν1=privateMean H1 reg ν1') :
    TypicalGuardStatistics.weight H0 H1 c ell0 ell1 M ξ B R Rp width reg ν0 ν1 W=
      TypicalGuardStatistics.weight H0 H1 c ell0 ell1 M ξ B R Rp width reg ν0' ν1' W := by
  by_cases hs : TypicalGuardStatistics.Structural H0 H1 c ell0 ell1 M
  · have hmean0 := meanMultiplier_congr_privateMean H0 c ell0 M ξ reg ν0 ν0' W hs.1 h0
    have hmean1 := meanMultiplier_congr_privateMean H1 c ell1 M ξ reg ν1 ν1' W hs.2.1 h1
    simp only [TypicalGuardStatistics.weight,if_pos hs,TypicalGuardStatistics.margin,
      TypicalGuardStatistics.partialMargin,hmean0,hmean1]
  · simp only [TypicalGuardStatistics.weight,if_neg hs]

end FCAppendix.Affine.Tail04.TypicalGuardEndpoints
