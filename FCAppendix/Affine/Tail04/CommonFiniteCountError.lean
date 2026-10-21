import FCAppendix.Affine.Tail04.CommonFlagCompression
import FCAppendix.Affine.Tail04.AllCountActiveFiniteGain

noncomputable section
namespace FCAppendix.Affine.Tail04.CommonFiniteCountError
open MeasureTheory ProbabilityTheory Set Classical
open MenuError CommonFlagCompression OriginalFlagCompression NativeTypicalCount
open EqualPrivateSignal SourceMenuPopulation
open scoped BigOperators

def coefficient (ξ b W δ : ℝ) : ℝ := 12/(ξ*b*W)+4/W+2/δ

lemma coefficient_nonnegative {ξ b W δ : ℝ} (hξ : 0< ξ) (hb : 1≤ b)
    (hW : 0< W) (hδ : 0< δ) : 0≤ coefficient ξ b W δ := by
  unfold coefficient
  positivity

lemma guard_numerator_bound {ξ share ρ B R Rp γ δ abar mbar hbar wbar : ℝ} {reg : Bool}
    (G : GuardInterior ξ share ρ B R Rp γ δ abar mbar hbar wbar reg)
    (hξ : ξ∈Icc (0:ℝ) 1) (hhbar : 0≤ hbar) (hB : 0≤ B) (hγ : 0≤ γ) :
    0< wbar ∧ |populationNumerator ξ ρ abar mbar hbar share|≤ wbar := by
  obtain ⟨hw,hlo,hhi⟩ := G.mean_margins hξ.1 hhbar
  have hn0 : 0≤ populationNumerator ξ ρ abar mbar hbar share/wbar := by
    have hκ : 0≤(1-ξ)*B := mul_nonneg (by linarith [hξ.2]) hB
    linarith
  have hn : 0≤ populationNumerator ξ ρ abar mbar hbar share := by
    have hh := (le_div_iff₀ hw).mp hn0
    simpa only [zero_mul] using hh
  refine ⟨hw,?_⟩
  rw [abs_of_nonneg hn]
  have hh := (div_le_iff₀ hw).mp
    (show populationNumerator ξ ρ abar mbar hbar share/wbar≤1 by linarith)
  simpa only [one_mul] using hh

section Pointwise
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
  (N : ℕ) (hN : 0< N) (row : Fin N→ X×unitInterval)
  (active private0 private1 : X→ Bool)
  (hactive : Measurable active) (hprivate0 : Measurable private0) (hprivate1 : Measurable private1)
  (p : X→ unitInterval) (hp : Measurable p) (bid : X→ℝ) (hbid : Measurable bid)
  (hfair : (∫ x,indicator private0 x ∂μ)=(∫ x,indicator private1 x ∂μ))
  (ξ share ρ B R Rp width γ δ : ℝ) (hξ : 0< ξ) (hξ1 : ξ≤1)
  (hρ : ρ∈Icc (0:ℝ) 1) (hB : 0≤ B) (hw : 0< width) (hwγ : width≤ γ) (hγ1 : γ≤1)

local notation "abar" => ∫ x,indicator active x ∂μ
local notation "mbar" => ∫ x,(p x:ℝ)*indicator active x ∂μ
local notation "hbar" => ∫ x,indicator private0 x ∂μ
local notation "wbar" => ∫ x,(p x:ℝ)*reciprocalWeight active bid x ∂μ
local notation "H0" => privateCount N (fun _ : Unit => row) private0 ()
local notation "H1" => privateCount N (fun _ : Unit => row) private1 ()
local notation "Z" => commonEmpiricalError μ N (fun _ : Unit => row) active private0 private1 p bid ()

variable (reg : Bool) (G : GuardInterior ξ share ρ B R Rp γ δ
    (∫ x,indicator active x ∂μ) (∫ x,(p x:ℝ)*indicator active x ∂μ)
    (∫ x,indicator private0 x ∂μ) (∫ x,(p x:ℝ)*reciprocalWeight active bid x ∂μ) reg)
  (ν0 : FiniteLaw (Marks (privateCount N (fun _ : Unit => row) private0 ())))
  (ν1 : FiniteLaw (Marks (privateCount N (fun _ : Unit => row) private1 ())))
  (hmean0 : privateMean (privateCount N (fun _ : Unit => row) private0 ()) reg ν0=
    share*privateCount N (fun _ : Unit => row) private0 ())
  (hmean1 : privateMean (privateCount N (fun _ : Unit => row) private1 ()) reg ν1=
    share*privateCount N (fun _ : Unit => row) private1 ())
  {A : ℕ} (e : Fin A≃Active (activePrefix row active))
  (i : Fin A) (hi : (e i).val=0) (target : Fin A)
  (b : ℝ) (hb : 1≤ b) (focal : Bool)
  (hphysical : ∀ j,active (row j).1=true → 1≤ bid (row j).1)

local notation "Pnum" => countParameters A H0 H1 (iidCapacity ρ N) ξ reg ν0 ν1
local notation "Phi" => TypicalGuardStatistics.phi A H0 H1 (iidCapacity ρ N) ξ B R Rp width reg ν0 ν1
local notation "br" => compressedBids (activePrefix row active) e (bidsPrefix row bid b)
local notation "zr" => compressedFlags (activePrefix row active) e (flagsPrefix row p focal)
local notation "weight" => targetTypicalWeight Phi br target zr
local notation "nbar" => populationNumerator ξ ρ abar mbar hbar share
local notation "ideal" => clippedCount ξ b nbar nbar wbar

include hN hactive hprivate0 hprivate1 hp hbid hfair γ hξ hξ1 hρ hB hw hwγ hγ1 G hmean0 hmean1 hi hb hphysical in
theorem target_count_error (fallback : CountLaw 2) (f : Fin 3→ℝ) :
    |(FiniteLaw.mixture (targetStateCount (Pnum).mixedCount br target zr i) fallback weight
        (targetTypicalWeight_bounds Phi br target zr).1
        (targetTypicalWeight_bounds Phi br target zr).2).expect f-
      (if focal then ideal else FiniteLaw.dirac 1).expect f|≤
        MenuError.oscillation f*coefficient ξ b wbar δ*Z+
          2*MenuError.oscillation f*(if i=target then 1 else 0) := by
  let M := flaggedMixedCount N (fun _ : Unit => row) (fun _ => (e target).val) active p focal ()
  let A0 := activeCount N (fun _ : Unit => row) active ()
  let W := flaggedReciprocal N (fun _ : Unit => row) (fun _ => (e target).val) active p bid b focal ()
  let Ze := guardError N A0 M H0 H1 W abar mbar hbar wbar
  let C := (Pnum).mixedCount (targetMixedSet target zr).card (mixedReciprocalSum (targetMixedSet target zr) br) b
  have hbf : br i=b := by simp only [compressedBids,hi,bidsPrefix,Fin.cons_zero]
  have hhbar : 0≤ hbar := integral_nonneg fun x => (indicator_bounds private0 x).1
  have hg0 : 0≤ γ := hw.le.trans hwγ
  have hnum := guard_numerator_bound G ⟨hξ.le,hξ1⟩ hhbar hB hg0
  have hZ : Ze≤ Z := flaggedGuardError_le_common μ N hN (fun _ : Unit => row)
    active private0 private1 hactive hprivate0 hprivate1 p hp bid hbid b hb focal
    (fun _ => (e target).val) hfair ()
  have hC : |C.expect f-(ideal).expect f|≤
      MenuError.oscillation f*(12/(ξ*b*wbar)+4/wbar)*Ze := by
    have hm := CommonFlagCompression.mixedCount_exact row active p bid e target hN
      private0 private1 ξ share ρ reg ν0 ν1 hmean0 hmean1 b hb focal hphysical
    change C=meanCountLaw ξ (iidCapacity ρ N)
      (clampedOwner (A0-M) (share*H0) (share*H1))
      (A0-M-clampedOwner (A0-M) (share*H0) (share*H1)) (share*H0) (share*H1) M ((N:ℝ)*W) b at hm
    rw [hm]
    exact meanCount_error_guard N A0 M H0 H1 hN
      (flaggedMixedCount_le_active N (fun _ : Unit => row) (fun _ => (e target).val) active p focal ())
      ξ share ρ b W abar mbar hbar wbar hξ hξ1 G.share_mem hρ hb hnum.1 hnum.2 f
  have hwgt : 1-weight≤ Ze/δ := by
    rw [phi_exact row active p bid e target hN private0 private1 ξ share ρ B R Rp width
      G.share_mem reg G.share_lower ν0 ν1 hmean0 hmean1 b hb focal hphysical]
    exact (scalarSourceWeight_defect_le N A0 M H0 H1 hN
      (flaggedMixedCount_le_active N (fun _ : Unit => row) (fun _ => (e target).val) active p focal ())
      ξ share ρ B R Rp width γ δ W abar mbar hbar wbar reg ⟨hξ.le,hξ1⟩ G.share_mem G.share_lower hρ
      hB hhbar hw hwγ hγ1 G.radius_pos G.radius_mixed G.radius_reciprocal G.radius_capacity
      G.radius_margin G.lower_endpoint G.upper_endpoint G.private_mean).2
  have hs : targetStateCount (Pnum).mixedCount br target zr i=
      if focal && !(decide (i=target)) then C else FiniteLaw.dirac 1 := by
    unfold targetStateCount
    rw [hbf]
    have hm := focal_membership row active p e target i hi focal
    simp only [hm]
    cases focal <;> by_cases he : i=target <;> simp [he,C]
  rw [hs]
  have he := masked_favored_count_error C fallback ideal f true focal (decide (i=target)) weight
    (targetTypicalWeight_bounds Phi br target zr).1 (targetTypicalWeight_bounds Phi br target zr).2
  simp only [ite_true,add_zero,decide_eq_true_eq] at he
  have ho : 0≤ MenuError.oscillation f := MenuError.oscillation_nonneg f
  have hK : 0≤ MenuError.oscillation f*(12/(ξ*b*wbar)+4/wbar) := by
    have hW := hnum.1
    positivity
  have hZ0 : 0≤ Ze := (guardError_bounds N A0 M H0 H1 W abar mbar hbar wbar).1
  have he0 := mul_le_mul_of_nonneg_left hwgt (by positivity : 0≤2*MenuError.oscillation f)
  have hKZ := mul_le_mul_of_nonneg_left hZ hK
  have hwZ := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hZ G.radius_pos.le) (by positivity : 0≤2*MenuError.oscillation f)
  unfold coefficient
  have hid : MenuError.oscillation f*(12/(ξ*b*wbar)+4/wbar+2/δ)*Z=
      MenuError.oscillation f*(12/(ξ*b*wbar)+4/wbar)*Z+2*MenuError.oscillation f*(Z/δ) := by ring
  rw [hid]
  linarith

end Pointwise
end FCAppendix.Affine.Tail04.CommonFiniteCountError
