import FCAppendix.Affine.Tail04.UnusedEmpiricalGuard
import FCAppendix.Affine.Tail04.UnusedBidIntermediate

noncomputable section
namespace FCAppendix.Affine.Tail04.UnusedMeanPrices
open MeasureTheory ProbabilityTheory Set Classical
open MenuError SourceMenuPopulation TypicalGuardEndpoints EqualPrivateSignal
open NativeTypicalCount WeightedFlagBound
open CommonFiniteCountError

theorem private_balance (N A M H0 H1 : ℕ) (hN : 0< N) (hMA : M≤ A)
    (share W abar mbar hbar wbar δ : ℝ) (hshare : share∈Icc (0:ℝ) 1)
    (hroom : 4*δ≤ abar-mbar)
    (hg : guardError N A M H0 H1 W abar mbar hbar wbar< δ) :
    |share*(H1:ℝ)-share*(H0:ℝ)|≤(A-M:ℕ) := by
  let Z:=guardError N A M H0 H1 W abar mbar hbar wbar
  have hn : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have he:=guardError_bounds N A M H0 H1 W abar mbar hbar wbar
  have hd : |(H1:ℝ)/N-(H0:ℝ)/N|≤2*Z := by
    have hh:=abs_sub_le ((H1:ℝ)/N) hbar ((H0:ℝ)/N)
    rw [abs_sub_comm hbar] at hh
    exact hh.trans (by linarith [he.2.2.2.1,he.2.2.2.2.1])
  have hg0 : 2*Z≤(A:ℝ)/N-(M:ℝ)/N := by
    have hAlo:=(abs_le.mp he.2.1).1
    have hMhi:=(abs_le.mp he.2.2.1).2
    dsimp only [Z] at *
    linarith
  have hd' : |share*((H1:ℝ)/N-(H0:ℝ)/N)|≤(A:ℝ)/N-(M:ℝ)/N := by
    rw [abs_mul,abs_of_nonneg hshare.1]
    have hh:=mul_le_mul_of_nonneg_left hd hshare.1
    have hZ:=he.1
    exact hh.trans (by nlinarith [hshare.2])
  have hn0 : (N:ℝ)≠0 := hn.ne'
  have hid : share*((H1:ℝ)/N-(H0:ℝ)/N)=
      (share*(H1:ℝ)-share*(H0:ℝ))/(N:ℝ) := by ring
  rw [hid,abs_div,abs_of_pos hn,←sub_div,←Nat.cast_sub hMA] at hd'
  exact (div_le_div_iff_of_pos_right hn).mp hd'

theorem clamped_eq_balanced (N A M H0 H1 : ℕ) (hN : 0< N) (hMA : M≤ A)
    (share W abar mbar hbar wbar δ : ℝ) (hshare : share∈Icc (0:ℝ) 1)
    (hroom : 4*δ≤ abar-mbar)
    (hg : guardError N A M H0 H1 W abar mbar hbar wbar< δ) :
    clampedOwner (A-M) (share*H0) (share*H1)=balancedOwnerQuota (A-M) (share*H0) (share*H1) := by
  exact min_eq_right (balancedOwnerQuota_guards (A-M) (share*H0) (share*H1)
    (private_balance N A M H0 H1 hN hMA share W abar mbar hbar wbar δ hshare hroom hg)).1

theorem price_errors (N A M H0 H1 : ℕ) (hN : 0< N) (hMA : M≤ A)
    (ξ share ρ B R Rp γ δ W abar mbar hbar wbar : ℝ) (reg : Bool)
    (hξ : ξ∈Icc (0:ℝ) 1) (hρ : ρ∈Icc (0:ℝ) 1) (hB : 0≤ B) (hhbar : 0≤ hbar) (hγ : 0≤ γ)
    (G : GuardInterior ξ share ρ B R Rp γ δ abar mbar hbar wbar reg)
    (hg : guardError N A M H0 H1 W abar mbar hbar wbar< δ) :
    let q:=clampedOwner (A-M) (share*H0) (share*H1)
    let Z:=guardError N A M H0 H1 W abar mbar hbar wbar
    let lam:=populationNumerator ξ ρ abar mbar hbar share/wbar
    0< W ∧
      |lambda (iidCapacity ρ N) q M ξ ((N:ℝ)*W) (share*H0)-lam|≤10*Z/wbar ∧
      |lambda (iidCapacity ρ N) (A-M-q) M ξ ((N:ℝ)*W) (share*H1)-lam|≤10*Z/wbar := by
  dsimp only
  let q:=clampedOwner (A-M) (share*H0) (share*H1)
  let Z:=guardError N A M H0 H1 W abar mbar hbar wbar
  let nbar:=populationNumerator ξ ρ abar mbar hbar share
  have hb:=guardError_bounds N A M H0 H1 W abar mbar hbar wbar
  have hwbar : 0< wbar := by linarith [G.radius_pos,G.radius_reciprocal]
  have hWlo : wbar/2≤ W := by linarith [(abs_le.mp hb.2.2.2.2.2.1).1,G.radius_reciprocal]
  have hW : 0< W := (half_pos hwbar).trans_le hWlo
  have hc : |(iidCapacity ρ N:ℝ)/N-ρ|≤ Z :=
    (iidCapacity_error hρ N hN).trans hb.2.2.2.2.2.2
  have ho:=owners_guardError N A M H0 H1 hN hMA G.share_mem W abar mbar hbar wbar
  have hnbar:=guard_numerator_bound G hξ hhbar hB hγ
  have h0:=endpointNumerator_error N (iidCapacity ρ N) q M H0 ξ share ρ abar mbar hbar Z
    hξ G.share_mem hb.2.2.1 hc ho.1 hb.2.2.2.1
  have h1:=endpointNumerator_error N (iidCapacity ρ N) (A-M-q) M H1 ξ share ρ abar mbar hbar Z
    hξ G.share_mem hb.2.2.1 hc ho.2 hb.2.2.2.2.1
  have r0:=Central.ratio_error (half_pos hwbar) hWlo hwbar hnbar.2 h0 hb.2.2.2.2.2.1
  have r1:=Central.ratio_error (half_pos hwbar) hWlo hwbar hnbar.2 h1 hb.2.2.2.2.2.1
  have hid : (4*Z+Z)/(wbar/2)=10*Z/wbar := by ring
  rw [hid] at r0 r1
  refine ⟨hW,?_,?_⟩
  · rw [lambda_normalized N (iidCapacity ρ N) q M H0 hN ξ W share hW.ne']
    exact r0
  · rw [lambda_normalized N (iidCapacity ρ N) (A-M-q) M H1 hN ξ W share hW.ne']
    exact r1

theorem price_errors_le_margin (N A M H0 H1 : ℕ) (hN : 0< N) (hMA : M≤ A)
    (ξ share ρ B R Rp γ δ W abar mbar hbar wbar : ℝ) (reg : Bool)
    (hξ : ξ∈Icc (0:ℝ) 1) (hρ : ρ∈Icc (0:ℝ) 1) (hB : 0≤ B) (hhbar : 0≤ hbar) (hγ : 0≤ γ)
    (G : GuardInterior ξ share ρ B R Rp γ δ abar mbar hbar wbar reg)
    (hg : guardError N A M H0 H1 W abar mbar hbar wbar< δ) :
    let q:=clampedOwner (A-M) (share*H0) (share*H1)
    let lam:=populationNumerator ξ ρ abar mbar hbar share/wbar
    |lambda (iidCapacity ρ N) q M ξ ((N:ℝ)*W) (share*H0)-lam|≤ γ ∧
      |lambda (iidCapacity ρ N) (A-M-q) M ξ ((N:ℝ)*W) (share*H1)-lam|≤ γ := by
  have he:=price_errors N A M H0 H1 hN hMA ξ share ρ B R Rp γ δ W abar mbar hbar wbar reg
    hξ hρ hB hhbar hγ G hg
  have hwbar : 0< wbar := by linarith [G.radius_pos,G.radius_reciprocal]
  have hsmall : 10*guardError N A M H0 H1 W abar mbar hbar wbar/wbar≤ γ :=
    (div_le_iff₀ hwbar).mpr (by linarith [G.radius_margin])
  exact ⟨he.2.1.trans hsmall,he.2.2.trans hsmall⟩

end FCAppendix.Affine.Tail04.UnusedMeanPrices
