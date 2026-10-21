import FCAppendix.Affine.Hybrid.SourceFiniteMenuError

set_option maxHeartbeats 1000000
noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory Set Filter Topology Classical

theorem exists_eventual_uniform_typical_menus (a h ρ z ξ eta L U W : ℝ)
    (ha : 0 < a) (hz0 : 0 ≤ z) (hz1 : z < 1) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hL : 0 < L) (hLU : L ≤ U) (hW : 0 ≤ W)
    (hlower : h/2 < ρ) (hupper : ρ < a+h/2)
    (hq0 : 0 < sourceExposure a h ρ z) (hq1 : sourceExposure a h ρ z < 1)
    (hboxlo : (1-ξ)*U < (1-ξ*sourceExposure a h ρ z)*L)
    (hboxhi : (1-ξ*sourceExposure a h ρ z)*U < L)
    (c : ℕ → ℕ) (hc : Tendsto (fun M => (c M : ℝ)/(M : ℝ)) atTop (𝓝 ρ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ M : ℕ in atTop, ∀ A H₀ H₁ : ℕ,
      |(A : ℝ)-(M : ℝ)*a| ≤ M*δ →
      |(H₀ : ℝ)-(M : ℝ)*(h/2)| ≤ M*δ →
      |(H₁ : ℝ)-(M : ℝ)*(h/2)| ≤ M*δ →
      let d₀ := activeResidual (c M) A H₀
      let d₁ := activeResidual (c M) A H₁
      let ell := exclusiveQuota z A
      let gap := residualDifference d₀ d₁
      let r := min d₀ d₁-ell
      d₀ ≠ d₁ →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι], Fintype.card ι=A →
      ∀ (i : ι) (G : Measure ℝ) [IsProbabilityMeasure G],
      (∀ᵐ x ∂G, x ∈ Icc L U) → ∀ b ∈ Icc L U, ∀ v : ℝ, |v| ≤ W →
      let h0 := 1-ξ*sourceExposure a h ρ z
      let q := exposure ξ (h0/reciprocalMean G) b
      |(∫ x : ι → ℝ, sourceOwnerPayoff ξ eta v (Function.update x i b) r (ell+gap) ell i
        ∂Measure.pi (fun _ : ι => G))-(z*(v-b)+(1-z)*independentTwo eta v b q)| < ε ∧
      |(∫ x : ι → ℝ, sourceSingletonPayoff ξ v (Function.update x i b) r (ell+gap) ell i
        ∂Measure.pi (fun _ : ι => G))-((z/2+(1-z)*q)*(v-b))| < ε := by
  have hU : 0 < U := hL.trans_le hLU
  let Cb := broadcastExposureModulus eta W U/(ξ*L)
  let Db := W+U+broadcastExposureModulus eta W U
  let Cs := (W+U)/(ξ*L)
  let Ds := W+U
  let C := Cb+Db+Cs+Ds+1
  have hmod : 0 ≤ broadcastExposureModulus eta W U := broadcastExposureModulus_nonneg hW hU.le
  have hCb : 0 ≤ Cb := div_nonneg hmod (mul_pos hξ hL).le
  have hDb : 0 ≤ Db := by dsimp [Db]; positivity
  have hCs : 0 ≤ Cs := div_nonneg (add_nonneg hW hU.le) (mul_pos hξ hL).le
  have hDs : 0 ≤ Ds := add_nonneg hW hU.le
  have hC : 0 < C := by dsimp [C]; linarith
  let τ := ε/C
  have hτ : 0 < τ := div_pos hε hC
  have hτeq : C*τ=ε := by dsimp [τ]; field_simp
  obtain ⟨δ,hδ,hcounts⟩ := exists_eventual_typical_finiteMenuError a h ρ z ξ L U ha hz0 hz1
    hξ hξ1 hL hU hlower hupper hq0 hq1 hboxlo hboxhi c hc τ hτ
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hcounts,eventually_gt_atTop (0:ℕ)] with M hMc hM
  intro A H₀ H₁ hA hH₀ hH₁
  let d₀ := activeResidual (c M) A H₀
  let d₁ := activeResidual (c M) A H₁
  let ell := exclusiveQuota z A
  let gap := residualDifference d₀ d₁
  let small := min d₀ d₁
  let K := 2*ell+gap
  let r := small-ell
  let h0 := 1-ξ*sourceExposure a h ρ z
  have hp := hMc A H₀ H₁ hA hH₀ hH₁
  change NormalizedGuardRegion ξ L U (finiteCountPoint M A small ell gap) ∧
    0 < A ∧ ell < small ∧ K < A ∧
    finiteHarmonicError ξ L U h0 A K r+1/(A : ℝ)+|(K : ℝ)/(A : ℝ)-z| < τ at hp
  dsimp only
  intro hne ι _ _ _ hcard i G _ hbox b hb v hv
  have hKpos : 1 ≤ K := by
    dsimp [K,gap,residualDifference]
    omega
  have hAN : 2 ≤ A := by omega
  have hsum : (ell+gap)+ell=K := by dsimp [K]; omega
  have hgEq := normalizedFactor_count_eq (ξ := ξ) M A small ell gap hM hp.2.2.1 hp.2.2.2.1
  have hg : 0 ≤ finiteReceiptFactor ξ (A-K) r := by
    rw [←hgEq]
    exact hp.1.2.2.2.1.le
  have hglo : (1-ξ)*U < finiteReceiptFactor ξ (A-K) r*L := by
    rw [←hgEq]
    exact hp.1.2.2.2.2.1
  have hghi : finiteReceiptFactor ξ (A-K) r*U < L := by
    rw [←hgEq]
    exact hp.1.2.2.2.2.2
  have hh0 : 0 ≤ h0 := by dsimp [h0]; nlinarith
  have hh01 : |h0| ≤ 1 := by rw [abs_of_nonneg hh0]; dsimp [h0]; nlinarith
  let H := finiteHarmonicError ξ L U h0 A K r
  let B := 1/(A : ℝ)+|(K : ℝ)/(A : ℝ)-z|
  have hH : 0 ≤ H := by dsimp [H,finiteHarmonicError]; positivity
  have hB : 0 ≤ B := add_nonneg (by positivity) (abs_nonneg _)
  have hnum : H+B < τ := by dsimp only [H,B]; linarith only [hp.2.2.2.2]
  have htotal : C*(H+B) < ε := by rw [←hτeq]; exact mul_lt_mul_of_pos_left hnum hC
  have hBbound := sourceOwnerPayoff_interim_error (eta := eta) (z := z) G hξ hξ1 hL hbox hb hh0 hh01 hboxlo hboxhi hv
    r (ell+gap) ell (by simpa only [hcard] using hAN) (by simpa only [hsum] using hKpos)
    (by simpa only [hsum,hcard] using hp.2.2.2.1)
    (by simpa only [hsum,hcard] using hg) (by simpa only [hsum,hcard] using hglo)
    (by simpa only [hsum,hcard] using hghi) i
  have hSbound := sourceSingletonPayoff_interim_error (z := z) G hξ hξ1 hL hbox hb hh0 hh01 hboxlo hboxhi hv
    r (ell+gap) ell (by simpa only [hcard] using hAN) (by simpa only [hsum] using hKpos)
    (by simpa only [hsum,hcard] using hp.2.2.2.1)
    (by simpa only [hsum,hcard] using hg) (by simpa only [hsum,hcard] using hglo)
    (by simpa only [hsum,hcard] using hghi) i
  simp only [hcard,hsum] at hBbound hSbound
  constructor
  · apply hBbound.trans_lt
    change Cb*H+Db*B < ε
    have he : Cb*H+Db*B ≤ C*(H+B) := by
      dsimp only [C]
      nlinarith only [mul_nonneg hCb hB,mul_nonneg hDb hH,mul_nonneg hCs hH,
        mul_nonneg hCs hB,mul_nonneg hDs hH,mul_nonneg hDs hB,hH,hB]
    exact he.trans_lt htotal
  · apply hSbound.trans_lt
    change Cs*H+Ds*B < ε
    have he : Cs*H+Ds*B ≤ C*(H+B) := by
      dsimp only [C]
      nlinarith only [mul_nonneg hCb hH,mul_nonneg hCb hB,mul_nonneg hDb hH,
        mul_nonneg hDb hB,mul_nonneg hCs hB,mul_nonneg hDs hH,hH,hB]
    exact he.trans_lt htotal

end FCAppendix.Affine.Hybrid
