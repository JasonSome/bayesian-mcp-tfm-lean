import FCAppendix.Affine.Hybrid.FiniteMenuMixture

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory Set Classical
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def favoredMultiplierError (xi h0 H : ℝ) (b : ι → ℝ) (r K : ℕ) : ℝ :=
  (favoredSetLaw b K).expect (fun E => |finiteMultiplier xi b (Finset.univ \ E) r-h0/H|)

lemma favored_owner_bias_to_z (b : ι → ℝ) (K : ℕ) (z : ℝ)
    (hN : 2 ≤ Fintype.card ι) (hK : 1 ≤ K) (hKN : K ≤ Fintype.card ι) (i : ι) :
    |(favoredSetLaw b K).prob (fun E => i ∈ E)-z| ≤
      1/(Fintype.card ι : ℝ)+|(K : ℝ)/(Fintype.card ι : ℝ)-z| := by
  have he : (favoredSetLaw b K).prob (fun E => i ∈ E)-z=
      ((favoredSetLaw b K).prob (fun E => i ∈ E)-(K : ℝ)/(Fintype.card ι : ℝ))+
      ((K : ℝ)/(Fintype.card ι : ℝ)-z) := by ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add (favoredSetLaw_bias_le b hN hK hKN i) le_rfl)

lemma favored_exposure_menu_error (G : Measure ℝ) [IsProbabilityMeasure G]
    {xi L U h0 z : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1) (hL : 0 < L)
    (_hbox : ∀ᵐ x ∂G, x ∈ Icc L U) (_hh0 : 0 ≤ h0)
    (_h0lo : (1-xi)*U < h0*L) (_h0hi : h0*U < L)
    (b : ι → ℝ) (hb : ∀ j, b j ∈ Icc L U) (r K : ℕ)
    (hN : 2 ≤ Fintype.card ι) (hK : 1 ≤ K) (hKN : K < Fintype.card ι)
    (hg : 0 ≤ finiteReceiptFactor xi (Fintype.card ι-K) r)
    (hglo : (1-xi)*U < finiteReceiptFactor xi (Fintype.card ι-K) r*L)
    (hghi : finiteReceiptFactor xi (Fintype.card ι-K) r*U < L)
    (i : ι) (a C D : ℝ) (mixed : ℝ → ℝ) (hC : 0 ≤ C)
    (hlip : ∀ q ∈ Icc (0:ℝ) 1,
      |mixed q-mixed (exposure xi (h0/reciprocalMean G) (b i))| ≤
        C*|q-exposure xi (h0/reciprocalMean G) (b i)|)
    (hgain : |a-mixed (exposure xi (h0/reciprocalMean G) (b i))| ≤ D) :
    |(favoredSetLaw b K).expect (fun E => if i∈E then a else
      mixed (exposure xi (finiteMultiplier xi b (Finset.univ \ E) r) (b i)))-
      (z*a+(1-z)*mixed (exposure xi (h0/reciprocalMean G) (b i)))| ≤
      (C/(xi*L))*favoredMultiplierError xi h0 (reciprocalMean G) b r K+
      D*(1/(Fintype.card ι : ℝ)+|(K : ℝ)/(Fintype.card ι : ℝ)-z|) := by
  apply finite_union_mixture_error (favoredSetLaw b K) (fun E => i∈E)
    a (mixed (exposure xi (h0/reciprocalMean G) (b i))) z _ (C/(xi*L)) D
    (fun E => mixed (exposure xi (finiteMultiplier xi b (Finset.univ \ E) r) (b i)))
    (fun E => |finiteMultiplier xi b (Finset.univ \ E) r-h0/reciprocalMean G|)
  · exact div_nonneg hC (mul_pos hxi hL).le
  · exact fun _ => abs_nonneg _
  · intro E hE _
    have hcard : (Finset.univ \ E).card = Fintype.card ι-K := by
      have he := favoredSetLaw_support b hN hK hKN.le E hE
      simp only [Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,he]
    have hD : (Finset.univ \ E).Nonempty := Finset.card_pos.mp (by rw [hcard]; omega)
    have hq := exposure_mem_of_finite_factor hxi hxi1 hL b hb (Finset.univ \ E) r hD
      (by simpa only [hcard] using hg) (by simpa only [hcard] using hglo)
      (by simpa only [hcard] using hghi) i
    have hh := (hlip _ hq).trans (mul_le_mul_of_nonneg_left
      (exposure_difference_bound (lam := finiteMultiplier xi b (Finset.univ \ E) r)
        (lam' := h0/reciprocalMean G) hxi hL (hb i).1) hC)
    calc
      _ ≤ C*(|finiteMultiplier xi b (Finset.univ \ E) r-h0/reciprocalMean G|/(xi*L)) := hh
      _ = _ := by ring
  · exact favored_owner_bias_to_z b K z hN hK hKN.le i
  · exact hgain

theorem sourceOwnerPayoff_menu_error (G : Measure ℝ) [IsProbabilityMeasure G]
    {xi eta L U h0 z v W : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1) (hL : 0 < L)
    (hbox : ∀ᵐ x ∂G, x ∈ Icc L U) (hh0 : 0 ≤ h0)
    (h0lo : (1-xi)*U < h0*L) (h0hi : h0*U < L) (hv : |v| ≤ W)
    (b : ι → ℝ) (hb : ∀ j, b j ∈ Icc L U) (r K1 K2 : ℕ)
    (hN : 2 ≤ Fintype.card ι) (hK : 1 ≤ K1+K2) (hKN : K1+K2 < Fintype.card ι)
    (hg : 0 ≤ finiteReceiptFactor xi (Fintype.card ι-(K1+K2)) r)
    (hglo : (1-xi)*U < finiteReceiptFactor xi (Fintype.card ι-(K1+K2)) r*L)
    (hghi : finiteReceiptFactor xi (Fintype.card ι-(K1+K2)) r*U < L) (i : ι) :
    |sourceOwnerPayoff xi eta v b r K1 K2 i-
      (z*(v-b i)+(1-z)*independentTwo eta v (b i) (exposure xi (h0/reciprocalMean G) (b i)))| ≤
      (broadcastExposureModulus eta W U/(xi*L))*
        favoredMultiplierError xi h0 (reciprocalMean G) b r (K1+K2)+
      (W+U+broadcastExposureModulus eta W U)*
        (1/(Fintype.card ι : ℝ)+|((K1+K2 : ℕ) : ℝ)/(Fintype.card ι : ℝ)-z|) := by
  have hbabs : |b i| ≤ U := by rw [abs_of_pos (hL.trans_le (hb i).1)]; exact (hb i).2
  have hq := exposure_mem_of_mean_factor G hxi hxi1 hL hbox (hb i) hh0 h0lo h0hi
  rw [sourceOwnerPayoff_eq_favored xi eta v b r K1 K2 i hN (by omega) hKN.le]
  exact favored_exposure_menu_error G hxi hxi1 hL hbox hh0 h0lo h0hi b hb r (K1+K2)
    hN hK hKN hg hglo hghi i (v-b i) (broadcastExposureModulus eta W U)
    (W+U+broadcastExposureModulus eta W U) (independentTwo eta v (b i))
    (broadcastExposureModulus_nonneg ((abs_nonneg v).trans hv) ((abs_nonneg (b i)).trans hbabs))
    (fun q hq' => independentTwo_lipschitz hv hbabs hq' hq)
    (broadcast_owner_difference_bound hv hbabs hq)

theorem sourceSingletonPayoff_menu_error (G : Measure ℝ) [IsProbabilityMeasure G]
    {xi L U h0 z v W : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1) (hL : 0 < L)
    (hbox : ∀ᵐ x ∂G, x ∈ Icc L U) (hh0 : 0 ≤ h0)
    (h0lo : (1-xi)*U < h0*L) (h0hi : h0*U < L) (hv : |v| ≤ W)
    (b : ι → ℝ) (hb : ∀ j, b j ∈ Icc L U) (r K1 K2 : ℕ)
    (hN : 2 ≤ Fintype.card ι) (hK : 1 ≤ K1+K2) (hKN : K1+K2 < Fintype.card ι)
    (hg : 0 ≤ finiteReceiptFactor xi (Fintype.card ι-(K1+K2)) r)
    (hglo : (1-xi)*U < finiteReceiptFactor xi (Fintype.card ι-(K1+K2)) r*L)
    (hghi : finiteReceiptFactor xi (Fintype.card ι-(K1+K2)) r*U < L) (i : ι) :
    |sourceSingletonPayoff xi v b r K1 K2 i-
      ((z/2+(1-z)*exposure xi (h0/reciprocalMean G) (b i))*(v-b i))| ≤
      ((W+U)/(xi*L))*favoredMultiplierError xi h0 (reciprocalMean G) b r (K1+K2)+
      (W+U)*(1/(Fintype.card ι : ℝ)+|((K1+K2 : ℕ) : ℝ)/(Fintype.card ι : ℝ)-z|) := by
  have hbabs : |b i| ≤ U := by rw [abs_of_pos (hL.trans_le (hb i).1)]; exact (hb i).2
  have hq := exposure_mem_of_mean_factor G hxi hxi1 hL hbox (hb i) hh0 h0lo h0hi
  have hh := favored_exposure_menu_error (z := z) G hxi hxi1 hL hbox hh0 h0lo h0hi b hb r (K1+K2)
    hN hK hKN hg hglo hghi i ((v-b i)/2) (W+U) (W+U) (fun q => (v-b i)*q)
    (add_nonneg ((abs_nonneg v).trans hv) ((abs_nonneg (b i)).trans hbabs))
    (fun q _ => singleton_exposure_lipschitz hv hbabs)
    (singleton_owner_difference_bound hv hbabs hq)
  rw [sourceSingletonPayoff_eq_favored xi v b r K1 K2 i hN (by omega) hKN.le]
  have he : z*((v-b i)/2)+(1-z)*((v-b i)*exposure xi (h0/reciprocalMean G) (b i))=
      (z/2+(1-z)*exposure xi (h0/reciprocalMean G) (b i))*(v-b i) := by ring
  rw [he] at hh
  exact hh

end FCAppendix.Affine.Hybrid
