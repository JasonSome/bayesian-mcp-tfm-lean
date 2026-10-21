import FCAppendix.Affine.Hybrid.FavoredRankJump

noncomputable section
namespace FCAppendix.Affine.Hybrid
open Set Filter Topology
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def sourceOwnerJump (xi eta v : ℝ) (b : ι→ℝ) (r K : ℕ) (i : ι) : ℝ :=
  (∑j∈tiedRivals b i,
    (favoredTargetPayoff xi eta v b r K i i-favoredTargetPayoff xi eta v b r K i j))/
      (2*rankDenominator ι)

theorem sourceOwnerJump_lower [Nonempty ι] {xi eta v L U vmin : ℝ}
    (b : ι→ℝ) (r K : ℕ) (i : ι) (hN : 2≤Fintype.card ι)
    (hK : 1≤K) (hKN : K≤Fintype.card ι)
    (heta : 0<eta) (hL : 0<L) (hbL : L≤b i) (hbU : b i≤U)
    (hUv : U<vmin) (hvv : vmin≤v) :
    ((tiedRivals b i).card:ℝ)*(1-fillFraction (ι:=ι) K)*
        (min (vmin-U) (eta*L)/2)/(2*rankDenominator ι)≤
      sourceOwnerJump xi eta v b r K i := by
  unfold sourceOwnerJump
  apply div_le_div_of_nonneg_right _ (show (0:ℝ)≤2*rankDenominator ι from mul_nonneg (by norm_num) rankDenominator_pos.le)
  calc
    _ = ∑j∈tiedRivals b i,(1-fillFraction (ι:=ι) K)*(min (vmin-U) (eta*L)/2) := by simp; ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j hj
      have ht := (Finset.mem_filter.mp hj).2
      exact favoredTargetPayoff_tie_gain b r K i j ht.1.symm ht.2.symm hN hK hKN
        heta hL hbL hbU hUv hvv

theorem sourceOwnerJump_lower_one_tie [Nonempty ι] {xi eta v L U vmin : ℝ}
    (b : ι→ℝ) (r K : ℕ) (i j : ι) (hij : i≠j) (hbid : b i=b j)
    (hN : 2≤Fintype.card ι) (hK : 1≤K) (hKN : K<Fintype.card ι)
    (heta : 0<eta) (hL : 0<L) (hbL : L≤b i) (hbU : b i≤U)
    (hUv : U<vmin) (hvv : vmin≤v) :
    (1-fillFraction (ι:=ι) K)*(min (vmin-U) (eta*L)/2)/
        ((Fintype.card ι:ℝ)*((Fintype.card ι:ℝ)+1))≤
      sourceOwnerJump xi eta v b r K i := by
  have hties : (1:ℝ)≤(tiedRivals b i).card := by
    exact_mod_cast Finset.one_le_card.mpr ⟨j,by simp [tiedRivals,hij.symm,hbid.symm]⟩
  have hg : 0≤(1-fillFraction (ι:=ι) K)*(min (vmin-U) (eta*L)/2) := by
    have hf := fillFraction_bounds hN hK hKN.le
    exact mul_nonneg (sub_nonneg.mpr hf.2) (by positivity)
  have hh := sourceOwnerJump_lower (xi:=xi) b r K i hN hK hKN.le heta hL hbL hbU hUv hvv
  have hm := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hties hg) (show (0:ℝ)≤2*rankDenominator ι from mul_nonneg (by norm_num) rankDenominator_pos.le)
  simp only [one_mul] at hm
  have hd : 2*rankDenominator ι=(Fintype.card ι:ℝ)*((Fintype.card ι:ℝ)+1) := by
    unfold rankDenominator
    ring
  rw [←hd]
  exact hm.trans (by simpa only [mul_assoc] using hh)

lemma sourceOwnerJump_pos_of_tie [Nonempty ι] {xi eta v L U vmin : ℝ}
    (b : ι→ℝ) (r K : ℕ) (i j : ι) (hij : i≠j) (hbid : b i=b j)
    (hN : 2≤Fintype.card ι) (hK : 1≤K) (hKN : K<Fintype.card ι)
    (heta : 0<eta) (hL : 0<L) (hbL : L≤b i) (hbU : b i≤U)
    (hUv : U<vmin) (hvv : vmin≤v) :
    0<sourceOwnerJump xi eta v b r K i := by
  have hNr : 1<(Fintype.card ι:ℝ) := by exact_mod_cast (show 1<Fintype.card ι by omega)
  have hKr : (K:ℝ)<Fintype.card ι := by exact_mod_cast hKN
  have hfill : fillFraction (ι:=ι) K<1 := by
    unfold fillFraction
    exact (div_lt_one (by linarith)).mpr (by linarith)
  have hmin : 0 < min (vmin-U) (eta*L) := lt_min (sub_pos.mpr hUv) (mul_pos heta hL)
  exact lt_of_lt_of_le (by positivity)
    (sourceOwnerJump_lower_one_tie (xi:=xi) b r K i j hij hbid hN hK hKN heta hL hbL hbU hUv hvv)

theorem eventually_sourceOwnerPayoff_gain [Nonempty ι] {xi eta v L U vmin : ℝ}
    (b : ι→ℝ) (r K1 K2 : ℕ) (i j : ι) (hij : i≠j) (hbid : b i=b j)
    (hN : 2≤Fintype.card ι) (hK0 : 0<K1+K2) (hKN : K1+K2<Fintype.card ι)
    (hb : ∀t,0<b t) (heta : 0<eta) (hL : 0<L) (hbL : L≤b i) (hbU : b i≤U)
    (hUv : U<vmin) (hvv : vmin≤v) :
    ∀ᶠx in 𝓝[>] b i,
      sourceOwnerPayoff xi eta v b r K1 K2 i+sourceOwnerJump xi eta v b r (K1+K2) i/2<
        sourceOwnerPayoff xi eta v (Function.update b i x) r K1 K2 i := by
  have hpos := sourceOwnerJump_pos_of_tie (xi:=xi) b r (K1+K2) i j hij hbid hN (by omega) hKN
    heta hL hbL hbU hUv hvv
  have hh := tendsto_sourceOwnerPayoff_right xi eta v b r K1 K2 i hN hK0 hKN hb
  change Tendsto _ _ (𝓝 (sourceOwnerPayoff xi eta v b r K1 K2 i+
    sourceOwnerJump xi eta v b r (K1+K2) i)) at hh
  exact hh.eventually (Ioi_mem_nhds (by linarith))

end FCAppendix.Affine.Hybrid
