import FCAppendix.Affine.Hybrid.FavoredUniformContinuity

noncomputable section
namespace FCAppendix.Affine.Hybrid
open Set Filter Topology
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem exists_sourceOwnerPayoff_finite_crossing {xi eta vlo vhi L U : ℝ}
    (hL : 0<L) (heta : 0<eta) (hUv : U<vlo) (r K1 K2 : ℕ) (i : ι)
    (hN : 2≤Fintype.card ι) (hK : 0<K1+K2) (hKN : K1+K2<Fintype.card ι)
    {e : ℝ} (he : 0<e) :
    let G:=(1-fillFraction (ι:=ι) (K1+K2))*(min (vlo-U) (eta*L)/2)
    ∃delta : ℝ,0<delta ∧ ∀x : FavoredBoxInput ι vlo vhi L U,∀y : Icc L U,
      (x.2 i:ℝ)<y→(y:ℝ)-(x.2 i:ℝ)<delta→
      (∑j:ι,if j≠i ∧ (x.2 j:ℝ)∈Icc (x.2 i:ℝ) (y:ℝ) then G/4 else 0)/rankDenominator ι-e ≤
        sourceOwnerPayoff xi eta x.1 (Function.update (fun j=>(x.2 j:ℝ)) i y) r K1 K2 i-
          sourceOwnerPayoff xi eta x.1 (fun j=>(x.2 j:ℝ)) r K1 K2 i := by
  dsimp only
  let G:=(1-fillFraction (ι:=ι) (K1+K2))*(min (vlo-U) (eta*L)/2)
  obtain ⟨da,hda,ha⟩:=exists_favored_near_tie_advantage (xi:=xi) (vhi:=vhi)
    hL heta hUv r (K1+K2) i hN (by omega) hKN
  obtain ⟨dm,hdm,hm⟩:=exists_favoredTargetPayoff_modulus (vlo:=vlo) (vhi:=vhi)
    hL xi eta r (K1+K2) i hN (by omega) hKN he
  refine ⟨min da dm,lt_min hda hdm,?_⟩
  intro x y hiy hstep
  let xp : FavoredBoxInput ι vlo vhi L U:=(x.1,Function.update x.2 i y)
  let b : ι→ℝ:=fun j=>(x.2 j:ℝ)
  let bp : ι→ℝ:=Function.update b i y
  let f : ι→ℝ:=fun t=>boxTargetPayoff xi eta r (K1+K2) i t x
  let fp : ι→ℝ:=fun t=>boxTargetPayoff xi eta r (K1+K2) i t xp
  have hbp : (fun j=>(xp.2 j:ℝ))=bp := by
    funext j
    by_cases hji : j=i <;> simp [xp,bp,b,hji]
  have hdist : dist x xp<dm := by
    have hp:=dist_update_box_le x.2 i y
    have hh : dist x xp=dist x.2 (Function.update x.2 i y) := by simp [xp,Prod.dist_eq]
    rw [hh]
    apply hp.trans_lt
    rw [Subtype.dist_eq,Real.dist_eq,abs_of_nonpos (by linarith : (x.2 i:ℝ)-(y:ℝ)≤0)]
    linarith [(lt_min_iff.mp hstep).2]
  have hvar : |(rankLaw bp).expect fp-(rankLaw bp).expect f|≤e := by
    apply abs_expect_sub_expect_le
    intro t
    have hh:=(hm x xp hdist t).le
    simpa only [f,fp,abs_sub_comm] using hh
  have hG : 0≤G := by
    have hn : (1:ℝ)<Fintype.card ι := by exact_mod_cast (show 1<Fintype.card ι by omega)
    have hk : (K1+K2:ℝ)<Fintype.card ι := by exact_mod_cast hKN
    have hf : fillFraction (ι:=ι) (K1+K2)<1 := by
      unfold fillFraction
      exact (div_lt_one (by linarith)).mpr (by push_cast;linarith)
    exact (mul_nonneg (sub_nonneg.mpr hf.le)
      (div_nonneg (le_min (sub_nonneg.mpr hUv.le) (mul_nonneg heta.le hL.le)) (by norm_num)))
  have hsum : (∑j:ι,if j≠i ∧ b j∈Icc (b i) (y:ℝ) then G/4 else 0)≤
      ∑j:ι,rankTransfer b i y j*(f i-f j) := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hc : j≠i ∧ b j∈Icc (b i) (y:ℝ)
    · rw [if_pos hc]
      have hclose : |(x.2 j:ℝ)-(x.2 i:ℝ)|<da := by
        rw [abs_of_nonneg (by exact sub_nonneg.mpr hc.2.1)]
        exact (sub_le_sub_right hc.2.2 _).trans_lt ((lt_min_iff.mp hstep).1)
      have hadv:=ha x j hc.1 hclose
      change G/2≤f i-f j at hadv
      have htr:=rankTransfer_half_le_between b i j y hc.1 hiy hc.2
      have hh:=mul_le_mul htr hadv (by positivity : (0:ℝ)≤G/2)
        (rankTransfer_nonneg b i j y hiy.le)
      nlinarith
    · rw [if_neg hc]
      by_cases hji : j=i
      · subst j;simp [rankTransfer_self]
      · have hout : b j∉Icc (b i) (y:ℝ) := by
          intro hh
          exact hc ⟨hji,hh⟩
        rw [rankTransfer_eq_zero_of_not_between b i j y hiy.le hout,zero_mul]
  have hrank:=rankLaw_update_expect b i (y:ℝ) f
  change (rankLaw bp).expect f-(rankLaw b).expect f=_ at hrank
  have hlower:=div_le_div_of_nonneg_right hsum (rankDenominator_pos (ι:=ι)).le
  rw [←hrank] at hlower
  have hnew : sourceOwnerPayoff xi eta x.1 bp r K1 K2 i=(rankLaw bp).expect fp := by
    rw [sourceOwnerPayoff_eq_rank xi eta x.1 bp r K1 K2 i hN hK hKN.le]
    apply FiniteLaw.expect_congr
    intro t
    simp only [fp,boxTargetPayoff,xp,hbp]
  have hold : sourceOwnerPayoff xi eta x.1 b r K1 K2 i=(rankLaw b).expect f := by
    rw [sourceOwnerPayoff_eq_rank xi eta x.1 b r K1 K2 i hN hK hKN.le]
    rfl
  change _ ≤ sourceOwnerPayoff xi eta x.1 bp r K1 K2 i-sourceOwnerPayoff xi eta x.1 b r K1 K2 i
  rw [hnew,hold]
  change (∑j:ι,if j≠i ∧ b j∈Icc (b i) (y:ℝ) then G/4 else 0)/rankDenominator ι-e≤_
  linarith [(abs_le.mp hvar).1]

end FCAppendix.Affine.Hybrid
