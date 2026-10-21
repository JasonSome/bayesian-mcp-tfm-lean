import FCAppendix.Affine.Hybrid.GuardedPayoff
import FCAppendix.Affine.Hybrid.FavoredCrossing
import FCAppendix.Affine.Hybrid.FavoredPayoffContinuity
import FCAppendix.Affine.Hybrid.SingletonPayoff

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open Classical
open scoped BigOperators

section FiniteEquivalences
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def finiteSetEquiv (e : α ≃ β) : Finset α ≃ Finset β where
  toFun S := S.map e.toEmbedding
  invFun T := T.map e.symm.toEmbedding
  left_inv S := by ext a; simp
  right_inv T := by ext b; simp

lemma finiteLaw_map_injective_mass {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (P : FiniteLaw Ω) (f : Ω → Ξ) (hf : Function.Injective f) (x : Ω) :
    (P.map f).mass (f x) = P.mass x := by
  classical
  simp only [FiniteLaw.map, hf.eq_iff]
  simp

def extendSubsetEquiv (S : Finset α) (T : Finset β)
    (e : S ≃ T) (e' : (Finset.univ \ S : Finset α) ≃ (Finset.univ \ T : Finset β)) :
    α ≃ β where
  toFun a := if ha : a ∈ S then (e ⟨a, ha⟩ : β)
    else (e' ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩⟩ : β)
  invFun b := if hb : b ∈ T then (e.symm ⟨b, hb⟩ : α)
    else (e'.symm ⟨b, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hb⟩⟩ : α)
  left_inv a := by
    by_cases ha : a ∈ S
    · have hb : (e ⟨a, ha⟩ : β) ∈ T := (e ⟨a, ha⟩).property
      simp only [dif_pos ha, dif_pos hb]
      exact congrArg Subtype.val (e.symm_apply_apply ⟨a, ha⟩)
    · let x : (Finset.univ \ S : Finset α) :=
        ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩⟩
      have hb : (e' x : β) ∉ T := (Finset.mem_sdiff.mp (e' x).property).2
      simp only [dif_neg ha]
      change (if h : (e' x : β) ∈ T then (e.symm ⟨e' x,h⟩ : α)
        else (e'.symm ⟨e' x,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,h⟩⟩ : α)) = a
      rw [dif_neg hb]
      exact congrArg Subtype.val (e'.symm_apply_apply x)
  right_inv b := by
    by_cases hb : b ∈ T
    · have ha : (e.symm ⟨b, hb⟩ : α) ∈ S := (e.symm ⟨b, hb⟩).property
      simp only [dif_pos hb, dif_pos ha]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨b, hb⟩)
    · let x : (Finset.univ \ T : Finset β) :=
        ⟨b, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hb⟩⟩
      have ha : (e'.symm x : α) ∉ S := (Finset.mem_sdiff.mp (e'.symm x).property).2
      simp only [dif_neg hb]
      change (if h : (e'.symm x : α) ∈ S then (e ⟨e'.symm x,h⟩ : β)
        else (e' ⟨e'.symm x,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,h⟩⟩ : β)) = b
      rw [dif_neg ha]
      exact congrArg Subtype.val (e'.apply_symm_apply x)

lemma extendSubsetEquiv_mem (S : Finset α) (T : Finset β)
    (e : S ≃ T) (e' : (Finset.univ \ S : Finset α) ≃ (Finset.univ \ T : Finset β))
    (a : α) (ha : a ∈ S) : extendSubsetEquiv S T e e' a = (e ⟨a, ha⟩ : β) := by
  change (if h : a ∈ S then (e ⟨a,h⟩ : β) else _) = _
  rw [dif_pos ha]

lemma extendSubsetEquiv_map (S : Finset α) (T : Finset β)
    (e : S ≃ T) (e' : (Finset.univ \ S : Finset α) ≃ (Finset.univ \ T : Finset β)) :
    S.map (extendSubsetEquiv S T e e').toEmbedding = T := by
  ext b
  constructor
  · intro hb
    obtain ⟨a, ha, hab⟩ := Finset.mem_map.mp hb
    rw [← hab, Equiv.coe_toEmbedding, extendSubsetEquiv_mem S T e e' a ha]
    exact (e ⟨a, ha⟩).property
  · intro hb
    let a : S := e.symm ⟨b, hb⟩
    apply Finset.mem_map.mpr
    refine ⟨(a : α), a.property, ?_⟩
    change extendSubsetEquiv S T e e' a = b
    rw [extendSubsetEquiv_mem S T e e' a a.property]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨b, hb⟩)

lemma exists_perm_fix_map_set (S T : Finset α) (t : α)
    (hcard : S.card = T.card) (hS : t ∈ S) (hT : t ∈ T) :
    ∃ e : Equiv.Perm α, e t = t ∧ S.map e.toEmbedding = T := by
  let e0 : S ≃ T := Fintype.equivOfCardEq (by simpa using hcard)
  let e : S ≃ T := e0.trans (Equiv.swap (e0 ⟨t, hS⟩) ⟨t, hT⟩)
  let ec : (Finset.univ \ S : Finset α) ≃ (Finset.univ \ T : Finset α) :=
    Fintype.equivOfCardEq (by
      simp only [Fintype.card_coe, Finset.card_sdiff_of_subset (Finset.subset_univ _),
        Finset.card_univ, hcard])
  let p := extendSubsetEquiv S T e ec
  refine ⟨p, ?_, extendSubsetEquiv_map S T e ec⟩
  rw [show p t = (e ⟨t, hS⟩ : α) from extendSubsetEquiv_mem S T e ec t hS]
  simp [e]

end FiniteEquivalences

section Uniformity
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

lemma finiteLaw_unique_uniform_support (P Q : FiniteLaw Ω) (S : Finset Ω)
    (hP : ∀ x, P.mass x ≠ 0 → x ∈ S) (hQ : ∀ x, Q.mass x ≠ 0 → x ∈ S)
    (hPu : ∀ x ∈ S, ∀ y ∈ S, P.mass x = P.mass y)
    (hQu : ∀ x ∈ S, ∀ y ∈ S, Q.mass x = Q.mass y) : P = Q := by
  have hex : ∃ x, P.mass x ≠ 0 := by
    by_contra hn
    have hz : ∀ x, P.mass x = 0 := fun x => by
      by_contra hx
      exact hn ⟨x, hx⟩
    have ht := P.total
    simp only [hz, Finset.sum_const_zero] at ht
    norm_num at ht
  obtain ⟨x0, hx0⟩ := hex
  have hxS := hP x0 hx0
  let p0 := P.mass x0
  let q0 := Q.mass x0
  have hp (x : Ω) : P.mass x = if x ∈ S then p0 else 0 := by
    by_cases hx : x ∈ S
    · rw [if_pos hx]
      exact hPu x hx x0 hxS
    · rw [if_neg hx]
      by_contra hn
      exact hx (hP x hn)
  have hq (x : Ω) : Q.mass x = if x ∈ S then q0 else 0 := by
    by_cases hx : x ∈ S
    · rw [if_pos hx]
      exact hQu x hx x0 hxS
    · rw [if_neg hx]
      by_contra hn
      exact hx (hQ x hn)
  have hpt : (S.card : ℝ) * p0 = 1 := by
    calc
      _ = ∑ x : Ω, if x ∈ S then p0 else 0 := by simp
      _ = ∑ x : Ω, P.mass x := Finset.sum_congr rfl (fun x _ => (hp x).symm)
      _ = 1 := P.total
  have hqt : (S.card : ℝ) * q0 = 1 := by
    calc
      _ = ∑ x : Ω, if x ∈ S then q0 else 0 := by simp
      _ = ∑ x : Ω, Q.mass x := Finset.sum_congr rfl (fun x _ => (hq x).symm)
      _ = 1 := Q.total
  have hcard : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨x0, hxS⟩
  have hpq : p0 = q0 := (mul_left_cancel₀ hcard.ne') (hpt.trans hqt.symm)
  apply FiniteLaw.ext
  intro x
  rw [hp, hq, hpq]

end Uniformity

section FillTransport
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

lemma conditionalFill_mass_eq_same_card (K : ℕ) (t : α) (S T : Finset α)
    (hcard : S.card = T.card) (hS : t ∈ S) (hT : t ∈ T) :
    (conditionalFill K t).mass S = (conditionalFill K t).mass T := by
  obtain ⟨e, ht, he⟩ := exists_perm_fix_map_set S T t hcard hS hT
  have hl := conditionalFill_relabel K t e
  rw [ht] at hl
  have hinj : Function.Injective (fun A : Finset α => A.map e.toEmbedding) :=
    (finiteSetEquiv e).injective
  calc
    _ = ((conditionalFill K t).map (fun A => A.map e.toEmbedding)).mass
        (S.map e.toEmbedding) :=
      (finiteLaw_map_injective_mass (conditionalFill K t) _ hinj S).symm
    _ = _ := by rw [← hl, he]

theorem conditionalFill_equiv (e : α ≃ β) {K : ℕ}
    (hN : 2 ≤ Fintype.card α) (hK : 1 ≤ K) (hKN : K ≤ Fintype.card α) (t : α) :
    conditionalFill K (e t) =
      (conditionalFill K t).map (fun S => S.map e.toEmbedding) := by
  let ef := finiteSetEquiv e
  have hef (A : Finset α) : ef A = A.map e.toEmbedding := rfl
  let P := conditionalFill K t
  let Q := (conditionalFill K (e t)).map ef.symm
  let S : Finset (Finset α) := Finset.univ.filter (fun A => A.card = K ∧ t ∈ A)
  have hN' : 2 ≤ Fintype.card β := by simpa only [Fintype.card_congr e] using hN
  have hKN' : K ≤ Fintype.card β := by simpa only [Fintype.card_congr e] using hKN
  have hQmass (A : Finset α) : Q.mass A = (conditionalFill K (e t)).mass (ef A) := by
    have hh := finiteLaw_map_injective_mass (conditionalFill K (e t)) ef.symm
      ef.symm.injective (ef A)
    simpa only [ef.symm_apply_apply] using hh
  have hPS (A : Finset α) (hA : P.mass A ≠ 0) : A ∈ S := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (conditionalFill_implements hN hK hKN t).1 A hA,
      conditionalFill_target_mem hN hK hKN t A hA⟩
  have hQS (A : Finset α) (hA : Q.mass A ≠ 0) : A ∈ S := by
    rw [hQmass] at hA
    have hc := (conditionalFill_implements hN' hK hKN' (e t)).1 (ef A) hA
    have ht := conditionalFill_target_mem hN' hK hKN' (e t) (ef A) hA
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · simpa only [hef, Finset.card_map] using hc
    · simpa only [hef, Finset.mem_map_equiv, Equiv.symm_apply_apply] using ht
  have hPu (A : Finset α) (hA : A ∈ S) (B : Finset α) (hB : B ∈ S) : P.mass A = P.mass B := by
    have ha := (Finset.mem_filter.mp hA).2
    have hb := (Finset.mem_filter.mp hB).2
    exact conditionalFill_mass_eq_same_card K t A B (ha.1.trans hb.1.symm) ha.2 hb.2
  have hQu (A : Finset α) (hA : A ∈ S) (B : Finset α) (hB : B ∈ S) : Q.mass A = Q.mass B := by
    have ha := (Finset.mem_filter.mp hA).2
    have hb := (Finset.mem_filter.mp hB).2
    rw [hQmass, hQmass]
    apply conditionalFill_mass_eq_same_card K (e t) (ef A) (ef B)
    · simpa only [hef, Finset.card_map] using ha.1.trans hb.1.symm
    · simpa only [hef, Finset.mem_map_equiv, Equiv.symm_apply_apply] using ha.2
    · simpa only [hef, Finset.mem_map_equiv, Equiv.symm_apply_apply] using hb.2
  have heq : P = Q := finiteLaw_unique_uniform_support P Q S hPS hQS hPu hQu
  apply FiniteLaw.ext_expect
  intro f
  change (conditionalFill K (e t)).expect f = (P.map ef).expect f
  rw [FiniteLaw.expect_map, heq]
  change (conditionalFill K (e t)).expect f =
    ((conditionalFill K (e t)).map ef.symm).expect (fun A => f (ef A))
  rw [FiniteLaw.expect_map]
  exact (conditionalFill K (e t)).expect_congr (fun A => by rw [ef.apply_symm_apply])

end FillTransport

section OwnerPayoffTransport
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [Nonempty α] [Nonempty β]

omit [Nonempty α] [Nonempty β] [DecidableEq α] [DecidableEq β] in
lemma averageRank_equiv (e : α ≃ β) (b : α → ℝ) (i : α) :
    averageRank (b ∘ e.symm) (e i) = averageRank b i := by
  unfold averageRank
  congr 1
  calc
    (∑ j, rankScore (b ∘ e.symm) (e i) j) =
        ∑ j, rankScore b i (e.symm j) := by
      apply Finset.sum_congr rfl
      intro j _
      simp [rankScore]
    _ = _ := Equiv.sum_comp e.symm _

omit [DecidableEq α] [DecidableEq β] in
lemma rankLaw_equiv (e : α ≃ β) (b : α → ℝ) :
    rankLaw (b ∘ e.symm) = (rankLaw b).map e := by
  apply FiniteLaw.ext_expect
  intro f
  rw [FiniteLaw.expect_map]
  unfold FiniteLaw.expect
  calc
    _ = ∑ i, (rankLaw (b ∘ e.symm)).mass (e i)*f (e i) := (Equiv.sum_comp e _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      change averageRank (b ∘ e.symm) (e i)/rankDenominator β*f (e i) = _
      rw [averageRank_equiv]
      simp only [rankLaw, rankDenominator, Fintype.card_congr e]

omit [Nonempty α] [Nonempty β] [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] in
lemma finiteMultiplier_equiv (e : α ≃ β) (xi : ℝ) (b : α → ℝ)
    (D : Finset α) (r : ℕ) :
    finiteMultiplier xi (b ∘ e.symm) (D.map e.toEmbedding) r =
      finiteMultiplier xi b D r := by
  simp only [finiteMultiplier, Finset.card_map, Finset.sum_map,
    Equiv.coe_toEmbedding, Function.comp_apply, Equiv.symm_apply_apply]

omit [Nonempty α] [Nonempty β] in
lemma ownerSetPayoff_equiv (e : α ≃ β) (xi eta v : ℝ) (b : α → ℝ)
    (r : ℕ) (i : α) (E : Finset α) :
    ownerSetPayoff xi eta v (b ∘ e.symm) r (e i) (E.map e.toEmbedding) =
      ownerSetPayoff xi eta v b r i E := by
  have hD : Finset.univ \ E.map e.toEmbedding = (Finset.univ \ E).map e.toEmbedding := by
    ext j
    simp
  simp only [ownerSetPayoff, Finset.mem_map_equiv, Equiv.symm_apply_apply,
    Function.comp_apply]
  rw [hD, finiteMultiplier_equiv]

theorem sourceOwnerPayoff_equiv (e : α ≃ β) (xi eta v : ℝ) (b : α → ℝ)
    (r K0 K1 : ℕ) (i : α) (hN : 2 ≤ Fintype.card α)
    (hK : 0 < K0+K1) (hKN : K0+K1 ≤ Fintype.card α) :
    sourceOwnerPayoff xi eta v (b ∘ e.symm) r K0 K1 (e i) =
      sourceOwnerPayoff xi eta v b r K0 K1 i := by
  have hN' : 2 ≤ Fintype.card β := by simpa only [Fintype.card_congr e] using hN
  have hKN' : K0+K1 ≤ Fintype.card β := by simpa only [Fintype.card_congr e] using hKN
  rw [sourceOwnerPayoff_eq_rank xi eta v (b ∘ e.symm) r K0 K1 (e i) hN' hK hKN',
    sourceOwnerPayoff_eq_rank xi eta v b r K0 K1 i hN hK hKN,
    rankLaw_equiv, FiniteLaw.expect_map]
  apply FiniteLaw.expect_congr
  intro t
  unfold favoredTargetPayoff
  rw [conditionalFill_equiv e hN (by omega) hKN t, FiniteLaw.expect_map]
  apply FiniteLaw.expect_congr
  intro E
  exact ownerSetPayoff_equiv e xi eta v b r i E

omit [Nonempty α] [Nonempty β] in
lemma ownerSetSingletonPayoff_equiv (e : α ≃ β) (xi v : ℝ) (b : α → ℝ)
    (r : ℕ) (i : α) (E : Finset α) :
    ownerSetSingletonPayoff xi v (b ∘ e.symm) r (e i) (E.map e.toEmbedding) =
      ownerSetSingletonPayoff xi v b r i E := by
  have hD : Finset.univ \ E.map e.toEmbedding = (Finset.univ \ E).map e.toEmbedding := by
    ext j
    simp
  simp only [ownerSetSingletonPayoff, Finset.mem_map_equiv, Equiv.symm_apply_apply,
    Function.comp_apply]
  rw [hD, finiteMultiplier_equiv]

theorem sourceSingletonPayoff_equiv (e : α ≃ β) (xi v : ℝ) (b : α → ℝ)
    (r K0 K1 : ℕ) (i : α) (hN : 2 ≤ Fintype.card α)
    (hK : 0 < K0+K1) (hKN : K0+K1 ≤ Fintype.card α) :
    sourceSingletonPayoff xi v (b ∘ e.symm) r K0 K1 (e i) =
      sourceSingletonPayoff xi v b r K0 K1 i := by
  have hN' : 2 ≤ Fintype.card β := by simpa only [Fintype.card_congr e] using hN
  have hKN' : K0+K1 ≤ Fintype.card β := by simpa only [Fintype.card_congr e] using hKN
  rw [sourceSingletonPayoff_eq_favored xi v (b ∘ e.symm) r K0 K1 (e i) hN' hK hKN',
    sourceSingletonPayoff_eq_favored xi v b r K0 K1 i hN hK hKN]
  simp only [favoredSetLaw, FiniteLaw.expect_finiteMix]
  rw [rankLaw_equiv, FiniteLaw.expect_map]
  apply FiniteLaw.expect_congr
  intro t
  rw [conditionalFill_equiv e hN (by omega) hKN t, FiniteLaw.expect_map]
  apply FiniteLaw.expect_congr
  intro E
  exact ownerSetSingletonPayoff_equiv e xi v b r i E

end OwnerPayoffTransport
end FCAppendix.Affine.Hybrid.Native02
