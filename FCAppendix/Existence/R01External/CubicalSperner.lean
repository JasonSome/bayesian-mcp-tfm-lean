/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
Modified for publication: explanatory comments removed;
namespace and Lean/Mathlib compatibility adapted where needed.
-/
module

public import FCAppendix.Existence.R01External.FreudenthalTriangulation
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.ZMod.Basic

@[expose] public section

open KuhnSimplex

abbrev ValidSimplex (n p : ℕ) := { S : KuhnSimplex n p // S.isValid }

noncomputable instance instFintypeValidSimplex (n p : ℕ) :
    Fintype (ValidSimplex n p) :=
  Fintype.subtype (Finset.univ.filter KuhnSimplex.isValid) (by simp)

section RainbowFaces

variable {n p : ℕ} (SC : SpernerColoring n p)

def isRainbowBoundaryFace (Sk : ValidSimplex n p × Fin (n + 1)) : Prop :=
  Sk.1.val.isRainbowFace Sk.1.property SC.color Sk.2 ∧ Sk.1.val.faceAdj Sk.2 = none

def isRainbowInteriorFace (Sk : ValidSimplex n p × Fin (n + 1)) : Prop :=
  Sk.1.val.isRainbowFace Sk.1.property SC.color Sk.2 ∧ Sk.1.val.faceAdj Sk.2 ≠ none

open Classical in

noncomputable def rainbowFaceCount (S : ValidSimplex n p) : ℕ :=
  Finset.card (Finset.univ.filter (fun k : Fin (n + 1) =>
    decide (S.val.isRainbowFace S.property SC.color k) = true))

open Classical in

lemma rainbowFaceCount_odd_iff (S : ValidSimplex n p) :
    Odd (rainbowFaceCount SC S) ↔ S.val.fullyColored S.property SC.color := by
  unfold rainbowFaceCount
  constructor
  ·
    intro hodd
    by_contra hnfc
    have h := S.val.not_fullyColored_rainbow_zero_or_two S.property SC.color hnfc
    rcases h with h0 | ⟨k₁, k₂, hne, hk₁, hk₂, huniq⟩
    ·
      have : (Finset.univ.filter (fun k : Fin (n + 1) =>
          decide (S.val.isRainbowFace S.property SC.color k) = true)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro k _; simp [h0 k]
      rw [this] at hodd; exact (Nat.not_odd_zero) hodd
    ·
      have : (Finset.univ.filter (fun k : Fin (n + 1) =>
          decide (S.val.isRainbowFace S.property SC.color k) = true)).card = 2 := by
        rw [Finset.card_eq_two]
        exact ⟨k₁, k₂, hne, by
          ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_insert, Finset.mem_singleton, decide_eq_true_eq]
          exact ⟨fun hk => huniq k hk, fun h => h.elim (· ▸ hk₁) (· ▸ hk₂)⟩⟩
      rw [this] at hodd; exact (by decide : ¬ Odd 2) hodd
  ·
    intro hfc
    obtain ⟨k₀, hk₀, huniq⟩ := S.val.fullyColored_rainbow_count S.property SC.color hfc
    have : (Finset.univ.filter (fun k : Fin (n + 1) =>
        decide (S.val.isRainbowFace S.property SC.color k) = true)).card = 1 := by
      rw [Finset.card_eq_one]
      exact ⟨k₀, by
        ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton, decide_eq_true_eq]
        exact ⟨fun hk => huniq k hk, fun h => h ▸ hk₀⟩⟩
    rw [this]; exact odd_one

end RainbowFaces

section Induction

def childEmbed (n p : ℕ) (v : Fin n → Fin (p + 1)) : Fin (n + 1) → Fin (p + 1) :=
  fun i => if h : i.val < n then v ⟨i.val, h⟩ else Fin.last p

noncomputable def childColoring {n p : ℕ}
    (SC : SpernerColoring (n + 1) p) : SpernerColoring n p where
  color v :=
    let c := SC.color (childEmbed n p v)
    ⟨c.val, by
      have h_last : (childEmbed n p v) ⟨n, by omega⟩ = Fin.last p := by
        simp [childEmbed]
      have h_le := (SC.proper (childEmbed n p v) ⟨n, by omega⟩).2 h_last
      omega⟩
  proper v k := by
    constructor
    · intro hv0 heq
      have hcv : (SC.color (childEmbed n p v)).val = k.val := by
        have := congr_arg Fin.val heq; simpa using this
      have h_embed : (childEmbed n p v) k.castSucc = 0 := by
        simp [childEmbed, hv0]
      have h_ne := (SC.proper (childEmbed n p v) k.castSucc).1 h_embed
      apply h_ne; ext; simp only [Fin.castSucc]; exact hcv
    · intro hvp
      have h_embed : (childEmbed n p v) k.castSucc = Fin.last p := by
        simp [childEmbed, hvp]
      exact (SC.proper (childEmbed n p v) k.castSucc).2 h_embed

end Induction

private lemma odd_card_odd_iff_odd_sum {α : Type*} [Fintype α]
    (f : α → ℕ) :
    Odd (Finset.univ.filter (fun a => Odd (f a))).card ↔ Odd (∑ a : α, f a) := by
  rw [← ZMod.natCast_eq_one_iff_odd, ← ZMod.natCast_eq_one_iff_odd, Nat.cast_sum]
  suffices h : ∀ x : α, (f x : ZMod 2) = if Odd (f x) then 1 else 0 by
    simp_rw [h, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul, mul_one]
  intro x
  rcases Nat.even_or_odd (f x) with he | ho
  · rw [if_neg (by rwa [Nat.not_odd_iff_even]), ZMod.natCast_eq_zero_iff_even.mpr he]
  · rw [if_pos ho, ZMod.natCast_eq_one_iff_odd.mpr ho]

open Classical in

private noncomputable def allRainbowPairs (n p : ℕ) (SC : SpernerColoring n p) :
    Finset (ValidSimplex n p × Fin (n + 1)) :=
  Finset.univ.filter (fun Sk : ValidSimplex n p × Fin (n + 1) =>
    decide (Sk.1.val.isRainbowFace Sk.1.property SC.color Sk.2) = true)

open Classical in

private lemma sum_rainbowFaceCount_eq_card (n p : ℕ) (SC : SpernerColoring n p) :
    ∑ S : ValidSimplex n p, rainbowFaceCount SC S =
    (allRainbowPairs n p SC).card := by

  unfold allRainbowPairs rainbowFaceCount
  set P := fun (Sk : ValidSimplex n p × Fin (n + 1)) =>
    decide (Sk.1.val.isRainbowFace Sk.1.property SC.color Sk.2) = true

  have hsummand : ∀ S : ValidSimplex n p,
    (Finset.univ.filter (fun k => decide (S.val.isRainbowFace S.property SC.color k) = true)).card =
    ((Finset.univ.filter P).filter (fun Sk => Sk.1 = S)).card := by
      intro S
      apply Finset.card_nbij' (fun k => (S, k)) (fun Sk => Sk.2)
      ·
        intro k hk
        rw [Finset.mem_coe] at hk
        have hk' := (Finset.mem_filter.mp hk).2
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk'⟩, rfl⟩
      ·
        intro ⟨S', k⟩ hSk
        have hSk' := Finset.mem_filter.mp hSk
        have hSk1 := (Finset.mem_filter.mp hSk'.1).2
        have hSk2 : S' = S := hSk'.2
        subst hSk2
        rw [Finset.mem_coe]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSk1⟩
      ·
        intro k _; rfl
      ·
        intro ⟨S', k⟩ hSk
        have hSk' := Finset.mem_filter.mp hSk
        have hSk2 : S' = S := hSk'.2
        subst hSk2; rfl
  simp_rw [hsummand]

  have key := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ.filter P) Finset.univ
    (fun Sk : ValidSimplex n p × Fin (n + 1) => Sk.1)
  simp only [Finset.mem_univ, Finset.filter_true_of_mem (fun _ _ => trivial)] at key
  exact key

private noncomputable def boundaryRainbowPairs (n p : ℕ) (SC : SpernerColoring n p) :
    Finset (ValidSimplex n p × Fin (n + 1)) :=
  (allRainbowPairs n p SC).filter (fun Sk => Sk.1.val.faceAdj Sk.2 = none)

private noncomputable def interiorRainbowPairs (n p : ℕ) (SC : SpernerColoring n p) :
    Finset (ValidSimplex n p × Fin (n + 1)) :=
  (allRainbowPairs n p SC).filter (fun Sk => Sk.1.val.faceAdj Sk.2 ≠ none)

private lemma even_card_of_fpf_invol {α : Type*}
    {s : Finset α} (f : α → α) (hf_mem : ∀ a ∈ s, f a ∈ s)
    (hf_inv : ∀ a ∈ s, f (f a) = a) (hf_ne : ∀ a ∈ s, f a ≠ a) :
    Even s.card := by
  have h : ∑ a ∈ s, (1 : ZMod 2) = 0 :=
    Finset.sum_involution (fun a _ => f a)
      (fun a _ => show (1 : ZMod 2) + 1 = 0 by decide)
      (fun a ha _ => hf_ne a ha)
      (fun a ha => hf_mem a ha)
      (fun a ha => hf_inv a ha)
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rwa [← ZMod.natCast_eq_zero_iff_even]

open Classical in
private lemma interior_rainbow_even (n p : ℕ) (SC : SpernerColoring n p) :
    Even (interiorRainbowPairs n p SC).card := by

  let invol : ValidSimplex n p × Fin (n + 1) → ValidSimplex n p × Fin (n + 1) :=
    fun ⟨⟨S, hv⟩, k⟩ =>
      match h : S.faceAdj k with
      | none => (⟨S, hv⟩, k)
      | some S' =>
        have hv' : S'.isValid := S.faceAdj_preserves_valid hv k h
        let k' := (S.faceAdj_shared_vertices hv k h hv').choose
        (⟨S', hv'⟩, k')

  have invol_some : ∀ (S : KuhnSimplex n p) (hv : S.isValid) (k : Fin (n + 1))
      (S' : KuhnSimplex n p) (hS' : S.faceAdj k = some S'),
      ∃ k', invol (⟨S, hv⟩, k) = (⟨S', S.faceAdj_preserves_valid hv k hS'⟩, k') ∧
        S'.faceAdj k' = some S ∧
        ∀ i : Fin (n + 1), i ≠ k →
          ∃ j : Fin (n + 1), j ≠ k' ∧
            S.vertex hv i = S'.vertex (S.faceAdj_preserves_valid hv k hS') j := by
    intro S hv k S' hS'
    simp only [invol]
    split
    next heq =>

      exact absurd (hS' ▸ heq) (Option.some_ne_none _)
    next S'' heq =>

      have hS''_eq : S'' = S' := Option.some_inj.mp (heq ▸ hS')
      subst hS''_eq
      set hv' := S.faceAdj_preserves_valid hv k heq
      set spec := S.faceAdj_shared_vertices hv k heq hv'
      exact ⟨spec.choose, by congr 1, spec.choose_spec⟩
  apply even_card_of_fpf_invol invol
  ·
    intro ⟨⟨S, hv⟩, k⟩ hmem
    simp only [interiorRainbowPairs, allRainbowPairs, Finset.mem_filter, Finset.mem_univ,
      true_and, ne_eq] at hmem
    obtain ⟨hrainbow, hinterior⟩ := hmem
    obtain ⟨S', hS'⟩ := Option.ne_none_iff_exists'.mp hinterior
    obtain ⟨k', hinvol_eq, hk'_adj, hk'_verts⟩ := invol_some S hv k S' hS'
    rw [hinvol_eq]
    simp only [interiorRainbowPairs, allRainbowPairs, Finset.mem_filter, Finset.mem_univ,
      true_and, ne_eq]
    constructor
    ·
      rw [decide_eq_true_eq]
      intro color
      have hrainbow' := decide_eq_true_eq.mp hrainbow
      obtain ⟨i, hi_ne, hi_color⟩ := hrainbow' color
      obtain ⟨j, hj_ne, hj_eq⟩ := hk'_verts i hi_ne
      exact ⟨j, hj_ne, by rw [← hj_eq]; exact hi_color⟩
    ·
      rw [hk'_adj]; exact Option.some_ne_none S
  ·
    intro ⟨⟨S, hv⟩, k⟩ hmem
    simp only [interiorRainbowPairs, allRainbowPairs, Finset.mem_filter, Finset.mem_univ,
      true_and, ne_eq] at hmem
    obtain ⟨_, hinterior⟩ := hmem
    obtain ⟨S', hS'⟩ := Option.ne_none_iff_exists'.mp hinterior
    obtain ⟨k', hinvol_eq, hk'_adj, hk'_verts⟩ := invol_some S hv k S' hS'

    rw [hinvol_eq]

    set hv' := S.faceAdj_preserves_valid hv k hS'
    obtain ⟨k'', hinvol_eq', hk''_adj, _⟩ := invol_some S' hv' k' S hk'_adj
    rw [hinvol_eq']

    congr 1
    exact S.faceAdj_injective k'' k hk''_adj hS'
  ·
    intro ⟨⟨S, hv⟩, k⟩ hmem
    simp only [interiorRainbowPairs, allRainbowPairs, Finset.mem_filter, Finset.mem_univ,
      true_and, ne_eq] at hmem
    obtain ⟨_, hinterior⟩ := hmem
    obtain ⟨S', hS'⟩ := Option.ne_none_iff_exists'.mp hinterior
    obtain ⟨k', hinvol_eq, _, _⟩ := invol_some S hv k S' hS'

    have hne : S' ≠ S := S.faceAdj_ne k hS'
    rw [hinvol_eq]
    intro heq
    exact hne (congr_arg Subtype.val (Prod.mk.inj heq).1)

private lemma total_parity_eq_boundary (n p : ℕ) (SC : SpernerColoring n p) :
    Odd (allRainbowPairs n p SC).card ↔
    Odd (boundaryRainbowPairs n p SC).card := by

  have hdisj : Disjoint (boundaryRainbowPairs n p SC) (interiorRainbowPairs n p SC) :=
    Finset.disjoint_filter.mpr fun _ _ h => not_not.mpr h
  have hunion : allRainbowPairs n p SC =
      boundaryRainbowPairs n p SC ∪ interiorRainbowPairs n p SC := by
    unfold boundaryRainbowPairs interiorRainbowPairs
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro h; exact (_root_.em _).elim (fun hb => Or.inl ⟨h, hb⟩) (fun hb => Or.inr ⟨h, hb⟩)
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  rw [hunion, Finset.card_union_of_disjoint hdisj]
  obtain ⟨m, hm⟩ := interior_rainbow_even n p SC
  constructor
  · intro ⟨k, hk⟩; exact ⟨k - m, by omega⟩
  · intro ⟨k, hk⟩; exact ⟨k + m, by omega⟩

private lemma base_case_zero (p : ℕ) (SC : SpernerColoring 0 p) (_hp : 0 < p) :
    Odd (∑ S : ValidSimplex 0 p, rainbowFaceCount SC S) := by

  have hUniq : ∀ (S : KuhnSimplex 0 p), S = ⟨Fin.elim0, Equiv.refl _⟩ := by
    intro S; cases S; congr
    · exact funext (fun i => Fin.elim0 i)
    · exact Equiv.ext (fun i => Fin.elim0 i)

  have hValid : ∀ (S : KuhnSimplex 0 p), S.isValid := by
    intro S j; exact Fin.elim0 j

  have hCard : Fintype.card (ValidSimplex 0 p) = 1 := by
    rw [← Finset.card_univ, Finset.card_eq_one]
    use ⟨⟨Fin.elim0, Equiv.refl _⟩, hValid _⟩
    ext ⟨S, hv⟩
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Subtype.ext (hUniq S)

  have hCount : ∀ (S : ValidSimplex 0 p), rainbowFaceCount SC S = 1 := by
    intro ⟨S, hv⟩
    unfold rainbowFaceCount
    rw [Finset.card_eq_one]
    use ⟨0, by omega⟩
    ext ⟨k, hk⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      decide_eq_true_eq]
    constructor
    · intro _; ext; omega
    · intro heq
      have : k = 0 := by have := congr_arg Fin.val heq; simpa using this
      subst this; intro c; exact Fin.elim0 c
  simp only [hCount]
  rw [Finset.sum_const, Finset.card_univ, hCard, smul_eq_mul, mul_one]
  exact odd_one

private lemma boundary_rainbow_on_last_coord {n p : ℕ} (SC : SpernerColoring (n + 1) p)
    (S : ValidSimplex (n + 1) p) (k : Fin (n + 2))
    (hrainbow : S.val.isRainbowFace S.property SC.color k)
    (hboundary : S.val.faceAdj k = none) :

    k.val = 0 ∧ S.val.perm ⟨0, by omega⟩ = ⟨n, by omega⟩ ∧
    ∀ i : Fin (n + 2), i ≠ k → (S.val.vertex S.property i ⟨n, by omega⟩).val = p := by

  have hn : n + 1 ≠ 0 := by omega
  unfold KuhnSimplex.faceAdj at hboundary
  simp only [hn, ↓reduceDIte] at hboundary
  split_ifs at hboundary with hk0 hb hkn hb
  ·

    have hperm_n : S.val.perm ⟨0, by omega⟩ = ⟨n, by omega⟩ := by
      by_contra hperm_ne
      have hperm_lt : (S.val.perm ⟨0, by omega⟩).val < n := by
        have h1 := (S.val.perm ⟨0, by omega⟩).isLt
        have h2 : (S.val.perm ⟨0, by omega⟩).val ≠ n := fun h => hperm_ne (Fin.ext h)
        omega
      set j := S.val.perm ⟨0, by omega⟩
      obtain ⟨i, hi_ne, hi_color⟩ := hrainbow ⟨n, by omega⟩
      have hi_pos : 0 < i.val := Nat.pos_of_ne_zero (fun h => hi_ne (Fin.ext (by omega)))
      have hsymm : (S.val.perm.symm j).val = 0 := by rw [S.val.perm.symm_apply_apply]
      have hvert_last : S.val.vertex S.property i j = Fin.last p := by
        ext; simp only [KuhnSimplex.vertex, KuhnSimplex.vertexVal, Fin.val_last]
        rw [hsymm, if_pos hi_pos]; have := S.property j; omega
      have hle := (SC.proper (S.val.vertex S.property i) j).2 hvert_last
      have hcn : (SC.color (S.val.vertex S.property i)).val = n := by
        have := congr_arg Fin.val hi_color; simp only [Fin.castSucc] at this; exact this
      omega
    refine ⟨hk0, hperm_n, ?_⟩

    intro i hi
    have hi_pos : 0 < i.val := Nat.pos_of_ne_zero (fun h => hi (Fin.ext (by omega)))

    have hsymm : (S.val.perm.symm ⟨n, by omega⟩).val = 0 := by
      rw [show (⟨n, by omega⟩ : Fin (n + 1)) = S.val.perm ⟨0, by omega⟩ from hperm_n.symm]
      rw [S.val.perm.symm_apply_apply]
    change S.val.vertexVal i ⟨n, by omega⟩ = p
    unfold KuhnSimplex.vertexVal; rw [hsymm, if_pos hi_pos]
    have := S.property ⟨n, by omega⟩
    rw [show S.val.base ⟨n, by omega⟩ = S.val.base (S.val.perm ⟨0, by omega⟩) from by rw [hperm_n]]
    have := S.property (S.val.perm ⟨0, by omega⟩)
    omega
  ·
    exfalso

    have hb' : (S.val.base (S.val.perm ⟨n, by omega⟩)).val = 0 := hb
    set j := S.val.perm ⟨n, by omega⟩
    obtain ⟨i, hi_ne, hi_color⟩ := hrainbow j
    have hi_le : i.val ≤ n := by have := i.isLt; simp [Fin.ext_iff] at hi_ne; omega
    have hvert0 : S.val.vertex S.property i j = 0 := by
      ext; simp only [KuhnSimplex.vertex, KuhnSimplex.vertexVal, Fin.val_zero]
      have hsymm : (S.val.perm.symm j).val = n := by
        change (S.val.perm.symm (S.val.perm ⟨n, _⟩)).val = n; rw [S.val.perm.symm_apply_apply]
      rw [hsymm, if_neg (by omega : ¬(n < i.val))]; exact hb'
    exact (SC.proper (S.val.vertex S.property i) j).1 hvert0 hi_color

private lemma perm_symm_pos_of_lt {n : ℕ} {σ : Equiv.Perm (Fin (n + 1))}
    (hσ0 : σ ⟨0, by omega⟩ = ⟨n, by omega⟩) {j : Fin (n + 1)} (hj : j.val < n) :
    0 < (σ.symm j).val := by
  by_contra h
  have h0 : (σ.symm j).val = 0 := by omega
  have := σ.apply_symm_apply j
  rw [show σ.symm j = ⟨0, by omega⟩ from Fin.ext h0] at this
  have := congr_arg Fin.val this; simp at this
  have := congr_arg Fin.val hσ0; simp at this
  omega

private lemma perm_succ_lt {n : ℕ} {σ : Equiv.Perm (Fin (n + 1))}
    (hσ0 : σ ⟨0, by omega⟩ = ⟨n, by omega⟩) (j : Fin n) :
    (σ ⟨j.val + 1, by omega⟩).val < n := by
  have hlt := (σ ⟨j.val + 1, by omega⟩).isLt
  by_contra h
  have heq : (σ ⟨j.val + 1, by omega⟩).val = n := by omega
  have h0 := congr_arg Fin.val hσ0; simp only [Fin.zero_eta] at h0
  have := σ.injective (Fin.ext (heq.trans h0.symm))
  simp [Fin.ext_iff] at this

private def permProject {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (hσ0 : σ ⟨0, by omega⟩ = ⟨n, by omega⟩) : Equiv.Perm (Fin n) where
  toFun j := ⟨(σ ⟨j.val + 1, by omega⟩).val, perm_succ_lt hσ0 j⟩
  invFun j := ⟨(σ.symm ⟨j.val, by omega⟩).val - 1, by
    have := (σ.symm ⟨j.val, by omega⟩).isLt
    have := perm_symm_pos_of_lt hσ0 (show (⟨j.val, by omega⟩ : Fin (n + 1)).val < n from j.isLt)
    omega⟩
  left_inv j := by
    ext; simp only

    have : (⟨(σ ⟨j.val + 1, by omega⟩).val, by omega⟩ : Fin (n + 1)) =
        σ ⟨j.val + 1, by omega⟩ := rfl
    rw [this, σ.symm_apply_apply]; simp
  right_inv j := by
    ext; simp only
    have hpos := perm_symm_pos_of_lt hσ0
      (show (⟨j.val, by omega⟩ : Fin (n + 1)).val < n from j.isLt)

    have h1 : (⟨(σ.symm ⟨j.val, by omega⟩).val - 1 + 1, by omega⟩ : Fin (n + 1)) =
        σ.symm ⟨j.val, by omega⟩ := Fin.ext (by simp; omega)
    rw [h1]; simp [σ.apply_symm_apply]

private def permLift {n : ℕ} (σ' : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) where
  toFun j :=
    if hj : j.val = 0 then ⟨n, by omega⟩
    else ⟨(σ' ⟨j.val - 1, by omega⟩).val, by have := (σ' ⟨j.val - 1, by omega⟩).isLt; omega⟩
  invFun j :=
    if hj : j.val = n then ⟨0, by omega⟩
    else ⟨(σ'.symm ⟨j.val, by omega⟩).val + 1, by
      have := (σ'.symm ⟨j.val, by omega⟩).isLt; omega⟩
  left_inv j := by
    ext
    simp only []
    by_cases hj : j.val = 0
    · simp [hj]
    · have hne : (σ' ⟨j.val - 1, by omega⟩).val ≠ n := by
        have := (σ' ⟨j.val - 1, by omega⟩).isLt; omega
      simp [hj, hne, σ'.symm_apply_apply]; omega
  right_inv j := by
    ext
    simp only []
    by_cases hj : j.val = n
    · simp [hj]
    · have hne : (σ'.symm ⟨j.val, by omega⟩).val + 1 ≠ 0 := by omega
      simp [hj, show (σ'.symm ⟨j.val, by omega⟩).val + 1 - 1 =
        (σ'.symm ⟨j.val, by omega⟩).val from by omega, σ'.apply_symm_apply]

private lemma permLift_zero {n : ℕ} (σ' : Equiv.Perm (Fin n)) :
    (permLift σ') ⟨0, by omega⟩ = ⟨n, by omega⟩ := by
  simp [permLift]

private lemma permProject_permLift {n : ℕ} (σ' : Equiv.Perm (Fin n)) :
    permProject (permLift σ') (permLift_zero σ') = σ' := by
  ext ⟨j, hj⟩; simp [permProject, permLift]

private lemma permLift_permProject {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (hσ0 : σ ⟨0, by omega⟩ = ⟨n, by omega⟩) :
    permLift (permProject σ hσ0) = σ := by
  ext ⟨j, hj⟩
  simp only [permLift, permProject]
  by_cases hj0 : j = 0
  · simp only [hj0]; exact (congr_arg Fin.val hσ0).symm
  · simp [hj0, show j - 1 + 1 = j from by omega]

private lemma permProject_symm_val {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (hσ0 : σ ⟨0, by omega⟩ = ⟨n, by omega⟩) (j : Fin n) :
    ((permProject σ hσ0).symm j).val = (σ.symm ⟨j.val, by omega⟩).val - 1 := by

  rfl

private def projectSimplex {n p : ℕ} (S : KuhnSimplex (n + 1) p)
    (hperm0 : S.perm ⟨0, by omega⟩ = ⟨n, by omega⟩) : KuhnSimplex n p where
  base j := S.base ⟨j.val, by omega⟩
  perm := permProject S.perm hperm0

private def liftSimplex {n p : ℕ} (hp : 0 < p) (S' : KuhnSimplex n p) :
    KuhnSimplex (n + 1) p where
  base j := if h : j.val < n then S'.base ⟨j.val, h⟩ else ⟨p - 1, by omega⟩
  perm := permLift S'.perm

private lemma liftSimplex_perm_zero {n p : ℕ} (hp : 0 < p) (S' : KuhnSimplex n p) :
    (liftSimplex hp S').perm ⟨0, by omega⟩ = ⟨n, by omega⟩ :=
  permLift_zero S'.perm

private lemma projectSimplex_liftSimplex {n p : ℕ} (hp : 0 < p) (S' : KuhnSimplex n p) :
    projectSimplex (liftSimplex hp S') (liftSimplex_perm_zero hp S') = S' := by
  cases S' with | mk b σ =>
  simp only [projectSimplex, liftSimplex, KuhnSimplex.mk.injEq]
  refine ⟨?_, permProject_permLift σ⟩
  ext ⟨j, hj⟩; simp [show j < n from hj]

private lemma liftSimplex_projectSimplex {n p : ℕ} (hp : 0 < p) (S : KuhnSimplex (n + 1) p)
    (hperm0 : S.perm ⟨0, by omega⟩ = ⟨n, by omega⟩)
    (hbase_n : (S.base ⟨n, by omega⟩).val = p - 1) :
    liftSimplex hp (projectSimplex S hperm0) = S := by
  cases S with | mk b σ =>
  simp only [projectSimplex, liftSimplex, KuhnSimplex.mk.injEq]
  refine ⟨?_, permLift_permProject σ hperm0⟩
  ext ⟨j, hj⟩
  simp only
  by_cases hjn : j < n
  · simp [hjn]
  · have hjn' : j = n := by omega
    simp only [hjn', Nat.lt_irrefl, dite_false]
    exact hbase_n.symm

private lemma projectSimplex_valid {n p : ℕ} (S : KuhnSimplex (n + 1) p) (hv : S.isValid)
    (hperm0 : S.perm ⟨0, by omega⟩ = ⟨n, by omega⟩) :
    (projectSimplex S hperm0).isValid :=
  fun j => hv ⟨j.val, by omega⟩

private lemma liftSimplex_valid {n p : ℕ} (hp : 0 < p) (S' : KuhnSimplex n p) (hv : S'.isValid) :
    (liftSimplex hp S').isValid := by
  intro ⟨j, hj⟩
  simp only [liftSimplex]
  by_cases hjn : j < n
  · simp only [hjn]; exact hv ⟨j, hjn⟩
  · simp [show ¬(j < n) from hjn]; omega

private lemma projectSimplex_vertex_eq {n p : ℕ} (S : KuhnSimplex (n + 1) p) (hv : S.isValid)
    (hperm0 : S.perm ⟨0, by omega⟩ = ⟨n, by omega⟩)
    (i : Fin (n + 2)) (j : Fin n) :
    S.vertex hv i ⟨j.val, by omega⟩ =
    (projectSimplex S hperm0).vertex (projectSimplex_valid S hv hperm0)
      ⟨i.val - 1, by omega⟩ j := by
  simp only [KuhnSimplex.vertex, KuhnSimplex.vertexVal, projectSimplex]
  ext; simp only
  congr 1

  have hsymm := permProject_symm_val S.perm hperm0 j
  have hpos : 0 < (S.perm.symm ⟨j.val, by omega⟩).val :=
    perm_symm_pos_of_lt hperm0 j.isLt

  split_ifs with h1 h2
  · rfl
  · exfalso; exact h2 (by omega)
  · exfalso; exact h1 (by omega)
  · rfl

private lemma childEmbed_projectSimplex_vertex {n p : ℕ} (S : KuhnSimplex (n + 1) p)
    (hv : S.isValid) (hperm0 : S.perm ⟨0, by omega⟩ = ⟨n, by omega⟩)
    (i : Fin (n + 2))
    (hcoord_n : (S.vertex hv i ⟨n, by omega⟩).val = p) :
    childEmbed n p ((projectSimplex S hperm0).vertex (projectSimplex_valid S hv hperm0)
      ⟨i.val - 1, by omega⟩) = S.vertex hv i := by
  ext ⟨c, hc⟩
  simp only [childEmbed]
  by_cases hcn : c < n
  · simp only [hcn]
    have := projectSimplex_vertex_eq S hv hperm0 i ⟨c, hcn⟩
    simp only [vertex, Fin.mk.injEq, ↓reduceDIte] at this ⊢
    exact this.symm
  · have hcn' : c = n := by omega
    simp only [hcn', Nat.lt_irrefl, dite_false, Fin.val_last]
    exact hcoord_n.symm

private lemma boundary_base_n_eq {n p : ℕ} (S : KuhnSimplex (n + 1) p) (hv : S.isValid)
    (hperm0 : S.perm ⟨0, by omega⟩ = ⟨n, by omega⟩)
    (hboundary : S.faceAdj ⟨0, by omega⟩ = none) :
    (S.base ⟨n, by omega⟩).val = p - 1 := by

  unfold KuhnSimplex.faceAdj at hboundary
  simp only [show n + 1 ≠ 0 from by omega, dite_false] at hboundary
  split_ifs at hboundary with hk0 hb
  ·
    have hperm0_val : (S.perm ⟨0, by omega⟩) = ⟨n, by omega⟩ := hperm0
    rw [hperm0_val] at hb
    have hvalid := hv ⟨n, by omega⟩
    omega
  · simp at hk0

private lemma liftSimplex_vertex_childEmbed {n p : ℕ} (hp : 0 < p) (S' : KuhnSimplex n p)
    (hv' : S'.isValid) (k : Fin (n + 1)) :
    (liftSimplex hp S').vertex (liftSimplex_valid hp S' hv') ⟨k.val + 1, by
      have := k.isLt; omega⟩ =
    childEmbed n p (S'.vertex hv' k) := by

  ext ⟨c, hc⟩
  simp only [childEmbed]
  by_cases hcn : c < n
  ·
    simp only [hcn, dite_true]

    simp only [KuhnSimplex.vertex, KuhnSimplex.vertexVal, liftSimplex, Fin.val_mk, hcn, dite_true]

    have h_pl : ((permLift S'.perm).symm ⟨c, by omega⟩).val =
        (S'.perm.symm ⟨c, hcn⟩).val + 1 := by
      simp [permLift, show c ≠ n from by omega]
    congr 1; split_ifs with h1 h2
    · rfl
    · exfalso; exact h2 (by rw [h_pl] at h1; omega)
    · exfalso; exact h1 (by rw [h_pl]; omega)
    · rfl
  ·
    have hcn' : c = n := by omega
    simp only [hcn', Nat.lt_irrefl, dite_false, KuhnSimplex.vertex, KuhnSimplex.vertexVal,
      liftSimplex, Fin.val_last, Fin.val_mk]

    have h_symm : ((permLift S'.perm).symm ⟨n, by omega⟩).val = 0 := by
      have : (permLift S'.perm).symm ⟨n, by omega⟩ = ⟨0, by omega⟩ := by
        apply (permLift S'.perm).injective
        rw [(permLift S'.perm).apply_symm_apply, permLift_zero]
      simp [this]
    rw [h_symm]; simp [show (0 : ℕ) < k.val + 1 from by omega]; omega

open Classical in

private lemma lift_fullyColored_to_boundary {n p : ℕ} (SC : SpernerColoring (n + 1) p)
    (hp : 0 < p) (S' : KuhnSimplex n p) (hv' : S'.isValid)
    (hfc : S'.fullyColored hv' (childColoring SC).color) :
    decide ((liftSimplex hp S').isRainbowFace (liftSimplex_valid hp S' hv') SC.color
      ⟨0, by omega⟩) = true ∧
    (liftSimplex hp S').faceAdj ⟨0, by omega⟩ = none := by
  constructor
  ·
    rw [decide_eq_true_eq]
    intro color
    obtain ⟨k, hk⟩ := hfc ⟨color.val, by have := color.isLt; omega⟩

    have hklt := k.isLt
    refine ⟨⟨k.val + 1, by omega⟩, by intro h; exact absurd (congr_arg Fin.val h) (by simp), ?_⟩

    have hvert := liftSimplex_vertex_childEmbed hp S' hv' k
    rw [hvert]

    have hval : (SC.color (childEmbed n p (S'.vertex hv' k))).val = color.val := by
      have := congr_arg Fin.val hk
      simp only [childColoring] at this
      exact this
    exact Fin.ext (by simp only [Fin.castSucc]; exact hval)
  ·

    have hperm0 := liftSimplex_perm_zero hp S'
    unfold KuhnSimplex.faceAdj
    simp only [
      show n + 1 ≠ 0 from by omega,
      dite_false,
      dite_true]

    split_ifs with hb
    · rfl
    · exfalso; apply hb
      rw [show (liftSimplex hp S').perm ⟨0, by omega⟩ = ⟨n, by omega⟩ from hperm0]
      simp [liftSimplex]
      omega

private lemma project_boundary_to_fullyColored {n p : ℕ} (SC : SpernerColoring (n + 1) p)
    (S : KuhnSimplex (n + 1) p) (hv : S.isValid) (k : Fin (n + 2))
    (hperm0 : S.perm ⟨0, by omega⟩ = ⟨n, by omega⟩)
    (hrainbow : S.isRainbowFace hv SC.color k)
    (hboundary : S.faceAdj k = none)
    (hcoord_n : ∀ i : Fin (n + 2), i ≠ k → (S.vertex hv i ⟨n, by omega⟩).val = p) :
    (projectSimplex S hperm0).fullyColored (projectSimplex_valid S hv hperm0)
      (childColoring SC).color := by

  intro c

  obtain ⟨i, hi_ne, hi_color⟩ := hrainbow ⟨c.val, by have := c.isLt; omega⟩

  have hk0 : k.val = 0 := by
    have hdata := boundary_rainbow_on_last_coord SC ⟨S, hv⟩ k hrainbow hboundary
    exact hdata.1
  have hi_pos : 0 < i.val := Nat.pos_of_ne_zero (fun h => hi_ne (Fin.ext (by omega)))

  refine ⟨⟨i.val - 1, by have := i.isLt; omega⟩, ?_⟩

  have hci := hcoord_n i hi_ne
  have hembed := childEmbed_projectSimplex_vertex S hv hperm0 i hci

  simp only [childColoring]
  apply Fin.ext
  simp only
  rw [hembed]
  have := congr_arg Fin.val hi_color
  simp only [Fin.castSucc] at this
  exact this

open Classical in
private lemma boundary_odd_inductive {n p : ℕ} (SC : SpernerColoring (n + 1) p) (hp : 0 < p)
    (ih : ∀ (SC' : SpernerColoring n p), Odd (∑ S : ValidSimplex n p, rainbowFaceCount SC' S)) :
    Odd (boundaryRainbowPairs (n + 1) p SC).card := by

  have h_fc : Odd (Finset.univ.filter (fun S' : ValidSimplex n p =>
      decide (S'.val.fullyColored S'.property (childColoring SC).color) = true)).card := by

    have h1 : (Finset.univ.filter (fun S' : ValidSimplex n p =>
        decide (S'.val.fullyColored S'.property (childColoring SC).color) = true)).card =
      (Finset.univ.filter (fun S' : ValidSimplex n p =>
        Odd (rainbowFaceCount (childColoring SC) S'))).card := by
      congr 1; ext S'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
      exact (rainbowFaceCount_odd_iff (childColoring SC) S').symm
    rw [h1, odd_card_odd_iff_odd_sum]
    exact ih (childColoring SC)

  let fcSet := Finset.univ.filter (fun S' : ValidSimplex n p =>
      decide (S'.val.fullyColored S'.property (childColoring SC).color) = true)
  suffices h_eq : (boundaryRainbowPairs (n + 1) p SC).card = fcSet.card by
    rw [h_eq]; exact h_fc

  let liftMap : ValidSimplex n p → ValidSimplex (n + 1) p × Fin (n + 2) :=
    fun ⟨S', hv'⟩ => (⟨liftSimplex hp S', liftSimplex_valid hp S' hv'⟩, ⟨0, by omega⟩)
  let projMap : ValidSimplex (n + 1) p × Fin (n + 2) → ValidSimplex n p :=
    fun ⟨⟨S, hv⟩, _⟩ =>
      if h : S.perm ⟨0, by omega⟩ = ⟨n, by omega⟩ then
        ⟨projectSimplex S h, projectSimplex_valid S hv h⟩
      else ⟨⟨fun _ => 0, Equiv.refl _⟩, fun j => by simp; omega⟩
  symm
  apply Finset.card_nbij' liftMap projMap
  ·
    intro ⟨S', hv'⟩ hmem
    simp only [Finset.mem_coe] at hmem ⊢
    simp only [fcSet, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hmem
    simp only [liftMap, boundaryRainbowPairs, allRainbowPairs, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact lift_fullyColored_to_boundary SC hp S' hv' hmem
  ·
    intro ⟨⟨S, hv⟩, k⟩ hmem
    simp only [Finset.mem_coe] at hmem ⊢
    simp only [boundaryRainbowPairs, allRainbowPairs, Finset.mem_filter, Finset.mem_univ,
      true_and] at hmem
    obtain ⟨hrainbow, hboundary⟩ := hmem
    have hdata := boundary_rainbow_on_last_coord SC ⟨S, hv⟩ k
      (decide_eq_true_eq.mp hrainbow) hboundary
    obtain ⟨hk0, hperm0, hcoord_n⟩ := hdata
    simp only [projMap, dif_pos hperm0, fcSet, Finset.mem_filter, Finset.mem_univ, true_and,
      decide_eq_true_eq]
    exact project_boundary_to_fullyColored SC S hv k hperm0
      (decide_eq_true_eq.mp hrainbow) hboundary hcoord_n
  ·
    intro ⟨S', hv'⟩ hmem
    simp only [liftMap, projMap]
    have hperm0 := liftSimplex_perm_zero hp S'
    simp only [dif_pos hperm0]
    exact Subtype.ext (projectSimplex_liftSimplex hp S')
  ·
    intro ⟨⟨S, hv⟩, k⟩ hmem
    simp only [Finset.mem_coe] at hmem
    simp only [boundaryRainbowPairs, allRainbowPairs, Finset.mem_filter, Finset.mem_univ,
      true_and] at hmem
    obtain ⟨hrainbow, hboundary⟩ := hmem
    have hdata := boundary_rainbow_on_last_coord SC ⟨S, hv⟩ k
      (decide_eq_true_eq.mp hrainbow) hboundary
    obtain ⟨hk0, hperm0, hcoord_n⟩ := hdata
    simp only [projMap, dif_pos hperm0, liftMap]
    have hbase_n := boundary_base_n_eq S hv hperm0 (by
      rwa [show (⟨0, by omega⟩ : Fin (n + 2)) = k from (Fin.ext (by omega)).symm])
    exact Prod.ext (Subtype.ext (liftSimplex_projectSimplex hp S hperm0 hbase_n))
      (Fin.ext (by simp [hk0]))

private theorem rainbow_sum_odd :
    ∀ (n p : ℕ) (SC : SpernerColoring n p) (_ : 0 < p),
    Odd (∑ S : ValidSimplex n p, rainbowFaceCount SC S) := by
  intro n
  induction n with
  | zero => exact base_case_zero
  | succ n ih =>
    intro p SC hp
    rw [sum_rainbowFaceCount_eq_card]
    rw [(total_parity_eq_boundary (n + 1) p SC)]
    exact boundary_odd_inductive SC hp (fun SC' => ih p SC' hp)

open Classical in

theorem cubicalSperner (n p : ℕ) (SC : SpernerColoring n p) (hp : 0 < p) :
    Odd (Finset.card (Finset.univ.filter (fun S : ValidSimplex n p =>
      decide (S.val.fullyColored S.property SC.color) = true))) := by

  suffices h : Odd (Finset.card (Finset.univ.filter (fun S : ValidSimplex n p =>
      Odd (rainbowFaceCount SC S)))) by
    convert h using 2; ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
    exact (rainbowFaceCount_odd_iff SC S).symm

  rw [odd_card_odd_iff_odd_sum]
  exact rainbow_sum_odd n p SC hp

open Classical in

theorem weakerCubicalSperner (n p : ℕ) (SC : SpernerColoring n p) (hp : 0 < p) :
    ∃ S : KuhnSimplex n p, ∃ hv : S.isValid,
      S.fullyColored hv SC.color := by
  have h := cubicalSperner n p SC hp
  obtain ⟨k, hk⟩ := h
  have hpos : 0 < (Finset.univ.filter (fun S : ValidSimplex n p =>
      decide (S.val.fullyColored S.property SC.color) = true)).card := by omega
  rw [Finset.card_pos] at hpos
  obtain ⟨⟨S, hv⟩, hmem⟩ := hpos
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  exact ⟨S, hv, of_decide_eq_true hmem⟩

lemma vertex_close {n p : ℕ} (S : KuhnSimplex n p) (hv : S.isValid)
    (k₁ k₂ : Fin (n + 1)) (j : Fin n) :
    (S.vertex hv k₁ j).val ≤ (S.vertex hv k₂ j).val + 1 :=
  S.vertexVal_le_add_one k₁ k₂ j
