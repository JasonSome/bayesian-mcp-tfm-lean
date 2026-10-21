/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
Modified for publication: explanatory comments removed;
namespace and Lean/Mathlib compatibility adapted where needed.
-/
module

public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Logic.Equiv.Fin.Rotate

@[expose] public section

structure KuhnSimplex (n p : ℕ) where
  base : Fin n → Fin (p + 1)
  perm : Equiv.Perm (Fin n)
  deriving DecidableEq

namespace KuhnSimplex

variable {n p : ℕ}

noncomputable instance instFintypePerm : Fintype (Equiv.Perm (Fin n)) :=
  Fintype.ofFinite _

noncomputable instance instFintype : Fintype (KuhnSimplex n p) :=
  Fintype.ofInjective (fun S : KuhnSimplex n p => (S.base, S.perm))
    (fun S₁ S₂ h => by cases S₁; cases S₂; simpa using h)

def vertexVal (S : KuhnSimplex n p) (k : Fin (n + 1)) (j : Fin n) : ℕ :=
  (S.base j).val + if (S.perm.symm j).val < k.val then 1 else 0

def isValid (S : KuhnSimplex n p) : Prop :=
  ∀ j : Fin n, (S.base j).val + 1 ≤ p

instance : DecidablePred (@isValid n p) :=
  fun _ => Fintype.decidableForallFintype

def vertex (S : KuhnSimplex n p) (hv : S.isValid) (k : Fin (n + 1)) :
    Fin n → Fin (p + 1) :=
  fun j => ⟨S.vertexVal k j, by
    unfold vertexVal
    have hb := (S.base j).is_lt
    have hv := hv j
    split <;> omega⟩

@[simp] lemma vertex_zero (S : KuhnSimplex n p) (hv : S.isValid) (j : Fin n) :
    S.vertex hv 0 j = S.base j := by
  simp [vertex, vertexVal]

lemma vertex_last (S : KuhnSimplex n p) (hv : S.isValid) (j : Fin n) :
    (S.vertex hv (Fin.last n) j).val = (S.base j).val + 1 := by
  simp [vertex, vertexVal, (S.perm.symm j).is_lt]

lemma vertexVal_mono (S : KuhnSimplex n p) {k₁ k₂ : Fin (n + 1)}
    (h : k₁ ≤ k₂) (j : Fin n) :
    S.vertexVal k₁ j ≤ S.vertexVal k₂ j := by
  unfold vertexVal; split <;> split <;> omega

lemma vertexVal_le_add_one (S : KuhnSimplex n p) (k₁ k₂ : Fin (n + 1)) (j : Fin n) :
    S.vertexVal k₁ j ≤ S.vertexVal k₂ j + 1 := by
  unfold vertexVal; split <;> split <;> omega

lemma vertex_injective (S : KuhnSimplex n p) (hv : S.isValid) :
    Function.Injective (S.vertex hv) := by
  intro k₁ k₂ h
  by_contra hne
  have hval : k₁.val ≠ k₂.val := Fin.val_ne_of_ne hne
  obtain hlt | hlt := Nat.lt_or_gt_of_ne hval
  ·
    have hk1n : k₁.val < n := by omega
    let j₀ := S.perm ⟨k₁.val, hk1n⟩
    have hsymm : S.perm.symm j₀ = ⟨k₁.val, hk1n⟩ := S.perm.symm_apply_apply _
    have hv1 : S.vertexVal k₁ j₀ = (S.base j₀).val := by
      unfold vertexVal; simp [hsymm]
    have hv2 : S.vertexVal k₂ j₀ = (S.base j₀).val + 1 := by
      unfold vertexVal; simp [hsymm, hlt]
    have heq : S.vertex hv k₁ j₀ = S.vertex hv k₂ j₀ := congr_fun h j₀
    simp [vertex] at heq
    omega
  ·
    have hk2n : k₂.val < n := by omega
    let j₀ := S.perm ⟨k₂.val, hk2n⟩
    have hsymm : S.perm.symm j₀ = ⟨k₂.val, hk2n⟩ := S.perm.symm_apply_apply _
    have hv2 : S.vertexVal k₂ j₀ = (S.base j₀).val := by
      unfold vertexVal; simp [hsymm]
    have hv1 : S.vertexVal k₁ j₀ = (S.base j₀).val + 1 := by
      unfold vertexVal; simp [hsymm, hlt]
    have heq : S.vertex hv k₁ j₀ = S.vertex hv k₂ j₀ := congr_fun h j₀
    simp [vertex] at heq
    omega

def faceAdj (S : KuhnSimplex n p) (k : Fin (n + 1)) : Option (KuhnSimplex n p) :=
  if hn : n = 0 then none
  else
    have hn' : 0 < n := Nat.pos_of_ne_zero hn
    if hk0 : k.val = 0 then
      let j₀ := S.perm ⟨0, hn'⟩
      if hb : (S.base j₀).val + 1 ≥ p then none
      else some ⟨
        Function.update S.base j₀ ⟨(S.base j₀).val + 1, by
          have := (S.base j₀).is_lt; omega⟩,
        (finRotate n).trans S.perm
      ⟩
    else if hkn : k.val = n then
      let jlast := S.perm ⟨n - 1, by omega⟩
      if hb : (S.base jlast).val = 0 then none
      else some ⟨
        Function.update S.base jlast ⟨(S.base jlast).val - 1, by omega⟩,
        (finRotate n).symm.trans S.perm
      ⟩
    else
      some ⟨
        S.base,
        (Equiv.swap ⟨k.val - 1, by omega⟩ ⟨k.val, by omega⟩).trans S.perm
      ⟩

lemma faceAdj_interior_some (S : KuhnSimplex n p) (k : Fin (n + 1))
    (hk0 : k.val ≠ 0) (hkn : k.val ≠ n) (hn : n ≠ 0) :
    ∃ S', S.faceAdj k = some S' := by
  unfold faceAdj
  simp [hn, hk0, hkn]

private lemma finRotate_pred_eq (n : ℕ) (hn : 0 < n) (h : n - 1 < n) :
    (finRotate n) ⟨n - 1, h⟩ = ⟨0, hn⟩ := by
  cases n with
  | zero => omega
  | succ m =>
    have : (⟨m + 1 - 1, h⟩ : Fin (m + 1)) = Fin.last m := by ext; simp [Fin.last]
    rw [this, finRotate_last]; ext; rfl

private lemma finRotate_symm_zero_eq (n : ℕ) (hn : 0 < n) :
    (finRotate n).symm ⟨0, hn⟩ = ⟨n - 1, by omega⟩ := by
  rw [Equiv.symm_apply_eq]; exact (finRotate_pred_eq n hn (by omega)).symm

private lemma faceAdj_top_eq (S : KuhnSimplex n p) (hn : n ≠ 0) :
    S.faceAdj ⟨n, by omega⟩ =
      if hb : (S.base (S.perm ⟨n - 1, by omega⟩)).val = 0 then none
      else some ⟨Function.update S.base (S.perm ⟨n - 1, by omega⟩)
          ⟨(S.base (S.perm ⟨n - 1, by omega⟩)).val - 1, by omega⟩,
        (finRotate n).symm.trans S.perm⟩ := by
  unfold faceAdj; simp only [hn, ↓reduceDIte]

private lemma faceAdj_bot_eq (S : KuhnSimplex n p) (hn : n ≠ 0) :
    S.faceAdj ⟨0, by omega⟩ =
      if hb : (S.base (S.perm ⟨0, Nat.pos_of_ne_zero hn⟩)).val + 1 ≥ p then none
      else some ⟨Function.update S.base (S.perm ⟨0, Nat.pos_of_ne_zero hn⟩)
          ⟨(S.base (S.perm ⟨0, Nat.pos_of_ne_zero hn⟩)).val + 1, by omega⟩,
        (finRotate n).trans S.perm⟩ := by unfold faceAdj; simp [hn]

theorem faceAdj_invol (S : KuhnSimplex n p) (hv : S.isValid) (k : Fin (n + 1))
    {S' : KuhnSimplex n p} (h : S.faceAdj k = some S') :
    ∃ k', S'.faceAdj k' = some S ∧
      (k.val = 0 → k'.val = n) ∧
      (k.val = n → k'.val = 0) ∧
      (k.val ≠ 0 → k.val ≠ n → k' = k) := by
  unfold faceAdj at h
  split_ifs at h with hn hk0 hb
  all_goals simp only [Fin.val_eq_zero_iff, dite_eq_ite, Option.ite_none_left_eq_some,
    Option.some.injEq, ge_iff_le, Option.dite_none_left_eq_some, not_le] at h

  · obtain ⟨_, hp⟩ := h; rw [← hp]
    have hn' : 0 < n := Nat.pos_of_ne_zero hn
    set j₀ := S.perm ⟨0, hn'⟩
    set S'' : KuhnSimplex n p := ⟨Function.update S.base j₀
        ⟨(S.base j₀).val + 1, by have := (S.base j₀).is_lt; omega⟩,
      (finRotate n).trans S.perm⟩
    refine ⟨⟨n, by omega⟩, ?_, fun _ => rfl,
      fun hkn' => by omega,
      fun h' => absurd hk0 h'⟩
    rw [faceAdj_top_eq _ hn]
    simp only [show S''.perm = (finRotate n).trans S.perm from rfl,
               show S''.base = Function.update S.base j₀ _ from rfl,
               Equiv.trans_apply,
               show S.perm ((finRotate n) ⟨n - 1, _⟩) = j₀ from by
                 rw [finRotate_pred_eq n hn' (by omega)],
               Function.update_self,
               show ¬ ((S.base j₀).val + 1 = 0) from by omega, dite_false]
    congr 1; cases S with | mk sb sp =>
    simp only [KuhnSimplex.mk.injEq]
    exact ⟨by
      change Function.update (Function.update sb (sp ⟨0, hn'⟩) _) (sp ⟨0, hn'⟩) _ = sb
      rw [Function.update_idem]
      convert Function.update_eq_self (sp ⟨0, hn'⟩) sb using 1
      congr 1,
     by
      change (finRotate n).symm.trans ((finRotate n).trans sp) = sp
      rw [← Equiv.trans_assoc, Equiv.symm_trans_self, Equiv.refl_trans]⟩

  · obtain ⟨hbne, hp⟩ := h; rw [← hp]
    have hn' : 0 < n := Nat.pos_of_ne_zero hn

    set jlast := S.perm ⟨n - 1, by omega⟩

    have hv_jlast := hv jlast

    have hbne_val : (S.base jlast).val ≠ 0 :=
      fun h0 => hbne (by ext; exact h0)
    set S'' : KuhnSimplex n p := ⟨Function.update S.base jlast
        ⟨(S.base jlast).val - 1, by omega⟩,
      (finRotate n).symm.trans S.perm⟩
    refine ⟨⟨0, by omega⟩, ?_, by intro h'; exact absurd h' hk0,
      fun _ => rfl,
      fun _ h' => absurd hb h'⟩
    rw [faceAdj_bot_eq _ hn]
    simp only [show S''.perm = (finRotate n).symm.trans S.perm from rfl,
               show S''.base = Function.update S.base jlast _ from rfl,
               Equiv.trans_apply,
               show S.perm ((finRotate n).symm ⟨0, _⟩) = jlast from by
                 rw [finRotate_symm_zero_eq n hn'],
               Function.update_self,
               show ¬ ((S.base jlast).val - 1 + 1 ≥ p) from by omega,
               dite_false]
    congr 1; cases S with | mk sb sp =>
    simp only [KuhnSimplex.mk.injEq]
    refine ⟨?_, ?_⟩
    · change Function.update (Function.update sb (sp ⟨n - 1, by omega⟩) _)
        (sp ⟨n - 1, by omega⟩) _ = sb
      rw [Function.update_idem]
      have hne : (sb (sp ⟨n - 1, by omega⟩)).val ≠ 0 :=
        fun h0 => hbne (by ext; exact h0)
      have : (⟨(sb (sp ⟨n - 1, by omega⟩)).val - 1 + 1,
          (by have := (sb (sp ⟨n - 1, by omega⟩)).is_lt; omega)⟩ : Fin (p + 1)) =
          sb (sp ⟨n - 1, by omega⟩) := by ext; simp; omega
      rw [this]; exact Function.update_eq_self _ _
    · change (finRotate n).trans ((finRotate n).symm.trans sp) = sp
      rw [← Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.refl_trans]

  · subst h
    refine ⟨k, ?_, fun h' => absurd h' hk0,
      fun h' => absurd h' hb,
      fun _ _ => rfl⟩
    unfold faceAdj
    simp only [hn, dite_false, hk0, hb]
    congr 1
    refine KuhnSimplex.mk.injEq .. |>.mpr ⟨rfl, ?_⟩
    rw [← Equiv.trans_assoc, Equiv.swap_swap, Equiv.refl_trans]

private lemma finRotate_symm_val_of_pos' {m : ℕ} (hm : 0 < m) (d : Fin m) (hd : 0 < d.val) :
    ((finRotate m).symm d).val = d.val - 1 := by
  have hlt : d.val - 1 < m := by omega
  suffices h : (finRotate m).symm d = ⟨d.val - 1, hlt⟩ by simp [h]
  apply Equiv.injective (finRotate m); rw [Equiv.apply_symm_apply]; ext
  cases m with
  | zero => omega
  | succ q => rw [finRotate_apply, Fin.val_add]; cases q with
    | zero => omega
    | succ q' =>
      rw [Fin.val_one, show d.val - 1 + 1 = d.val from by omega, Nat.mod_eq_of_lt d.isLt]

private lemma finRotate_symm_val_of_zero' {m : ℕ} (hm : 1 < m) :
    ((finRotate m).symm ⟨0, by omega⟩).val = m - 1 := by
  suffices h : (finRotate m).symm ⟨0, by omega⟩ = ⟨m - 1, by omega⟩ by simp [h]
  apply Equiv.injective (finRotate m); rw [Equiv.apply_symm_apply]; ext
  cases m with
  | zero => omega
  | succ q => rw [finRotate_apply, Fin.val_add]; cases q with
    | zero => omega
    | succ q' =>
      rw [Fin.val_one, show (q' + 1 + 1 - 1 : ℕ) + 1 = q' + 2 from by omega]
      exact (Nat.mod_self _).symm

theorem faceAdj_shared_vertices (S : KuhnSimplex n p) (hv : S.isValid)
    (k : Fin (n + 1)) {S' : KuhnSimplex n p} (h : S.faceAdj k = some S')
    (hv' : S'.isValid) :
    ∃ k', S'.faceAdj k' = some S ∧
      ∀ i : Fin (n + 1), i ≠ k →
        ∃ j : Fin (n + 1), j ≠ k' ∧
          S.vertex hv i = S'.vertex hv' j := by
  obtain ⟨k', hk', hk'_bot, hk'_top, hk'_int⟩ := S.faceAdj_invol hv k h
  refine ⟨k', hk', ?_⟩

  unfold faceAdj at h
  split_ifs at h with hn hk0 hb
  all_goals simp only [Fin.val_eq_zero_iff, dite_eq_ite, Option.ite_none_left_eq_some,
    Option.some.injEq, ge_iff_le, Option.dite_none_left_eq_some, not_le] at h
  ·
    obtain ⟨_, hp⟩ := h; subst hp
    have hn' : 0 < n := Nat.pos_of_ne_zero hn
    intro i hi
    have hi0 : i.val ≠ 0 := fun h0 => hi (Fin.ext (by omega))
    refine ⟨⟨i.val - 1, by have := i.isLt; omega⟩,
      by
        intro heq
        have := congr_arg Fin.val heq
        simp only [] at this
        have := hk'_bot hk0
        have := i.isLt;
        omega,
      ?_⟩

    ext c; simp only [vertex]
    show S.vertexVal i c = (⟨Function.update S.base _ ⟨(S.base _).val + 1, _⟩,
      (finRotate n).trans S.perm⟩ : KuhnSimplex n p).vertexVal ⟨i.val - 1, _⟩ c
    unfold vertexVal; simp only [Equiv.symm_trans_apply]
    by_cases hcj : c = S.perm ⟨0, hn'⟩
    · subst hcj
      simp only [Function.update_self, S.perm.symm_apply_apply]
      have hval : ((finRotate n).symm ⟨0, hn'⟩).val = n - 1 := by
        cases n with | zero => omega | succ m =>
        cases m with
        | zero => simp [finRotate_one]
        | succ m' => exact finRotate_symm_val_of_zero' (by omega)
      simp only [hval]; split_ifs <;> omega
    · rw [Function.update_of_ne hcj]
      have hd_ne : S.perm.symm c ≠ ⟨0, hn'⟩ :=
        fun h0 => hcj (by rw [← S.perm.apply_symm_apply c, h0])
      have hd_pos : 0 < (S.perm.symm c).val := Nat.pos_of_ne_zero (Fin.val_ne_of_ne hd_ne)
      have hrot : ((finRotate n).symm (S.perm.symm c)).val = (S.perm.symm c).val - 1 :=
        finRotate_symm_val_of_pos' hn' _ hd_pos
      simp only [hrot]
      split_ifs <;> omega
  ·
    obtain ⟨hbne, hp⟩ := h; subst hp
    have hn' : 0 < n := Nat.pos_of_ne_zero hn
    intro i hi
    have hin : i.val ≠ n := fun h0 => hi (Fin.ext (by omega))
    refine ⟨⟨i.val + 1, by omega⟩,
    by
      intro heq
      have := congr_arg Fin.val heq
      simp only [] at this
      have := hk'_top hb
      omega,
    ?_⟩

    ext c; simp only [vertex]
    show S.vertexVal i c = (⟨Function.update S.base _ ⟨(S.base _).val - 1, _⟩,
      (finRotate n).symm.trans S.perm⟩ : KuhnSimplex n p).vertexVal ⟨i.val + 1, _⟩ c
    unfold vertexVal; simp only [Equiv.symm_trans_apply, Equiv.symm_symm]
    by_cases hcj : c = S.perm ⟨n - 1, by omega⟩
    · subst hcj
      simp only [Function.update_self, S.perm.symm_apply_apply]
      have hval : ((finRotate n) ⟨n - 1, by omega⟩).val = 0 := by
        rw [finRotate_pred_eq n hn' (by omega)]
      simp only [hval]
      have hbpos : 0 < (S.base (S.perm ⟨n - 1, by omega⟩)).val :=
        Nat.pos_of_ne_zero (fun h => hbne (Fin.ext h))
      have hblt := (S.base (S.perm ⟨n - 1, by omega⟩)).is_lt
      split_ifs with h1 h2 <;> omega
    · rw [Function.update_of_ne hcj]
      have hd_ne : S.perm.symm c ≠ ⟨n - 1, by omega⟩ :=
        fun h0 => hcj (by rw [← S.perm.apply_symm_apply c, h0])
      have hrot : ((finRotate n) (S.perm.symm c)).val = (S.perm.symm c).val + 1 := by
        cases n with | zero => exact Fin.elim0 c | succ m =>
        apply coe_finRotate_of_ne_last
        rwa [show Fin.last m = ⟨m + 1 - 1, by omega⟩ from by simp [Fin.ext_iff, Fin.val_last]]
      simp only [hrot]; split_ifs <;> omega
  ·

    subst h
    intro i hi
    refine ⟨i, hk'_int hk0 hb ▸ hi, ?_⟩
    ext c; simp only [vertex, vertexVal]; congr 1
    have hi_val : i.val ≠ k.val := Fin.val_ne_of_ne hi

    have key : ((Equiv.swap ⟨k.val - 1, (by omega : k.val - 1 < n)⟩
        ⟨k.val, (by omega : k.val < n)⟩).trans S.perm).symm c =
      (Equiv.swap ⟨k.val - 1, (by omega : k.val - 1 < n)⟩
        ⟨k.val, (by omega : k.val < n)⟩) (S.perm.symm c) := by
      simp [Equiv.symm_swap]
    rw [key]
    set d := S.perm.symm c
    set km1 : Fin n := ⟨k.val - 1, by omega⟩
    set kf : Fin n := ⟨k.val, by omega⟩
    by_cases h1 : d = km1
    ·
      rw [h1, Equiv.swap_apply_left]
      split <;> split <;> simp_all [km1, kf] <;> omega
    · by_cases h2 : d = kf
      ·
        rw [h2, Equiv.swap_apply_right]
        split <;> split <;> simp_all [km1, kf] <;> omega
      ·
        rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

structure SpernerColoring (n p : ℕ) where
  color : (Fin n → Fin (p + 1)) → Fin (n + 1)
  proper : ∀ v : Fin n → Fin (p + 1), ∀ k : Fin n,
    (v k = 0 → color v ≠ k.castSucc) ∧
    (v k = Fin.last p → (color v).val ≤ k.val)

variable (SC : SpernerColoring n p)

def fullyColored (S : KuhnSimplex n p) (hv : S.isValid)
    (c : (Fin n → Fin (p + 1)) → Fin (n + 1)) : Prop :=
  Function.Surjective (fun k : Fin (n + 1) => c (S.vertex hv k))

def isRainbowFace (S : KuhnSimplex n p) (hv : S.isValid)
    (c : (Fin n → Fin (p + 1)) → Fin (n + 1)) (k : Fin (n + 1)) : Prop :=
  ∀ color : Fin n, ∃ i : Fin (n + 1), i ≠ k ∧
    c (S.vertex hv i) = color.castSucc

lemma fullyColored_rainbow_count (S : KuhnSimplex n p) (hv : S.isValid)
    (c : (Fin n → Fin (p + 1)) → Fin (n + 1))
    (hfc : S.fullyColored hv c) :
    ∃! k, S.isRainbowFace hv c k := by
  have hinj : Function.Injective (fun k : Fin (n + 1) => c (S.vertex hv k)) :=
    Finite.injective_iff_surjective.mpr hfc
  obtain ⟨k₀, hk₀⟩ := hfc (Fin.last n)
  change c (S.vertex hv k₀) = Fin.last n at hk₀
  use k₀
  constructor
  ·
    intro color
    obtain ⟨i, hi⟩ := hfc color.castSucc
    change c (S.vertex hv i) = color.castSucc at hi
    refine ⟨i, ?_, hi⟩
    intro heq; subst heq
    exact absurd (hi.symm.trans hk₀) (Fin.castSucc_ne_last color)
  ·
    intro k₁ hk₁
    by_contra hne
    choose i_c hi_c using hk₁
    have hinj_ic : Function.Injective i_c := by
      intro a b hab
      have ha := (hi_c a).2; have hb := (hi_c b).2
      rw [hab] at ha
      exact Fin.castSucc_injective n (ha.symm.trans hb)
    have hk₀_nr : ∀ c1 : Fin n, i_c c1 ≠ k₀ := by
      intro c1 heq; have := (hi_c c1).2; rw [heq] at this
      exact absurd (this.symm.trans hk₀) (Fin.castSucc_ne_last c1)

    let f' : Fin n → {x : Fin (n + 1) | x ≠ k₁} := fun c1 => ⟨i_c c1, (hi_c c1).1⟩
    have hf'_inj : Function.Injective f' := fun a b h => hinj_ic (Subtype.ext_iff.mp h)
    have hcard : Fintype.card (Fin n) = Fintype.card {x : Fin (n + 1) | x ≠ k₁} := by
      exact Fintype.card_congr (finSuccAboveEquiv k₁)
    have hf'_surj : Function.Surjective f' := by
      rwa [← Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hcard)]
    obtain ⟨c1, hc1⟩ := hf'_surj ⟨k₀, Ne.symm hne⟩
    exact hk₀_nr c1 (Subtype.ext_iff.mp hc1)

lemma not_fullyColored_rainbow_zero_or_two (S : KuhnSimplex n p) (hv : S.isValid)
    (c : (Fin n → Fin (p + 1)) → Fin (n + 1))
    (hnfc : ¬ S.fullyColored hv c) :
    (∀ k, ¬ S.isRainbowFace hv c k) ∨
    (∃ k₁ k₂, k₁ ≠ k₂ ∧ S.isRainbowFace hv c k₁ ∧ S.isRainbowFace hv c k₂ ∧
      ∀ k₃, S.isRainbowFace hv c k₃ → k₃ = k₁ ∨ k₃ = k₂) := by
  let f := fun k : Fin (n + 1) => c (S.vertex hv k)

  have hnsurj : ¬ Function.Surjective f := hnfc
  by_cases h_last : ∃ k, f k = Fin.last n
  ·

    left
    intro k hk
    unfold Function.Surjective at hnsurj; push Not at hnsurj
    obtain ⟨c₀, hc₀⟩ := hnsurj

    have hc₀_ne : c₀ ≠ Fin.last n := by
      intro heq; obtain ⟨k', hk'⟩ := h_last; exact hc₀ k' (heq ▸ hk')
    obtain ⟨c₀', hc₀'⟩ := (Fin.exists_castSucc_eq (i := c₀)).mpr hc₀_ne

    obtain ⟨i, _, hi⟩ := hk c₀'
    exact hc₀ i (hc₀' ▸ hi)
  ·
    push Not at h_last
    choose g hg using fun k => (Fin.exists_castSucc_eq (i := f k)).mpr (h_last k)

    have hninj : ¬ Function.Injective g := by
      intro hinj; exact absurd (Fintype.card_le_of_injective g hinj) (by simp)
    unfold Function.Injective at hninj; push Not at hninj
    obtain ⟨k₁, k₂, hgeq, hne⟩ := hninj

    let g₁ : {x : Fin (n + 1) | x ≠ k₁} → Fin n := fun x => g x.val
    have hcard₁ : Fintype.card {x : Fin (n + 1) | x ≠ k₁} = Fintype.card (Fin n) := by
      exact (Fintype.card_congr (finSuccAboveEquiv k₁)).symm
    by_cases hg₁_inj : Function.Injective g₁
    ·

      have hg₁_surj : Function.Surjective g₁ := by
        rwa [← Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hcard₁)]

      let g₂ : {x : Fin (n + 1) | x ≠ k₂} → Fin n := fun x => g x.val
      have hg₂_inj : Function.Injective g₂ := by
        intro ⟨a, ha⟩ ⟨b, hb⟩ (h : g a = g b)
        simp only [Subtype.mk.injEq]
        by_contra hab
        by_cases hak : a = k₁
        · have hbk : b ≠ k₁ := fun h' => hab (hak.trans h'.symm)
          have h1 : (⟨k₂, hne.symm⟩ : {x // x ≠ k₁}) = ⟨b, hbk⟩ :=
            hg₁_inj (show g k₂ = g b from hgeq.symm.trans (hak ▸ h))
          exact hb (Subtype.ext_iff.mp h1).symm
        · by_cases hbk : b = k₁
          · have h1 : (⟨k₂, hne.symm⟩ : {x // x ≠ k₁}) = ⟨a, hak⟩ :=
              hg₁_inj (show g k₂ = g a from hgeq.symm.trans (hbk ▸ h.symm))
            exact ha (Subtype.ext_iff.mp h1).symm
          · have h1 : (⟨a, hak⟩ : {x // x ≠ k₁}) = ⟨b, hbk⟩ := hg₁_inj h
            exact hab (Subtype.ext_iff.mp h1)
      have hg₂_surj : Function.Surjective g₂ := by
        have hcard₂ : Fintype.card {x : Fin (n + 1) | x ≠ k₂} = Fintype.card (Fin n) := by
          exact (Fintype.card_congr (finSuccAboveEquiv k₂)).symm
        rwa [← Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hcard₂)]
      right; use k₁, k₂, hne
      refine ⟨?_, ?_, ?_⟩
      ·
        intro color
        obtain ⟨⟨i, hi⟩, hgi⟩ := hg₁_surj color
        exact ⟨i, hi, by change f i = _; rw [← hg]; exact congrArg _ hgi⟩
      ·
        intro color
        obtain ⟨⟨i, hi⟩, hgi⟩ := hg₂_surj color
        exact ⟨i, hi, by change f i = _; rw [← hg]; exact congrArg _ hgi⟩
      ·
        intro k₃ hk₃
        by_contra h; push Not at h

        have : ∀ j, g j = g k₃ → j = k₃ := by
          intro j hj; by_contra hjne
          by_cases hjk : j = k₁
          · have hk₂k₃ : g k₂ = g k₃ := hgeq.symm.trans (hjk ▸ hj)
            have : (⟨k₂, hne.symm⟩ : {x : Fin (n+1) | x ≠ k₁}) =
                   ⟨k₃, h.1⟩ := hg₁_inj hk₂k₃
            exact h.2 (Subtype.ext_iff.mp this).symm
          · have : (⟨j, hjk⟩ : {x : Fin (n+1) | x ≠ k₁}) = ⟨k₃, h.1⟩ := hg₁_inj hj
            exact hjne (Subtype.ext_iff.mp this)
        obtain ⟨i, hi_ne, hi_eq⟩ := hk₃ (g k₃)
        exact hi_ne (this i (Fin.castSucc_injective n ((hg i).trans hi_eq)))
    ·

      left; intro k hk

      unfold Function.Injective at hg₁_inj; push Not at hg₁_inj
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab_g, hab_ne⟩ := hg₁_inj
      simp only [Subtype.mk.injEq, ne_eq, g₁] at hab_g hab_ne

      have hsurv : ∃ a' b', a' ≠ k ∧ b' ≠ k ∧ a' ≠ b' ∧ g a' = g b' := by
        by_cases hak : a ≠ k <;> by_cases hbk : b ≠ k <;> try simp only [not_not] at *
        · exact ⟨a, b, hak, hbk, hab_ne, hab_g⟩
        · by_cases hk₁k : k₁ ≠ k <;> try simp only [not_not] at *
          · by_cases hk₂k : k₂ ≠ k <;> try simp only [not_not] at *
            · exact ⟨k₁, k₂, hk₁k, hk₂k, hne, hgeq⟩
            · refine ⟨k₁, a, hk₁k, hak, Ne.symm ha, ?_⟩
              calc g k₁ = g k₂ := hgeq
                _ = g b := by rw [hk₂k, hbk]
                _ = g a := hab_g.symm
          · exact absurd (hk₁k.trans hbk.symm) (Ne.symm hb)
        · by_cases hk₁k : k₁ ≠ k <;> try simp only [not_not] at *
          · by_cases hk₂k : k₂ ≠ k <;> try simp only [not_not] at *
            · exact ⟨k₁, k₂, hk₁k, hk₂k, hne, hgeq⟩
            · refine ⟨k₁, b, hk₁k, hbk, Ne.symm hb, ?_⟩
              calc g k₁ = g k₂ := hgeq
                _ = g a := by rw [hk₂k, hak]
                _ = g b := hab_g
          · exact absurd (hk₁k.trans hak.symm) (Ne.symm ha)
        · exact absurd (hak.trans hbk.symm) hab_ne
      obtain ⟨a', b', ha'k, hb'k, ha'b', hga'b'⟩ := hsurv

      let gk : {x : Fin (n + 1) | x ≠ k} → Fin n := fun x => g x.val
      have hgk_ninj : ¬ Function.Injective gk := by
        intro hinj
        exact ha'b' (Subtype.ext_iff.mp (hinj (show gk ⟨a', ha'k⟩ = gk ⟨b', hb'k⟩ from hga'b')))

      have hcardk : Fintype.card {x : Fin (n + 1) | x ≠ k} = Fintype.card (Fin n) := by
        exact (Fintype.card_congr (finSuccAboveEquiv k)).symm
      have hgk_nsurj : ¬ Function.Surjective gk := by
        rwa [← Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hcardk)]

      unfold Function.Surjective at hgk_nsurj; push Not at hgk_nsurj
      obtain ⟨c_miss, hc_miss⟩ := hgk_nsurj
      obtain ⟨i, hi_ne, hi_eq⟩ := hk c_miss
      exact hc_miss ⟨i, hi_ne⟩ (Fin.castSucc_injective n ((hg i).trans hi_eq))

lemma faceAdj_preserves_valid (S : KuhnSimplex n p) (hv : S.isValid)
    (k : Fin (n + 1)) {S' : KuhnSimplex n p} (h : S.faceAdj k = some S') :
    S'.isValid := by
  unfold faceAdj at h
  split_ifs at h with hn hk0 hb
  all_goals simp only [Fin.val_eq_zero_iff, dite_eq_ite, Option.ite_none_left_eq_some,
    Option.some.injEq, ge_iff_le, Option.dite_none_left_eq_some, not_le] at h
  ·
    obtain ⟨_, hp⟩ := h; subst hp; intro j
    by_cases hj : j = S.perm ⟨0, Nat.pos_of_ne_zero hn⟩
    · subst hj; simp [Function.update_self]; omega
    · simp only [Function.update_of_ne hj]; exact hv j
  ·
    obtain ⟨_, hp⟩ := h; subst hp; intro j
    by_cases hj : j = S.perm ⟨n - 1, by omega⟩
    · subst hj; simp only [Function.update_self]; have := hv (S.perm ⟨n-1, by omega⟩); omega
    · simp only [Function.update_of_ne hj]; exact hv j
  ·
    subst h; exact hv

lemma faceAdj_ne (S : KuhnSimplex n p)
    (k : Fin (n + 1)) {S' : KuhnSimplex n p} (h : S.faceAdj k = some S') :
    S' ≠ S := by
  unfold faceAdj at h
  split_ifs at h with hn hk0 hb
  all_goals simp only [Fin.val_eq_zero_iff, dite_eq_ite, Option.ite_none_left_eq_some,
    Option.some.injEq, ge_iff_le, Option.dite_none_left_eq_some, not_le] at h
  ·
    obtain ⟨_, hp⟩ := h; subst hp
    intro heq
    have hbase := congr_arg KuhnSimplex.base heq
    have hval := congr_arg Fin.val (congr_fun hbase (S.perm ⟨0, Nat.pos_of_ne_zero hn⟩))
    simp only [Function.update_self, Fin.val_mk] at hval
    omega
  ·
    obtain ⟨hbne, hp⟩ := h; subst hp
    intro heq
    have hbase := congr_arg KuhnSimplex.base heq
    have hval := congr_arg Fin.val (congr_fun hbase (S.perm ⟨n - 1, by omega⟩))
    simp only [Function.update_self, Fin.val_mk] at hval
    have hne : (S.base (S.perm ⟨n - 1, by omega⟩)).val ≠ 0 :=
      fun h0 => hbne (Fin.ext h0)
    omega
  ·
    subst h; intro heq
    have hperm := congr_arg KuhnSimplex.perm heq
    simp only at hperm

    have hswap_ne : (⟨k.val - 1, by omega⟩ : Fin n) ≠ ⟨k.val, by omega⟩ := by
      simp [Fin.ext_iff]; omega

    have hswap_eq :
      Equiv.swap (⟨k.val - 1, by omega⟩ : Fin n) ⟨k.val, by omega⟩ = Equiv.refl _ := by
        ext x
        have := Equiv.ext_iff.mp hperm x
        simp [Equiv.trans_apply] at this
        simp [Equiv.refl_apply, this]
    rw [Equiv.swap_eq_refl_iff] at hswap_eq
    exact hswap_ne hswap_eq

private lemma adj_swap_eq_implies (k₁ k₂ : Fin (n + 1))
    (hk₁0 : k₁.val ≠ 0) (hk₁n : k₁.val ≠ n) (hk₂0 : k₂.val ≠ 0) (hk₂n : k₂.val ≠ n)
    (h : Equiv.swap (⟨k₁.val - 1, by omega⟩ : Fin n) ⟨k₁.val, by omega⟩ =
         Equiv.swap (⟨k₂.val - 1, by omega⟩ : Fin n) ⟨k₂.val, by omega⟩) :
    k₁ = k₂ := by
  have hab : (⟨k₁.val - 1, by omega⟩ : Fin n) ≠ ⟨k₁.val, by omega⟩ := by
    simp [Fin.ext_iff]; omega
  have h1 : (Equiv.swap (⟨k₂.val - 1, by omega⟩ : Fin n) ⟨k₂.val, by omega⟩)
      ⟨k₁.val, by omega⟩ = ⟨k₁.val - 1, by omega⟩ := by
    have := Equiv.ext_iff.mp h ⟨k₁.val, by omega⟩
    simp only [Equiv.swap_apply_right] at this; exact this.symm
  by_cases h2 : (⟨k₁.val, by omega⟩ : Fin n) = ⟨k₂.val - 1, by omega⟩
  · rw [h2, Equiv.swap_apply_left] at h1; simp [Fin.ext_iff] at h2 h1; omega
  · by_cases h3 : (⟨k₁.val, by omega⟩ : Fin n) = ⟨k₂.val, by omega⟩
    · simp only [Fin.ext_iff] at h3; exact Fin.ext h3
    · rw [Equiv.swap_apply_of_ne_of_ne h2 h3] at h1; exact absurd h1.symm hab

private lemma swap_of_trans_perm_eq (σ : Equiv.Perm (Fin n))
    (s₁ s₂ : Equiv.Perm (Fin n)) (h : s₁.trans σ = s₂.trans σ) : s₁ = s₂ :=
  Equiv.ext fun x => σ.injective (by have := congr_arg (· x) h; simpa [Equiv.trans_apply])

lemma faceAdj_injective (S : KuhnSimplex n p)
    (k₁ k₂ : Fin (n + 1)) {S' : KuhnSimplex n p}
    (h₁ : S.faceAdj k₁ = some S') (h₂ : S.faceAdj k₂ = some S') :
    k₁ = k₂ := by
  have hn : n ≠ 0 := by intro h; simp [faceAdj, h] at h₁
  unfold faceAdj at h₁ h₂; simp only [hn, ↓reduceDIte] at h₁ h₂
  by_cases hk₁0 : k₁.val = 0 <;> simp only [hk₁0, ↓reduceDIte] at h₁
  · split_ifs at h₁ with hb₁; rw [Option.some_inj] at h₁
    by_cases hk₂0 : k₂.val = 0
    · exact Fin.ext (by omega)
    · simp only [hk₂0, ↓reduceDIte] at h₂
      by_cases hk₂n : k₂.val = n <;> simp only [hk₂n, ↓reduceDIte] at h₂
      · split_ifs at h₂ with hb₂; rw [Option.some_inj] at h₂
        obtain ⟨hbase, _⟩ := (KuhnSimplex.mk.injEq ..).mp (h₁.trans h₂.symm)
        have h_at := congr_fun hbase (S.perm ⟨n - 1, by omega⟩)
        rw [Function.update_self, Function.update_apply] at h_at
        split_ifs at h_at with hjeq
        · simp only [Fin.ext_iff] at h_at; rw [← hjeq] at h_at; omega
        · simp [Fin.ext_iff] at h_at; omega
      · rw [Option.some_inj] at h₂
        obtain ⟨hbase, _⟩ := (KuhnSimplex.mk.injEq ..).mp (h₁.trans h₂.symm)
        have h_at := congr_fun hbase (S.perm ⟨0, Nat.pos_of_ne_zero hn⟩)
        rw [Function.update_self] at h_at; simp [Fin.ext_iff] at h_at
  · by_cases hk₁n : k₁.val = n <;> simp only [hk₁n, ↓reduceDIte] at h₁
    · split_ifs at h₁ with hb₁; rw [Option.some_inj] at h₁
      by_cases hk₂0 : k₂.val = 0 <;> simp only [hk₂0, ↓reduceDIte] at h₂
      · split_ifs at h₂ with hb₂; rw [Option.some_inj] at h₂
        obtain ⟨hbase, _⟩ := (KuhnSimplex.mk.injEq ..).mp (h₁.trans h₂.symm)
        have h_at := congr_fun hbase (S.perm ⟨0, Nat.pos_of_ne_zero hn⟩)
        rw [Function.update_self, Function.update_apply] at h_at
        split_ifs at h_at with hjeq
        · simp only [Fin.ext_iff] at h_at; rw [← hjeq] at h_at; omega
        · simp [Fin.ext_iff] at h_at
      · by_cases hk₂n : k₂.val = n <;> simp only [hk₂n, ↓reduceDIte] at h₂
        · exact Fin.ext (by omega)
        · rw [Option.some_inj] at h₂
          obtain ⟨hbase, _⟩ := (KuhnSimplex.mk.injEq ..).mp (h₁.trans h₂.symm)
          have h_at := congr_fun hbase (S.perm ⟨n - 1, by omega⟩)
          rw [Function.update_self] at h_at; simp [Fin.ext_iff] at h_at; omega
    · rw [Option.some_inj] at h₁
      by_cases hk₂0 : k₂.val = 0 <;> simp only [hk₂0, ↓reduceDIte] at h₂
      · split_ifs at h₂ with hb₂; rw [Option.some_inj] at h₂
        obtain ⟨hbase, _⟩ := (KuhnSimplex.mk.injEq ..).mp (h₁.trans h₂.symm)
        have h_at := congr_fun hbase (S.perm ⟨0, Nat.pos_of_ne_zero hn⟩)
        rw [Function.update_self] at h_at; simp [Fin.ext_iff] at h_at
      · by_cases hk₂n : k₂.val = n <;> simp only [hk₂n, ↓reduceDIte] at h₂
        · split_ifs at h₂ with hb₂; rw [Option.some_inj] at h₂
          obtain ⟨hbase, _⟩ := (KuhnSimplex.mk.injEq ..).mp (h₁.trans h₂.symm)
          have h_at := congr_fun hbase (S.perm ⟨n - 1, by omega⟩)
          rw [Function.update_self] at h_at; simp [Fin.ext_iff] at h_at; omega
        · rw [Option.some_inj] at h₂
          obtain ⟨_, hperm⟩ := (KuhnSimplex.mk.injEq ..).mp (h₁.trans h₂.symm)
          exact adj_swap_eq_implies k₁ k₂ hk₁0 hk₁n hk₂0 hk₂n
            (swap_of_trans_perm_eq S.perm _ _ hperm)

end KuhnSimplex
