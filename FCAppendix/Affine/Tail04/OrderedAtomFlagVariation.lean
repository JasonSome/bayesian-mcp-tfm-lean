import FCAppendix.Affine.Tail04.OrderedAtomUniformCluster

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomFlagVariation
open MeasureTheory ProbabilityTheory Set Classical
open OriginalValues FiniteTailNoisyGame SourceTailNoisyFixedPoint
open CompactPromotionErrors ActiveGainUniformModulus IntegratedActiveFiniteGain
open scoped BigOperators

variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t) (N : ℕ)
local notation "Ds" => installOriginal D P t ht

def comparisonVariation (kind : Fin N→ Fin 4) (reg : Bool)
    (b : Fin ((Ds).count kind 1+1)→ℝ) (y : ℝ) : ℝ :=
  flagVariation (D.e0 reg) D.F (freezeFocal b 0 y) b+
    flagVariation (D.e0 reg) D.F (Function.update b 0 y) b

lemma comparisonVariation_nonneg (kind : Fin N→ Fin 4) (reg : Bool)
    (b : Fin ((Ds).count kind 1+1)→ℝ) (y : ℝ) :
    0≤ comparisonVariation D P t ht N kind reg b y :=
  add_nonneg (flagVariation_nonneg _ _ _ _) (flagVariation_nonneg _ _ _ _)

theorem exists_source_pair_modulus (C : ℝ) {e : ℝ} (he : 0< e) :
    ∃ δ : ℝ,0< δ ∧ ∀ kind : Fin N→ Fin 4,∀ reg : Bool,
      ∀ b d : Fin ((Ds).count kind 1+1)→ Icc (1:ℝ) C,
      (∀ k,|(b k:ℝ)-(d k:ℝ)|< δ) →
        flagVariation (D.e0 reg) D.F (fun k => (b k:ℝ)) (fun k => (d k:ℝ))< e := by
  have hex (q : (Fin N→ Fin 4)×Bool) :=
    exists_flagVariation_modulus (ι:=Fin ((Ds).count q.1 1+1)) (D.e0 q.2) D.F C he
  choose r hr hp using hex
  obtain ⟨δ,hδ,hδr⟩ := finite_common_radius r hr
  refine ⟨δ,hδ,?_⟩
  intro kind reg b d hbd
  apply hp (kind,reg) b d
  apply (dist_pi_lt_iff (hr (kind,reg))).mpr
  intro k
  simpa only [Subtype.dist_eq,Real.dist_eq] using (hbd k).trans_le (hδr (kind,reg))

theorem exists_source_flag_modulus (C : ℝ) {e : ℝ} (he : 0< e) :
    ∃ δ : ℝ,0< δ ∧ ∀ kind : Fin N→ Fin 4,∀ reg : Bool,∀ B : ℝ,B≤ C →
      ∀ b : Fin ((Ds).count kind 1+1)→ Icc (1:ℝ) B,
      ∀ y : Icc (1:ℝ) B,(b 0:ℝ)≤ y → (y:ℝ)-(b 0:ℝ)< δ →
        comparisonVariation D P t ht N kind reg (fun k => (b k:ℝ)) y< e := by
  have hex (q : (Fin N→ Fin 4)×Bool) :=
    exists_flagVariation_modulus (ι:=Fin ((Ds).count q.1 1+1))
      (D.e0 q.2) D.F C (e:=e/2) (by linarith)
  choose r hr hp using hex
  obtain ⟨δ,hδ,hδr⟩ := finite_common_radius r hr
  refine ⟨δ,hδ,?_⟩
  intro kind reg B hBC b y hy hnear
  let bC : Fin ((Ds).count kind 1+1)→ Icc (1:ℝ) C :=
    fun k => ⟨b k,(b k).2.1,(b k).2.2.trans hBC⟩
  let dC : Fin ((Ds).count kind 1+1)→ Icc (1:ℝ) C := fun k =>
    ⟨freezeFocal (fun j => (b j:ℝ)) 0 y k,
      (freezeFocal_bounds (fun j => (b j:ℝ)) 0 y (fun j => (b j).2) k).1,
      (freezeFocal_bounds (fun j => (b j:ℝ)) 0 y (fun j => (b j).2) k).2.trans hBC⟩
  let aC : Fin ((Ds).count kind 1+1)→ Icc (1:ℝ) C :=
    Function.update bC 0 ⟨y,y.2.1,y.2.2.trans hBC⟩
  have hdb : dist dC bC< r (kind,reg) := by
    apply (dist_pi_lt_iff (hr (kind,reg))).mpr
    intro k
    simpa only [Subtype.dist_eq,Real.dist_eq] using
      (freezeFocal_close (fun j => (b j:ℝ)) 0 y hy k).trans_lt
        (hnear.trans_le (hδr (kind,reg)))
  have hab : dist aC bC< r (kind,reg) := by
    apply (dist_pi_lt_iff (hr (kind,reg))).mpr
    intro k
    by_cases hk : k=0
    · subst k
      change |(y:ℝ)-(b 0:ℝ)|<_
      rw [abs_of_nonneg (sub_nonneg.mpr hy)]
      exact hnear.trans_le (hδr (kind,reg))
    · simpa only [aC,Function.update_of_ne hk,dist_self] using hr (kind,reg)
  have hd := hp (kind,reg) dC bC hdb
  have ha := hp (kind,reg) aC bC hab
  have heq : (fun k => (aC k:ℝ))=Function.update (fun k => (b k:ℝ)) 0 (y:ℝ) := by
    funext k
    by_cases hk : k=0 <;> simp [aC,bC,hk]
  change flagVariation (D.e0 reg) D.F
    (freezeFocal (fun j => (b j:ℝ)) 0 y) (fun j => (b j:ℝ))< e/2 at hd
  rw [heq] at ha
  change flagVariation (D.e0 reg) D.F
    (Function.update (fun j => (b j:ℝ)) 0 y) (fun j => (b j:ℝ))< e/2 at ha
  dsimp only [comparisonVariation]
  linarith

@[simp] theorem comparisonVariation_atNoise
    (eps : ℝ) (heps : 0< eps) (hsmall : eps< D.eps)
    (kind : Fin N→ Fin 4) (reg : Bool)
    (b : Fin ((Ds).count kind 1+1)→ℝ) (y : ℝ) :
    comparisonVariation (atNoise D eps heps hsmall) P t ht N kind reg b y=
      comparisonVariation D P t ht N kind reg b y := rfl

end FCAppendix.Affine.Tail04.OrderedAtomFlagVariation
