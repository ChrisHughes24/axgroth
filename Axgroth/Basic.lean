import Mathlib

open Topology

lemma tendsto_inv_cobounded {𝕜 : Type*} [NormedDivisionRing 𝕜] :
    Filter.Tendsto (.⁻¹) (𝓝[≠] (0 : 𝕜)) (Bornology.cobounded 𝕜) := by
  simp [Filter.Tendsto]

lemma thing {ι : Type*} [Fintype ι] [Nonempty ι] (f : (ι → ℂ) ≃ (ι → ℂ)) (hf : Continuous f)
    {s : Set (ι → ℂ)} (hs : Dense (f ⁻¹' s)) {x : ι → ℂ}
    (hg : Filter.Tendsto f.symm (𝓝[s] x) (Filter.cocompact _)) : False := by
  have : Filter.Tendsto f (𝓝[f ⁻¹' s] (f.symm x)) (𝓝[s] f (f.symm x)) :=
    tendsto_nhdsWithin_iff.2 ⟨hf.continuousAt.mono_left nhdsWithin_le_nhds,
        eventually_nhdsWithin_of_forall <| by simp⟩
  simp only [Equiv.apply_symm_apply] at this
  have : Filter.Tendsto (fun x => x) (𝓝[f ⁻¹' s] f.symm x) (Filter.cocompact _) := by
    simpa using hg.comp this
  simp only [Filter.Tendsto, Filter.map_id', Filter.le_def, Filter.mem_cocompact, mem_nhdsWithin,
    forall_exists_index, and_imp] at this
  rcases this (Metric.closedBall (f.symm x) 1)ᶜ (Metric.closedBall (f.symm x) 1)
    (by exact isCompact_closedBall (f.symm x) 1) (fun _ a => a) with ⟨U, hU⟩
  rcases Metric.isOpen_iff.1 hU.1 (f.symm x) hU.2.1 with ⟨ε, ε0, hε⟩
  rcases hs.exists_mem_open Metric.isOpen_ball
    ⟨f.symm x, show f.symm x ∈ Metric.ball (f.symm x) (min ε 1) by simp [ε0]⟩ with ⟨y, hy⟩
  have h1 := hU.2.2 (Set.mem_inter (hε (Metric.ball_subset_ball (by simp) hy.2)) hy.1)
  have h2 := hy.2
  simp only [Set.mem_compl_iff, Metric.mem_closedBall, not_le, Metric.mem_ball, lt_inf_iff] at h1 h2
  linarith

lemma thing' (f : ℂ ≃ ℂ) (hf : Continuous f) (x : ℂ)
    (hg : Filter.Tendsto f.symm (𝓝[≠] x) (Filter.cocompact _)) : False := by
  have : Filter.Tendsto f (𝓝[≠] (f.symm x)) (𝓝[≠] f (f.symm x)) :=
    tendsto_nhdsWithin_iff.2 ⟨hf.continuousAt.mono_left nhdsWithin_le_nhds,
        eventually_nhdsWithin_of_forall <| by simp +contextual [not_imp_not, eq_comm]⟩
  simp only [Equiv.apply_symm_apply] at this
  have : Filter.Tendsto (fun x => x) (𝓝[≠] f.symm x) (Filter.cocompact _) := by
    simpa using hg.comp this
  simp only [Filter.Tendsto, Filter.map_id', Filter.le_def, Filter.mem_cocompact, mem_nhdsWithin,
    forall_exists_index, and_imp] at this
  rcases this (Metric.closedBall (f.symm x) 1)ᶜ (Metric.closedBall (f.symm x) 1)
    (by exact isCompact_closedBall (f.symm x) 1) (fun _ a => a) with ⟨U, hU⟩
  rcases Metric.isOpen_iff.1 hU.1 (f.symm x) hU.2.1 with ⟨ε, ε0, hε⟩
  have : f.symm x + (↑(min (1 : ℝ) (ε / 2)) : ℂ) ∈ Metric.ball (f.symm x) ε := by
    simp [abs_of_nonneg (le_min zero_le_one (le_of_lt (half_pos ε0))), ε0]
  have := hU.2.2 (Set.mem_inter (hε this) (by simp [ne_of_gt ε0, min_eq_iff]))
  simp [abs_of_nonneg (le_min zero_le_one (le_of_lt (half_pos ε0)))] at this

lemma eq_zero_of_eqOn_nonempty_open {ι : Type*} (p : MvPolynomial ι ℂ) (U : Set (ι → ℂ))
    (hU : U.Nonempty) (u_open : IsOpen U) (U0 : ∀ x ∈ U, p.eval x = 0) : p = 0 := by
  rw [isOpen_pi_iff] at u_open
  rcases hU with ⟨x, hx⟩
  rcases u_open x hx with ⟨H, u, hIu⟩
  let v : ι → Set ℂ := fun i => by classical exact if i ∈ H then u i else Set.univ
  exact MvPolynomial.funext_set v (p := p) (q := 0)
    (by
      intro i
      simp only [v]
      split_ifs with hH
      · refine infinite_of_mem_nhds (x i) ?_
        rw [mem_nhds_iff]
        use u i
        simp [hIu.1 i hH]
      · exact Set.infinite_univ)
    (by
      intro y hy
      simp at hy
      simp only [map_zero]
      apply U0
      apply hIu.2
      simp
      intro i Hi
      simp [v] at hy
      exact hy i Hi)

lemma dense_zero {ι : Type*} {p : MvPolynomial ι ℂ} (p0 : p ≠ 0) : Dense { x : ι → ℂ | p.eval x ≠ 0 } := by
  rw [dense_iff_inter_open]
  intro U u_open u_none
  by_contra h
  simp only [ne_eq, Set.nonempty_iff_ne_empty, Set.ext_iff, Set.mem_inter_iff, Set.mem_setOf_eq,
    Set.mem_empty_iff_false, iff_false, not_and, Decidable.not_not, not_forall, not_exists] at h
  apply p0
  exact eq_zero_of_eqOn_nonempty_open p U u_none u_open h

section MvPolynomial

open MvPolynomial

variable {K L ι : Type*} [Field K] [Field L]

lemma injective_iff_mem_radical [Finite ι] [Algebra K L] [IsAlgClosed L] {p : ι → MvPolynomial ι K} :
    Function.Injective (fun x i => (aeval x (p i) : L)) ↔
    (∀ i : ι, ((.X (Sum.inl i) : MvPolynomial (ι ⊕ ι) K) - .X (Sum.inr i)) ∈
      Ideal.radical (Ideal.span (Set.range (fun i : ι => (p i).rename Sum.inl -
        (p i).rename Sum.inr)))) := by
  simp only [Function.Injective, funext_iff, ← vanishingIdeal_zeroLocus_eq_radical (K := L),
    zeroLocus_span, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff, map_sub, aeval_rename,
    Function.comp_def, sub_eq_zero, mem_vanishingIdeal_iff, Set.mem_setOf_eq, aeval_X, Sum.forall_sum]
  exact ⟨fun h _ _ _ h2 => h h2 _, fun h _ _ h2 _ => h _ _ _ h2⟩

lemma bijective_of_injective_on_isAlgClosed [Finite ι] [IsAlgClosed L] [Algebra K L] [CharZero K]
    (p : ι → MvPolynomial ι K) (hInj : Function.Injective (fun x i => (aeval x (p i) : L))) :
    Function.Bijective (fun x i => eval x (p i)) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have (x : ι → K) : (aeval (fun j => algebraMap K L (x j))).toRingHom = (algebraMap K L).comp (eval x) := by ext <;> simp
    replace hInj := @hInj (fun j => algebraMap K L (x j)) (fun j => algebraMap K L (y j))
    simp only [AlgHom.toRingHom_eq_coe, RingHom.ext_iff, RingHom.coe_coe, RingHom.coe_comp,
      Function.comp_apply] at this
    simp only [this, funext_iff, algebraMap.coe_inj] at hInj hxy
    ext
    apply hInj
    exact hxy
  · replace hInj : Function.Injective (fun x i => (aeval x (p i) : AlgebraicClosure K)) := by
      simpa only [injective_iff_mem_radical] using hInj
    intro x
    simp only [aeval_def, ← eval_map] at hInj
    rcases ax_grothendieck_univ (fun i => (p i).map (algebraMap K (AlgebraicClosure K))) hInj
      (fun i => algebraMap _ _ (x i)) with ⟨y, hy⟩
    simp only [eval_map, ← aeval_def, funext_iff] at hy
    have : IntermediateField.fixedField (F := K) (E := AlgebraicClosure K) ⊤ = ⊥ :=
      InfiniteGalois.fixedField_bot
    simp only [IntermediateField.ext_iff, IntermediateField.mem_fixedField_iff, Subgroup.mem_top,
      forall_const] at this
    have : ∀ i, y i ∈ (⊥ : IntermediateField K (AlgebraicClosure K)) := by
      intro i
      rw [← this]
      intro f
      have hom_eq : ∀ x : ι → AlgebraicClosure K,
        aeval (fun i => f (x i)) = f.toAlgHom.comp (aeval x) := by
        intros; ext; simp
      have := @hInj y (fun i => f (y i))
      simp only [eval_map, ← aeval_def, hy, hom_eq, AlgEquiv.toAlgHom_eq_coe, AlgHom.comp_apply,
        AlgHom.commutes, funext_iff, forall_const] at this
      rw [← this]
    simp only [IntermediateField.mem_bot, Set.mem_range, Classical.skolem] at this
    rcases this with ⟨z, hz⟩
    use z
    ext i
    have : (aeval y).toRingHom = (algebraMap K (AlgebraicClosure K)).comp (eval z) := by
      ext
      simp
      simp [← hz]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.ext_iff, RingHom.coe_coe, RingHom.coe_comp,
      Function.comp_apply] at this
    apply RingHom.injective (algebraMap K (AlgebraicClosure K))
    rw [← hy, this]

section FractionRing

variable [Algebra K ℂ]

def NonZeroDenom (r : FractionRing (MvPolynomial ι K)) (x : ι → ℂ) : Prop :=
  ∃ p : MvPolynomial ι K × MvPolynomial ι K,
      r * algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)) p.2 =
      algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)) p.1 ∧
      p.2.aeval x ≠ 0

noncomputable def evalFractionRing (r : FractionRing (MvPolynomial ι K)) (x : ι → ℂ) : ℂ := by
  classical exact
    if h : NonZeroDenom r x
    then let (p, q) := Classical.choose h; p.aeval x / q.aeval x
    else 0

lemma evalFractionRing_eq_of_eq (r : FractionRing (MvPolynomial ι K)) (x : ι → ℂ)
    (p q : MvPolynomial ι K)
    (h : r * algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)) q =
      algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)) p)
    (hq : q.aeval x ≠ 0) :
    evalFractionRing r x = p.aeval x / q.aeval x := by
  rw [evalFractionRing]
  have : ∃ p : MvPolynomial ι K × MvPolynomial ι K,
      r * algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)) p.2 =
      algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)) p.1 ∧
      p.2.aeval x ≠ 0 := ⟨(p, q), h, hq⟩
  delta NonZeroDenom
  rw [dif_pos this]
  simp only [ne_eq]
  have psec := Classical.choose_spec this
  rw [div_eq_div_iff psec.2 hq]
  rw [← map_mul, ← map_mul]
  congr 1
  apply_fun (algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)))
  · rw [map_mul, map_mul, ← psec.1, ← h]
    simp [mul_comm, mul_assoc, mul_left_comm]
  · intro _; simp

@[simp]
lemma evalFractionRing_algebraMap (a : K) (x : ι → ℂ) :
    evalFractionRing (algebraMap K (FractionRing (MvPolynomial ι K)) a) x = algebraMap K ℂ a := by
  rw [evalFractionRing_eq_of_eq _ x (.C a) 1 (by simp; rfl) (by simp)]
  simp

@[simp]
lemma evalFractionRing_X (x : ι → ℂ) (i : ι) :
    evalFractionRing (algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)) (X i)) x = x i := by
  rw [evalFractionRing_eq_of_eq _ x (.X i) 1 (by simp) (by simp)]
  simp

lemma nonZeroDenom_add {r₁ r₂ : FractionRing (MvPolynomial ι K)} {x : ι → ℂ} :
    NonZeroDenom r₁ x → NonZeroDenom r₂ x → NonZeroDenom (r₁ + r₂) x := by
  rintro ⟨⟨p₁, q₁⟩, h₁⟩ ⟨⟨p₂, q₂⟩, h₂⟩
  use ((p₁ * q₂ + p₂ * q₁), q₁ * q₂)
  simp [h₁.2, h₂.2, add_mul]
  rw [← mul_assoc, h₁.1, ← mul_assoc, mul_right_comm, h₂.1]

lemma evalFractionRing_add {r₁ r₂ : FractionRing (MvPolynomial ι K)} {x : ι → ℂ} :
    NonZeroDenom r₁ x → NonZeroDenom r₂ x →
    evalFractionRing (r₁ + r₂) x = evalFractionRing r₁ x + evalFractionRing r₂ x := by
  rintro ⟨⟨p₁, q₁⟩, h₁⟩ ⟨⟨p₂, q₂⟩, h₂⟩
  have := evalFractionRing_eq_of_eq (r₁ + r₂) x (p₁ * q₂ + p₂ * q₁) (q₁ * q₂)
  rw [evalFractionRing_eq_of_eq r₁ x p₁ q₁ h₁.1 h₁.2,
    evalFractionRing_eq_of_eq r₂ x p₂ q₂ h₂.1 h₂.2]
  simp only [ne_eq] at h₁ h₂
  simp [h₁.2, h₂.2, add_mul] at this
  rw [← mul_assoc, h₁.1, ← mul_assoc, mul_right_comm, h₂.1] at this
  replace this := this rfl
  rw [this, div_add_div _ _ (by simp [h₁.2]) (by simp [h₂.2])]
  ring_nf

lemma nonZeroDenom_mul {r₁ r₂ : FractionRing (MvPolynomial ι K)} {x : ι → ℂ} :
    NonZeroDenom r₁ x → NonZeroDenom r₂ x → NonZeroDenom (r₁ * r₂) x := by
  rintro ⟨⟨p₁, q₁⟩, h₁⟩ ⟨⟨p₂, q₂⟩, h₂⟩
  use (p₁ * p₂, q₁ * q₂)
  simp [h₁.2, h₂.2]
  rw [← h₁.1, ← h₂.1]; ring

lemma evalFractionRing_mul {r₁ r₂ : FractionRing (MvPolynomial ι K)} {x : ι → ℂ} :
    NonZeroDenom r₁ x → NonZeroDenom r₂ x →
    evalFractionRing (r₁ * r₂) x = evalFractionRing r₁ x * evalFractionRing r₂ x := by
  rintro ⟨⟨p₁, q₁⟩, h₁⟩ ⟨⟨p₂, q₂⟩, h₂⟩
  have := evalFractionRing_eq_of_eq (r₁ * r₂) x (p₁ * p₂) (q₁ * q₂)
  rw [evalFractionRing_eq_of_eq r₁ x p₁ q₁ h₁.1 h₁.2,
    evalFractionRing_eq_of_eq r₂ x p₂ q₂ h₂.1 h₂.2]
  simp only [ne_eq] at h₁ h₂
  simp [h₁.2, h₂.2] at this
  rw [← h₁.1, ← h₂.1] at this
  replace this := this (by ring)
  rw [this]
  ring_nf

lemma nonZeroDenom_aeval (p : MvPolynomial ι K)
    (r : ι → FractionRing (MvPolynomial ι K)) (x : ι → ℂ)
    (hr : ∀ i, NonZeroDenom (r i) x)  :
    NonZeroDenom (p.aeval r) x := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    use (.C a, 1)
    simp; rfl
  | add p q ihp ihq =>
    rw [map_add]
    exact nonZeroDenom_add ihp ihq
  | mul_X i p ihp =>
    rw [map_mul, aeval_X]
    exact nonZeroDenom_mul ihp (hr p)

lemma evalFractionRing_aeval (p : MvPolynomial ι K)
    (r : ι → FractionRing (MvPolynomial ι K)) (x : ι → ℂ)
    (hr : ∀ i, NonZeroDenom (r i) x)  :
    evalFractionRing (p.aeval r) x = p.aeval (fun i => evalFractionRing (r i) x) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q ihp ihq =>
    rw [map_add, map_add, ← ihp, ← ihq]
    refine (evalFractionRing_add ?_ ?_)
    · exact nonZeroDenom_aeval p r x hr
    · exact nonZeroDenom_aeval q r x hr
  | mul_X i p ihp =>
    rw [map_mul, aeval_X, map_mul, aeval_X, ← ihp]
    refine evalFractionRing_mul ?_ (hr p)
    exact nonZeroDenom_aeval i r x hr

end FractionRing

lemma exists_MvRatFunc_inverse [Finite ι] [Algebra K ℂ]
    (p : ι → MvPolynomial ι K)
    (hInj : Function.Injective (fun x i => (aeval x (p i) : ℂ))) :
    ∃ r : ι → FractionRing (MvPolynomial ι K),
      ∀ (x : ι → ℂ), (∀ i, NonZeroDenom (r i) x) →
      ∀ i, (p i).aeval (fun i => evalFractionRing (r i) x) = x i := by
  have : CharZero K := RingHom.charZero (algebraMap K ℂ)
  have := (bijective_of_injective_on_isAlgClosed (K := FractionRing (MvPolynomial ι K))
    (L := AlgebraicClosure (FractionRing (MvPolynomial ι K))) (ι := ι)
    (fun i => (p i).map (algebraMap _ _))
    (by
      let : Algebra K (AlgebraicClosure (FractionRing (MvPolynomial ι K))) :=
        Algebra.compHom _ (algebraMap K (FractionRing (MvPolynomial ι K)))
      have : (algebraMap (FractionRing (MvPolynomial ι K)) (AlgebraicClosure (FractionRing (MvPolynomial ι K)))).comp
        (algebraMap K ((FractionRing (MvPolynomial ι K)))) = algebraMap _ _ := rfl
      simp only [aeval_def, ← eval_map, map_map, this]
      simp only [eval_map, ← aeval_def]
      simpa [injective_iff_mem_radical] using hInj)).2
    (fun i => algebraMap (MvPolynomial ι K) _ (MvPolynomial.X i))
  rcases this with ⟨r, hr⟩
  have hInj': Function.Injective (fun x i => eval x ((p i).map (algebraMap K ℂ ))) := by
    convert hInj; simp [aeval_def]
  simp only [eval_map, ← aeval_def] at hr
  use r
  intro x hx i
  rw [← evalFractionRing_aeval _ _ _ hx]
  simp only [funext_iff] at hr
  rw [hr]
  rw [evalFractionRing_X]
