/-
    Tasnia Kader
    May 10th, 2023

    ## Group Homomorphism from the Dihedral Group to the Orthogonal Group

    ## References

    * https://en.wikipedia.org/wiki/Dihedral_group
    * The zmod_to_angle code was taken from 
    https://github.com/leanprover-community/mathlib/pull/8559/files/
-/

import data.real.basic
import group_theory.specific_groups.dihedral
import data.matrix.basic
import analysis.special_functions.trigonometric.angle
import orthogonal_group
import special_orthogonal_group

open_locale matrix
open_locale orthogonal_matrix
open_locale special_orthogonal_matrix
open orthogonal_matrix
open special_orthogonal_matrix
open real.angle

universes u v
variables (m : Type u)(α : Type v)[decidable_eq m][fintype m][field α]
variables (n : ℕ)[fact (0 < n)]

open examples

noncomputable def zmod_to_angle : zmod n →+ real.angle :=
zmod.lift n ⟨zmultiples_hom real.angle ↑(2 * real.pi / n),
  begin
    suffices : n • (2 * real.pi / ↑n) = 2 * real.pi,
    { simpa using congr_arg (coe : _ → real.angle) this },
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (fact.out _ : 0 < n).ne',
    field_simp,
    ring,
end⟩

local notation `∠` x := (zmod_to_angle n x).to_real

noncomputable def dihedral_to_orth : dihedral_group n → O(2, ℝ)
| (dihedral_group.r i) := rotation_2D_orth (∠ i)
| (dihedral_group.sr i) := ref_x_rot_orth (∠ i)

lemma orth_presv_r_mul_r (d₁ d₂ : zmod n) : 
rotation_2D (∠ (d₁ + d₂)) = rotation_2D (∠ d₁) ⬝ rotation_2D (∠ d₂) :=
begin
  dsimp [rotation_2D],
  rw matrix.mul_fin_two,
  simp only [map_add, cos_to_real, sin_to_real, neg_mul, mul_neg, embedding_like.apply_eq_iff_eq],
  rw [tactic.ring.add_neg_eq_sub, ← cos_add, ← sin_add, ← neg_add],
  nth_rewrite 5 add_comm,
  rw ← sin_add,
  nth_rewrite 7 add_comm,
  rw [tactic.ring.add_neg_eq_sub, ← cos_add],
end 

lemma orth_presv_r_mul_sr (d₁ d₂ : zmod n) : 
ref_x_rot (∠ (d₂ - d₁)) = rotation_2D (∠ d₁) ⬝ ref_x_rot (∠ d₂) :=
begin
  dsimp [rotation_2D, ref_x_rot],
  rw matrix.mul_fin_two,
  ext, fin_cases i; fin_cases j; 
  simp only [map_sub, cos_to_real, sin_to_real, matrix.of_apply, 
  matrix.cons_val_zero, mul_neg, neg_mul],
  {rw [sub_eq_add_neg, cos_add, cos_neg, sin_neg], ring},
  {simp only [matrix.cons_val_one, matrix.head_cons],
  rw [sub_eq_add_neg, sin_add, cos_neg, sin_neg], ring},
  {simp only [matrix.cons_val_one, matrix.head_cons, matrix.cons_val_zero],
  rw [sub_eq_add_neg, sin_add, cos_neg, sin_neg], ring},
  {simp only [matrix.cons_val_one, matrix.head_cons],
  rw [sub_eq_add_neg, cos_add, cos_neg, sin_neg], ring},
end

lemma orth_presv_sr_mul_r (d₁ d₂ : zmod n) : 
ref_x_rot (∠ (d₁ + d₂)) = ref_x_rot (∠ d₁) ⬝ rotation_2D (∠ d₂) :=
begin
  dsimp [rotation_2D, ref_x_rot],
  rw matrix.mul_fin_two,
  ext, fin_cases i; fin_cases j; 
  simp only [map_add, cos_to_real, sin_to_real, matrix.of_apply, matrix.cons_val_zero, neg_mul],
  {rw cos_add, ring},
  {simp only [matrix.cons_val_one, matrix.head_cons, mul_neg, neg_neg],
  rw sin_add, ring},
  {simp only [matrix.cons_val_one, matrix.head_cons, mul_neg, neg_neg],
  simp only [matrix.cons_val_zero], rw sin_add},
  {simp only [matrix.cons_val_one, matrix.head_cons, mul_neg],
  rw cos_add, ring_nf},
end

lemma orth_presv_sr_mul_sr (d₁ d₂ : zmod n) : 
rotation_2D (∠ (d₂ - d₁)) = ref_x_rot (∠ d₁) ⬝ ref_x_rot (∠ d₂) :=
begin
  dsimp [rotation_2D, ref_x_rot],
  rw matrix.mul_fin_two,
  ext, fin_cases i; fin_cases j; 
  simp only [map_sub, cos_to_real, sin_to_real, matrix.of_apply, 
  matrix.cons_val_zero, mul_neg, neg_mul, neg_neg],
  {rw [sub_eq_add_neg, cos_add, cos_neg, sin_neg], ring},
  {simp only [matrix.cons_val_one, matrix.head_cons],
  rw [sub_eq_add_neg, sin_add, cos_neg, sin_neg], ring},
  {simp only [matrix.cons_val_one, matrix.head_cons, matrix.cons_val_zero],
  rw [sub_eq_add_neg, sin_add, cos_neg, sin_neg], ring},
  {simp only [matrix.cons_val_one, matrix.head_cons],
  rw [sub_eq_add_neg, cos_add, cos_neg, sin_neg], ring},
end

noncomputable def dihedral_orth_hom : dihedral_group n →* O(2, ℝ) :=
{
  to_fun := dihedral_to_orth n,
  map_one' :=
  begin 
    rw dihedral_group.one_def, 
    dsimp [dihedral_to_orth, rotation_2D_orth, rotation_2D],
    simp only [map_zero, real.angle.to_real_zero, real.cos_zero, real.sin_zero, neg_zero, matrix_one],
    refl,
  end,
  map_mul' := λ d₁ d₂, 
  begin
    cases d₁; cases d₂; simp,
    all_goals {simp only [dihedral_to_orth, reflect_2D_orth, rotation_2D_orth, ref_x_rot_orth]},
    {simp only [orth_presv_r_mul_r], refl},
    {simp only [orth_presv_r_mul_sr], refl},
    {simp only [orth_presv_sr_mul_r], refl},
    {simp only [orth_presv_sr_mul_sr], refl},
  end,
}