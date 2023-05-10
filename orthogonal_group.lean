/-
    Tasnia Kader
    May 10th, 2023

    ## Orthogonal Group

    ## References

    * [Anne Baanen, *special_linear_group*][baanen2020]
    * https://en.wikipedia.org/wiki/Orthogonal_group
-/

import data.real.basic
import data.finsupp.fintype
import data.matrix.basic
import linear_algebra.matrix.nonsingular_inverse
import analysis.inner_product_space.basic
import data.matrix.notation
import analysis.matrix
import data.finset.fin
import analysis.inner_product_space.pi_L2
import data.is_R_or_C.basic
import analysis.inner_product_space.adjoint
import geometry.euclidean.angle.unoriented.basic
import algebra.group.defs
import auxiliary_theorems

namespace orthogonal_matrix
universes u v
variables (m : Type u)(α : Type v)
variables [decidable_eq m][fintype m][field α]

open_locale matrix

section

def orthogonal := { A : matrix m m α // A.mul Aᵀ = 1}

end

localized "notation `O(` m `,` α `)`:= orthogonal_matrix.orthogonal (fin m) α" in orthogonal_matrix

namespace orthogonal

-- Instances

instance has_coe_to_matrix : has_coe (orthogonal m α) (matrix m m α) :=
⟨λ A, A.val⟩

local prefix `↑ₘ`:1024 := @coe _ (matrix m m α) _

lemma ext_iff (A B : orthogonal m α) : A = B ↔ (∀ i j, ↑ₘA i j = ↑ₘB i j) := 
by rw [subtype.ext_iff, matrix.ext_iff]

instance has_one : has_one (orthogonal m α) :=
⟨⟨1, by rw [matrix.transpose_one, matrix.one_mul]⟩⟩

instance has_inv : has_inv (orthogonal m α) :=
⟨λ A, ⟨(↑ₘA)ᵀ, by {simp, rw [matrix.mul_eq_one_comm, A.prop]}⟩⟩

instance has_mul : has_mul (orthogonal m α) :=
⟨λ A B, ⟨↑ₘA ⬝ ↑ₘB, by {simp [B.prop], rw [← matrix.mul_assoc, matrix.mul_assoc ↑ₘA, B.prop, matrix.mul_one, A.prop]}⟩⟩

instance has_pow : has_pow (orthogonal m α) ℕ :=
⟨λ A n, ⟨A ^ n, 
begin 
  rw matrix.transpose_pow,
  induction n with k hk,
  {repeat {rw pow_zero}, rw matrix.mul_one},
  {
    calc
      (↑ₘA) ^ k.succ ⬝ (↑ₘA)ᵀ ^ k.succ = (↑ₘA) ^ (k + 1) ⬝ (↑ₘA)ᵀ ^ (k + 1) : by refl
      ... = (↑ₘA) ^ (k + 1) ⬝ (↑ₘA)ᵀ ^ (1 + k) : by rw add_comm
      ... = (↑ₘA) ^ k ⬝ (↑ₘA) ^ 1 ⬝ ((↑ₘA)ᵀ ^ 1 ⬝ (↑ₘA)ᵀ ^ k) : by {repeat {rw pow_add, rw matrix.mul_eq_mul}}
      ... = (↑ₘA) ^ k ⬝ (↑ₘA ⬝ (↑ₘA)ᵀ) ⬝ (↑ₘA)ᵀ ^ k : by {simp only [pow_one], rw [matrix.mul_assoc, ← matrix.mul_assoc ↑ₘA, ← matrix.mul_assoc ((↑ₘA) ^ k)]}
      ... = (↑ₘA) ^ k ⬝ 1 ⬝ (↑ₘA)ᵀ ^ k : by rw A.prop
      ... = (↑ₘA) ^ k ⬝ (↑ₘA)ᵀ ^ k : by rw matrix.mul_one
      ... = 1 : by rw hk
  },
end⟩⟩ 

instance has_neg : has_neg (orthogonal m α) :=
⟨λ A, ⟨- ↑ₘA, by {simp only [matrix.transpose_neg, matrix.mul_neg, matrix.neg_mul, neg_neg], rw A.prop}⟩⟩ 

-- Coersion Lemmas

section coe_lemmas

variables (A B : orthogonal m α)

@[simp] lemma coe_mk (A : matrix m m α) (hA : A.mul Aᵀ = 1) :
  ↑(⟨A, hA⟩ : orthogonal m α) = A := rfl

@[simp] lemma inv_coe : ↑ₘ(A⁻¹) = (↑ₘA)ᵀ := rfl

@[simp] lemma coe_mul : ↑ₘ(A * B) = ↑ₘA ⬝ ↑ₘB := rfl

@[simp] lemma coe_one : ↑ₘ(1 : orthogonal m α) = (1 : matrix m m α) := rfl

lemma orth_prop : (↑ₘA)ᵀ.mul ↑ₘA = 1 := by rw [matrix.mul_eq_one_comm, A.prop]

lemma coe_inv : (↑ₘA)⁻¹ = (↑ₘA)ᵀ :=
by {have hA := orth_prop _ _ A, exact matrix.inv_eq_left_inv hA}

@[simp] lemma coe_inv_eq_inv_coe : (↑ₘA)⁻¹ = ↑ₘ(A⁻¹) := by rw [coe_inv, inv_coe]

@[simp] lemma coe_pow (n : ℕ) : ↑ₘ(A ^ n) = (↑ₘA) ^ n := rfl

end coe_lemmas

-- Orthogonal matrices form a group under multiplication

instance orth_monoid : monoid (orthogonal m α) :=
{
  one_mul := λ A, by {ext, simp only [coe_mul, coe_one, matrix.one_mul]},
  mul_one := λ A, by {ext, simp only [coe_mul, coe_one, matrix.mul_one]},
  mul_assoc := λ A B C, by {ext, simp only [coe_mul], rw matrix.mul_assoc},
  ..orthogonal.has_mul _ _,
  ..orthogonal.has_one _ _
}

instance orth_group : group (orthogonal m α) :=
{
  mul_left_inv := λ A, by {ext, simp only [coe_mul, inv_coe, coe_one], rw orth_prop},
  ..orthogonal.orth_monoid _ _,
  ..orthogonal.has_inv _ _ 
}

-- Linear Transformation from αᵐ → αᵐ 

def to_lin' : orthogonal m α →* (m → α) ≃ₗ[α] (m → α) :=
{
  to_fun := λ A, 
  begin 
    have h₀ := linear_equiv.of_linear (matrix.to_lin' ↑ₘA) (matrix.to_lin' ↑ₘ(A⁻¹)),
    apply h₀, 
    rw [← matrix.to_lin'_mul, inv_coe, A.prop, matrix.to_lin'_one],
    rw [← matrix.to_lin'_mul, inv_coe, orth_prop, matrix.to_lin'_one], 
  end,
  map_one' := by {simp only [matrix.to_lin'_one, inv_one, coe_one], exact rfl},
  map_mul' := λ A B, by {simp only [matrix.to_lin'_mul, inv_coe, mul_inv_rev, coe_mul], exact rfl},
} 

lemma to_lin'_apply (A : orthogonal m α) (u : m → α) :
  orthogonal.to_lin' m α A u = matrix.to_lin' ↑ₘA u := rfl

lemma to_lin'_to_linear_map (A : orthogonal m α) :
  ↑(orthogonal.to_lin' m α A) = matrix.to_lin' ↑ₘA := rfl

lemma to_lin'_symm_apply (A : orthogonal m α) (u : m → α) :
  (orthogonal.to_lin' m α A).symm u = matrix.to_lin' ↑ₘ(A⁻¹) u := rfl

lemma to_lin'_symm_to_linear_map (A : orthogonal m α) :
  ↑((orthogonal.to_lin' m α A).symm) = matrix.to_lin' ↑ₘ(A⁻¹) := rfl

lemma to_lin'_injective (A : orthogonal m α):
  function.injective (orthogonal.to_lin' m α A) :=
begin
  rintros a₁ a₂ h₀,
  repeat {rw to_lin'_apply at h₀},
  have h₁ : (matrix.to_lin' (↑ₘA)⁻¹).comp (matrix.to_lin' ↑ₘA) a₁ = 
  (matrix.to_lin' (↑ₘA)⁻¹).comp (matrix.to_lin' ↑ₘA) a₂,
  {rw ← matrix.to_lin'_mul, simp [h₀]},
  rw [← matrix.to_lin'_mul, coe_inv, orth_prop, matrix.to_lin'_one] at h₁,
  dsimp [linear_map.id] at h₁,
  exact h₁,
end

lemma to_lin'_surjective (A : orthogonal m α):
  function.surjective (orthogonal.to_lin' m α A) :=
begin
  intro b,
  use ((↑ₘA)ᵀ).mul_vec b,
  rw to_lin'_apply,
  simp only [matrix.to_lin'_apply, matrix.mul_vec_mul_vec, A.prop, matrix.one_mul_vec],
end

-- Properties of Orthogonal Matrices

-- The Determinant of Orthogonal Matrices is +/-1

theorem orth_det (A : orthogonal m α) : (↑ₘA).det = (1 : α) ∨ (↑ₘA).det = (-1 : α) :=  
begin
  have h₀ := matrix.det_one,
  rw [←A.prop, matrix.det_mul, matrix.det_transpose, ← pow_two] at h₀,
  apply sq_eq_one_iff.mp h₀,
end

-- Geometric Properties

variables (n : ℕ)(A : O(n, ℝ))
variables (u v : euclidean_space ℝ (fin n))

open inner_product_geometry

local prefix `↑ₙ`:1024 := @coe (O(n, ℝ)) (matrix (fin n) (fin n) ℝ) _

local notation `⟪`x`, `y`⟫ₑ` := euclidean_space.inner_product_space.inner x y
local notation `T ` := matrix.to_euclidean_lin (↑ₙA)

theorem orth_presv_inner : ⟪T u, T v⟫ₑ = ⟪u, v⟫ₑ :=
begin
  rw [← linear_map.adjoint_inner_left,
  ← matrix.to_euclidean_lin_conj_transpose_eq_adjoint],
  have h₀ : (↑ₙA)ᴴ = (↑ₙA)ᵀ,
  {exact rfl},
  rw [← linear_map.comp_apply, 
  matrix.to_euclidean_lin_eq_to_lin,
  ← matrix.to_lin_mul, h₀, orth_prop],
  simp only [matrix.to_lin_one, linear_map.id_coe, id.def],
end

def orth_if_presv_inner (B : matrix (fin n) (fin n) ℝ)
(h₀ : ∀ u v, ⟪B.to_euclidean_lin u, B.to_euclidean_lin v⟫ₑ = ⟪u, v⟫ₑ) : 
O(n, ℝ) := ⟨B,
begin
  have h₁ : ∀ u, ∀ (v : euclidean_space ℝ (fin n)), ⟪matrix.to_euclidean_lin (Bᴴ ⬝ B) u, v⟫ₑ = ⟪u, v⟫ₑ,
  {intros u v, 
  rw [matrix.to_euclidean_lin_eq_to_lin, 
  matrix.to_lin_mul _ _ _ Bᴴ B, 
  ← matrix.to_euclidean_lin_eq_to_lin,
  linear_map.comp_apply,
  matrix.to_euclidean_lin_conj_transpose_eq_adjoint,
  linear_map.adjoint_inner_left], apply h₀},
  have h₂ : ∀ u : euclidean_space ℝ (fin n), (matrix.to_euclidean_lin (Bᴴ ⬝ B)) u = u,
  {intro u, apply ext_inner_right ℝ (h₁ u)},
  have h₃ : ∀ u, (1 : matrix (fin n) (fin n) ℝ).to_euclidean_lin u = u,
  {intro u, rw [matrix.to_euclidean_lin_eq_to_lin, matrix.to_lin_one, linear_map.id_apply]},
  have h₄ : ∀ u, (Bᴴ ⬝ B).to_euclidean_lin u = (1 : matrix (fin n) (fin n) ℝ).to_euclidean_lin u,
  {intro u, rw h₂ u, rw h₃ u},
  rw matrix.to_euclidean_lin_eq_to_lin at h₄,
  have h₅ : (Bᴴ ⬝ B).to_euclidean_lin = (1 : matrix (fin n) (fin n) ℝ).to_euclidean_lin,
  {rw matrix.to_euclidean_lin_eq_to_lin, apply linear_map.ext h₄},
  rw matrix.mul_eq_one_comm,
  have h₆ : Bᴴ = Bᵀ,
  {exact rfl},
  rw h₆ at h₅,
  rw matrix.to_euclidean_lin_eq_to_lin at h₅,
  apply inj n h₅,
end⟩

theorem orth_presv_norm : ‖ T u ‖ = ‖ u ‖ := 
by {repeat {rw [norm_eq_sqrt_real_inner]}, rw orth_presv_inner}

theorem orth_presv_dist : dist (T u) (T v) = dist u v :=
begin
  repeat {rw dist_eq_norm},
  rw ← linear_map.map_sub,
  exact orth_presv_norm n A (u - v),
end

theorem orth_is_iso : isometry ( T ) :=
by {apply isometry.of_dist_eq, apply orth_presv_dist n A}

theorem orth_presv_angle : angle u v = angle (T u) (T v) :=
begin
  repeat {rw inner_product_geometry.angle},
  rw orth_presv_inner,
  repeat {rw orth_presv_norm},
end

def orth_to_GL : orthogonal m α →* linear_map.general_linear_group α (m → α) := 
begin
  have h₀ := (linear_map.general_linear_group.general_linear_equiv α (m → α)).symm,
  have h₁ := orthogonal.to_lin' m α,
  have h₂ := mul_equiv.to_monoid_hom h₀,
  apply monoid_hom.comp h₂ h₁,
end

end orthogonal

end orthogonal_matrix

namespace examples

-- Examples of Orthogonal Matrices

variables (n : ℕ)(θ φ : ℝ)

open orthogonal_matrix orthogonal_matrix.orthogonal
open_locale orthogonal_matrix

-- Reflection

noncomputable def reflect_2D_orth : O(2, ℝ) := ⟨reflect_2D θ,
begin
  dsimp [reflect_2D], 
  rw [matrix_transpose, matrix.mul_fin_two], 
  ring_nf, 
  simp only [real.cos_sq_add_sin_sq, matrix_one],
end⟩

-- Rotation

noncomputable def rotation_2D_orth : O(2, ℝ) := ⟨rotation_2D θ, 
begin
  dsimp [rotation_2D], 
  rw [matrix_transpose, matrix.mul_fin_two], 
  ring_nf, 
  simp only [real.cos_sq_add_sin_sq, matrix_one],
end⟩  

-- Rotation & Reflection

noncomputable def rotoreflection_2D_orth : O(2, ℝ) := ⟨rotoreflection_2D θ φ, 
begin 
  dsimp [rotoreflection_2D, rotation_2D, reflect_2D], 
  rw [matrix.mul_fin_two, matrix_transpose, matrix.mul_fin_two, real.sin_two_mul, real.cos_two_mul],
  ring_nf,
  rw real.sin_sq,
  ring_nf,
  simp only [real.cos_sq_add_sin_sq, matrix_one],
end⟩ 

noncomputable def reflrotation_2D_orth : O(2, ℝ) := ⟨reflrotation_2D θ φ, 
begin 
  dsimp [reflrotation_2D, rotation_2D, reflect_2D], 
  rw [matrix.mul_fin_two, matrix_transpose, matrix.mul_fin_two, real.sin_two_mul, real.cos_two_mul],
  ring_nf,
  rw real.sin_sq,
  ring_nf,
  rw [sub_eq_add_neg, ← add_assoc (4 * real.cos φ ^ 2), 
  ← mul_add (4) (real.cos φ ^ 2)  (real.sin φ ^ 2)],
  simp only [real.cos_sq_add_sin_sq, mul_one, add_right_neg, zero_mul, zero_add, matrix_one],
end⟩ 

noncomputable def ref_x_rot_orth : O(2, ℝ) := ⟨ref_x_rot θ, 
begin
  dsimp [ref_x_rot],
  rw [matrix_transpose, matrix.mul_fin_two],
  ring_nf,
  simp only [real.cos_sq_add_sin_sq, matrix_one],
end⟩ 

end examples

